#include "llvm_codegen.h"
#include "llvm_jit.h"
#include "../builtins_internal.h"
#include <llvm-c/Analysis.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Apply a named enum fn-attribute (e.g. "nounwind", "willreturn") to `fn`.
// Silently skips if the LLVM build doesn't know the attribute kind.
static void add_fn_attr(valk_llvm_ctx_t *c, LLVMValueRef fn, const char *name) {
  unsigned kind = LLVMGetEnumAttributeKindForName(name, strlen(name));
  if (kind == 0) return;
  LLVMAttributeRef attr = LLVMCreateEnumAttribute(c->ctx, kind, 0);
  LLVMAddAttributeAtIndex(fn, LLVMAttributeFunctionIndex, attr);
}

// Encoded `memory(argmem: read)` for the LLVM `memory` attribute. LLVM 16+
// replaced readonly/readnone/argmemonly with a single memory attribute
// carrying a bitmask of MemoryEffects. Layout: 3 locations × 2 bits —
// ArgMem(0), InaccessibleMem(1), Other(2); each slot holds {NoModRef=0,
// Ref=1, Mod=2, ModRef=3}. "argmem: read" ⇒ ArgMem=Ref, rest=NoModRef ⇒
// bitmask = Ref << (ArgMem * 2) = 1.
#define VALK_MEMEFFECTS_ARGMEM_READ ((uint64_t)1)

static void add_argmem_read_attr(valk_llvm_ctx_t *c, LLVMValueRef fn) {
  unsigned kind = LLVMGetEnumAttributeKindForName("memory", 6);
  if (kind == 0) return;
  LLVMAttributeRef attr = LLVMCreateEnumAttribute(
    c->ctx, kind, VALK_MEMEFFECTS_ARGMEM_READ);
  LLVMAddAttributeAtIndex(fn, LLVMAttributeFunctionIndex, attr);
}

// Every runtime helper we emit is a plain C function — no C++ exceptions,
// no longjmp up the call chain — so `nounwind` is always safe. `willreturn`
// is safe for every helper we declare: allocators + env ops do finite work;
// eval/eval_call terminate under the tree walker's recursion invariants.
// Allocators intentionally do NOT get `readnone`/`readonly` — CSE on
// `valk_lval_num(0)` would alias two allocations to one pointer. Only
// genuinely pure readers (`valk_lval_is_truthy`) get the memory attrs.
static void mark_nounwind_willreturn(valk_llvm_ctx_t *c, LLVMValueRef fn) {
  add_fn_attr(c, fn, "nounwind");
  add_fn_attr(c, fn, "willreturn");
}

void valk_llvm_declare_runtime_fns(valk_llvm_ctx_t *c) {
  LLVMTypeRef ptr = c->ptr_type;
  LLVMTypeRef i64 = c->i64_type;
  LLVMTypeRef i1 = c->i1_type;
  LLVMTypeRef vd = c->void_type;
  LLVMTypeRef p1[] = {ptr};
  LLVMTypeRef p2[] = {ptr, ptr};
  LLVMTypeRef p3[] = {ptr, ptr, ptr};

  c->fn_lval_num = LLVMAddFunction(c->module, "valk_lval_num",
    LLVMFunctionType(ptr, (LLVMTypeRef[]){i64}, 1, 0));
  c->fn_lval_str = LLVMAddFunction(c->module, "valk_lval_str",
    LLVMFunctionType(ptr, p1, 1, 0));
  c->fn_lval_nil = LLVMAddFunction(c->module, "valk_lval_nil",
    LLVMFunctionType(ptr, NULL, 0, 0));
  c->fn_lval_sym = LLVMAddFunction(c->module, "valk_lval_sym",
    LLVMFunctionType(ptr, p1, 1, 0));
  c->fn_lval_cons = LLVMAddFunction(c->module, "valk_lval_cons",
    LLVMFunctionType(ptr, p2, 2, 0));
  c->fn_lval_qcons = LLVMAddFunction(c->module, "valk_lval_qcons",
    LLVMFunctionType(ptr, p2, 2, 0));
  c->fn_lval_lambda = LLVMAddFunction(c->module, "valk_lval_lambda",
    LLVMFunctionType(ptr, p3, 3, 0));
  c->fn_lval_copy = LLVMAddFunction(c->module, "valk_lval_copy",
    LLVMFunctionType(ptr, p1, 1, 0));
  c->fn_lval_is_truthy = LLVMAddFunction(c->module, "valk_lval_is_truthy",
    LLVMFunctionType(i1, p1, 1, 0));
  c->fn_lenv_get = LLVMAddFunction(c->module, "valk_lenv_get",
    LLVMFunctionType(ptr, p2, 2, 0));
  c->fn_lenv_put = LLVMAddFunction(c->module, "valk_lenv_put",
    LLVMFunctionType(vd, p3, 3, 0));
  c->fn_lenv_def = LLVMAddFunction(c->module, "valk_lenv_def",
    LLVMFunctionType(vd, p3, 3, 0));
  c->fn_lenv_empty = LLVMAddFunction(c->module, "valk_lenv_empty",
    LLVMFunctionType(ptr, NULL, 0, 0));
  c->fn_lval_eval = LLVMAddFunction(c->module, "valk_lval_eval",
    LLVMFunctionType(ptr, p2, 2, 0));
  c->fn_lval_eval_call = LLVMAddFunction(c->module, "valk_lval_eval_call",
    LLVMFunctionType(ptr, p3, 3, 0));
  c->fn_lval_println = LLVMAddFunction(c->module, "valk_lval_println",
    LLVMFunctionType(vd, p1, 1, 0));
  c->fn_lval_print = LLVMAddFunction(c->module, "valk_lval_print",
    LLVMFunctionType(vd, p1, 1, 0));
  c->fn_printf = LLVMAddFunction(c->module, "printf",
    LLVMFunctionType(LLVMInt32TypeInContext(c->ctx), p1, 1, 1));

  // Broad-stroke nounwind/willreturn across every helper. Safe because
  // nothing throws and nothing loops forever (env_get walks a finite
  // parent chain; eval/eval_call return via normal tree-walker paths).
  mark_nounwind_willreturn(c, c->fn_lval_num);
  mark_nounwind_willreturn(c, c->fn_lval_str);
  mark_nounwind_willreturn(c, c->fn_lval_nil);
  mark_nounwind_willreturn(c, c->fn_lval_sym);
  mark_nounwind_willreturn(c, c->fn_lval_cons);
  mark_nounwind_willreturn(c, c->fn_lval_qcons);
  mark_nounwind_willreturn(c, c->fn_lval_lambda);
  mark_nounwind_willreturn(c, c->fn_lval_copy);
  mark_nounwind_willreturn(c, c->fn_lval_is_truthy);
  mark_nounwind_willreturn(c, c->fn_lenv_get);
  mark_nounwind_willreturn(c, c->fn_lenv_put);
  mark_nounwind_willreturn(c, c->fn_lenv_def);
  mark_nounwind_willreturn(c, c->fn_lenv_empty);
  mark_nounwind_willreturn(c, c->fn_lval_eval);
  mark_nounwind_willreturn(c, c->fn_lval_eval_call);
  mark_nounwind_willreturn(c, c->fn_lval_println);
  mark_nounwind_willreturn(c, c->fn_lval_print);
  add_fn_attr(c, c->fn_printf, "nounwind");

  // valk_lval_is_truthy is the only pure reader in the list: it inspects
  // the lval's flags/num fields and returns an i1. No allocation, no
  // globals touched, no mutation. `memory(argmem: read)` tells LLVM the
  // function's only memory effect is reading through its pointer arg, so
  // repeated truthiness checks on the same value can CSE.
  add_argmem_read_attr(c, c->fn_lval_is_truthy);
}

valk_llvm_ctx_t *valk_llvm_ctx_new(const char *module_name) {
  valk_llvm_init();
  valk_llvm_ctx_t *c = calloc(1, sizeof(valk_llvm_ctx_t));
  c->ctx = LLVMContextCreate();
  c->module = LLVMModuleCreateWithNameInContext(module_name, c->ctx);
  c->builder = LLVMCreateBuilderInContext(c->ctx);

  c->ptr_type = LLVMPointerTypeInContext(c->ctx, 0);
  c->i64_type = LLVMInt64TypeInContext(c->ctx);
  c->i8_type = LLVMInt8TypeInContext(c->ctx);
  c->i1_type = LLVMInt1TypeInContext(c->ctx);
  c->void_type = LLVMVoidTypeInContext(c->ctx);

  valk_llvm_declare_runtime_fns(c);
  return c;
}

void valk_llvm_ctx_free(valk_llvm_ctx_t *ctx) {
  if (!ctx) return;
  if (ctx->builder) LLVMDisposeBuilder(ctx->builder);
  if (ctx->module) LLVMDisposeModule(ctx->module);
  if (ctx->ctx) LLVMContextDispose(ctx->ctx);
  free(ctx);
}

static LLVMValueRef emit_global_string(valk_llvm_ctx_t *c, const char *str) {
  char name[64];
  snprintf(name, sizeof(name), ".str.%llu", (unsigned long long)c->str_counter++);
  LLVMValueRef global = LLVMBuildGlobalStringPtr(c->builder, str, name);
  return global;
}

// Emit the `valk_lval_sym(".str.N")` call directly at the builder's current
// position. Used as the low-level primitive by emit_make_sym and by the
// hoist path below.
static LLVMValueRef emit_make_sym_inline(valk_llvm_ctx_t *c,
                                          const char *name) {
  LLVMValueRef str = emit_global_string(c, name);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, 1, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_sym, &str, 1, "sym");
}

// Stage 7: per-body sym-lval hoist. `valk_lval_sym(name)` has no meaningful
// variation across invocations (the interned string is deterministic and
// the returned lval is semantically equal to any other lval for the same
// name). Without this, a recursive body re-allocs a fresh sym lval each
// iteration for every symbol it looks up (`+`, `-`, `==`, `is-odd`, …).
// With `sym_cache.anchor_bb` set to the current fn's entry_bb, the first
// use of each name emits the alloc into entry_bb *before* its terminator
// (`br body_bb`), and every subsequent use reuses the SSA value. The fast
// variant's phi+branch TCO loop still runs, but without re-allocating syms
// every iteration.
//
// Safety re. GC: the tree walker already treats sym lvals as ephemeral
// (not rooted in any table) and Valkyria's GC runs only at explicit
// safepoints. As long as no safepoint is crossed during the fn body,
// neither the current inline alloc nor the hoisted alloc survives a GC;
// and the body doesn't hit a safepoint, so both are equivalently safe.
static LLVMValueRef emit_make_sym(valk_llvm_ctx_t *c, const char *name) {
  if (!c->sym_cache.anchor_bb) {
    return emit_make_sym_inline(c, name);
  }
  for (size_t i = 0; i < c->sym_cache.count; i++) {
    if (strcmp(c->sym_cache.names[i], name) == 0) {
      return c->sym_cache.vals[i];
    }
  }

  LLVMBasicBlockRef saved_bb = LLVMGetInsertBlock(c->builder);
  LLVMValueRef term = LLVMGetBasicBlockTerminator(c->sym_cache.anchor_bb);
  if (term) {
    LLVMPositionBuilderBefore(c->builder, term);
  } else {
    LLVMPositionBuilderAtEnd(c->builder, c->sym_cache.anchor_bb);
  }
  LLVMValueRef sym = emit_make_sym_inline(c, name);
  LLVMPositionBuilderAtEnd(c->builder, saved_bb);

  if (c->sym_cache.count == c->sym_cache.cap) {
    c->sym_cache.cap = c->sym_cache.cap ? c->sym_cache.cap * 2 : 8;
    c->sym_cache.names = realloc(c->sym_cache.names,
      c->sym_cache.cap * sizeof(*c->sym_cache.names));
    c->sym_cache.vals = realloc(c->sym_cache.vals,
      c->sym_cache.cap * sizeof(*c->sym_cache.vals));
  }
  c->sym_cache.names[c->sym_cache.count] = strdup(name);
  c->sym_cache.vals[c->sym_cache.count] = sym;
  c->sym_cache.count++;
  return sym;
}

static void sym_cache_enter(valk_llvm_ctx_t *c, LLVMBasicBlockRef anchor_bb) {
  c->sym_cache.anchor_bb = anchor_bb;
}

static void sym_cache_leave(valk_llvm_ctx_t *c) {
  for (size_t i = 0; i < c->sym_cache.count; i++) {
    free(c->sym_cache.names[i]);
  }
  free(c->sym_cache.names);
  free(c->sym_cache.vals);
  c->sym_cache.anchor_bb = nullptr;
  c->sym_cache.names = nullptr;
  c->sym_cache.vals = nullptr;
  c->sym_cache.count = 0;
  c->sym_cache.cap = 0;
}

static LLVMValueRef build_qcons_list(valk_llvm_ctx_t *c,
                                     LLVMValueRef *items, u64 count) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  LLVMValueRef list = LLVMBuildCall2(c->builder, fn_type,
    c->fn_lval_nil, NULL, 0, "nil");

  LLVMTypeRef qcons_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type}, 2, 0);

  for (i64 i = (i64)count - 1; i >= 0; i--) {
    LLVMValueRef args[] = {items[i], list};
    list = LLVMBuildCall2(c->builder, qcons_type, c->fn_lval_qcons,
      args, 2, "qcons");
  }
  return list;
}

static LLVMValueRef codegen_expr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                 LLVMValueRef env_param);

static LLVMValueRef codegen_num(valk_llvm_ctx_t *c, valk_lval_t *expr) {
  LLVMValueRef val = LLVMConstInt(c->i64_type, (u64)expr->num, 1);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->i64_type}, 1, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_num, &val, 1, "num");
}

static LLVMValueRef codegen_str(valk_llvm_ctx_t *c, valk_lval_t *expr) {
  LLVMValueRef str = emit_global_string(c, expr->str);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, 1, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_str, &str, 1, "str");
}

static LLVMValueRef codegen_nil(valk_llvm_ctx_t *c) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_nil, NULL, 0, "nil");
}

static LLVMValueRef codegen_sym_lookup(valk_llvm_ctx_t *c,
                                       valk_lval_t *expr,
                                       LLVMValueRef env_param) {
  // Keywords (symbols beginning with `:`) are self-evaluating in the tree
  // walker (see eval.c). AOT must match, otherwise `:method` gets looked up
  // as a variable and returns an LVAL_ERR. Emit the sym lval directly.
  if (expr->str && expr->str[0] == ':') {
    return emit_make_sym(c, expr->str);
  }
  // Stage 2: if this symbol is a formal of the current fast-variant
  // lambda, resolve directly to the LLVM arg without calling lenv_get.
  if (c->formals_map.count && expr->str) {
    for (size_t i = 0; i < c->formals_map.count; i++) {
      if (strcmp(c->formals_map.names[i], expr->str) == 0) {
        return c->formals_map.vals[i];
      }
    }
  }
  LLVMValueRef sym = emit_make_sym(c, expr->str);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type}, 2, 0);
  LLVMValueRef args[] = {env_param, sym};
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lenv_get, args, 2, "lookup");
}

static u64 cons_list_len(valk_lval_t *list) {
  u64 n = 0;
  while (list && LVAL_TYPE(list) == LVAL_CONS) {
    n++;
    list = list->cons.tail;
  }
  return n;
}

static valk_lval_t *cons_list_nth(valk_lval_t *list, u64 idx) {
  for (u64 i = 0; i < idx; i++) {
    list = list->cons.tail;
  }
  return list->cons.head;
}

static bool is_sym(valk_lval_t *expr, const char *name) {
  return LVAL_TYPE(expr) == LVAL_SYM && strcmp(expr->str, name) == 0;
}

// Mirror the tree-walker's CONT_IF_BRANCH logic for `if` / `do` sub-forms:
// a qexpr branch is unwrapped to a cons and then (if it contains exactly
// one element) reduced to that element so `{42}` codegens as the literal
// 42 rather than as an attempt to call 42 with no args. Matches the
// count==1 SINGLE_ELEM path in eval.c `valk_lval_eval_iterative`.
static valk_lval_t *unwrap_branch_qexpr(valk_lval_t *branch) {
  if (!branch) return branch;
  if (LVAL_TYPE(branch) != LVAL_CONS) return branch;
  if (!(branch->flags & LVAL_FLAG_QUOTED)) return branch;
  valk_lval_t *cons = valk_qexpr_to_cons(branch);
  if (cons && LVAL_TYPE(cons) == LVAL_CONS && cons->cons.tail &&
      LVAL_TYPE(cons->cons.tail) == LVAL_NIL) {
    return cons->cons.head;
  }
  return cons;
}

static LLVMValueRef codegen_if(valk_llvm_ctx_t *c, valk_lval_t *args,
                               u64 argc, LLVMValueRef env_param) {
  if (argc < 2) return codegen_nil(c);

  valk_lval_t *cond_expr = cons_list_nth(args, 0);
  valk_lval_t *then_expr = cons_list_nth(args, 1);
  valk_lval_t *else_expr = argc > 2 ? cons_list_nth(args, 2) : NULL;

  then_expr = unwrap_branch_qexpr(then_expr);
  else_expr = unwrap_branch_qexpr(else_expr);

  bool saved_tail = c->in_tail;

  c->in_tail = false;
  LLVMValueRef cond_val = codegen_expr(c, cond_expr, env_param);

  LLVMTypeRef truthy_type = LLVMFunctionType(c->i1_type,
    (LLVMTypeRef[]){c->ptr_type}, 1, 0);
  LLVMValueRef is_truthy = LLVMBuildCall2(c->builder, truthy_type,
    c->fn_lval_is_truthy, &cond_val, 1, "cond");

  LLVMValueRef fn = LLVMGetBasicBlockParent(LLVMGetInsertBlock(c->builder));

  char then_name[32], else_name[32], merge_name[32];
  snprintf(then_name, sizeof(then_name), "then.%llu",
    (unsigned long long)c->block_counter);
  snprintf(else_name, sizeof(else_name), "else.%llu",
    (unsigned long long)c->block_counter);
  snprintf(merge_name, sizeof(merge_name), "merge.%llu",
    (unsigned long long)c->block_counter++);

  LLVMBasicBlockRef then_bb = LLVMAppendBasicBlockInContext(c->ctx, fn, then_name);
  LLVMBasicBlockRef else_bb = LLVMAppendBasicBlockInContext(c->ctx, fn, else_name);

  LLVMBuildCondBr(c->builder, is_truthy, then_bb, else_bb);

  // When this if is in tail position, emit `ret` directly in each branch
  // instead of merging through a phi. The X86 backend only converts a
  // `tail`-marked call to a sibcall (jmp) when the call's result flows
  // *directly* to a ret in the same block — `call; br merge; phi; ret`
  // doesn't qualify. Sinking the ret makes mutual tail recursion work.
  // The caller's trailing LLVMBuildRet lands on `tail.dead` and is DCE'd.
  if (saved_tail) {
    LLVMPositionBuilderAtEnd(c->builder, then_bb);
    c->in_tail = true;
    LLVMValueRef then_val = codegen_expr(c, then_expr, env_param);
    LLVMBuildRet(c->builder, then_val);

    LLVMPositionBuilderAtEnd(c->builder, else_bb);
    c->in_tail = true;
    LLVMValueRef else_val = else_expr ? codegen_expr(c, else_expr, env_param)
                                      : codegen_nil(c);
    LLVMBuildRet(c->builder, else_val);

    LLVMBasicBlockRef dead =
      LLVMAppendBasicBlockInContext(c->ctx, fn, "tail.dead");
    LLVMPositionBuilderAtEnd(c->builder, dead);
    c->in_tail = saved_tail;
    return LLVMGetUndef(c->ptr_type);
  }

  LLVMBasicBlockRef merge_bb = LLVMAppendBasicBlockInContext(c->ctx, fn, merge_name);

  LLVMPositionBuilderAtEnd(c->builder, then_bb);
  LLVMValueRef then_val = codegen_expr(c, then_expr, env_param);
  LLVMBuildBr(c->builder, merge_bb);
  LLVMBasicBlockRef then_end = LLVMGetInsertBlock(c->builder);

  LLVMPositionBuilderAtEnd(c->builder, else_bb);
  LLVMValueRef else_val;
  if (else_expr) {
    else_val = codegen_expr(c, else_expr, env_param);
  } else {
    else_val = codegen_nil(c);
  }
  LLVMBuildBr(c->builder, merge_bb);
  LLVMBasicBlockRef else_end = LLVMGetInsertBlock(c->builder);

  LLVMPositionBuilderAtEnd(c->builder, merge_bb);
  LLVMValueRef phi = LLVMBuildPhi(c->builder, c->ptr_type, "if.result");
  LLVMValueRef incoming_vals[] = {then_val, else_val};
  LLVMBasicBlockRef incoming_bbs[] = {then_end, else_end};
  LLVMAddIncoming(phi, incoming_vals, incoming_bbs, 2);
  return phi;
}

static LLVMValueRef codegen_do(valk_llvm_ctx_t *c, valk_lval_t *args,
                               u64 argc, LLVMValueRef env_param) {
  LLVMValueRef result = codegen_nil(c);
  valk_lval_t *cur = args;
  bool saved_tail = c->in_tail;
  for (u64 i = 0; i < argc; i++) {
    c->in_tail = (i == argc - 1) ? saved_tail : false;
    result = codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }
  c->in_tail = saved_tail;
  return result;
}

static LLVMValueRef codegen_def(valk_llvm_ctx_t *c, valk_lval_t *args,
                                u64 argc, LLVMValueRef env_param,
                                bool global) {
  if (argc < 2) return codegen_nil(c);

  valk_lval_t *syms_expr = cons_list_nth(args, 0);

  LLVMTypeRef put_type = LLVMFunctionType(c->void_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  LLVMValueRef put_fn = global ? c->fn_lenv_def : c->fn_lenv_put;

  if (LVAL_TYPE(syms_expr) == LVAL_SYM) {
    LLVMValueRef sym = emit_make_sym(c, syms_expr->str);
    LLVMValueRef val = codegen_expr(c, cons_list_nth(args, 1), env_param);
    LLVMValueRef put_args[] = {env_param, sym, val};
    LLVMBuildCall2(c->builder, put_type, put_fn, put_args, 3, "");
    return val;
  }

  if (LVAL_TYPE(syms_expr) == LVAL_CONS) {
    u64 sym_count = cons_list_len(syms_expr);
    u64 val_count = argc - 1;
    u64 n = sym_count < val_count ? sym_count : val_count;

    LLVMValueRef last = codegen_nil(c);
    valk_lval_t *sym_cur = syms_expr;
    valk_lval_t *val_cur = args->cons.tail;
    for (u64 i = 0; i < n; i++) {
      valk_lval_t *s = sym_cur->cons.head;
      LLVMValueRef sym = emit_make_sym(c, s->str);
      LLVMValueRef val = codegen_expr(c, val_cur->cons.head, env_param);
      LLVMValueRef put_args[] = {env_param, sym, val};
      LLVMBuildCall2(c->builder, put_type, put_fn, put_args, 3, "");
      last = val;
      sym_cur = sym_cur->cons.tail;
      val_cur = val_cur->cons.tail;
    }
    return last;
  }

  return codegen_nil(c);
}

static LLVMValueRef codegen_lambda(valk_llvm_ctx_t *c, valk_lval_t *args,
                                   u64 argc, LLVMValueRef env_param) {
  if (argc < 2) return codegen_nil(c);

  valk_lval_t *formals = cons_list_nth(args, 0);
  valk_lval_t *body = cons_list_nth(args, 1);

  LLVMValueRef formals_val = codegen_expr(c, formals, env_param);
  LLVMValueRef body_val = codegen_expr(c, body, env_param);

  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  LLVMValueRef lam_args[] = {env_param, formals_val, body_val};
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_lambda,
    lam_args, 3, "lambda");
}

static LLVMValueRef codegen_literal(valk_llvm_ctx_t *c, valk_lval_t *expr);

static LLVMValueRef codegen_qexpr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                  __attribute__((unused)) LLVMValueRef env_param) {
  return codegen_literal(c, expr);
}

static LLVMValueRef build_cons_list(valk_llvm_ctx_t *c,
                                    LLVMValueRef *items, u64 count,
                                    bool quoted) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  LLVMValueRef list = LLVMBuildCall2(c->builder, fn_type,
    c->fn_lval_nil, NULL, 0, "nil");

  LLVMValueRef cons_fn = quoted ? c->fn_lval_qcons : c->fn_lval_cons;
  LLVMTypeRef cons_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type}, 2, 0);

  for (i64 i = (i64)count - 1; i >= 0; i--) {
    LLVMValueRef args[] = {items[i], list};
    list = LLVMBuildCall2(c->builder, cons_type, cons_fn,
      args, 2, quoted ? "qcons" : "cons");
  }
  return list;
}

static LLVMValueRef codegen_literal(valk_llvm_ctx_t *c, valk_lval_t *expr) {
  if (!expr) return codegen_nil(c);

  switch (LVAL_TYPE(expr)) {
    case LVAL_NUM:
      return codegen_num(c, expr);
    case LVAL_STR:
      return codegen_str(c, expr);
    case LVAL_NIL:
      return codegen_nil(c);
    case LVAL_SYM:
      return emit_make_sym(c, expr->str);
    case LVAL_CONS: {
      bool quoted = (expr->flags & LVAL_FLAG_QUOTED) != 0;
      u64 len = cons_list_len(expr);
      LLVMValueRef *items = malloc(sizeof(LLVMValueRef) * len);
      valk_lval_t *cur = expr;
      for (u64 i = 0; i < len; i++) {
        items[i] = codegen_literal(c, cur->cons.head);
        cur = cur->cons.tail;
      }
      LLVMValueRef result = build_cons_list(c, items, len, quoted);
      free(items);
      return result;
    }
    default:
      return codegen_nil(c);
  }
}

// Numeric-op specialization.
//
// For arity-2 applications of the standard arithmetic and comparison
// operators, emit a runtime type check: if both operands are LVAL_NUM (and
// divisor is non-zero for `/`), use a native op + valk_lval_num boxing. On
// any non-number or divide-by-zero, phi over to the general call path, which
// preserves the semantics of any user-shadowed definition.
//
// The user-shadow story: we do NOT verify that the operator symbol still
// resolves to the builtin. If the user has redefined `+` to behave as
// string-concat and then calls it with two numbers, this fast path will do
// integer add instead. Tree-walker respects the redefinition; JIT does not.
// This matches V8/LuaJIT's standard behavior for hot-path operators.

typedef enum {
  BINOP_ADD, BINOP_SUB, BINOP_MUL, BINOP_DIV,
  BINOP_LT,  BINOP_GT,  BINOP_LE,  BINOP_GE, BINOP_EQ,
} numeric_binop_e;

static bool match_numeric_binop(const char *s, numeric_binop_e *out) {
  if (strcmp(s, "+") == 0)  { *out = BINOP_ADD; return true; }
  if (strcmp(s, "-") == 0)  { *out = BINOP_SUB; return true; }
  if (strcmp(s, "*") == 0)  { *out = BINOP_MUL; return true; }
  if (strcmp(s, "/") == 0)  { *out = BINOP_DIV; return true; }
  if (strcmp(s, "<") == 0)  { *out = BINOP_LT;  return true; }
  if (strcmp(s, ">") == 0)  { *out = BINOP_GT;  return true; }
  if (strcmp(s, "<=") == 0) { *out = BINOP_LE;  return true; }
  if (strcmp(s, ">=") == 0) { *out = BINOP_GE;  return true; }
  if (strcmp(s, "==") == 0) { *out = BINOP_EQ;  return true; }
  return false;
}

static LLVMValueRef emit_load_num_field(valk_llvm_ctx_t *c,
                                        LLVMValueRef lval_ptr,
                                        const char *name) {
  LLVMValueRef off = LLVMConstInt(c->i64_type, offsetof(valk_lval_t, num), 0);
  LLVMValueRef fp = LLVMBuildInBoundsGEP2(c->builder, c->i8_type,
    lval_ptr, &off, 1, "num_ptr");
  return LLVMBuildLoad2(c->builder, c->i64_type, fp, name);
}

static LLVMValueRef emit_load_type_bits(valk_llvm_ctx_t *c,
                                        LLVMValueRef lval_ptr,
                                        const char *name) {
  LLVMValueRef off = LLVMConstInt(c->i64_type, offsetof(valk_lval_t, flags), 0);
  LLVMValueRef fp = LLVMBuildInBoundsGEP2(c->builder, c->i8_type,
    lval_ptr, &off, 1, "flags_ptr");
  LLVMValueRef flags = LLVMBuildLoad2(c->builder, c->i64_type, fp, "flags");
  LLVMValueRef mask = LLVMConstInt(c->i64_type, LVAL_TYPE_MASK, 0);
  return LLVMBuildAnd(c->builder, flags, mask, name);
}

static LLVMValueRef codegen_funcall(valk_llvm_ctx_t *c, valk_lval_t *head,
                                    valk_lval_t *args_list, u64 argc,
                                    LLVMValueRef env_param);

static bool is_num_literal(valk_lval_t *expr, i64 *out) {
  if (!expr || LVAL_TYPE(expr) != LVAL_NUM) return false;
  *out = expr->num;
  return true;
}

// Returns non-NULL if specialization was emitted, else NULL (caller must fall
// back to generic codegen_funcall).
//
// Arity-2 handles all nine operators (+ - * / < > <= >= ==). Arity-1 and
// arity-N (N>=3) handle just the four arithmetic folds: the `ord` builtins
// accept exactly 2 args, so non-2-arity comparisons fall through. Matches
// `valk_builtin_math` in src/builtins_math.c:
//   (+ a b c)     → ((a+b)+c)           left-fold
//   (- a b c)     → ((a-b)-c)           left-fold
//   (- a)         → -a                   unary negate
//   (+ a) (* a) (/ a) → a                unary identity (builtin pops first,
//                                        leaves result = first->num, returns)
//   (/ a b c)     → ((a/b)/c), slow detour whenever any divisor <= 0 so the
//                   builtin's "Division By Zero" error is preserved (the
//                   builtin errors on y <= 0, not just y == 0 — preserve it).
static LLVMValueRef try_codegen_numeric_binop(valk_llvm_ctx_t *c,
                                              valk_lval_t *head,
                                              valk_lval_t *args_list,
                                              u64 argc,
                                              LLVMValueRef env_param) {
  if (argc == 0) return NULL;
  if (LVAL_TYPE(head) != LVAL_SYM) return NULL;
  numeric_binop_e op;
  if (!match_numeric_binop(head->str, &op)) return NULL;

  bool is_arith = (op == BINOP_ADD || op == BINOP_SUB ||
                   op == BINOP_MUL || op == BINOP_DIV);
  if (!is_arith && argc != 2) return NULL;

  // Gather args. Operand-by-operand literal detection; non-literals get
  // codegen_expr'd once and share between type-check and fast-path.
  bool *is_lit  = malloc(sizeof(bool) * argc);
  i64  *lits    = malloc(sizeof(i64)  * argc);
  LLVMValueRef *vals = malloc(sizeof(LLVMValueRef) * argc);
  valk_lval_t *cur = args_list;
  bool saved_tail = c->in_tail;
  c->in_tail = false;
  for (u64 i = 0; i < argc; i++) {
    is_lit[i] = is_num_literal(cur->cons.head, &lits[i]);
    vals[i] = is_lit[i] ? nullptr : codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }
  c->in_tail = saved_tail;

  // Type check = AND of (operand[i] is LVAL_NUM) for each non-literal.
  // All literals → check collapses to true (constant-folded out).
  LLVMValueRef num_const = LLVMConstInt(c->i64_type, LVAL_NUM, 0);
  LLVMValueRef check = LLVMConstInt(c->i1_type, 1, 0);
  for (u64 i = 0; i < argc; i++) {
    if (is_lit[i]) continue;
    LLVMValueRef ty = emit_load_type_bits(c, vals[i], "arg_type");
    LLVMValueRef is_num = LLVMBuildICmp(c->builder, LLVMIntEQ, ty, num_const,
                                        "arg_is_num");
    check = LLVMBuildAnd(c->builder, check, is_num, "all_num");
  }

  LLVMValueRef fn = LLVMGetBasicBlockParent(LLVMGetInsertBlock(c->builder));
  char fast_name[32], slow_name[32], merge_name[32];
  snprintf(fast_name,  sizeof fast_name,  "num.fast.%llu",
    (unsigned long long)c->block_counter);
  snprintf(slow_name,  sizeof slow_name,  "num.slow.%llu",
    (unsigned long long)c->block_counter);
  snprintf(merge_name, sizeof merge_name, "num.merge.%llu",
    (unsigned long long)c->block_counter++);

  LLVMBasicBlockRef fast_bb  = LLVMAppendBasicBlockInContext(c->ctx, fn, fast_name);
  LLVMBasicBlockRef slow_bb  = LLVMAppendBasicBlockInContext(c->ctx, fn, slow_name);
  LLVMBasicBlockRef merge_bb = LLVMAppendBasicBlockInContext(c->ctx, fn, merge_name);

  LLVMBuildCondBr(c->builder, check, fast_bb, slow_bb);

  // Fast path -------------------------------------------------------------
  LLVMPositionBuilderAtEnd(c->builder, fast_bb);

  // Load the i64 value for each operand (const for literals).
  LLVMValueRef *nums = malloc(sizeof(LLVMValueRef) * argc);
  for (u64 i = 0; i < argc; i++) {
    nums[i] = is_lit[i]
      ? LLVMConstInt(c->i64_type, (u64)lits[i], 1)
      : emit_load_num_field(c, vals[i], "arg_num");
  }

  LLVMValueRef fast_i64;
  bool fast_is_i1 = false;

  if (argc == 1 && is_arith) {
    // Unary: (- x) negates; (+ x), (* x), (/ x) return x as-is.
    if (op == BINOP_SUB) {
      LLVMValueRef zero = LLVMConstInt(c->i64_type, 0, 1);
      fast_i64 = LLVMBuildSub(c->builder, zero, nums[0], "neg");
    } else {
      fast_i64 = nums[0];
    }
  } else if (argc == 2 && !is_arith) {
    // Arity-2 comparison.
    LLVMIntPredicate pred =
      (op == BINOP_LT) ? LLVMIntSLT :
      (op == BINOP_GT) ? LLVMIntSGT :
      (op == BINOP_LE) ? LLVMIntSLE :
      (op == BINOP_GE) ? LLVMIntSGE :
                         LLVMIntEQ;
    const char *nm =
      (op == BINOP_LT) ? "lt" : (op == BINOP_GT) ? "gt" :
      (op == BINOP_LE) ? "le" : (op == BINOP_GE) ? "ge" : "eq";
    fast_i64 = LLVMBuildICmp(c->builder, pred, nums[0], nums[1], nm);
    fast_is_i1 = true;
  } else {
    // Arity-N arithmetic fold (N>=2). For DIV, per-step detour on y<=0
    // so the "Division By Zero" error lval from the builtin is preserved
    // for every negative/zero divisor — matches valk_builtin_math's
    // `if (y->num > 0) result /= y->num; else return err`.
    LLVMValueRef acc = nums[0];
    for (u64 i = 1; i < argc; i++) {
      if (op == BINOP_DIV) {
        LLVMValueRef zero = LLVMConstInt(c->i64_type, 0, 1);
        LLVMValueRef bad = LLVMBuildICmp(c->builder, LLVMIntSLE,
          nums[i], zero, "div_bad");
        char fast2_name[32];
        snprintf(fast2_name, sizeof fast2_name, "num.div.%llu",
          (unsigned long long)c->block_counter++);
        LLVMBasicBlockRef fast2_bb =
          LLVMAppendBasicBlockInContext(c->ctx, fn, fast2_name);
        LLVMBuildCondBr(c->builder, bad, slow_bb, fast2_bb);
        LLVMPositionBuilderAtEnd(c->builder, fast2_bb);
      }
      switch (op) {
        case BINOP_ADD: acc = LLVMBuildAdd(c->builder,  acc, nums[i], "add"); break;
        case BINOP_SUB: acc = LLVMBuildSub(c->builder,  acc, nums[i], "sub"); break;
        case BINOP_MUL: acc = LLVMBuildMul(c->builder,  acc, nums[i], "mul"); break;
        case BINOP_DIV: acc = LLVMBuildSDiv(c->builder, acc, nums[i], "div"); break;
        default: break;  // unreachable: is_arith guarded above
      }
    }
    fast_i64 = acc;
  }

  if (fast_is_i1) {
    fast_i64 = LLVMBuildZExt(c->builder, fast_i64, c->i64_type, "cmp.ext");
  }

  free(nums);

  LLVMTypeRef num_ty = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->i64_type}, 1, 0);
  LLVMValueRef fast_val = LLVMBuildCall2(c->builder, num_ty, c->fn_lval_num,
    &fast_i64, 1, "fast.num");
  LLVMBuildBr(c->builder, merge_bb);
  LLVMBasicBlockRef fast_end = LLVMGetInsertBlock(c->builder);

  // Slow path -------------------------------------------------------------
  LLVMPositionBuilderAtEnd(c->builder, slow_bb);
  LLVMValueRef slow_val = codegen_funcall(c, head, args_list, argc, env_param);
  LLVMBuildBr(c->builder, merge_bb);
  LLVMBasicBlockRef slow_end = LLVMGetInsertBlock(c->builder);

  // Merge -----------------------------------------------------------------
  LLVMPositionBuilderAtEnd(c->builder, merge_bb);
  LLVMValueRef phi = LLVMBuildPhi(c->builder, c->ptr_type, "num.result");
  LLVMValueRef incoming_vals[] = {fast_val, slow_val};
  LLVMBasicBlockRef incoming_bbs[] = {fast_end, slow_end};
  LLVMAddIncoming(phi, incoming_vals, incoming_bbs, 2);

  free(is_lit);
  free(lits);
  free(vals);
  return phi;
}

static LLVMValueRef codegen_funcall(valk_llvm_ctx_t *c, valk_lval_t *head,
                                    valk_lval_t *args_list, u64 argc,
                                    LLVMValueRef env_param) {
  bool saved_tail = c->in_tail;
  c->in_tail = false;

  LLVMValueRef fn_val = codegen_expr(c, head, env_param);

  LLVMValueRef *arg_vals = malloc(sizeof(LLVMValueRef) * argc);
  valk_lval_t *cur = args_list;
  for (u64 i = 0; i < argc; i++) {
    arg_vals[i] = codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }

  LLVMValueRef qargs = build_qcons_list(c, arg_vals, argc);
  free(arg_vals);

  LLVMTypeRef call_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  LLVMValueRef call_args[] = {env_param, fn_val, qargs};
  LLVMValueRef ret = LLVMBuildCall2(c->builder, call_type, c->fn_lval_eval_call,
    call_args, 3, "call");
  c->in_tail = saved_tail;
  return ret;
}

// Stage 1: when `sym` resolves in the build-time env to an LVAL_FUN lambda
// that already has `native_name` set and matches argc == #formals exactly
// (no `&` varargs, no partial app), emit a direct call to that native fn.
//
// Codegen: build a fresh call_env via valk_lenv_empty(), set its parent to
// the global `valk_aot_root_env` (the loaded image env at runtime), bind
// each formal via valk_lenv_put, then call the target native fn directly.
// Bypasses valk_lval_eval_call + qexpr arg packing.
static LLVMValueRef try_codegen_direct_call(valk_llvm_ctx_t *c,
                                            valk_lval_t *head,
                                            valk_lval_t *args_list,
                                            u64 argc,
                                            LLVMValueRef env_param) {
  if (!c->build_env) return nullptr;
  if (LVAL_TYPE(head) != LVAL_SYM) return nullptr;

  valk_lval_t *target = valk_lenv_get(c->build_env, head);
  if (!target || LVAL_TYPE(target) != LVAL_FUN) return nullptr;
  if (target->fun.builtin) return nullptr;
  if (!target->fun.native_name) return nullptr;

  // Reject varargs (`&`) and mismatched arity — fall back to generic call
  // which handles partial application and variadics.
  valk_lval_t *formals = target->fun.formals;
  u64 nformals = 0;
  for (valk_lval_t *f = formals; f && LVAL_TYPE(f) == LVAL_CONS; f = f->cons.tail) {
    valk_lval_t *fh = f->cons.head;
    if (LVAL_TYPE(fh) == LVAL_SYM && strcmp(fh->str, "&") == 0) return nullptr;
    nformals++;
  }
  if (nformals != argc) return nullptr;

  // Evaluate arg expressions in caller order (before building call_env so
  // side effects sequence matches the generic path). Arg evaluation is
  // never in tail position — only the call itself can be.
  bool saved_tail = c->in_tail;
  c->in_tail = false;
  LLVMValueRef *arg_vals = malloc(sizeof(LLVMValueRef) * argc);
  valk_lval_t *cur = args_list;
  for (u64 i = 0; i < argc; i++) {
    arg_vals[i] = codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }
  c->in_tail = saved_tail;

  // Locate the root env global once — used by both fast (env arg) and
  // slow (call_env parent) paths.
  LLVMValueRef root_env_global = LLVMGetNamedGlobal(c->module, "valk_aot_root_env");
  if (!root_env_global) {
    root_env_global = LLVMAddGlobal(c->module, c->ptr_type, "valk_aot_root_env");
    LLVMSetLinkage(root_env_global, LLVMExternalLinkage);
  }

  // Stage 2: if a `_fast` variant exists in this module, call it directly
  // with the evaluated args + root env as env_param. Bypasses call_env
  // construction entirely.
  char fast_name[80];
  snprintf(fast_name, sizeof fast_name, "%s_fast", target->fun.native_name);
  LLVMValueRef fast_fn = LLVMGetNamedFunction(c->module, fast_name);
  if (fast_fn) {
    // Stage 3: self-recursive tail call. Instead of pushing a stack frame,
    // feed the new arg values through the body_bb phi nodes and branch
    // back to body_bb. Constant stack space regardless of recursion depth.
    if (saved_tail && c->tco.fn && fast_fn == c->tco.fn &&
        argc == c->tco.nformals) {
      LLVMBasicBlockRef cur_bb = LLVMGetInsertBlock(c->builder);
      for (u64 i = 0; i < argc; i++) {
        LLVMAddIncoming(c->tco.formal_phis[i], &arg_vals[i], &cur_bb, 1);
      }
      LLVMBuildBr(c->builder, c->tco.body_bb);

      // Position on a fresh unreachable block so any subsequent IR built
      // by the caller (e.g. codegen_if's phi-merge, final BuildRet) has a
      // valid insert point. LLVM's DCE will prune the block.
      LLVMValueRef fn_here = LLVMGetBasicBlockParent(cur_bb);
      LLVMBasicBlockRef dead =
        LLVMAppendBasicBlockInContext(c->ctx, fn_here, "tco.dead");
      LLVMPositionBuilderAtEnd(c->builder, dead);
      free(arg_vals);
      return LLVMGetUndef(c->ptr_type);
    }

    LLVMTypeRef *params = malloc(sizeof(LLVMTypeRef) * (argc + 1));
    params[0] = c->ptr_type;
    for (u64 i = 0; i < argc; i++) params[i + 1] = c->ptr_type;
    LLVMTypeRef fast_ty = LLVMFunctionType(c->ptr_type, params,
                                           (unsigned)(argc + 1), 0);
    free(params);

    LLVMValueRef root_env = LLVMBuildLoad2(c->builder, c->ptr_type,
      root_env_global, "aot_root");
    LLVMValueRef *fast_args = malloc(sizeof(LLVMValueRef) * (argc + 1));
    fast_args[0] = root_env;
    for (u64 i = 0; i < argc; i++) fast_args[i + 1] = arg_vals[i];
    LLVMValueRef ret = LLVMBuildCall2(c->builder, fast_ty, fast_fn,
      fast_args, (unsigned)(argc + 1), "direct.fast");
    // When this call is in tail position, hint `tail` so LLVM's
    // TailCallElim pass can fold the merge-phi-ret pattern (codegen_if's
    // else branch flows through merge_bb's ret) into a sibling call.
    // Enables mutual tail recursion across fast variants.
    if (saved_tail) LLVMSetTailCall(ret, 1);
    free(fast_args);
    free(arg_vals);
    return ret;
  }

  // BYOL error short-circuit on the slow fallback. The fast variant branch
  // above delegates to a fast body that checks at entry (see
  // valk_llvm_compile_lambda_body_fast "byol.err"). The slow body trusts
  // its caller to have filtered errors (TW's CONT_COLLECT_ARG does this),
  // but here we bypass the tree walker and feed arg_vals straight into a
  // fresh call_env — so we must do the check ourselves or recursive walk
  // lambdas loop forever on error input (see eval.c CONT_COLLECT_ARG, and
  // the memory note `project_aot_byol_invariant`).
  LLVMBasicBlockRef pre_bb = LLVMGetInsertBlock(c->builder);
  LLVMValueRef caller_fn = LLVMGetBasicBlockParent(pre_bb);
  LLVMBasicBlockRef err_bb =
    LLVMAppendBasicBlockInContext(c->ctx, caller_fn, "direct.err");
  LLVMBasicBlockRef ok_bb =
    LLVMAppendBasicBlockInContext(c->ctx, caller_fn, "direct.ok");
  LLVMBasicBlockRef merge_bb =
    LLVMAppendBasicBlockInContext(c->ctx, caller_fn, "direct.merge");

  LLVMValueRef err_const = LLVMConstInt(c->i64_type, LVAL_ERR, 0);
  LLVMValueRef first_err = LLVMConstNull(c->ptr_type);
  LLVMValueRef any_err = LLVMConstInt(c->i1_type, 0, 0);
  for (u64 i = 0; i < argc; i++) {
    LLVMValueRef type = emit_load_type_bits(c, arg_vals[i], "direct.type");
    LLVMValueRef is_err = LLVMBuildICmp(c->builder, LLVMIntEQ, type,
                                        err_const, "direct.is_err");
    first_err = LLVMBuildSelect(c->builder, is_err, arg_vals[i], first_err,
                                "direct.first_err");
    any_err = LLVMBuildOr(c->builder, any_err, is_err, "direct.any_err");
  }
  LLVMBuildCondBr(c->builder, any_err, err_bb, ok_bb);

  LLVMPositionBuilderAtEnd(c->builder, err_bb);
  LLVMBuildBr(c->builder, merge_bb);

  LLVMPositionBuilderAtEnd(c->builder, ok_bb);

  // call_env = valk_lenv_empty()
  LLVMTypeRef empty_ty = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  LLVMValueRef call_env = LLVMBuildCall2(c->builder, empty_ty,
    c->fn_lenv_empty, NULL, 0, "call_env");

  // call_env->parent = valk_aot_root_env
  LLVMValueRef root_env = LLVMBuildLoad2(c->builder, c->ptr_type,
    root_env_global, "aot_root");
  LLVMValueRef parent_off = LLVMConstInt(c->i64_type,
    offsetof(valk_lenv_t, parent), 0);
  LLVMValueRef parent_ptr = LLVMBuildInBoundsGEP2(c->builder, c->i8_type,
    call_env, &parent_off, 1, "parent_ptr");
  LLVMBuildStore(c->builder, root_env, parent_ptr);

  // Bind each formal: valk_lenv_put(call_env, sym(formal_name), arg_val)
  LLVMTypeRef put_ty = LLVMFunctionType(c->void_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  cur = formals;
  for (u64 i = 0; i < argc; i++) {
    valk_lval_t *fh = cur->cons.head;
    LLVMValueRef fsym = emit_make_sym(c, fh->str);
    LLVMValueRef put_args[] = {call_env, fsym, arg_vals[i]};
    LLVMBuildCall2(c->builder, put_ty, c->fn_lenv_put, put_args, 3, "");
    cur = cur->cons.tail;
  }
  free(arg_vals);

  // Call the AOT'd native fn directly: valk_lval_t *(*)(valk_lenv_t *)
  LLVMTypeRef native_ty = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, 1, 0);
  LLVMValueRef native_fn = LLVMGetNamedFunction(c->module, target->fun.native_name);
  if (!native_fn) {
    native_fn = LLVMAddFunction(c->module, target->fun.native_name, native_ty);
    LLVMSetLinkage(native_fn, LLVMExternalLinkage);
  }
  LLVMValueRef ret = LLVMBuildCall2(c->builder, native_ty, native_fn,
    &call_env, 1, "direct");
  LLVMBasicBlockRef ok_end = LLVMGetInsertBlock(c->builder);
  LLVMBuildBr(c->builder, merge_bb);

  LLVMPositionBuilderAtEnd(c->builder, merge_bb);
  LLVMValueRef phi = LLVMBuildPhi(c->builder, c->ptr_type, "direct.result");
  LLVMValueRef incoming_vals[] = {first_err, ret};
  LLVMBasicBlockRef incoming_bbs[] = {err_bb, ok_end};
  LLVMAddIncoming(phi, incoming_vals, incoming_bbs, 2);
  return phi;
}

static LLVMValueRef codegen_sexpr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                  LLVMValueRef env_param) {
  valk_lval_t *head = expr->cons.head;
  valk_lval_t *rest = expr->cons.tail;
  u64 argc = 0;
  if (rest && LVAL_TYPE(rest) == LVAL_CONS)
    argc = cons_list_len(rest);

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (is_sym(head, "if"))
      return codegen_if(c, rest, argc, env_param);
    if (is_sym(head, "do"))
      return codegen_do(c, rest, argc, env_param);
    if (is_sym(head, "def"))
      return codegen_def(c, rest, argc, env_param, true);
    if (is_sym(head, "="))
      return codegen_def(c, rest, argc, env_param, false);
    if (is_sym(head, "\\"))
      return codegen_lambda(c, rest, argc, env_param);

    LLVMValueRef specialized =
      try_codegen_numeric_binop(c, head, rest, argc, env_param);
    if (specialized) return specialized;

    LLVMValueRef direct =
      try_codegen_direct_call(c, head, rest, argc, env_param);
    if (direct) return direct;
  }

  return codegen_funcall(c, head, rest, argc, env_param);
}

static LLVMValueRef codegen_expr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                 LLVMValueRef env_param) {
  if (!expr) return codegen_nil(c);

  valk_ltype_e type = LVAL_TYPE(expr);

  switch (type) {
    case LVAL_NUM:
      return codegen_num(c, expr);
    case LVAL_STR:
      return codegen_str(c, expr);
    case LVAL_NIL:
      return codegen_nil(c);
    case LVAL_SYM:
      return codegen_sym_lookup(c, expr, env_param);
    case LVAL_CONS: {
      bool quoted = (expr->flags & LVAL_FLAG_QUOTED) != 0;
      if (quoted)
        return codegen_qexpr(c, expr, env_param);
      return codegen_sexpr(c, expr, env_param);
    }
    default:
      return codegen_nil(c);
  }
}

LLVMValueRef valk_llvm_compile_expr(valk_llvm_ctx_t *ctx,
                                    valk_lval_t *expr,
                                    LLVMValueRef env_param) {
  return codegen_expr(ctx, expr, env_param);
}

// Recursive scan: does `expr` contain an s-expression whose head is a
// symbol in {`\`, `fn`, `def`, `=`}? Those forms capture or mutate the
// call_env, which the fast variant doesn't build.
//
// Qexprs must be scanned too: `if`/`do`/lambda-body/etc. branches are
// written as qexprs in source but are executed as code at runtime (see
// eval.c CONT_IF_BRANCH, valk_eval_apply_func_iter body unwrap). A
// forbidden head nested inside a qexpr branch is still forbidden.
// Over-scanning quoted *data* (e.g. `'(= x 1)`) costs us a slow-path
// compile but never miscompiles; skipping them misses the `=` inside an
// if-branch and silently writes formals to the AOT root env.
static bool body_has_forbidden_head(valk_lval_t *expr) {
  if (!expr) return false;
  if (LVAL_TYPE(expr) != LVAL_CONS) return false;
  valk_lval_t *head = expr->cons.head;
  if (head && LVAL_TYPE(head) == LVAL_SYM) {
    const char *s = head->str;
    if (strcmp(s, "\\") == 0 || strcmp(s, "fn") == 0 ||
        strcmp(s, "def") == 0 || strcmp(s, "=") == 0) {
      return true;
    }
  }
  for (valk_lval_t *c = expr; c && LVAL_TYPE(c) == LVAL_CONS; c = c->cons.tail) {
    if (body_has_forbidden_head(c->cons.head)) return true;
  }
  return false;
}

bool valk_llvm_body_is_fast_safe(valk_lval_t *body) {
  if (!body) return true;
  valk_lval_t *eff = body;
  if (LVAL_TYPE(eff) == LVAL_CONS && (eff->flags & LVAL_FLAG_QUOTED)) {
    eff = valk_qexpr_to_cons(eff);
  }
  if (eff && LVAL_TYPE(eff) == LVAL_CONS) {
    for (valk_lval_t *c = eff; c && LVAL_TYPE(c) == LVAL_CONS;
         c = c->cons.tail) {
      if (body_has_forbidden_head(c->cons.head)) return false;
    }
  }
  return true;
}

LLVMValueRef valk_llvm_compile_lambda_body_fast(valk_llvm_ctx_t *ctx,
                                                valk_lval_t *body,
                                                valk_lval_t *formals,
                                                const char *fn_name) {
  // Collect formal names, skipping `&` varargs. (Fast variant doesn't
  // support varargs — build_aot.c already filters these out.)
  size_t nformals = 0;
  for (valk_lval_t *f = formals; f && LVAL_TYPE(f) == LVAL_CONS;
       f = f->cons.tail) {
    valk_lval_t *fh = f->cons.head;
    if (!fh || LVAL_TYPE(fh) != LVAL_SYM) return nullptr;
    if (strcmp(fh->str, "&") == 0) return nullptr;
    nformals++;
  }

  LLVMTypeRef *params = malloc(sizeof(LLVMTypeRef) * (nformals + 1));
  params[0] = ctx->ptr_type;
  for (size_t i = 0; i < nformals; i++) params[i + 1] = ctx->ptr_type;
  LLVMTypeRef fn_type = LLVMFunctionType(ctx->ptr_type, params,
                                         (unsigned)(nformals + 1), 0);
  free(params);

  // Reuse a pre-declared function if one exists (build_aot.c declares all
  // fast variants upfront so mutually-recursive bodies can resolve each
  // other). Otherwise add a fresh one.
  LLVMValueRef fn = LLVMGetNamedFunction(ctx->module, fn_name);
  if (!fn) {
    fn = LLVMAddFunction(ctx->module, fn_name, fn_type);
    LLVMSetLinkage(fn, LLVMExternalLinkage);
  }

  // Stage 3 TCO layout:
  //   entry_bb:  br body_bb
  //   body_bb:   formal_phi_i = phi [ param_i, entry_bb ], [ new_i, tail_call_bb ]
  //              ... body IR ...
  //              ret result
  // A self-recursive tail call adds an incoming to the formal phis and
  // branches to body_bb instead of invoking a fresh fast call.
  LLVMBasicBlockRef entry_bb =
    LLVMAppendBasicBlockInContext(ctx->ctx, fn, "entry");
  LLVMBasicBlockRef body_bb =
    LLVMAppendBasicBlockInContext(ctx->ctx, fn, "body");
  LLVMPositionBuilderAtEnd(ctx->builder, entry_bb);
  LLVMBuildBr(ctx->builder, body_bb);

  LLVMPositionBuilderAtEnd(ctx->builder, body_bb);

  // Anchor the sym cache on entry_bb — it dominates every use site
  // (body_bb and everything reachable from it). Hoisted allocs land
  // between entry_bb's existing `br body_bb` terminator and the start
  // of entry_bb, one per unique sym name.
  sym_cache_enter(ctx, entry_bb);

  LLVMValueRef env_param = LLVMGetParam(fn, 0);

  // Phi nodes for formals. Initial incoming is the matching fn param
  // from entry_bb. try_codegen_direct_call adds tail-call incomings.
  LLVMValueRef *formal_phis = malloc(sizeof(*formal_phis) * nformals);
  const char **names = malloc(sizeof(*names) * nformals);
  valk_lval_t *f = formals;
  for (size_t i = 0; i < nformals; i++) {
    names[i] = f->cons.head->str;
    formal_phis[i] = LLVMBuildPhi(ctx->builder, ctx->ptr_type, "formal.phi");
    LLVMValueRef init = LLVMGetParam(fn, (unsigned)(i + 1));
    LLVMAddIncoming(formal_phis[i], &init, &entry_bb, 1);
    f = f->cons.tail;
  }

  ctx->formals_map.names = names;
  ctx->formals_map.vals = formal_phis;
  ctx->formals_map.count = nformals;
  ctx->tco.fn = fn;
  ctx->tco.body_bb = body_bb;
  ctx->tco.env_phi = nullptr;  // env is invariant across tail calls
  ctx->tco.formal_phis = formal_phis;
  ctx->tco.nformals = nformals;

  // BYOL error short-circuit: TW's CONT_COLLECT_ARG returns the error
  // without invoking user lambdas if any arg is LVAL_ERR. AOT must match
  // or recursive walkers loop forever on error input (see eval.c:636).
  // Emit this check in body_bb so TCO tail-call incomings get re-checked.
  if (nformals > 0) {
    LLVMBasicBlockRef err_bb =
      LLVMAppendBasicBlockInContext(ctx->ctx, fn, "byol.err");
    LLVMBasicBlockRef cont_bb =
      LLVMAppendBasicBlockInContext(ctx->ctx, fn, "body.cont");
    LLVMValueRef type_mask =
      LLVMConstInt(ctx->i64_type, LVAL_TYPE_MASK, 0);
    LLVMValueRef err_const =
      LLVMConstInt(ctx->i64_type, LVAL_ERR, 0);
    LLVMValueRef flags_off =
      LLVMConstInt(ctx->i64_type, offsetof(valk_lval_t, flags), 0);
    LLVMValueRef null_ptr = LLVMConstNull(ctx->ptr_type);
    LLVMValueRef first_err = null_ptr;
    LLVMValueRef any_err = LLVMConstInt(ctx->i1_type, 0, 0);
    for (size_t i = 0; i < nformals; i++) {
      LLVMValueRef flags_ptr = LLVMBuildInBoundsGEP2(
        ctx->builder, ctx->i8_type, formal_phis[i], &flags_off, 1,
        "byol.flags_ptr");
      LLVMValueRef flags = LLVMBuildLoad2(
        ctx->builder, ctx->i64_type, flags_ptr, "byol.flags");
      LLVMValueRef type = LLVMBuildAnd(
        ctx->builder, flags, type_mask, "byol.type");
      LLVMValueRef is_err = LLVMBuildICmp(
        ctx->builder, LLVMIntEQ, type, err_const, "byol.is_err");
      first_err = LLVMBuildSelect(
        ctx->builder, is_err, formal_phis[i], first_err, "byol.first_err");
      any_err = LLVMBuildOr(
        ctx->builder, any_err, is_err, "byol.any_err");
    }
    LLVMBuildCondBr(ctx->builder, any_err, err_bb, cont_bb);
    LLVMPositionBuilderAtEnd(ctx->builder, err_bb);
    LLVMBuildRet(ctx->builder, first_err);
    LLVMPositionBuilderAtEnd(ctx->builder, cont_bb);
  }

  LLVMValueRef result = codegen_nil(ctx);
  valk_lval_t *eff = body;
  if (eff && LVAL_TYPE(eff) == LVAL_CONS && (eff->flags & LVAL_FLAG_QUOTED)) {
    eff = valk_qexpr_to_cons(eff);
  }
  if (eff && LVAL_TYPE(eff) == LVAL_CONS) {
    valk_lval_t *first = eff->cons.head;
    bool first_is_list = first && LVAL_TYPE(first) == LVAL_CONS;
    u64 count = valk_lval_list_count(eff);
    if (first_is_list) {
      // Multi-statement body: only the final stmt is in tail position.
      valk_lval_t *cur = eff;
      while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        bool last = !(cur->cons.tail && LVAL_TYPE(cur->cons.tail) == LVAL_CONS);
        ctx->in_tail = last;
        result = codegen_expr(ctx, cur->cons.head, env_param);
        cur = cur->cons.tail;
      }
    } else if (count == 1) {
      ctx->in_tail = true;
      result = codegen_expr(ctx, first, env_param);
    } else {
      ctx->in_tail = true;
      result = codegen_expr(ctx, eff, env_param);
    }
  } else if (eff) {
    ctx->in_tail = true;
    result = codegen_expr(ctx, eff, env_param);
  }

  ctx->in_tail = false;
  ctx->formals_map.names = nullptr;
  ctx->formals_map.vals = nullptr;
  ctx->formals_map.count = 0;
  ctx->tco.fn = nullptr;
  ctx->tco.body_bb = nullptr;
  ctx->tco.formal_phis = nullptr;
  ctx->tco.nformals = 0;
  free(names);
  free(formal_phis);

  LLVMBuildRet(ctx->builder, result);
  sym_cache_leave(ctx);
  return fn;
}

LLVMValueRef valk_llvm_compile_lambda_body_slow_adapter(
    valk_llvm_ctx_t *ctx, valk_lval_t *formals,
    const char *slow_name, const char *fast_name) {
  size_t nformals = 0;
  for (valk_lval_t *f = formals; f && LVAL_TYPE(f) == LVAL_CONS;
       f = f->cons.tail) {
    nformals++;
  }

  LLVMTypeRef slow_type = LLVMFunctionType(ctx->ptr_type,
    (LLVMTypeRef[]){ctx->ptr_type}, 1, 0);
  LLVMValueRef slow_fn = LLVMGetNamedFunction(ctx->module, slow_name);
  if (!slow_fn) {
    slow_fn = LLVMAddFunction(ctx->module, slow_name, slow_type);
    LLVMSetLinkage(slow_fn, LLVMExternalLinkage);
  }

  LLVMBasicBlockRef entry =
    LLVMAppendBasicBlockInContext(ctx->ctx, slow_fn, "entry");
  LLVMPositionBuilderAtEnd(ctx->builder, entry);

  LLVMValueRef call_env = LLVMGetParam(slow_fn, 0);

  // Build fast signature: (env, formal_0, ..., formal_N-1).
  LLVMTypeRef *fparams = malloc(sizeof(LLVMTypeRef) * (nformals + 1));
  fparams[0] = ctx->ptr_type;
  for (size_t i = 0; i < nformals; i++) fparams[i + 1] = ctx->ptr_type;
  LLVMTypeRef fast_type = LLVMFunctionType(ctx->ptr_type, fparams,
                                           (unsigned)(nformals + 1), 0);
  free(fparams);
  LLVMValueRef fast_fn = LLVMGetNamedFunction(ctx->module, fast_name);
  if (!fast_fn) {
    fast_fn = LLVMAddFunction(ctx->module, fast_name, fast_type);
    LLVMSetLinkage(fast_fn, LLVMExternalLinkage);
  }

  LLVMTypeRef get_ty = LLVMFunctionType(ctx->ptr_type,
    (LLVMTypeRef[]){ctx->ptr_type, ctx->ptr_type}, 2, 0);

  LLVMValueRef *args = malloc(sizeof(LLVMValueRef) * (nformals + 1));
  LLVMValueRef root_env_global =
    LLVMGetNamedGlobal(ctx->module, "valk_aot_root_env");
  if (!root_env_global) {
    root_env_global = LLVMAddGlobal(ctx->module, ctx->ptr_type,
                                    "valk_aot_root_env");
    LLVMSetLinkage(root_env_global, LLVMExternalLinkage);
  }
  args[0] = LLVMBuildLoad2(ctx->builder, ctx->ptr_type, root_env_global,
                           "aot_root");

  valk_lval_t *f = formals;
  for (size_t i = 0; i < nformals; i++) {
    LLVMValueRef sym = emit_make_sym(ctx, f->cons.head->str);
    LLVMValueRef get_args[] = {call_env, sym};
    args[i + 1] = LLVMBuildCall2(ctx->builder, get_ty, ctx->fn_lenv_get,
                                 get_args, 2, "formal");
    f = f->cons.tail;
  }

  LLVMValueRef ret = LLVMBuildCall2(ctx->builder, fast_type, fast_fn,
                                    args, (unsigned)(nformals + 1), "fast");
  LLVMSetTailCall(ret, 1);
  LLVMBuildRet(ctx->builder, ret);
  free(args);

  return slow_fn;
}

LLVMValueRef valk_llvm_compile_lambda_body(valk_llvm_ctx_t *ctx,
                                           valk_lval_t *body,
                                           const char *fn_name) {
  LLVMTypeRef fn_type = LLVMFunctionType(ctx->ptr_type,
    (LLVMTypeRef[]){ctx->ptr_type}, 1, 0);
  LLVMValueRef fn = LLVMAddFunction(ctx->module, fn_name, fn_type);
  LLVMSetLinkage(fn, LLVMExternalLinkage);

  LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(ctx->ctx, fn, "entry");
  LLVMPositionBuilderAtEnd(ctx->builder, entry);
  sym_cache_enter(ctx, entry);

  LLVMValueRef env_param = LLVMGetParam(fn, 0);
  LLVMValueRef result = codegen_nil(ctx);

  // Mirror tree-walker body semantics (see src/eval.c valk_eval_apply_func_iter
  // plus the count==1 single-elem special case in valk_lval_eval_iterative):
  //   - unwrap outer qexpr to cons
  //   - if first elem is a list → multi-statement body (compile each head)
  //   - else if list has exactly one element → evaluate that element directly
  //     (matches SINGLE_ELEM continuation, so `{precomputed}` yields the
  //     bound value instead of trying to call it)
  //   - else → compile the cons as a regular s-expr (function call)
  valk_lval_t *eff = body;
  if (eff && LVAL_TYPE(eff) == LVAL_CONS && (eff->flags & LVAL_FLAG_QUOTED)) {
    eff = valk_qexpr_to_cons(eff);
  }

  if (eff && LVAL_TYPE(eff) == LVAL_CONS) {
    valk_lval_t *first = eff->cons.head;
    bool first_is_list = first && LVAL_TYPE(first) == LVAL_CONS;
    u64 count = valk_lval_list_count(eff);
    if (first_is_list) {
      valk_lval_t *cur = eff;
      while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
        result = codegen_expr(ctx, cur->cons.head, env_param);
        cur = cur->cons.tail;
      }
    } else if (count == 1) {
      result = codegen_expr(ctx, first, env_param);
    } else {
      result = codegen_expr(ctx, eff, env_param);
    }
  } else if (eff) {
    result = codegen_expr(ctx, eff, env_param);
  }

  LLVMBuildRet(ctx->builder, result);
  sym_cache_leave(ctx);
  return fn;
}

LLVMValueRef valk_llvm_compile_toplevel(valk_llvm_ctx_t *ctx,
                                        valk_lval_t *expr) {
  char name[64];
  snprintf(name, sizeof(name), "__valk_expr_%llu",
    (unsigned long long)ctx->expr_counter++);

  LLVMTypeRef fn_type = LLVMFunctionType(ctx->ptr_type,
    (LLVMTypeRef[]){ctx->ptr_type}, 1, 0);
  LLVMValueRef fn = LLVMAddFunction(ctx->module, name, fn_type);
  LLVMSetLinkage(fn, LLVMExternalLinkage);

  LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(ctx->ctx, fn, "entry");
  LLVMPositionBuilderAtEnd(ctx->builder, entry);
  sym_cache_enter(ctx, entry);

  LLVMValueRef env_param = LLVMGetParam(fn, 0);
  LLVMValueRef result = codegen_expr(ctx, expr, env_param);

  LLVMBuildRet(ctx->builder, result);
  sym_cache_leave(ctx);
  return fn;
}

LLVMValueRef valk_llvm_compile_program(valk_llvm_ctx_t *ctx,
                                       valk_lval_t *exprs) {
  u64 count = 0;
  valk_lval_t *cur = exprs;
  while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
    count++;
    cur = cur->cons.tail;
  }

  LLVMValueRef *fns = malloc(sizeof(LLVMValueRef) * count);
  cur = exprs;
  for (u64 i = 0; i < count; i++) {
    fns[i] = valk_llvm_compile_toplevel(ctx, cur->cons.head);
    cur = cur->cons.tail;
  }

  LLVMTypeRef main_type = LLVMFunctionType(ctx->ptr_type,
    (LLVMTypeRef[]){ctx->ptr_type}, 1, 0);
  LLVMValueRef main_fn = LLVMAddFunction(ctx->module, "__valk_main", main_type);
  LLVMSetLinkage(main_fn, LLVMExternalLinkage);

  LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(ctx->ctx, main_fn, "entry");
  LLVMPositionBuilderAtEnd(ctx->builder, entry);

  LLVMValueRef env_param = LLVMGetParam(main_fn, 0);
  LLVMValueRef result = codegen_nil(ctx);

  LLVMTypeRef fn_type = LLVMFunctionType(ctx->ptr_type,
    (LLVMTypeRef[]){ctx->ptr_type}, 1, 0);

  for (u64 i = 0; i < count; i++) {
    result = LLVMBuildCall2(ctx->builder, fn_type, fns[i],
      &env_param, 1, "expr.result");
  }

  LLVMBuildRet(ctx->builder, result);
  free(fns);
  return main_fn;
}

char *valk_llvm_dump_ir(valk_llvm_ctx_t *ctx) {
  return LLVMPrintModuleToString(ctx->module);
}

bool valk_llvm_verify(valk_llvm_ctx_t *ctx, char **error) {
  char *err = NULL;
  LLVMBool failed = LLVMVerifyModule(ctx->module,
    LLVMReturnStatusAction, &err);
  if (failed) {
    if (error) *error = err;
    else LLVMDisposeMessage(err);
    return false;
  }
  if (err) LLVMDisposeMessage(err);
  return true;
}
