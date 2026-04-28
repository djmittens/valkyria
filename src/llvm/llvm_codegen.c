#include "llvm_codegen.h"
#include "llvm_codegen_internal.h"
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

// Encoded `memory(argmem: read)` for the LLVM `memory` attribute (LLVM 16+
// replaced readonly/argmemonly with a single bitmask-encoded attribute).
// 3 locations × 2 bits — ArgMem(0), InaccessibleMem(1), Other(2); each
// holds {NoModRef=0, Ref=1, Mod=2, ModRef=3}. argmem:read ⇒ bitmask = 1.
#define VALK_MEMEFFECTS_ARGMEM_READ ((uint64_t)1)

static void add_argmem_read_attr(valk_llvm_ctx_t *c, LLVMValueRef fn) {
  unsigned kind = LLVMGetEnumAttributeKindForName("memory", 6);
  if (kind == 0) return;
  LLVMAttributeRef attr = LLVMCreateEnumAttribute(
    c->ctx, kind, VALK_MEMEFFECTS_ARGMEM_READ);
  LLVMAddAttributeAtIndex(fn, LLVMAttributeFunctionIndex, attr);
}

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

static LLVMValueRef codegen_sexpr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                  LLVMValueRef env_param) {
  valk_lval_t *head = expr->cons.head;
  valk_lval_t *rest = expr->cons.tail;
  u64 argc = 0;
  if (rest && LVAL_TYPE(rest) == LVAL_CONS)
    argc = valk_codegen_cons_list_len(rest);

  if (LVAL_TYPE(head) == LVAL_SYM) {
    if (valk_codegen_is_sym(head, "if"))
      return valk_codegen_if(c, rest, argc, env_param);
    if (valk_codegen_is_sym(head, "do"))
      return valk_codegen_do(c, rest, argc, env_param);
    if (valk_codegen_is_sym(head, "def"))
      return valk_codegen_def(c, rest, argc, env_param, true);
    if (valk_codegen_is_sym(head, "="))
      return valk_codegen_def(c, rest, argc, env_param, false);
    if (valk_codegen_is_sym(head, "\\"))
      return valk_codegen_lambda(c, rest, argc, env_param);

    LLVMValueRef specialized =
      valk_codegen_try_numeric_binop(c, head, rest, argc, env_param);
    if (specialized) return specialized;

    LLVMValueRef direct =
      valk_codegen_try_direct_call(c, head, rest, argc, env_param);
    if (direct) return direct;
  }

  return valk_codegen_funcall(c, head, rest, argc, env_param);
}

LLVMValueRef valk_codegen_expr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                               LLVMValueRef env_param) {
  if (!expr) return valk_codegen_nil(c);

  valk_ltype_e type = LVAL_TYPE(expr);

  switch (type) {
    case LVAL_NUM:
      return valk_codegen_num(c, expr);
    case LVAL_STR:
      return valk_codegen_str(c, expr);
    case LVAL_NIL:
      return valk_codegen_nil(c);
    case LVAL_SYM:
      return valk_codegen_sym_lookup(c, expr, env_param);
    case LVAL_CONS: {
      bool quoted = (expr->flags & LVAL_FLAG_QUOTED) != 0;
      if (quoted)
        return valk_codegen_qexpr(c, expr, env_param);
      return codegen_sexpr(c, expr, env_param);
    }
    default:
      return valk_codegen_nil(c);
  }
}

LLVMValueRef valk_llvm_compile_expr(valk_llvm_ctx_t *ctx,
                                    valk_lval_t *expr,
                                    LLVMValueRef env_param) {
  return valk_codegen_expr(ctx, expr, env_param);
}

// Recursive scan: forbidden head = symbol in {`\`, `fn`, `def`, `=`}.
// Those forms capture or mutate call_env, which the fast variant doesn't
// build. Qexprs must be scanned too — qexpr branches are executed as
// code at runtime. Over-scanning quoted *data* costs a slow-path compile
// but never miscompiles.
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

  LLVMValueRef fn = LLVMGetNamedFunction(ctx->module, fn_name);
  if (!fn) {
    fn = LLVMAddFunction(ctx->module, fn_name, fn_type);
    LLVMSetLinkage(fn, LLVMExternalLinkage);
  }

  // Stage 3 TCO layout: entry_bb branches to body_bb whose phis re-bind
  // formals on each tail call instead of pushing a new stack frame.
  LLVMBasicBlockRef entry_bb =
    LLVMAppendBasicBlockInContext(ctx->ctx, fn, "entry");
  LLVMBasicBlockRef body_bb =
    LLVMAppendBasicBlockInContext(ctx->ctx, fn, "body");
  LLVMPositionBuilderAtEnd(ctx->builder, entry_bb);
  LLVMBuildBr(ctx->builder, body_bb);

  LLVMPositionBuilderAtEnd(ctx->builder, body_bb);

  valk_codegen_sym_cache_enter(ctx, entry_bb);

  LLVMValueRef env_param = LLVMGetParam(fn, 0);

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
  ctx->tco.env_phi = nullptr;
  ctx->tco.formal_phis = formal_phis;
  ctx->tco.nformals = nformals;

  // BYOL error short-circuit. See header comment on
  // valk_llvm_compile_lambda_body_fast for invariant.
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

  LLVMValueRef result = valk_codegen_nil(ctx);
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
        bool last = !(cur->cons.tail && LVAL_TYPE(cur->cons.tail) == LVAL_CONS);
        ctx->in_tail = last;
        result = valk_codegen_expr(ctx, cur->cons.head, env_param);
        cur = cur->cons.tail;
      }
    } else if (count == 1) {
      ctx->in_tail = true;
      result = valk_codegen_expr(ctx, first, env_param);
    } else {
      ctx->in_tail = true;
      result = valk_codegen_expr(ctx, eff, env_param);
    }
  } else if (eff) {
    ctx->in_tail = true;
    result = valk_codegen_expr(ctx, eff, env_param);
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
  valk_codegen_sym_cache_leave(ctx);
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
    LLVMValueRef sym = valk_codegen_emit_make_sym(ctx, f->cons.head->str);
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
  valk_codegen_sym_cache_enter(ctx, entry);

  LLVMValueRef env_param = LLVMGetParam(fn, 0);
  LLVMValueRef result = valk_codegen_nil(ctx);

  // Mirror tree-walker body semantics (eval.c valk_eval_apply_func_iter
  // + count==1 SINGLE_ELEM in valk_lval_eval_iterative).
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
        result = valk_codegen_expr(ctx, cur->cons.head, env_param);
        cur = cur->cons.tail;
      }
    } else if (count == 1) {
      result = valk_codegen_expr(ctx, first, env_param);
    } else {
      result = valk_codegen_expr(ctx, eff, env_param);
    }
  } else if (eff) {
    result = valk_codegen_expr(ctx, eff, env_param);
  }

  LLVMBuildRet(ctx->builder, result);
  valk_codegen_sym_cache_leave(ctx);
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
  valk_codegen_sym_cache_enter(ctx, entry);

  LLVMValueRef env_param = LLVMGetParam(fn, 0);
  LLVMValueRef result = valk_codegen_expr(ctx, expr, env_param);

  LLVMBuildRet(ctx->builder, result);
  valk_codegen_sym_cache_leave(ctx);
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
  LLVMValueRef result = valk_codegen_nil(ctx);

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
