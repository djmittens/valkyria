#include "vir_to_llvm.h"
#include "llvm_codegen_internal.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

typedef struct {
  valk_llvm_ctx_t *c;
  LLVMValueRef *val_map;
  u32 val_map_size;
  LLVMBasicBlockRef *bb_map;
  u32 bb_map_cap;
  LLVMValueRef fn_gc_safepoint;
  // Set true by tail-call lowering after it emits its own ret. Tells
  // the loop to skip the next VIR_RET (which ast_to_vir's lower_tail
  // emitted as a placeholder — musttail must be the last inst before
  // ret in the same basic block, so we emit ret right after the call).
  bool skip_next_ret;
} lower_ctx_t;

static void ensure_val_map(lower_ctx_t *ctx, u32 id) {
  if (id >= ctx->val_map_size) {
    u32 new_size = (id + 1) * 2;
    ctx->val_map = realloc(ctx->val_map, new_size * sizeof(LLVMValueRef));
    memset(ctx->val_map + ctx->val_map_size, 0,
           (new_size - ctx->val_map_size) * sizeof(LLVMValueRef));
    ctx->val_map_size = new_size;
  }
}

static void ensure_bb_map(lower_ctx_t *ctx, u32 id) {
  if (id >= ctx->bb_map_cap) {
    u32 new_size = (id + 1) * 2;
    ctx->bb_map = realloc(ctx->bb_map, new_size * sizeof(LLVMBasicBlockRef));
    memset(ctx->bb_map + ctx->bb_map_cap, 0,
           (new_size - ctx->bb_map_cap) * sizeof(LLVMBasicBlockRef));
    ctx->bb_map_cap = new_size;
  }
}

static void set_val(lower_ctx_t *ctx, u32 id, LLVMValueRef val) {
  ensure_val_map(ctx, id);
  ctx->val_map[id] = val;
}

static LLVMValueRef get_val(lower_ctx_t *ctx, u32 id) {
  if (id < ctx->val_map_size) return ctx->val_map[id];
  return NULL;
}

static LLVMBasicBlockRef get_bb(lower_ctx_t *ctx, u32 id) {
  if (id < ctx->bb_map_cap) return ctx->bb_map[id];
  return NULL;
}

static LLVMValueRef emit_global_str(lower_ctx_t *ctx, const char *str) {
  char name[64];
  snprintf(name, sizeof(name), ".str.%llu",
    (unsigned long long)ctx->c->str_counter++);
  return LLVMBuildGlobalStringPtr(ctx->c->builder, str, name);
}

static LLVMValueRef call1(lower_ctx_t *ctx, LLVMValueRef fn,
                          LLVMTypeRef ret, LLVMValueRef arg,
                          const char *name) {
  LLVMTypeRef ft = LLVMFunctionType(ret, (LLVMTypeRef[]){
    LLVMTypeOf(arg)}, 1, 0);
  return LLVMBuildCall2(ctx->c->builder, ft, fn, &arg, 1, name);
}

static LLVMValueRef call2(lower_ctx_t *ctx, LLVMValueRef fn,
                          LLVMTypeRef ret, LLVMValueRef a, LLVMValueRef b,
                          const char *name) {
  LLVMValueRef args[] = {a, b};
  LLVMTypeRef ft = LLVMFunctionType(ret, (LLVMTypeRef[]){
    LLVMTypeOf(a), LLVMTypeOf(b)}, 2, 0);
  return LLVMBuildCall2(ctx->c->builder, ft, fn, args, 2, name);
}

static LLVMValueRef call3(lower_ctx_t *ctx, LLVMValueRef fn,
                          LLVMTypeRef ret, LLVMValueRef a,
                          LLVMValueRef b, LLVMValueRef d,
                          const char *name) {
  LLVMValueRef args[] = {a, b, d};
  LLVMTypeRef ft = LLVMFunctionType(ret, (LLVMTypeRef[]){
    LLVMTypeOf(a), LLVMTypeOf(b), LLVMTypeOf(d)}, 3, 0);
  return LLVMBuildCall2(ctx->c->builder, ft, fn, args, 3, name);
}

static void declare_gc_fns(lower_ctx_t *ctx, LLVMModuleRef mod) {
  valk_llvm_ctx_t *c = ctx->c;
  LLVMTypeRef vd = c->void_type;

  // Only the safepoint poll remains. GC roots are discovered by the
  // runtime's conservative native-stack scan at every STW pause; the
  // compiler doesn't emit any root tracking.
  //
  // Reuse the existing extern declaration if another vir_to_llvm_func
  // call already added it to this module. Without the GetNamed check
  // LLVM appends a unique suffix (.21, .22, ...) for every duplicate
  // declaration, producing "undefined reference to valk_gc_safepoint_fn.21"
  // at link time. build_aot.c calls vir_to_llvm_func once per AOT
  // candidate sharing one LLVM module, so dedup is required.
  ctx->fn_gc_safepoint = LLVMGetNamedFunction(mod, "valk_gc_safepoint_fn");
  if (!ctx->fn_gc_safepoint) {
    ctx->fn_gc_safepoint = LLVMAddFunction(mod, "valk_gc_safepoint_fn",
      LLVMFunctionType(vd, NULL, 0, 0));
  }
}

static LLVMValueRef lower_value(lower_ctx_t *ctx, vir_value_t *v) {
  valk_llvm_ctx_t *c = ctx->c;
  LLVMValueRef result = NULL;

  switch (v->opcode) {
    case VIR_CONST_NUM: {
      LLVMValueRef num = LLVMConstInt(c->i64_type, (u64)v->num_val, 1);
      result = call1(ctx, c->fn_lval_num, c->ptr_type, num, "num");
      break;
    }
    case VIR_CONST_STR: {
      LLVMValueRef str = emit_global_str(ctx, v->str_val);
      result = call1(ctx, c->fn_lval_str, c->ptr_type, str, "str");
      break;
    }
    case VIR_CONST_NIL: {
      LLVMTypeRef ft = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
      result = LLVMBuildCall2(c->builder, ft, c->fn_lval_nil, NULL, 0, "nil");
      break;
    }
    case VIR_CONST_SYM: {
      // Use cached sym (one alloc per unique name per function).
      result = valk_codegen_emit_make_sym(c, v->str_val);
      break;
    }

    case VIR_TRUTHY: {
      LLVMValueRef op = get_val(ctx, v->operands[0]->id);
      result = call1(ctx, c->fn_lval_is_truthy, c->i1_type, op, "truthy");
      break;
    }

    case VIR_ENV_GET: {
      LLVMValueRef env = get_val(ctx, v->operands[0]->id);
      LLVMValueRef sym_val = valk_codegen_emit_make_sym(c, v->str_val);
      result = call2(ctx, c->fn_lenv_get, c->ptr_type, env, sym_val, "get");
      break;
    }
    case VIR_ENV_PUT:
    case VIR_ENV_DEF: {
      LLVMValueRef env = get_val(ctx, v->operands[0]->id);
      LLVMValueRef val = get_val(ctx, v->operands[1]->id);
      LLVMValueRef sym_val = valk_codegen_emit_make_sym(c, v->str_val);
      LLVMValueRef fn = (v->opcode == VIR_ENV_DEF) ?
                         c->fn_lenv_def : c->fn_lenv_put;
      call3(ctx, fn, c->void_type, env, sym_val, val, "");
      break;
    }

    case VIR_CONS:
    case VIR_QCONS: {
      LLVMValueRef head = get_val(ctx, v->operands[0]->id);
      LLVMValueRef tail = get_val(ctx, v->operands[1]->id);
      LLVMValueRef fn = (v->opcode == VIR_QCONS) ?
                         c->fn_lval_qcons : c->fn_lval_cons;
      result = call2(ctx, fn, c->ptr_type, head, tail,
                     v->opcode == VIR_QCONS ? "qcons" : "cons");
      break;
    }

    case VIR_LAMBDA: {
      LLVMValueRef env = get_val(ctx, v->operands[0]->id);
      LLVMValueRef formals = get_val(ctx, v->operands[1]->id);
      LLVMValueRef body = get_val(ctx, v->operands[2]->id);
      result = call3(ctx, c->fn_lval_lambda, c->ptr_type,
                     env, formals, body, "lambda");
      break;
    }

    case VIR_CALL:
    case VIR_TAIL_CALL: {
      LLVMValueRef fn_val = get_val(ctx, v->operands[0]->id);
      LLVMValueRef args_list = get_val(ctx, v->call.args[0]->id);
      LLVMValueRef call_inst = call3(ctx, c->fn_lval_eval_call, c->ptr_type,
                     get_val(ctx, v->parent->parent->params[0]->id),
                     fn_val, args_list, "call");
      result = call_inst;
      // Tail-position indirect call: hint to LLVM (TailCallKindTail, not
      // MustTail) — LLVM may sibcall when convenient. We can't use
      // musttail here because eval_call's signature (3 ptrs) doesn't
      // match the compiled fn's signature (1 ptr); LLVM verifier
      // rejects musttail with mismatched signatures. The hint still
      // helps the optimizer pick sibcall when the calling convention
      // and stack layout permit it; if not, it's a regular call (and
      // grows the C stack — but only for indirect calls, the common
      // self-recursive case uses VIR_DIRECT_CALL which CAN musttail).
      if (v->call.is_tail) {
        LLVMSetTailCallKind(call_inst, LLVMTailCallKindTail);
      }
      break;
    }

    case VIR_DIRECT_CALL: {
      // Build a fresh call_env, parent = valk_aot_root_env (the global
      // env loaded by the AOT main shim before any compiled code runs).
      // lenv_put each formal name → arg value. Then call the target's
      // slow ABI: native_fn(call_env). Mirrors codegen_try_direct_call's
      // slow fallback in llvm_codegen_call.c.
      u32 nargs = v->direct_call.nargs;
      LLVMTypeRef empty_ty = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
      LLVMValueRef call_env = LLVMBuildCall2(c->builder, empty_ty,
        c->fn_lenv_empty, NULL, 0, "call_env");

      // Set call_env->parent = root_env. parent is at offset
      // offsetof(valk_lenv_t, parent), which we hardcode here as
      // 56 to match the OLD codegen — it does the same direct field
      // store. (sizeof(valk_lenv_t) layout: flags 8 + symbols.items 8
      // + symbols.count 8 + symbols.capacity 8 + vals.items 8 + vals.count 8
      // + vals.capacity 8 = 56 bytes before parent.)
      LLVMValueRef root_env_global =
        LLVMGetNamedGlobal(c->module, "valk_aot_root_env");
      if (!root_env_global) {
        root_env_global = LLVMAddGlobal(c->module, c->ptr_type,
          "valk_aot_root_env");
        LLVMSetLinkage(root_env_global, LLVMExternalLinkage);
      }
      LLVMValueRef root_env = LLVMBuildLoad2(c->builder, c->ptr_type,
        root_env_global, "aot_root");
      LLVMValueRef parent_off = LLVMConstInt(c->i64_type, 56, 0);
      LLVMValueRef parent_ptr = LLVMBuildInBoundsGEP2(c->builder, c->i8_type,
        call_env, &parent_off, 1, "parent_ptr");
      LLVMBuildStore(c->builder, root_env, parent_ptr);

      // lenv_put each formal.
      LLVMTypeRef put_ty = LLVMFunctionType(c->void_type,
        (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
      for (u32 i = 0; i < nargs; i++) {
        LLVMValueRef arg = get_val(ctx, v->direct_call.arg_vals[i]->id);
        LLVMValueRef sym = valk_codegen_emit_make_sym(c,
          v->direct_call.formal_names[i]);
        LLVMValueRef pa[] = {call_env, sym, arg};
        LLVMBuildCall2(c->builder, put_ty, c->fn_lenv_put, pa, 3, "");
      }

      // Call the target's compiled function.
      LLVMTypeRef target_ty = LLVMFunctionType(c->ptr_type,
        (LLVMTypeRef[]){c->ptr_type}, 1, 0);
      LLVMValueRef target_fn = LLVMGetNamedFunction(c->module,
        v->direct_call.native_name);
      if (!target_fn) {
        target_fn = LLVMAddFunction(c->module, v->direct_call.native_name,
          target_ty);
        LLVMSetLinkage(target_fn, LLVMExternalLinkage);
      }
      result = LLVMBuildCall2(c->builder, target_ty, target_fn,
        &call_env, 1, "direct");
      // Tail-position direct call → musttail + immediate ret. LLVM
      // sibcalls these, so chains of direct AOT-to-AOT calls don't
      // grow the C stack regardless of recursion depth.
      if (v->direct_call.is_tail) {
        LLVMSetTailCallKind(result, LLVMTailCallKindMustTail);
        LLVMBuildRet(c->builder, result);
        ctx->skip_next_ret = true;
      }
      break;
    }

    case VIR_BR:
      LLVMBuildBr(c->builder, (LLVMBasicBlockRef)get_bb(ctx, v->br.target->id));
      break;

    case VIR_BR_IF: {
      LLVMValueRef cond = get_val(ctx, v->operands[0]->id);
      LLVMBuildCondBr(c->builder, cond,
        (LLVMBasicBlockRef)get_bb(ctx, v->br_if.true_bb->id),
        (LLVMBasicBlockRef)get_bb(ctx, v->br_if.false_bb->id));
      break;
    }

    case VIR_RET: {
      // A tail call already emitted its own ret immediately after the
      // musttail call; this VIR_RET is the placeholder that ast_to_vir
      // emits unconditionally. Skip it (the basic block is already
      // terminated).
      if (ctx->skip_next_ret) {
        ctx->skip_next_ret = false;
        break;
      }
      LLVMValueRef val = get_val(ctx, v->operands[0]->id);
      LLVMBuildRet(c->builder, val);
      break;
    }

    case VIR_PHI:
      result = LLVMBuildPhi(c->builder, c->ptr_type, "phi");
      break;

    case VIR_GC_SAFEPOINT: {
      LLVMTypeRef ft = LLVMFunctionType(c->void_type, NULL, 0, 0);
      LLVMBuildCall2(c->builder, ft, ctx->fn_gc_safepoint, NULL, 0, "");
      break;
    }

    default:
      fprintf(stderr, "vir_to_llvm: unhandled opcode %s (%d)\n",
              vir_opcode_name(v->opcode), v->opcode);
      abort();
  }

  if (result) set_val(ctx, v->id, result);
  return result;
}

static void fixup_phis(lower_ctx_t *ctx, vir_func_t *fn) {
  vir_block_t *bb = fn->block_list;
  while (bb) {
    vir_value_t *v = bb->first;
    while (v) {
      if (v->opcode == VIR_PHI) {
        LLVMValueRef phi = get_val(ctx, v->id);
        if (phi && v->phi.num_incoming > 0) {
          LLVMValueRef *vals = calloc(v->phi.num_incoming,
                                      sizeof(LLVMValueRef));
          LLVMBasicBlockRef *bbs = calloc(v->phi.num_incoming,
                                          sizeof(LLVMBasicBlockRef));
          for (u32 i = 0; i < v->phi.num_incoming; i++) {
            vals[i] = get_val(ctx, v->phi.incoming_vals[i]->id);
            bbs[i] = (LLVMBasicBlockRef)get_bb(ctx, v->phi.incoming_blocks[i]->id);
          }
          LLVMAddIncoming(phi, vals, bbs, v->phi.num_incoming);
          free(vals);
          free(bbs);
        }
      }
      v = v->next;
    }
    bb = bb->next;
  }
}

LLVMValueRef vir_to_llvm_func(valk_llvm_ctx_t *c, vir_func_t *fn) {
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, fn->num_params, 0);
  // Reuse a forward-declared function if one exists with this name.
  // build_aot.c's phase 1 pre-declares all candidate names so phase 2
  // bodies (compiled here) can resolve direct calls to forward-defined
  // siblings. Without this lookup, we'd add a second function with a
  // suffixed name (.1) and the original declaration would link as an
  // undefined extern.
  LLVMValueRef llvm_fn = LLVMGetNamedFunction(c->module, fn->name);
  if (!llvm_fn) {
    llvm_fn = LLVMAddFunction(c->module, fn->name, fn_type);
  }
  LLVMSetLinkage(llvm_fn, LLVMExternalLinkage);

  lower_ctx_t ctx = {.c = c};
  declare_gc_fns(&ctx, c->module);

  for (u32 i = 0; i < fn->num_params; i++)
    set_val(&ctx, fn->params[i]->id, LLVMGetParam(llvm_fn, i));

  vir_block_t *bb = fn->block_list;
  while (bb) {
    LLVMBasicBlockRef llvm_bb = LLVMAppendBasicBlockInContext(
      c->ctx, llvm_fn, bb->name);
    ensure_bb_map(&ctx, bb->id);
    ctx.bb_map[bb->id] = llvm_bb;
    bb = bb->next;
  }

  // Anchor the per-fn sym cache at the entry block. valk_codegen_emit_make_sym
  // hoists each unique symbol's `valk_lval_sym` call here and reuses the
  // cached SSA value at every subsequent reference. Without this, every
  // env_get / direct_call / qcons builds a fresh sym on every dispatch,
  // which is the dominant alloc cost in compiled code (LSP startup
  // touches ~1500 unique syms; with cache it's 1500 allocs per call,
  // not 1500*N).
  LLVMBasicBlockRef anchor = (LLVMBasicBlockRef)get_bb(&ctx,
    fn->block_list->id);
  valk_codegen_sym_cache_enter(c, anchor);

  bb = fn->block_list;
  while (bb) {
    LLVMPositionBuilderAtEnd(c->builder,
      (LLVMBasicBlockRef)get_bb(&ctx, bb->id));
    vir_value_t *v = bb->first;
    while (v) {
      lower_value(&ctx, v);
      v = v->next;
    }
    bb = bb->next;
  }

  valk_codegen_sym_cache_leave(c);

  fixup_phis(&ctx, fn);

  free(ctx.val_map);
  free(ctx.bb_map);
  return llvm_fn;
}

void vir_to_llvm_module(valk_llvm_ctx_t *ctx, vir_module_t *vmod) {
  vir_func_t *fn = vmod->func_list;
  while (fn) {
    vir_to_llvm_func(ctx, fn);
    fn = fn->next;
  }
}
