#include "llvm_codegen_internal.h"
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

LLVMValueRef valk_codegen_funcall(valk_llvm_ctx_t *c, valk_lval_t *head,
                                  valk_lval_t *args_list, u64 argc,
                                  LLVMValueRef env_param) {
  bool saved_tail = c->in_tail;
  c->in_tail = false;

  LLVMValueRef fn_val = valk_codegen_expr(c, head, env_param);

  LLVMValueRef *arg_vals = malloc(sizeof(LLVMValueRef) * argc);
  valk_lval_t *cur = args_list;
  for (u64 i = 0; i < argc; i++) {
    arg_vals[i] = valk_codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }

  LLVMValueRef qargs = valk_codegen_build_qcons_list(c, arg_vals, argc);
  free(arg_vals);

  LLVMTypeRef call_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  LLVMValueRef call_args[] = {env_param, fn_val, qargs};
  LLVMValueRef ret = LLVMBuildCall2(c->builder, call_type, c->fn_lval_eval_call,
    call_args, 3, "call");
  c->in_tail = saved_tail;
  return ret;
}

// Stage 1: when `head` resolves in the build-time env to an LVAL_FUN
// lambda with `native_name` and matching arity, emit a direct call to
// that native fn. See llvm_codegen.h for the BYOL invariant the slow
// fallback path enforces here (`direct.err` block).
LLVMValueRef valk_codegen_try_direct_call(valk_llvm_ctx_t *c,
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

  valk_lval_t *formals = target->fun.formals;
  u64 nformals = 0;
  for (valk_lval_t *f = formals; f && LVAL_TYPE(f) == LVAL_CONS; f = f->cons.tail) {
    valk_lval_t *fh = f->cons.head;
    if (LVAL_TYPE(fh) == LVAL_SYM && strcmp(fh->str, "&") == 0) return nullptr;
    nformals++;
  }
  if (nformals != argc) return nullptr;

  bool saved_tail = c->in_tail;
  c->in_tail = false;
  LLVMValueRef *arg_vals = malloc(sizeof(LLVMValueRef) * argc);
  valk_lval_t *cur = args_list;
  for (u64 i = 0; i < argc; i++) {
    arg_vals[i] = valk_codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }
  c->in_tail = saved_tail;

  LLVMValueRef root_env_global = LLVMGetNamedGlobal(c->module, "valk_aot_root_env");
  if (!root_env_global) {
    root_env_global = LLVMAddGlobal(c->module, c->ptr_type, "valk_aot_root_env");
    LLVMSetLinkage(root_env_global, LLVMExternalLinkage);
  }

  // Stage 2: if a `_fast` variant exists, call it directly with the
  // evaluated args + root env. Bypasses call_env construction.
  char fast_name[80];
  snprintf(fast_name, sizeof fast_name, "%s_fast", target->fun.native_name);
  LLVMValueRef fast_fn = LLVMGetNamedFunction(c->module, fast_name);
  if (fast_fn) {
    // Stage 3: self-recursive tail call → feed body_bb phis + branch back.
    if (saved_tail && c->tco.fn && fast_fn == c->tco.fn &&
        argc == c->tco.nformals) {
      LLVMBasicBlockRef cur_bb = LLVMGetInsertBlock(c->builder);
      for (u64 i = 0; i < argc; i++) {
        LLVMAddIncoming(c->tco.formal_phis[i], &arg_vals[i], &cur_bb, 1);
      }
      LLVMBuildBr(c->builder, c->tco.body_bb);

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
    if (saved_tail) LLVMSetTailCall(ret, 1);
    free(fast_args);
    free(arg_vals);
    return ret;
  }

  // Slow fallback: BYOL error short-circuit + call_env construction.
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
    LLVMValueRef type =
        valk_codegen_emit_load_type_bits(c, arg_vals[i], "direct.type");
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

  LLVMTypeRef empty_ty = LLVMFunctionType(c->ptr_type, NULL, 0, 0);
  LLVMValueRef call_env = LLVMBuildCall2(c->builder, empty_ty,
    c->fn_lenv_empty, NULL, 0, "call_env");

  LLVMValueRef root_env = LLVMBuildLoad2(c->builder, c->ptr_type,
    root_env_global, "aot_root");
  LLVMValueRef parent_off = LLVMConstInt(c->i64_type,
    offsetof(valk_lenv_t, parent), 0);
  LLVMValueRef parent_ptr = LLVMBuildInBoundsGEP2(c->builder, c->i8_type,
    call_env, &parent_off, 1, "parent_ptr");
  LLVMBuildStore(c->builder, root_env, parent_ptr);

  LLVMTypeRef put_ty = LLVMFunctionType(c->void_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  cur = formals;
  for (u64 i = 0; i < argc; i++) {
    valk_lval_t *fh = cur->cons.head;
    LLVMValueRef fsym = valk_codegen_emit_make_sym(c, fh->str);
    LLVMValueRef put_args[] = {call_env, fsym, arg_vals[i]};
    LLVMBuildCall2(c->builder, put_ty, c->fn_lenv_put, put_args, 3, "");
    cur = cur->cons.tail;
  }
  free(arg_vals);

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
