#include "llvm_codegen_internal.h"
#include <stdio.h>

LLVMValueRef valk_codegen_if(valk_llvm_ctx_t *c, valk_lval_t *args, u64 argc,
                             LLVMValueRef env_param) {
  if (argc < 2) return valk_codegen_nil(c);

  valk_lval_t *cond_expr = valk_codegen_cons_list_nth(args, 0);
  valk_lval_t *then_expr = valk_codegen_cons_list_nth(args, 1);
  valk_lval_t *else_expr = argc > 2 ? valk_codegen_cons_list_nth(args, 2) : NULL;

  then_expr = valk_codegen_unwrap_branch_qexpr(then_expr);
  else_expr = valk_codegen_unwrap_branch_qexpr(else_expr);

  bool saved_tail = c->in_tail;

  c->in_tail = false;
  LLVMValueRef cond_val = valk_codegen_expr(c, cond_expr, env_param);

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

  // Tail-position if: emit ret directly in each branch so X86's
  // TailCallElim can convert sibling calls to jmps. A merge phi+ret
  // would block the optimization.
  if (saved_tail) {
    LLVMPositionBuilderAtEnd(c->builder, then_bb);
    c->in_tail = true;
    LLVMValueRef then_val = valk_codegen_expr(c, then_expr, env_param);
    LLVMBuildRet(c->builder, then_val);

    LLVMPositionBuilderAtEnd(c->builder, else_bb);
    c->in_tail = true;
    LLVMValueRef else_val = else_expr
        ? valk_codegen_expr(c, else_expr, env_param)
        : valk_codegen_nil(c);
    LLVMBuildRet(c->builder, else_val);

    LLVMBasicBlockRef dead =
      LLVMAppendBasicBlockInContext(c->ctx, fn, "tail.dead");
    LLVMPositionBuilderAtEnd(c->builder, dead);
    c->in_tail = saved_tail;
    return LLVMGetUndef(c->ptr_type);
  }

  LLVMBasicBlockRef merge_bb = LLVMAppendBasicBlockInContext(c->ctx, fn, merge_name);

  LLVMPositionBuilderAtEnd(c->builder, then_bb);
  LLVMValueRef then_val = valk_codegen_expr(c, then_expr, env_param);
  LLVMBuildBr(c->builder, merge_bb);
  LLVMBasicBlockRef then_end = LLVMGetInsertBlock(c->builder);

  LLVMPositionBuilderAtEnd(c->builder, else_bb);
  LLVMValueRef else_val;
  if (else_expr) {
    else_val = valk_codegen_expr(c, else_expr, env_param);
  } else {
    else_val = valk_codegen_nil(c);
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

LLVMValueRef valk_codegen_do(valk_llvm_ctx_t *c, valk_lval_t *args, u64 argc,
                             LLVMValueRef env_param) {
  LLVMValueRef result = valk_codegen_nil(c);
  valk_lval_t *cur = args;
  bool saved_tail = c->in_tail;
  for (u64 i = 0; i < argc; i++) {
    c->in_tail = (i == argc - 1) ? saved_tail : false;
    result = valk_codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }
  c->in_tail = saved_tail;
  return result;
}

LLVMValueRef valk_codegen_def(valk_llvm_ctx_t *c, valk_lval_t *args, u64 argc,
                              LLVMValueRef env_param, bool global) {
  if (argc < 2) return valk_codegen_nil(c);

  valk_lval_t *syms_expr = valk_codegen_cons_list_nth(args, 0);

  LLVMTypeRef put_type = LLVMFunctionType(c->void_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  LLVMValueRef put_fn = global ? c->fn_lenv_def : c->fn_lenv_put;

  if (LVAL_TYPE(syms_expr) == LVAL_SYM) {
    LLVMValueRef sym = valk_codegen_emit_make_sym(c, syms_expr->str);
    LLVMValueRef val = valk_codegen_expr(c,
        valk_codegen_cons_list_nth(args, 1), env_param);
    LLVMValueRef put_args[] = {env_param, sym, val};
    LLVMBuildCall2(c->builder, put_type, put_fn, put_args, 3, "");
    return val;
  }

  if (LVAL_TYPE(syms_expr) == LVAL_CONS) {
    u64 sym_count = valk_codegen_cons_list_len(syms_expr);
    u64 val_count = argc - 1;
    u64 n = sym_count < val_count ? sym_count : val_count;

    LLVMValueRef last = valk_codegen_nil(c);
    valk_lval_t *sym_cur = syms_expr;
    valk_lval_t *val_cur = args->cons.tail;
    for (u64 i = 0; i < n; i++) {
      valk_lval_t *s = sym_cur->cons.head;
      LLVMValueRef sym = valk_codegen_emit_make_sym(c, s->str);
      LLVMValueRef val = valk_codegen_expr(c, val_cur->cons.head, env_param);
      LLVMValueRef put_args[] = {env_param, sym, val};
      LLVMBuildCall2(c->builder, put_type, put_fn, put_args, 3, "");
      last = val;
      sym_cur = sym_cur->cons.tail;
      val_cur = val_cur->cons.tail;
    }
    return last;
  }

  return valk_codegen_nil(c);
}

LLVMValueRef valk_codegen_lambda(valk_llvm_ctx_t *c, valk_lval_t *args,
                                 u64 argc, LLVMValueRef env_param) {
  if (argc < 2) return valk_codegen_nil(c);

  valk_lval_t *formals = valk_codegen_cons_list_nth(args, 0);
  valk_lval_t *body = valk_codegen_cons_list_nth(args, 1);

  LLVMValueRef formals_val = valk_codegen_expr(c, formals, env_param);
  LLVMValueRef body_val = valk_codegen_expr(c, body, env_param);

  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type, c->ptr_type, c->ptr_type}, 3, 0);
  LLVMValueRef lam_args[] = {env_param, formals_val, body_val};
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_lambda,
    lam_args, 3, "lambda");
}
