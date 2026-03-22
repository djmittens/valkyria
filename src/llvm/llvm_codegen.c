#include "llvm_codegen.h"
#include "llvm_jit.h"
#include <llvm-c/Analysis.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void declare_runtime_fns(valk_llvm_ctx_t *c) {
  LLVMTypeRef ptr = c->ptr_type;
  LLVMTypeRef i64 = c->i64_type;
  LLVMTypeRef i1 = c->i1_type;
  LLVMTypeRef vd = c->void_type;

  // valk_lval_t* valk_lval_num(long x)
  LLVMTypeRef num_args[] = {i64};
  c->fn_lval_num = LLVMAddFunction(c->module, "valk_lval_num",
    LLVMFunctionType(ptr, num_args, 1, 0));

  // valk_lval_t* valk_lval_str(const char *s)
  LLVMTypeRef str_args[] = {ptr};
  c->fn_lval_str = LLVMAddFunction(c->module, "valk_lval_str",
    LLVMFunctionType(ptr, str_args, 1, 0));

  // valk_lval_t* valk_lval_nil(void)
  c->fn_lval_nil = LLVMAddFunction(c->module, "valk_lval_nil",
    LLVMFunctionType(ptr, NULL, 0, 0));

  // valk_lval_t* valk_lval_sym(const char *s)
  LLVMTypeRef sym_args[] = {ptr};
  c->fn_lval_sym = LLVMAddFunction(c->module, "valk_lval_sym",
    LLVMFunctionType(ptr, sym_args, 1, 0));

  // valk_lval_t* valk_lval_cons(valk_lval_t*, valk_lval_t*)
  LLVMTypeRef cons_args[] = {ptr, ptr};
  c->fn_lval_cons = LLVMAddFunction(c->module, "valk_lval_cons",
    LLVMFunctionType(ptr, cons_args, 2, 0));

  // valk_lval_t* valk_lval_qcons(valk_lval_t*, valk_lval_t*)
  c->fn_lval_qcons = LLVMAddFunction(c->module, "valk_lval_qcons",
    LLVMFunctionType(ptr, cons_args, 2, 0));

  // valk_lval_t* valk_lval_lambda(valk_lenv_t*, valk_lval_t*, valk_lval_t*)
  LLVMTypeRef lam_args[] = {ptr, ptr, ptr};
  c->fn_lval_lambda = LLVMAddFunction(c->module, "valk_lval_lambda",
    LLVMFunctionType(ptr, lam_args, 3, 0));

  // valk_lval_t* valk_lval_copy(valk_lval_t*)
  LLVMTypeRef copy_args[] = {ptr};
  c->fn_lval_copy = LLVMAddFunction(c->module, "valk_lval_copy",
    LLVMFunctionType(ptr, copy_args, 1, 0));

  // bool valk_lval_is_truthy(valk_lval_t*)
  LLVMTypeRef truthy_args[] = {ptr};
  c->fn_lval_is_truthy = LLVMAddFunction(c->module, "valk_lval_is_truthy",
    LLVMFunctionType(i1, truthy_args, 1, 0));

  // valk_lval_t* valk_lenv_get(valk_lenv_t*, valk_lval_t*)
  LLVMTypeRef env_get_args[] = {ptr, ptr};
  c->fn_lenv_get = LLVMAddFunction(c->module, "valk_lenv_get",
    LLVMFunctionType(ptr, env_get_args, 2, 0));

  // void valk_lenv_put(valk_lenv_t*, valk_lval_t*, valk_lval_t*)
  LLVMTypeRef env_put_args[] = {ptr, ptr, ptr};
  c->fn_lenv_put = LLVMAddFunction(c->module, "valk_lenv_put",
    LLVMFunctionType(vd, env_put_args, 3, 0));

  // void valk_lenv_def(valk_lenv_t*, valk_lval_t*, valk_lval_t*)
  c->fn_lenv_def = LLVMAddFunction(c->module, "valk_lenv_def",
    LLVMFunctionType(vd, env_put_args, 3, 0));

  // valk_lenv_t* valk_lenv_empty(void)
  c->fn_lenv_empty = LLVMAddFunction(c->module, "valk_lenv_empty",
    LLVMFunctionType(ptr, NULL, 0, 0));

  // valk_lval_t* valk_lval_eval(valk_lenv_t*, valk_lval_t*)
  LLVMTypeRef eval_args[] = {ptr, ptr};
  c->fn_lval_eval = LLVMAddFunction(c->module, "valk_lval_eval",
    LLVMFunctionType(ptr, eval_args, 2, 0));

  // valk_lval_t* valk_lval_eval_call(valk_lenv_t*, valk_lval_t*, valk_lval_t*)
  LLVMTypeRef call_args[] = {ptr, ptr, ptr};
  c->fn_lval_eval_call = LLVMAddFunction(c->module, "valk_lval_eval_call",
    LLVMFunctionType(ptr, call_args, 3, 0));

  // void valk_lval_println(valk_lval_t*)
  LLVMTypeRef print_args[] = {ptr};
  c->fn_lval_println = LLVMAddFunction(c->module, "valk_lval_println",
    LLVMFunctionType(vd, print_args, 1, 0));

  c->fn_lval_print = LLVMAddFunction(c->module, "valk_lval_print",
    LLVMFunctionType(vd, print_args, 1, 0));

  // int printf(const char*, ...)
  LLVMTypeRef printf_args[] = {ptr};
  c->fn_printf = LLVMAddFunction(c->module, "printf",
    LLVMFunctionType(LLVMInt32TypeInContext(c->ctx), printf_args, 1, 1));
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

  declare_runtime_fns(c);
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

static LLVMValueRef emit_make_sym(valk_llvm_ctx_t *c, const char *name) {
  LLVMValueRef str = emit_global_string(c, name);
  LLVMTypeRef fn_type = LLVMFunctionType(c->ptr_type,
    (LLVMTypeRef[]){c->ptr_type}, 1, 0);
  return LLVMBuildCall2(c->builder, fn_type, c->fn_lval_sym, &str, 1, "sym");
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

static LLVMValueRef codegen_if(valk_llvm_ctx_t *c, valk_lval_t *args,
                               u64 argc, LLVMValueRef env_param) {
  if (argc < 2) return codegen_nil(c);

  valk_lval_t *cond_expr = cons_list_nth(args, 0);
  valk_lval_t *then_expr = cons_list_nth(args, 1);
  valk_lval_t *else_expr = argc > 2 ? cons_list_nth(args, 2) : NULL;

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
  LLVMBasicBlockRef merge_bb = LLVMAppendBasicBlockInContext(c->ctx, fn, merge_name);

  LLVMBuildCondBr(c->builder, is_truthy, then_bb, else_bb);

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
  for (u64 i = 0; i < argc; i++) {
    result = codegen_expr(c, cur->cons.head, env_param);
    cur = cur->cons.tail;
  }
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

static LLVMValueRef codegen_funcall(valk_llvm_ctx_t *c, valk_lval_t *head,
                                    valk_lval_t *args_list, u64 argc,
                                    LLVMValueRef env_param) {
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
  return LLVMBuildCall2(c->builder, call_type, c->fn_lval_eval_call,
    call_args, 3, "call");
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

  LLVMValueRef env_param = LLVMGetParam(fn, 0);
  LLVMValueRef result = codegen_expr(ctx, expr, env_param);

  LLVMBuildRet(ctx->builder, result);
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
