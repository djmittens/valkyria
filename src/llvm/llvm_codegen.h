#pragma once
#include <stdbool.h>
#include <llvm-c/Core.h>
#include <llvm-c/Types.h>
#include "../parser.h"

typedef struct {
  LLVMContextRef ctx;
  LLVMModuleRef module;
  LLVMBuilderRef builder;

  LLVMTypeRef ptr_type;
  LLVMTypeRef i64_type;
  LLVMTypeRef i8_type;
  LLVMTypeRef i1_type;
  LLVMTypeRef void_type;

  LLVMValueRef fn_lval_num;
  LLVMValueRef fn_lval_str;
  LLVMValueRef fn_lval_nil;
  LLVMValueRef fn_lval_sym;
  LLVMValueRef fn_lval_cons;
  LLVMValueRef fn_lval_qcons;
  LLVMValueRef fn_lval_lambda;
  LLVMValueRef fn_lval_copy;
  LLVMValueRef fn_lval_is_truthy;
  LLVMValueRef fn_lenv_get;
  LLVMValueRef fn_lenv_put;
  LLVMValueRef fn_lenv_def;
  LLVMValueRef fn_lenv_empty;
  LLVMValueRef fn_lval_eval;
  LLVMValueRef fn_lval_eval_call;
  LLVMValueRef fn_lval_print;
  LLVMValueRef fn_lval_println;
  LLVMValueRef fn_printf;

  u64 expr_counter;
  u64 str_counter;
  u64 block_counter;
} valk_llvm_ctx_t;

valk_llvm_ctx_t *valk_llvm_ctx_new(const char *module_name);
void valk_llvm_ctx_free(valk_llvm_ctx_t *ctx);

LLVMValueRef valk_llvm_compile_expr(valk_llvm_ctx_t *ctx,
                                    valk_lval_t *expr,
                                    LLVMValueRef env_param);

LLVMValueRef valk_llvm_compile_toplevel(valk_llvm_ctx_t *ctx,
                                        valk_lval_t *expr);

LLVMValueRef valk_llvm_compile_program(valk_llvm_ctx_t *ctx,
                                       valk_lval_t *exprs);

char *valk_llvm_dump_ir(valk_llvm_ctx_t *ctx);
bool valk_llvm_verify(valk_llvm_ctx_t *ctx, char **error);
