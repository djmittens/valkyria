#pragma once
#include <stdbool.h>
#include <llvm-c/Core.h>
#include "llvm_codegen.h"
#include "../parser.h"

// Internal codegen primitives shared across llvm_codegen_*.c. Not part of
// the public API (see llvm_codegen.h for that).

LLVMValueRef valk_codegen_emit_global_string(valk_llvm_ctx_t *c, const char *s);

// GC root emission (see llvm_codegen.c "GC root emission" comment).
void valk_codegen_emit_env_root_push(valk_llvm_ctx_t *ctx, LLVMValueRef env);
LLVMValueRef valk_codegen_emit_env_root_save(valk_llvm_ctx_t *ctx);
void valk_codegen_emit_env_root_restore(valk_llvm_ctx_t *ctx, LLVMValueRef mark);
void valk_codegen_emit_root_restore(valk_llvm_ctx_t *ctx, LLVMValueRef mark);
LLVMValueRef valk_codegen_emit_make_sym(valk_llvm_ctx_t *c, const char *name);
LLVMValueRef valk_codegen_emit_make_sym_inline(valk_llvm_ctx_t *c, const char *name);

void valk_codegen_sym_cache_enter(valk_llvm_ctx_t *c, LLVMBasicBlockRef anchor);
void valk_codegen_sym_cache_leave(valk_llvm_ctx_t *c);

LLVMValueRef valk_codegen_build_qcons_list(valk_llvm_ctx_t *c,
                                           LLVMValueRef *items, u64 count);
LLVMValueRef valk_codegen_build_cons_list(valk_llvm_ctx_t *c,
                                          LLVMValueRef *items, u64 count,
                                          bool quoted);

u64 valk_codegen_cons_list_len(valk_lval_t *list);
valk_lval_t *valk_codegen_cons_list_nth(valk_lval_t *list, u64 idx);
bool valk_codegen_is_sym(valk_lval_t *expr, const char *name);
bool valk_codegen_is_num_literal(valk_lval_t *expr, i64 *out);
// Unwraps a `{...}` branch to the expression to compile. Sets *out_single
// when the branch held exactly one element, in which case the caller must
// use valk_codegen_single_elem rather than valk_codegen_expr.
valk_lval_t *valk_codegen_unwrap_branch_qexpr(valk_lval_t *branch,
                                              bool *out_single);
// Compile `elem` as the sole element of a one-element S-expression: the
// value, then the zero-arg apply the tree walker performs when that value
// turns out to be a function (CONT_SINGLE_ELEM in eval.c).
LLVMValueRef valk_codegen_single_elem(valk_llvm_ctx_t *c, valk_lval_t *elem,
                                      LLVMValueRef env_param);

LLVMValueRef valk_codegen_emit_load_num_field(valk_llvm_ctx_t *c,
                                              LLVMValueRef lval_ptr,
                                              const char *name);
LLVMValueRef valk_codegen_emit_load_type_bits(valk_llvm_ctx_t *c,
                                              LLVMValueRef lval_ptr,
                                              const char *name);

LLVMValueRef valk_codegen_num(valk_llvm_ctx_t *c, valk_lval_t *expr);
LLVMValueRef valk_codegen_str(valk_llvm_ctx_t *c, valk_lval_t *expr);
LLVMValueRef valk_codegen_nil(valk_llvm_ctx_t *c);
LLVMValueRef valk_codegen_sym_lookup(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                     LLVMValueRef env_param);
LLVMValueRef valk_codegen_qexpr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                                LLVMValueRef env_param);
LLVMValueRef valk_codegen_literal(valk_llvm_ctx_t *c, valk_lval_t *expr);

// `and` / `or`. Emitted, not called: the operands past the deciding one
// must never execute, so this cannot go through valk_codegen_funcall.
LLVMValueRef valk_codegen_and_or(valk_llvm_ctx_t *c, valk_lval_t *args,
                                 u64 argc, bool is_and,
                                 LLVMValueRef env_param);
LLVMValueRef valk_codegen_if(valk_llvm_ctx_t *c, valk_lval_t *args, u64 argc,
                             LLVMValueRef env_param);
LLVMValueRef valk_codegen_do(valk_llvm_ctx_t *c, valk_lval_t *args, u64 argc,
                             LLVMValueRef env_param);
LLVMValueRef valk_codegen_def(valk_llvm_ctx_t *c, valk_lval_t *args, u64 argc,
                              LLVMValueRef env_param, bool global);
LLVMValueRef valk_codegen_lambda(valk_llvm_ctx_t *c, valk_lval_t *args,
                                 u64 argc, LLVMValueRef env_param);

LLVMValueRef valk_codegen_funcall(valk_llvm_ctx_t *c, valk_lval_t *head,
                                  valk_lval_t *args_list, u64 argc,
                                  LLVMValueRef env_param);
LLVMValueRef valk_codegen_try_direct_call(valk_llvm_ctx_t *c,
                                          valk_lval_t *head,
                                          valk_lval_t *args_list,
                                          u64 argc,
                                          LLVMValueRef env_param);
LLVMValueRef valk_codegen_try_numeric_binop(valk_llvm_ctx_t *c,
                                            valk_lval_t *head,
                                            valk_lval_t *args_list,
                                            u64 argc,
                                            LLVMValueRef env_param);

LLVMValueRef valk_codegen_expr(valk_llvm_ctx_t *c, valk_lval_t *expr,
                               LLVMValueRef env_param);
