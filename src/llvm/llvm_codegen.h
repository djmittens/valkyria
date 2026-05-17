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

  // GC safe-point hook. AOT-compiled code calls this before any
  // operation that might race with a concurrent GC cycle (notably
  // lenv_get and lval_eval_call). Without these calls, the AOT
  // function's local pointers (env, captured lvals) can become stale
  // during the function body if GC evacuates objects under it.
  // Implementation: tiny C function `valk_gc_safepoint_aot` that
  // expands the VALK_GC_SAFE_POINT() macro.
  LLVMValueRef fn_safepoint;

  u64 expr_counter;
  u64 str_counter;
  u64 block_counter;

  // Build-time env (--build AOT). When non-null, codegen may resolve
  // applied symbols against this env and emit direct calls to compiled
  // lambdas whose `native_name` is set. NULL outside of --build.
  valk_lenv_t *build_env;

  // Transient formals map for the current lambda-body compile (Stage 2
  // "fast" variant). When set, `codegen_sym_lookup` checks here first to
  // resolve formal symbols to LLVM args, bypassing `valk_lenv_get`.
  // Cleared after compile_lambda_body_fast finishes.
  struct {
    const char **names;
    LLVMValueRef *vals;
    size_t count;
  } formals_map;

  // Stage 3: TCO state for the current fast-variant compile. When `fn` is
  // non-null, a self-recursive call in tail position branches to `body_bb`
  // and feeds new arg values through `env_phi` + `formal_phis` rather than
  // pushing a new stack frame.
  struct {
    LLVMValueRef fn;
    LLVMBasicBlockRef body_bb;
    LLVMValueRef env_phi;
    LLVMValueRef *formal_phis;
    size_t nformals;
  } tco;
  bool in_tail;

  // Stage 7: sym-lval hoisting cache for the current lambda-body compile.
  // When `anchor_bb` is non-null, `emit_make_sym(name)` emits one
  // `valk_lval_sym(...)` call into `anchor_bb` per unique name and
  // caches the result; later calls for the same name reuse it. The
  // anchor must dominate every use (so: entry_bb of the current fn).
  // Turns N per-iteration allocs into N one-shot allocs at fn entry.
  struct {
    LLVMBasicBlockRef anchor_bb;
    char **names;
    LLVMValueRef *vals;
    size_t count;
    size_t cap;
  } sym_cache;
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

// Lambda-body compilation lives entirely in the VIR pipeline now. See
// src/llvm/build_aot.c::compile_slow_body_via_vir and
// src/vir/ast_to_vir.c::vir_lower_lambda_body_with_env. The fast/slow
// duplication that used to live here is retired — the unified VIR path
// handles all lambdas with TCO via musttail (vir_to_llvm.c VIR_CALL.is_tail).

char *valk_llvm_dump_ir(valk_llvm_ctx_t *ctx);
bool valk_llvm_verify(valk_llvm_ctx_t *ctx, char **error);
void valk_llvm_declare_runtime_fns(valk_llvm_ctx_t *c);
