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

// Compile a lambda body into a named function with signature
// valk_lval_t *(*)(valk_lenv_t *). Caller is responsible for binding
// formals into the env before invoking the resulting function.
// `body` may be a qexpr (each head form is a body statement, result of last
// is returned) or a single expression.
//
// BYOL ERROR INVARIANT (caller-enforced). Unlike the _fast variant, the slow
// body does NOT check formals for LVAL_ERR at entry. Callers must ensure no
// formal bound in the call_env is LVAL_ERR:
//   * Tree-walker dispatch: CONT_COLLECT_ARG (eval.c) short-circuits on
//     LVAL_ERR args before the native fn is ever invoked.
//   * try_codegen_direct_call's slow fallback in llvm_codegen.c: emits its
//     own BYOL check around the call site (see the `direct.err` block).
// Failing to uphold this invariant causes recursive walk-like lambdas to
// loop forever on error input. See memory `project_aot_byol_invariant`.
LLVMValueRef valk_llvm_compile_lambda_body(valk_llvm_ctx_t *ctx,
                                           valk_lval_t *body,
                                           const char *fn_name);

// Return true if `body` contains no forms that would require the full
// call_env at runtime: no nested `\` / `fn` lambdas (closures capture env),
// no `def` or `=` (local mutation touches env_param). Safe bodies may be
// compiled via `valk_llvm_compile_lambda_body_fast`.
bool valk_llvm_body_is_fast_safe(valk_lval_t *body);

// Compile a lambda body into a function with signature
// `valk_lval_t *(*)(valk_lenv_t *env, valk_lval_t *formal_0, ...)` where
// each formal is passed as a direct LLVM argument. Inside the body,
// `codegen_sym_lookup` resolves formals from the argument map instead of
// walking `env`. `env` is still used for non-formal symbols (globals).
// `formals` is the lambda's formals list (LVAL_CONS of LVAL_SYM). Caller
// must ensure the body is "fast safe" (see valk_llvm_body_is_fast_safe).
//
// BYOL ERROR INVARIANT (self-enforced). Emits a `byol.err` check at entry
// that returns the first LVAL_ERR formal without running the body. Safe to
// call with any arg values.
LLVMValueRef valk_llvm_compile_lambda_body_fast(valk_llvm_ctx_t *ctx,
                                                valk_lval_t *body,
                                                valk_lval_t *formals,
                                                const char *fn_name);

// Compile a "slow adapter": a function with signature
// `valk_lval_t *(*)(valk_lenv_t *call_env)` that unpacks each formal from
// `call_env` by name, then calls the matching `_fast` variant with the
// global `valk_aot_root_env` and the unpacked formal values. This is what
// gets installed as the lambda's native_fn so the tree walker can dispatch
// to native code; the adapter then trampolines into the _fast chain where
// mutual tail calls can become sibcalls.
//
// BYOL ERROR INVARIANT (delegated to _fast). The adapter forwards formals
// into the _fast variant, whose byol.err block handles the LVAL_ERR case.
LLVMValueRef valk_llvm_compile_lambda_body_slow_adapter(
    valk_llvm_ctx_t *ctx, valk_lval_t *formals,
    const char *slow_name, const char *fast_name);

char *valk_llvm_dump_ir(valk_llvm_ctx_t *ctx);
bool valk_llvm_verify(valk_llvm_ctx_t *ctx, char **error);
void valk_llvm_declare_runtime_fns(valk_llvm_ctx_t *c);
