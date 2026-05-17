#include "llvm_jit.h"
#include "build_aot.h"
#include "llvm_codegen.h"

#include <llvm-c/Core.h>
#include <llvm-c/LLJIT.h>
#include <llvm-c/Orc.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Use the host's underscore prefix configuration. On ELF Linux this is
// 0; on Mach-O macOS it's '_'. LLJITGetGlobalPrefix queries the target.

extern valk_lenv_t *valk_aot_root_env;

struct valk_jit_t {
  LLVMOrcLLJITRef lljit;
  LLVMOrcResourceTrackerRef rt;
  size_t resolved_count;
};

static void log_error(LLVMErrorRef err, const char *ctx) {
  if (!err) return;
  char *msg = LLVMGetErrorMessage(err);
  fprintf(stderr, "valk-jit: %s: %s\n", ctx, msg ? msg : "(null)");
  LLVMDisposeErrorMessage(msg);
}

// Build an LLJIT with a process-symbol resolver so the compiled module
// can reference runtime symbols (valk_lval_*, valk_lenv_*, etc.) that
// live in the running process (libvalkyria + the valk binary).
static LLVMOrcLLJITRef build_lljit(void) {
  LLVMOrcLLJITBuilderRef builder = LLVMOrcCreateLLJITBuilder();
  LLVMOrcLLJITRef lljit = nullptr;
  LLVMErrorRef err = LLVMOrcCreateLLJIT(&lljit, builder);
  if (err) {
    log_error(err, "LLVMOrcCreateLLJIT");
    return nullptr;
  }

  LLVMOrcJITDylibRef main_dylib = LLVMOrcLLJITGetMainJITDylib(lljit);
  LLVMOrcDefinitionGeneratorRef gen = nullptr;
  err = LLVMOrcCreateDynamicLibrarySearchGeneratorForProcess(
      &gen, LLVMOrcLLJITGetGlobalPrefix(lljit), nullptr, nullptr);
  if (err) {
    log_error(err, "CreateDynamicLibrarySearchGeneratorForProcess");
    LLVMOrcDisposeLLJIT(lljit);
    return nullptr;
  }
  LLVMOrcJITDylibAddGenerator(main_dylib, gen);

  return lljit;
}

// Adopt the codegen ctx's module into the LLJIT under a fresh resource
// tracker. Ownership of the LLVMModuleRef + LLVMContextRef transfers
// into ORC; we steal them out of `ctx` so valk_llvm_ctx_free won't
// dispose them.
static LLVMOrcResourceTrackerRef adopt_module(LLVMOrcLLJITRef lljit,
                                              valk_llvm_ctx_t *ctx) {
  LLVMOrcThreadSafeContextRef ts_ctx =
      LLVMOrcCreateNewThreadSafeContextFromLLVMContext(ctx->ctx);
  LLVMOrcThreadSafeModuleRef tsm =
      LLVMOrcCreateNewThreadSafeModule(ctx->module, ts_ctx);
  LLVMOrcDisposeThreadSafeContext(ts_ctx);

  // Steal: LLJIT owns these now.
  ctx->module = nullptr;
  ctx->ctx = nullptr;

  LLVMOrcJITDylibRef dylib = LLVMOrcLLJITGetMainJITDylib(lljit);
  LLVMOrcResourceTrackerRef rt = LLVMOrcJITDylibCreateResourceTracker(dylib);
  LLVMErrorRef err = LLVMOrcLLJITAddLLVMIRModuleWithRT(lljit, rt, tsm);
  if (err) {
    log_error(err, "LLVMOrcLLJITAddLLVMIRModuleWithRT");
    LLVMOrcReleaseResourceTracker(rt);
    return nullptr;
  }
  return rt;
}

// Walk env, look up each compiled lambda's symbol via ORC, and assign
// to v->fun.native_fn. Returns the number of lambdas resolved.
//
// Lookup is by `native_name` (the strdup'd "valk_aot_NNN" string set
// during phase 1 of valk_aot_compile_env). On lookup failure we leave
// native_fn null — that lambda stays interpreted, no fatal error.
static size_t resolve_compiled_symbols(LLVMOrcLLJITRef lljit,
                                       valk_lenv_t *env) {
  size_t resolved = 0;
  for (u64 i = 0; i < env->symbols.count; i++) {
    valk_lval_t *v = env->vals.items[i];
    if (!v || LVAL_TYPE(v) != LVAL_FUN || !v->fun.native_name) continue;

    LLVMOrcExecutorAddress addr = 0;
    LLVMErrorRef err = LLVMOrcLLJITLookup(lljit, &addr, v->fun.native_name);
    if (err) {
      log_error(err, "LLVMOrcLLJITLookup");
      // Clear native_name so the runtime won't pretend it's resolvable.
      free(v->fun.native_name);
      v->fun.native_name = nullptr;
      continue;
    }
    if (!addr) continue;

    typedef valk_lval_t *(*aot_fn_t)(valk_lenv_t *);
    v->fun.native_fn = (aot_fn_t)(uintptr_t)addr;
    resolved++;
  }
  return resolved;
}

valk_jit_t *valk_jit_compile_env(valk_lenv_t *env) {
  if (!env) return nullptr;

  size_t compiled = 0;
  valk_llvm_ctx_t *ctx = valk_aot_compile_env(env, &compiled);
  if (!ctx) return nullptr;

  // Edge case: nothing AOT-eligible in env. Skip ORC entirely; nothing
  // to JIT, but this isn't an error — the env just runs interpreted.
  if (compiled == 0) {
    valk_llvm_ctx_free(ctx);
    return nullptr;
  }

  LLVMOrcLLJITRef lljit = build_lljit();
  if (!lljit) {
    // Roll back: clear native_names so eval.c doesn't dispatch to nothing.
    for (u64 i = 0; i < env->symbols.count; i++) {
      valk_lval_t *v = env->vals.items[i];
      if (v && LVAL_TYPE(v) == LVAL_FUN && v->fun.native_name) {
        free(v->fun.native_name);
        v->fun.native_name = nullptr;
      }
    }
    valk_llvm_ctx_free(ctx);
    return nullptr;
  }

  LLVMOrcResourceTrackerRef rt = adopt_module(lljit, ctx);
  // Even on adopt failure, ctx->module and ctx->ctx are now stolen
  // (best-effort) — pass through ctx_free which sees null fields and
  // skips the disposes.
  valk_llvm_ctx_free(ctx);

  if (!rt) {
    LLVMOrcDisposeLLJIT(lljit);
    for (u64 i = 0; i < env->symbols.count; i++) {
      valk_lval_t *v = env->vals.items[i];
      if (v && LVAL_TYPE(v) == LVAL_FUN && v->fun.native_name) {
        free(v->fun.native_name);
        v->fun.native_name = nullptr;
      }
    }
    return nullptr;
  }

  // Wire up the global root env that compiled code references via
  // `valk_aot_root_env` (resolved by the dynamic-library generator
  // against libvalkyria's exported symbol).
  valk_aot_root_env = env;

  size_t resolved = resolve_compiled_symbols(lljit, env);

  valk_jit_t *jit = calloc(1, sizeof(*jit));
  jit->lljit = lljit;
  jit->rt = rt;
  jit->resolved_count = resolved;
  return jit;
}

void valk_jit_free(valk_jit_t *jit) {
  if (!jit) return;
  if (jit->rt) {
    LLVMOrcResourceTrackerRemove(jit->rt);
    LLVMOrcReleaseResourceTracker(jit->rt);
  }
  if (jit->lljit) {
    LLVMErrorRef err = LLVMOrcDisposeLLJIT(jit->lljit);
    if (err) log_error(err, "LLVMOrcDisposeLLJIT");
  }
  free(jit);
}

size_t valk_jit_compiled_count(valk_jit_t *jit) {
  return jit ? jit->resolved_count : 0;
}
