#include "build_aot.h"

#include <llvm-c/Analysis.h>
#include <llvm-c/Core.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "llvm_aot.h"
#include "llvm_codegen.h"
#include "vir_to_llvm.h"
#include "../vir/vir.h"

// Slow-body lambda compile via the VIR pipeline.
//
// AST → VIR (ast_to_vir.c::vir_lower_lambda_body_with_env) → safepoint
// pass → LLVM IR (vir_to_llvm.c::vir_to_llvm_func), all into the same
// LLVM context build_aot.c is managing. Replaces the hand-rolled
// valk_llvm_compile_lambda_body path that used to live in
// llvm_codegen.c.
//
// VIR is the proper IR layer: liveness analysis, safepoint placement,
// and any future optimization passes are added at the IR level. Direct
// AOT-to-AOT calls (resolved against build_env) are emitted as
// VIR_DIRECT_CALL ops; lower_value lowers them to a build-call_env +
// lenv_put each formal + native_fn(call_env) sequence, bypassing
// valk_lval_eval_call.
static LLVMValueRef compile_slow_body_via_vir(valk_llvm_ctx_t *ctx,
                                              valk_lval_t *body,
                                              const char *fn_name) {
  vir_module_t *vmod = vir_module_new(fn_name);
  vir_builder_t *b = vir_builder_new(vmod);

  // Pass build_env so ast_to_vir can resolve direct AOT-to-AOT calls.
  // ctx->build_env points at the env containing every AOT candidate's
  // lambda lval (with native_name already assigned in phase 1).
  vir_func_t *vfn = vir_lower_lambda_body_with_env(b, body, fn_name,
                                                    ctx->build_env);
  if (!vfn) {
    vir_builder_free(b);
    vir_module_free(vmod);
    return NULL;
  }

  vir_gc_insert_safepoints(vmod);

  LLVMValueRef llvm_fn = vir_to_llvm_func(ctx, vfn);

  vir_builder_free(b);
  vir_module_free(vmod);
  return llvm_fn;
}

typedef struct {
  char *name;  // strdup'd; owned by this struct
} aot_entry_t;

// Closures created at runtime (e.g. `(make-counter 10)`) capture a
// non-trivial env chain holding the values they close over. AOT
// compilation discards captured env state — fast variants build a
// fresh env parented at `valk_aot_root_env`, slow variants use the
// caller's call_env. Either way, a closure's captured `start`/etc.
// is unreachable from the compiled body.
//
// Detect closures by env identity: a top-level lambda has
// `v->fun.env == build_env` (the env the AOT compile is iterating);
// a closure has some other env. Skip AOT for closures so they stay
// interpreter-evaluated against their captured env.
//
// Macros (LVAL_FLAG_MACRO) are also skipped: their bodies typically
// contain `(quasiquote ...)` and `(unquote ...)` forms, which VIR
// doesn't lower as special forms — they fall through to funcall
// against env, which fails because quasiquote/unquote aren't bound.
// Macros are called only at expansion time anyway (and in `--build`
// mode never at runtime, since expansion already happened in the
// load phase); AOT'ing them is dead work that breaks JIT mode where
// `(eval {macro-using-form})` re-triggers expansion at runtime.
static bool is_aot_candidate(valk_lval_t *v, valk_lenv_t *build_env) {
  if (!v || LVAL_TYPE(v) != LVAL_FUN) return false;
  if (v->fun.builtin != nullptr) return false;
  if (!v->fun.body) return false;
  if (v->fun.native_name) return false;
  if (v->fun.env != build_env) return false;
  if (v->flags & LVAL_FLAG_MACRO) return false;
  return true;
}

static void write_dispatch_c(FILE *f, aot_entry_t *entries, size_t n) {
  fprintf(f,
          "#include <stddef.h>\n"
          "#include \"parser.h\"\n"
          "#include \"image.h\"\n"
          "\n");
  for (size_t i = 0; i < n; i++) {
    fprintf(f, "extern valk_lval_t *%s(valk_lenv_t *);\n", entries[i].name);
  }
  fprintf(f, "\n");
  if (n > 0) {
    fprintf(f, "static const valk_aot_entry_t _table[] = {\n");
    for (size_t i = 0; i < n; i++) {
      fprintf(f, "  {\"%s\", %s},\n", entries[i].name, entries[i].name);
    }
    fprintf(f, "};\n");
    fprintf(f, "const valk_aot_entry_t *const valk_aot_table = _table;\n");
  } else {
    fprintf(f, "const valk_aot_entry_t *const valk_aot_table = NULL;\n");
  }
  fprintf(f, "const size_t valk_aot_table_count = %zu;\n", n);
}

// VALK_AOT_VERBOSE=1 prints per-candidate compile decisions on stderr so
// users can see which lambdas got AOT'd and which fell back to the tree
// walker. Off by default to keep the build quiet.
static bool aot_verbose(void) {
  const char *e = getenv("VALK_AOT_VERBOSE");
  return e && *e && *e != '0';
}

// Compile every AOT-eligible lambda in `env` to LLVM IR. Returns a new
// llvm ctx with the populated, verified, optimized module on success;
// NULL on failure. Sets v->fun.native_name on each compiled candidate.
// Caller owns the returned ctx — must call valk_llvm_ctx_free OR
// transfer ownership into a JIT runner.
//
// On `*count_out`: number of compiled candidates (their native_names
// are now set on env entries). Walk env to find them: any LVAL_FUN
// with non-null native_name was compiled into this ctx's module.
//
// This is the shared pipeline for `--build` (which emits a .o + dispatch
// table) and the JIT (which hands ctx->module to ORC). Both paths drive
// phases 1-5 (identify candidates, compile slow/fast, verify, optimize)
// identically.
//
// On failure, env is rolled back: any v->fun.native_name set during
// phase 1 is freed and cleared, so the caller can fall back to the
// tree walker without dangling references.
valk_llvm_ctx_t *valk_aot_compile_env(valk_lenv_t *env, size_t *count_out) {
  if (!env) return nullptr;

  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("valk_aot");
  if (!ctx) return nullptr;
  ctx->build_env = env;
  bool verbose = aot_verbose();

  aot_entry_t *entries = nullptr;
  size_t n = 0, cap = 0;

  // Single-pass compile: every AOT candidate gets one VIR-lowered
  // function. The earlier fast/slow split is gone — fast was a
  // duplicate codegen path that lacked TCO and led to architectural
  // drift between the two pipelines (each fix had to be applied to
  // both, and slow-body recursion blew the C stack because TCO only
  // existed in fast). VIR now handles tail calls via musttail (see
  // ast_to_vir.c::lower_tail and vir_to_llvm.c VIR_CALL.is_tail), so
  // one pipeline covers all cases.
  //
  // Two-phase loop keeps mutual recursion working: phase 1 declares
  // every candidate's symbol so phase 2's bodies can resolve direct
  // calls (via VIR_DIRECT_CALL → LLVMGetNamedFunction) regardless of
  // ordering.

  // Phase 1: declare every candidate's compiled-fn symbol and assign
  // native_name. This must happen before any body is compiled so that
  // direct-call lowering during phase 2 can resolve the target by name.
  for (u64 i = 0; i < env->symbols.count; i++) {
    valk_lval_t *v = env->vals.items[i];
    if (!is_aot_candidate(v, env)) continue;

    char name[64];
    snprintf(name, sizeof(name), "valk_aot_%zu", n);

    LLVMTypeRef fn_ty = LLVMFunctionType(ctx->ptr_type,
      (LLVMTypeRef[]){ctx->ptr_type}, 1, 0);
    LLVMValueRef fn = LLVMAddFunction(ctx->module, name, fn_ty);
    LLVMSetLinkage(fn, LLVMExternalLinkage);

    v->fun.native_name = strdup(name);

    if (n == cap) {
      cap = cap ? cap * 2 : 8;
      entries = realloc(entries, cap * sizeof(*entries));
    }
    entries[n].name = strdup(name);
    n++;
  }

  // Phase 2: compile each body via VIR. lower_funcall sees other
  // candidates' native_names in build_env and emits VIR_DIRECT_CALL
  // for AOT-to-AOT calls; ast_to_vir's lower_tail marks tail-position
  // calls so vir_to_llvm emits musttail (sibcall).
  bool ok = true;
  for (u64 i = 0; i < env->symbols.count && ok; i++) {
    valk_lval_t *v = env->vals.items[i];
    // Recognize candidates by native_name (set in phase 1 above) — we
    // can't call is_aot_candidate here because that predicate excludes
    // anything with native_name already set, which is exactly what
    // we just did to every candidate.
    if (!v || LVAL_TYPE(v) != LVAL_FUN) continue;
    if (!v->fun.native_name) continue;
    if (!v->fun.body) continue;

    LLVMValueRef fn = compile_slow_body_via_vir(ctx, v->fun.body,
                                                v->fun.native_name);
    if (!fn) {
      fprintf(stderr, "[AOT] skip: %s (codegen returned null)\n",
              env->symbols.items[i] ? env->symbols.items[i]
                                    : v->fun.native_name);
      ok = false;
      break;
    }
    if (LLVMVerifyFunction(fn, LLVMReturnStatusAction)) {
      fprintf(stderr, "valk --build: %s failed verify; aborting\n",
              v->fun.native_name);
      ok = false;
      break;
    }
    if (verbose) {
      fprintf(stderr, "[AOT] compiled: %s\n",
              env->symbols.items[i] ? env->symbols.items[i]
                                    : v->fun.native_name);
    }
  }

  // Roll back env state on failure so the caller sees a clean env (no
  // dangling native_name pointers) and doesn't leak.
#define COMPILE_FAIL_CLEANUP() do {                                       \
    for (u64 _i = 0; _i < env->symbols.count; _i++) {                     \
      valk_lval_t *_v = env->vals.items[_i];                              \
      if (_v && LVAL_TYPE(_v) == LVAL_FUN && _v->fun.native_name) {       \
        free(_v->fun.native_name);                                        \
        _v->fun.native_name = nullptr;                                    \
      }                                                                   \
    }                                                                     \
    for (size_t _i = 0; _i < n; _i++) free(entries[_i].name);             \
    free(entries);                                                        \
    valk_llvm_ctx_free(ctx);                                              \
  } while (0)

  if (!ok) {
    COMPILE_FAIL_CLEANUP();
    return nullptr;
  }

  char *mod_err = nullptr;
  if (LLVMVerifyModule(ctx->module, LLVMReturnStatusAction, &mod_err)) {
    fprintf(stderr, "valk_aot_compile_env: AOT module verify failed: %s\n",
            mod_err ? mod_err : "unknown");
    if (mod_err) LLVMDisposeMessage(mod_err);
    COMPILE_FAIL_CLEANUP();
    return nullptr;
  }
  if (mod_err) LLVMDisposeMessage(mod_err);

  if (n > 0) {
    if (getenv("VALK_DUMP_AOT_IR")) {
      valk_aot_emit_ir(ctx, "/tmp/valk_aot_pre.ll");
    }
    // Run LLVM's new-PM default<O2> pipeline. Hand-written IR has
    // unreachable tco.dead blocks, redundant valk_lval_num boxing
    // after tail calls, and direct calls that could be sibcalled —
    // the optimizer handles all three cleanly.
    if (valk_aot_optimize(ctx) != 0) {
      fprintf(stderr, "valk_aot_compile_env: optimize failed\n");
      COMPILE_FAIL_CLEANUP();
      return nullptr;
    }
    if (getenv("VALK_DUMP_AOT_IR")) {
      valk_aot_emit_ir(ctx, "/tmp/valk_aot_post.ll");
    }
  }

#undef COMPILE_FAIL_CLEANUP

  // Both consumers (build and JIT) re-derive what they need by walking
  // env post-compile, so we can free the entries array here.
  for (size_t i = 0; i < n; i++) free(entries[i].name);
  free(entries);

  if (count_out) *count_out = n;
  return ctx;
}

// Walk env, collect compiled candidates' native_names into a fresh
// entry array. Used by valk_build_emit_aot to build the dispatch table
// and by the JIT layer to walk symbols for ORC lookup. Caller owns the
// returned array and must free it via valk_aot_free_entries.
typedef struct {
  char *name;          // strdup'd (matches v->fun.native_name)
  valk_lval_t *lval;   // points back to env entry
} valk_aot_compiled_t;

static valk_aot_compiled_t *collect_compiled_entries(valk_lenv_t *env,
                                                     size_t *out_count) {
  size_t cap = 0, n = 0;
  valk_aot_compiled_t *out = nullptr;
  for (u64 i = 0; i < env->symbols.count; i++) {
    valk_lval_t *v = env->vals.items[i];
    if (!v || LVAL_TYPE(v) != LVAL_FUN || !v->fun.native_name) continue;
    if (n == cap) {
      cap = cap ? cap * 2 : 8;
      out = realloc(out, cap * sizeof(*out));
    }
    out[n].name = strdup(v->fun.native_name);
    out[n].lval = v;
    n++;
  }
  *out_count = n;
  return out;
}

static void free_compiled_entries(valk_aot_compiled_t *entries, size_t n) {
  if (!entries) return;
  for (size_t i = 0; i < n; i++) free(entries[i].name);
  free(entries);
}

int valk_build_emit_aot(valk_lenv_t *env, const char *o_path,
                        const char *c_path, size_t *out_count) {
  size_t n = 0;
  valk_llvm_ctx_t *ctx = valk_aot_compile_env(env, &n);
  if (!ctx) return -1;

  size_t entry_count = 0;
  valk_aot_compiled_t *compiled = collect_compiled_entries(env, &entry_count);

  // Adapt to the legacy aot_entry_t shape that write_dispatch_c expects.
  aot_entry_t *entries = malloc(entry_count * sizeof(*entries));
  for (size_t i = 0; i < entry_count; i++) {
    entries[i].name = strdup(compiled[i].name);
  }

  int rc = 0;
  if (n > 0) {
    if (valk_aot_emit_object(ctx, o_path) != 0) {
      fprintf(stderr, "valk --build: AOT emit object failed\n");
      rc = -1;
    }
  }

  FILE *f = fopen(c_path, "w");
  if (!f) {
    fprintf(stderr, "valk --build: cannot write %s\n", c_path);
    rc = -1;
  } else {
    write_dispatch_c(f, entries, entry_count);
    fclose(f);
  }

  for (size_t i = 0; i < entry_count; i++) free(entries[i].name);
  free(entries);
  free_compiled_entries(compiled, entry_count);
  valk_llvm_ctx_free(ctx);

  if (out_count) *out_count = n;
  return rc;
}
