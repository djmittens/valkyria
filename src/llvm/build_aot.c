#include "build_aot.h"

#include <llvm-c/Analysis.h>
#include <llvm-c/Core.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "llvm_aot.h"
#include "llvm_codegen.h"

typedef struct {
  char *name;  // strdup'd; owned by this struct
} aot_entry_t;

// Mutable state per candidate across the multi-phase compile below.
typedef struct {
  valk_lval_t *lval;          // the LVAL_FUN
  char *slow_name;            // strdup'd; matches v->fun.native_name
  char *fast_name;            // strdup'd; null if body isn't fast-safe
  LLVMValueRef slow_fn;       // compiled (or declared-empty) slow variant
  LLVMValueRef fast_fn;       // declared (pre) then populated; nullable
  valk_lval_t *formals;       // for adapter emission (fast-safe only)
  bool is_fast;               // compile slow as adapter if true
} aot_cand_t;

static bool is_aot_candidate(valk_lval_t *v) {
  if (!v || LVAL_TYPE(v) != LVAL_FUN) return false;
  if (v->fun.builtin != nullptr) return false;
  if (!v->fun.body) return false;
  if (v->fun.native_name) return false;
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

// Count the formals in a lambda's formals list, rejecting `&` varargs.
// Returns SIZE_MAX if the list is malformed or contains varargs.
static size_t count_fast_formals(valk_lval_t *formals) {
  size_t n = 0;
  for (valk_lval_t *f = formals; f && LVAL_TYPE(f) == LVAL_CONS;
       f = f->cons.tail) {
    valk_lval_t *fh = f->cons.head;
    if (!fh || LVAL_TYPE(fh) != LVAL_SYM) return SIZE_MAX;
    if (strcmp(fh->str, "&") == 0) return SIZE_MAX;
    n++;
  }
  return n;
}

// VALK_AOT_VERBOSE=1 prints per-candidate compile decisions on stderr so
// users can see which lambdas got AOT'd and which fell back to the tree
// walker. Off by default to keep the build quiet.
static bool aot_verbose(void) {
  const char *e = getenv("VALK_AOT_VERBOSE");
  return e && *e && *e != '0';
}

int valk_build_emit_aot(valk_lenv_t *env, const char *o_path,
                        const char *c_path, size_t *out_count) {
  if (!env) return -1;

  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("valk_aot");
  if (!ctx) return -1;
  ctx->build_env = env;
  bool verbose = aot_verbose();

  aot_entry_t *entries = nullptr;
  size_t n = 0, cap = 0;

  // Phase 1 — identify candidates, assign native_name, and emit slow
  // variants for NON-fast-safe candidates. For fast-safe candidates we
  // only reserve the slow name here; the slow body is emitted in phase 4
  // as an adapter that trampolines into the fast variant (the body
  // already lives in the fast function, so slow doesn't need it).
  // Skipping the full slow-body compile also means forward references
  // don't matter for fast-safe candidates — phase 4 only needs the fast
  // name, which phase 2 guarantees exists.
  aot_cand_t *cands = nullptr;

  for (u64 i = 0; i < env->symbols.count; i++) {
    valk_lval_t *v = env->vals.items[i];
    if (!is_aot_candidate(v)) continue;

    char name[64];
    snprintf(name, sizeof(name), "valk_aot_%zu", n);

    bool safe = valk_llvm_body_is_fast_safe(v->fun.body);
    size_t nf = safe ? count_fast_formals(v->fun.formals) : SIZE_MAX;
    bool is_fast = safe && (nf != SIZE_MAX);

    LLVMValueRef fn;
    if (is_fast) {
      // Reserve the slow name with no body — phase 4 fills it in.
      LLVMTypeRef slow_ty = LLVMFunctionType(ctx->ptr_type,
        (LLVMTypeRef[]){ctx->ptr_type}, 1, 0);
      fn = LLVMAddFunction(ctx->module, name, slow_ty);
      LLVMSetLinkage(fn, LLVMExternalLinkage);
      if (verbose) {
        fprintf(stderr, "[AOT] fast: %s (%zu formals)\n",
                env->symbols.items[i] ? env->symbols.items[i] : name, nf);
      }
    } else {
      fn = valk_llvm_compile_lambda_body(ctx, v->fun.body, name);
      if (!fn) {
        if (verbose) {
          fprintf(stderr, "[AOT] skip: %s (codegen returned null)\n",
                  env->symbols.items[i] ? env->symbols.items[i] : name);
        }
        continue;
      }
      if (LLVMVerifyFunction(fn, LLVMReturnStatusAction)) {
        if (verbose) {
          fprintf(stderr, "[AOT] skip: %s (verify failed)\n",
                  env->symbols.items[i] ? env->symbols.items[i] : name);
        }
        LLVMDeleteFunction(fn);
        continue;
      }
      if (verbose) {
        fprintf(stderr, "[AOT] slow: %s\n",
                env->symbols.items[i] ? env->symbols.items[i] : name);
      }
    }

    v->fun.native_name = strdup(name);

    if (n == cap) {
      cap = cap ? cap * 2 : 8;
      entries = realloc(entries, cap * sizeof(*entries));
      cands = realloc(cands, cap * sizeof(*cands));
    }
    entries[n].name = strdup(name);
    cands[n].lval = v;
    cands[n].slow_name = strdup(name);
    cands[n].fast_name = nullptr;
    cands[n].slow_fn = fn;
    cands[n].fast_fn = nullptr;
    cands[n].formals = v->fun.formals;
    cands[n].is_fast = is_fast;
    n++;
  }

  // Phase 2 — pre-declare fast variants for all fast-safe candidates.
  // This is the whole point: when we compile the body of fast_A in
  // phase 3 and it references fast_B (forward or mutual), phase 2 has
  // already added fast_B to the module, so try_codegen_direct_call
  // resolves the LLVMGetNamedFunction lookup and emits a direct call.
  // Without this pre-declaration, fast_A would fall through to the
  // slow path for fast_B, killing TCO across the pair.
  for (size_t i = 0; i < n; i++) {
    if (!cands[i].is_fast) continue;
    size_t nf = count_fast_formals(cands[i].formals);

    char fast_name[80];
    snprintf(fast_name, sizeof fast_name, "%s_fast", cands[i].slow_name);

    LLVMTypeRef *params = malloc(sizeof(LLVMTypeRef) * (nf + 1));
    params[0] = ctx->ptr_type;
    for (size_t j = 0; j < nf; j++) params[j + 1] = ctx->ptr_type;
    LLVMTypeRef ft = LLVMFunctionType(ctx->ptr_type, params,
                                      (unsigned)(nf + 1), 0);
    free(params);

    LLVMValueRef ffn = LLVMAddFunction(ctx->module, fast_name, ft);
    LLVMSetLinkage(ffn, LLVMExternalLinkage);
    cands[i].fast_name = strdup(fast_name);
    cands[i].fast_fn = ffn;
  }

  // Phase 3 — populate fast variant bodies. Each body can now direct-call
  // any other fast variant by name. If verification fails for any fast
  // variant, the module is likely corrupt because other fast bodies may
  // already reference this fn by value — bail out and fall back to the
  // slow-only path (return -1 from this function; the caller treats
  // AOT emit failure as "skip AOT, use tree walker"). In practice fast
  // bodies share semantics with slow + arg threading, so this only
  // triggers on codegen bugs.
  bool fast_ok = true;
  for (size_t i = 0; i < n && fast_ok; i++) {
    if (!cands[i].fast_fn) continue;
    valk_lval_t *v = cands[i].lval;

    LLVMValueRef ffn = valk_llvm_compile_lambda_body_fast(
      ctx, v->fun.body, v->fun.formals, cands[i].fast_name);
    if (!ffn) { fast_ok = false; break; }

    if (LLVMVerifyFunction(ffn, LLVMReturnStatusAction)) {
      fprintf(stderr, "valk --build: fast variant %s failed verify; "
                      "dropping AOT for whole module\n",
              cands[i].fast_name);
      fast_ok = false;
    }
  }

  // Phase 4 — emit slow bodies for fast-safe candidates as thin adapters
  // that unpack formals from call_env by name and tail-call the matching
  // _fast variant with (valk_aot_root_env, arg_0, ...). This is what the
  // tree walker actually invokes via native_fn; the adapter then enters
  // the _fast call chain where mutual recursion turns into sibcall jmps.
  // Without this, native_fn for fast-safe lambdas would dispatch to the
  // empty reserved slow stub (undefined IR) or to a full slow body that
  // never enters _fast and so bounces back through the tree walker on
  // every forward/mutual reference.
  for (size_t i = 0; i < n && fast_ok; i++) {
    if (!cands[i].is_fast) continue;

    LLVMValueRef sfn = valk_llvm_compile_lambda_body_slow_adapter(
      ctx, cands[i].formals, cands[i].slow_name, cands[i].fast_name);
    if (!sfn || LLVMVerifyFunction(sfn, LLVMReturnStatusAction)) {
      fprintf(stderr, "valk --build: slow adapter %s failed verify; "
                      "dropping AOT for whole module\n",
              cands[i].slow_name);
      fast_ok = false;
    }
  }

  if (!fast_ok) {
    for (size_t i = 0; i < n; i++) {
      valk_lval_t *v = cands[i].lval;
      if (v && LVAL_TYPE(v) == LVAL_FUN && v->fun.native_name) {
        free(v->fun.native_name);
        v->fun.native_name = nullptr;
      }
      free(cands[i].slow_name);
      free(cands[i].fast_name);
      free(entries[i].name);
    }
    free(cands);
    free(entries);
    valk_llvm_ctx_free(ctx);
    return -1;
  }

  char *mod_err = nullptr;
  if (LLVMVerifyModule(ctx->module, LLVMReturnStatusAction, &mod_err)) {
    fprintf(stderr, "valk --build: AOT module verify failed: %s\n",
            mod_err ? mod_err : "unknown");
    if (mod_err) LLVMDisposeMessage(mod_err);
    // Roll back native_name assignments so runtime doesn't try to
    // resolve symbols that won't exist.
    for (u64 i = 0; i < env->symbols.count; i++) {
      valk_lval_t *v = env->vals.items[i];
      if (v && LVAL_TYPE(v) == LVAL_FUN && v->fun.native_name) {
        free(v->fun.native_name);
        v->fun.native_name = nullptr;
      }
    }
    for (size_t i = 0; i < n; i++) {
      free(entries[i].name);
      free(cands[i].slow_name);
      free(cands[i].fast_name);
    }
    free(cands);
    free(entries);
    valk_llvm_ctx_free(ctx);
    return -1;
  }
  if (mod_err) LLVMDisposeMessage(mod_err);

  int rc = 0;
  if (n > 0) {
    if (getenv("VALK_DUMP_AOT_IR")) {
      valk_aot_emit_ir(ctx, "/tmp/valk_aot_pre.ll");
    }
    // Run LLVM's new-PM default<O2> pipeline. Hand-written IR has
    // unreachable tco.dead blocks, redundant valk_lval_num boxing
    // after tail calls, and direct calls that could be sibcalled —
    // the optimizer handles all three cleanly.
    if (valk_aot_optimize(ctx) != 0) {
      fprintf(stderr, "valk --build: AOT optimize failed\n");
      rc = -1;
    } else {
      if (getenv("VALK_DUMP_AOT_IR")) {
        valk_aot_emit_ir(ctx, "/tmp/valk_aot_post.ll");
      }
      if (valk_aot_emit_object(ctx, o_path) != 0) {
        fprintf(stderr, "valk --build: AOT emit object failed\n");
        rc = -1;
      }
    }
  }

  FILE *f = fopen(c_path, "w");
  if (!f) {
    fprintf(stderr, "valk --build: cannot write %s\n", c_path);
    rc = -1;
  } else {
    write_dispatch_c(f, entries, n);
    fclose(f);
  }

  for (size_t i = 0; i < n; i++) {
    free(entries[i].name);
    free(cands[i].slow_name);
    free(cands[i].fast_name);
  }
  free(cands);
  free(entries);
  valk_llvm_ctx_free(ctx);

  if (out_count) *out_count = n;
  return rc;
}
