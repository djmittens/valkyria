#define _POSIX_C_SOURCE 200809L
#include <editline/readline.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <limits.h>

#include "build.h"
#include "coverage.h"
#include "gc.h"
#include "log.h"
#include "macro.h"
#include "memory.h"
#include "parser.h"
#include "type_env.h"

// Global pointers for signal handler (Phase 8: Telemetry)
static valk_mem_arena_t* g_scratch_for_signal = nullptr;
static valk_gc_heap_t* g_heap_for_signal = nullptr;

// Per-evaluation memory tracking for REPL profile dashboard
static valk_repl_mem_snapshot_t g_last_eval_before;
static valk_repl_mem_snapshot_t g_last_eval_after;

// Weakly-imported JIT entry points. Resolve to the impls in
// src/llvm/llvm_jit.c when valk_llvm is linked. NULL otherwise — the
// script loader then falls through to the tree walker.
typedef struct valk_jit_t valk_jit_t;
__attribute__((weak)) valk_jit_t *valk_jit_compile_env(valk_lenv_t *env);
__attribute__((weak)) void valk_jit_free(valk_jit_t *jit);
__attribute__((weak)) size_t valk_jit_compiled_count(valk_jit_t *jit);

// Process-lifetime JIT handle. The script loader compiles every
// AOT-eligible lambda in env once after pass 1 (defs evaluated) and
// holds the result here so JIT'd code stays mapped for the rest of
// the process. Freed at exit (intentionally leaked: process teardown
// frees everything anyway, and freeing the LLJIT before any callbacks
// have finished settling could invalidate function pointers held by
// async tasks still draining).
static valk_jit_t *g_script_jit = nullptr;

// Returns true if JIT is available and the user opted in via VALK_JIT=1.
// Default OFF for now — JIT exposes a few async/thread-related codegen
// edge cases (closures + async, env-reachability under heavy parallel
// load) that the `--build` AOT path doesn't trigger but JIT does.
// Once those are nailed down, flip the default and rename to
// VALK_NO_JIT for the inverse semantics.
static bool jit_should_compile(void) {
  if (&valk_jit_compile_env == nullptr) return false;
  const char *on = getenv("VALK_JIT");
  if (!on || !*on || *on == '0') return false;
  return true;
}

// Compile every AOT-eligible lambda in env to native code via LLVM ORC.
// Idempotent — only the first call does work; subsequent calls are
// no-ops (the JIT is permanent for the process). If JIT compile fails,
// returns silently and execution continues interpreted.
static void jit_compile_script_env(valk_lenv_t *env) {
  if (!jit_should_compile()) return;
  if (g_script_jit) return;
  g_script_jit = valk_jit_compile_env(env);
  if (g_script_jit && getenv("VALK_JIT_VERBOSE")) {
    fprintf(stderr, "[JIT] compiled %zu lambdas\n",
            valk_jit_compiled_count(g_script_jit));
  }
}

// True if `form` is a top-level binding form whose evaluation only
// adds to env without doing user-visible work — i.e., it's safe to
// defer JIT compilation past it. Recognized after macro expansion:
//   (def {name} value) - direct binding
//   (sig 'name ...)    - type signature decl
//   (load "...")       - bring in another file's defs
// Anything else (a top-level call, a (println ...), etc.) is "work"
// — we trigger JIT compile right before it runs so the work executes
// against compiled code.
static bool form_is_def_like(valk_lval_t *form) {
  if (!form || LVAL_TYPE(form) != LVAL_CONS) return false;
  if (form->flags & LVAL_FLAG_QUOTED) return false;
  valk_lval_t *h = form->cons.head;
  if (!h || LVAL_TYPE(h) != LVAL_SYM) return false;
  return strcmp(h->str, "def") == 0
      || strcmp(h->str, "sig") == 0
      || strcmp(h->str, "load") == 0;
}

// SIGUSR1 handler: Print memory statistics to stderr
// Usage: kill -USR1 <pid>
static void sigusr1_handler(int sig) {
  (void)sig;
  if (g_scratch_for_signal != nullptr && g_heap_for_signal != nullptr) {
    fprintf(stderr, "\n[SIGUSR1] Memory statistics requested:\n");
    valk_memory_print_stats(g_scratch_for_signal, g_heap_for_signal, stderr);
  }
}

int main(int argc, char* argv[]) {
  char* input;
  u64 scratch_bytes = 128ULL * 1024 * 1024;

  const char* scratch_env = getenv("VALK_SCRATCH_SIZE");
  if (scratch_env && scratch_env[0] != '\0') {
    scratch_bytes = strtoull(scratch_env, nullptr, 10);
  }

  valk_system_config_t sys_cfg = valk_system_config_default();
  const char* hard_limit_env = getenv("VALK_HEAP_HARD_LIMIT");
  if (hard_limit_env && hard_limit_env[0] != '\0') {
    sys_cfg.gc_heap_size = strtoull(hard_limit_env, nullptr, 10);
  }

  valk_system_t* sys = valk_system_create(&sys_cfg);
  if (!sys) {
    fprintf(stderr, "Failed to create system\n");
    return EXIT_FAILURE;
  }

  valk_lval_init_singletons();

  valk_gc_heap_t* gc_heap = sys->heap;

  // Note: valk_system_create() already registers the calling thread for GC.
  // We just need to set up scratch arena and override the allocator.

  valk_mem_arena_t* scratch = malloc(scratch_bytes);
  valk_mem_arena_init(scratch, scratch_bytes - sizeof(*scratch));

  // Set thread allocator to GC heap for persistent structures
  valk_thread_ctx.allocator = (void*)gc_heap;
  valk_thread_ctx.scratch = scratch;
  valk_thread_ctx.checkpoint_threshold = VALK_CHECKPOINT_THRESHOLD_DEFAULT;
  valk_thread_ctx.checkpoint_enabled = true;

  valk_coverage_init();
  if (valk_coverage_enabled()) {
    atexit(valk_coverage_save_on_exit);
  }
  
  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);
  valk_macro_env_init(env);

  VALK_WITH_ALLOC((void*)gc_heap) {
    valk_lval_t** argv_items = malloc(argc * sizeof(valk_lval_t*));
    for (int i = 0; i < argc; i++)
      argv_items[i] = valk_lval_str(argv[i]);
    valk_lenv_def(env, valk_lval_sym("sys/argv"), valk_lval_qlist(argv_items, argc));
    free(argv_items);
  }

  // Set root environment for GC marking and checkpoint evacuation
  valk_gc_set_root(gc_heap, env);
  valk_thread_ctx.root_env = env;

  // Bootstrap: load prelude + core libs into root env (no module, no rewrite)
  {
    valk_lval_t *r = valk_load_file(env, "stdlib/prelude.valk");
    if (LVAL_TYPE(r) == LVAL_ERR) {
      fprintf(stderr, "Failed to load prelude: ");
      valk_lval_println(r);
    }
    r = valk_load_file(env, "stdlib/aio/handles.valk");
    if (LVAL_TYPE(r) == LVAL_ERR) {
      fprintf(stderr, "Failed to load handles: ");
      valk_lval_println(r);
    }
  }

  // Set up SIGUSR1 handler for runtime memory stats (Phase 8: Telemetry)
  // Usage: kill -USR1 <pid> to print memory statistics
  g_scratch_for_signal = scratch;
  g_heap_for_signal = gc_heap;
  struct sigaction sa = {
      .sa_handler = sigusr1_handler,
      .sa_flags = SA_RESTART,  // Restart interrupted syscalls (e.g., readline)
  };
  sigemptyset(&sa.sa_mask);
  sigaction(SIGUSR1, &sa, nullptr);

  // AIO system is NOT auto-created. Scripts must explicitly call (aio/start)
  // with their desired configuration to use async/networking features.
  // This avoids singleton confusion and ensures config is always explicit.

  bool script_mode = false;
  bool force_repl = false;
  if (argc >= 2) {
    for (int i = 1; i < argc; ++i) {
      if (strcmp(argv[i], "--quality-snapshot") == 0) {
        const char *dir = (i + 1 < argc) ? argv[++i] : ".";
        char resolved[PATH_MAX];
        if (!realpath(dir, resolved)) {
          fprintf(stderr, "quality-snapshot: cannot resolve path: %s\n", dir);
          return 1;
        }
        VALK_WITH_ALLOC((void*)gc_heap) {
          valk_lenv_put(env, valk_lval_sym("VALK_QUALITY_DIR"),
                        valk_lval_str(resolved));
        }
        char script_path[PATH_MAX];
        snprintf(script_path, sizeof(script_path), "%s/stdlib/diag/quality.valk", resolved);
        script_mode = true;
        valk_lval_t *res;
        VALK_WITH_ALLOC((void*)gc_heap) {
          res = valk_parse_file(script_path);
        }
        if (LVAL_TYPE(res) == LVAL_ERR) {
          valk_lval_println(res);
          return 1;
        }
        // Stash res into eval_expr so mark_eval_stack_roots covers it
        // for the lifetime of the load loop. The inner valk_lval_eval
        // saves/restores eval_expr through saved_eval_exprs[] so our
        // outer assignment survives across each form's evaluation.
        valk_lval_t *saved_outer_expr = valk_thread_ctx.eval_expr;
        valk_thread_ctx.eval_expr = res;
        while (valk_lval_list_count(res) > 0) {
          valk_lval_t *x;
          VALK_WITH_ALLOC((void*)gc_heap) {
            x = valk_type_transform_expr(valk_lval_pop(res, 0));
          }
          if (LVAL_TYPE(x) == LVAL_NIL) continue;
          if (LVAL_TYPE(x) == LVAL_ERR) { valk_lval_println(x); break; }
          valk_lval_t *saved_outer_value = valk_thread_ctx.eval_value;
          valk_thread_ctx.eval_value = x;
          VALK_WITH_ALLOC((void*)scratch) {
            x = valk_lval_eval(env, x);
          }
          valk_thread_ctx.eval_value = saved_outer_value;
          if (LVAL_TYPE(x) == LVAL_ERR) { valk_lval_println(x); break; }
          VALK_GC_SAFE_POINT();
          if (valk_gc_should_collect(gc_heap)) valk_gc_heap_collect(gc_heap);
        }
        valk_thread_ctx.eval_expr = saved_outer_expr;
        continue;
      }
      if (strcmp(argv[i], "--build") == 0) {
        const char *src = (i + 1 < argc) ? argv[++i] : NULL;
        const char *out = NULL;
        if (src && i + 1 < argc && strcmp(argv[i + 1], "-o") == 0 &&
            i + 2 < argc) {
          out = argv[i + 2];
          i += 2;
        }
        if (!src || !out) {
          fprintf(stderr, "usage: valk --build SRC -o OUT\n");
          return 1;
        }
        int rc = valk_build(env, src, out);
        valk_system_unregister_thread(sys);
        free(scratch);
        valk_system_shutdown(sys, 5000);
        valk_system_destroy(sys);
        return rc;
      }
      if (strcmp(argv[i], "--script") == 0) {
        script_mode = true;
        continue;
      }
      if (strcmp(argv[i], "--repl") == 0) {
        force_repl = true;
        continue;
      }
      if (strcmp(argv[i], "--") == 0) {
        break;
      }
      script_mode = true;  // Any file argument implies script mode
      valk_lval_t* res;
      // Parse into GC heap (persistent - AST must survive checkpoints)
      VALK_WITH_ALLOC((void*)gc_heap) {
        res = valk_parse_file(argv[i]);
      }
      if (LVAL_TYPE(res) == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        // Stash res into eval_expr for GC coverage across all three
        // passes. valk_lval_eval is invoked from passes 1 and 3; in both
        // cases the inner eval saves/restores eval_expr via
        // saved_eval_exprs[] so this outer assignment survives.
        valk_lval_t *saved_outer_expr = valk_thread_ctx.eval_expr;
        valk_thread_ctx.eval_expr = res;

        // Pass 1: macro-expand top-level forms. (macro ...) defs eval into
        // env; other forms get their macro calls expanded. A top-level
        // (module X) macro here sets the pending prefix via side effect.
        VALK_WITH_ALLOC((void*)gc_heap) {
          valk_lval_t *cur = res;
          while (cur && LVAL_TYPE(cur) == LVAL_CONS) {
            if (valk_macro_is_def(cur->cons.head)) {
              valk_lval_t *r = valk_lval_eval(env, cur->cons.head);
              if (LVAL_TYPE(r) == LVAL_ERR) valk_lval_println(r);
              cur->cons.head = valk_lval_nil();
            } else {
              cur->cons.head = valk_macro_expand_one(env, cur->cons.head);
            }
            cur = cur->cons.tail;
          }
        }

        // Pass 2: apply module prefix if (module X) was declared.
        char *script_prefix = valk_take_pending_module_prefix();
        if (script_prefix)
          valk_module_apply_prefix(res, script_prefix);

        // Pass 3: type-transform + eval each form.
        //
        // JIT trigger point: just before the first non-def-like form
        // evaluates, compile every AOT-eligible lambda in env (stdlib
        // + script defs) into native code via LLVM ORC. By then all
        // top-level (def {f} (\ ...))/(fun {f} ...)/(load) forms have
        // populated env, so the JIT batch covers everything the
        // following work could call. Same compile pipeline as
        // `valk --build`; the difference is ORC keeps the equivalent
        // of the .o in memory and resolves runtime symbols against
        // the running process. Set VALK_NO_JIT=1 to disable.
        while (valk_lval_list_count(res) > 0) {
          valk_lval_t* x;
          VALK_WITH_ALLOC((void*)gc_heap) {
            x = valk_lval_pop(res, 0);
            x = valk_type_transform_expr(x);
          }
          if (LVAL_TYPE(x) == LVAL_NIL) continue;
          if (LVAL_TYPE(x) == LVAL_ERR) {
            valk_lval_println(x);
            break;
          }
          if (!form_is_def_like(x)) {
            jit_compile_script_env(env);
          }
          valk_lval_t *saved_outer_value = valk_thread_ctx.eval_value;
          valk_thread_ctx.eval_value = x;
          VALK_WITH_ALLOC((void*)scratch) {
            x = valk_lval_eval(env, x);
          }
          valk_thread_ctx.eval_value = saved_outer_value;

          if (LVAL_TYPE(x) == LVAL_ERR) {
            valk_lval_println(x);
            break;
          }
          if (atomic_load(&sys->shutting_down)) break;

          VALK_GC_SAFE_POINT();
          if (valk_gc_should_collect(gc_heap)) {
            valk_gc_heap_collect(gc_heap);
          }
        }
        if (script_prefix) free(script_prefix);
        valk_thread_ctx.eval_expr = saved_outer_expr;
      }
    }
  }

  // If script mode (and not forced REPL), cleanup and exit instead of entering REPL
  if (script_mode && !force_repl) {
    int exit_code = EXIT_SUCCESS;
    valk_lval_t* exit_val = valk_lenv_get(env, valk_lval_sym("VALK_EXIT_CODE"));
    if (LVAL_TYPE(exit_val) == LVAL_NUM) {
      exit_code = (int)exit_val->num;
    }

    if (valk_coverage_enabled()) {
      valk_coverage_report(valk_coverage_output_path());
      valk_coverage_reset();
    }

    valk_system_unregister_thread(sys);
    free(scratch);
    valk_system_shutdown(sys, 5000);
    valk_system_destroy(sys);

    return exit_code;
  }

  // This is the L in repL
  while ((input = readline("valkyria> ")) != nullptr) {
    int pos = 0;
    add_history(input);

    valk_repl_mem_take_snapshot(gc_heap, scratch, &g_last_eval_before);

    valk_lval_t* result = valk_lval_nil();
    VALK_WITH_ALLOC((void*)scratch) {
      while (input[pos] != '\0') {
        while (input[pos] && strchr(" \t\n\r", input[pos])) pos++;
        if (input[pos] == '\0') break;

        valk_lval_t* expr = valk_lval_read(&pos, input);
        if (LVAL_TYPE(expr) == LVAL_ERR) {
          result = expr;
          break;
        }

        expr = valk_type_transform_expr(expr);
        if (LVAL_TYPE(expr) == LVAL_NIL) continue;
        if (LVAL_TYPE(expr) == LVAL_ERR) {
          result = expr;
          break;
        }

        if (valk_log_would_log(VALK_LOG_TRACE)) {
          fprintf(stdout, "AST: ");
          valk_lval_println(expr);
        }

        result = valk_lval_eval(env, expr);
        if (LVAL_TYPE(result) == LVAL_ERR) break;
      }
    }
    valk_lval_println(result);

    free(input);

    VALK_GC_SAFE_POINT();

    valk_repl_mem_take_snapshot(gc_heap, scratch, &g_last_eval_after);
    i64 heap_delta, scratch_delta, lval_delta, lenv_delta;
    valk_repl_mem_snapshot_delta(&g_last_eval_before, &g_last_eval_after,
                                 &heap_delta, &scratch_delta,
                                 &lval_delta, &lenv_delta);
    valk_repl_set_eval_delta(heap_delta, scratch_delta, lval_delta, lenv_delta);

    // GC safe point: all evaluation done, scratch reset, only environment is
    // live Classic Lisp approach - collect between expressions, never during
    // evaluation
    if (valk_gc_should_collect(gc_heap)) {
      valk_gc_heap_collect(gc_heap);  // No additional roots in REPL
    }
  }

  valk_system_unregister_thread(sys);
  free(scratch);
  valk_system_shutdown(sys, 5000);
  valk_system_destroy(sys);

  return EXIT_SUCCESS;
}
