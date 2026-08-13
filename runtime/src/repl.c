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

  valk_coverage_init();
  if (valk_coverage_enabled()) {
    atexit(valk_coverage_save_on_exit);
  }
  
  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);
  // The root env is read on every symbol resolution and, under the threaded
  // runtime (LSP workers), mutated and read concurrently. Back it with the
  // concurrent hash map: lock-free reads, striped-lock writes, O(1) lookup.
  valk_lenv_make_concurrent(env);
  valk_macro_env_init(env);

  VALK_WITH_ALLOC((void*)gc_heap) {
    valk_lval_t** argv_items = malloc(argc * sizeof(valk_lval_t*));
    for (int i = 0; i < argc; i++)
      argv_items[i] = valk_lval_str(argv[i]);
    valk_lenv_def(env, valk_lval_sym("sys/argv"), valk_lval_qlist(argv_items, argc));
    free(argv_items);
  }

  // Set root environment for GC marking
  valk_gc_set_root(gc_heap, env);
  valk_thread_ctx.root_env = env;

  // Bootstrap: load prelude + core libs into root env (no module, no rewrite)
  {
    valk_lval_t *r = valk_load_file(env, "stdlib/prelude.valk");
    if (LVAL_TYPE(r) == LVAL_ERR) {
      fprintf(stderr, "Failed to load prelude: %s\n", r->str);
      return EXIT_FAILURE;
    }
    r = valk_load_file(env, "stdlib/aio/handles.valk");
    if (LVAL_TYPE(r) == LVAL_ERR) {
      fprintf(stderr, "Failed to load handles: %s\n", r->str);
      return EXIT_FAILURE;
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
        script_mode = true;
        valk_lval_t *res = valk_load_file(env, "quality/quality.valk");
        if (LVAL_TYPE(res) == LVAL_ERR) {
          valk_lval_println(res);
          return 1;
        }
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
      // The script goes through the same loader pipeline as any (load ...):
      // file-as-(do ...), module nesting, alias resolution.
      valk_lval_t *res = valk_load_file(env, argv[i]);
      if (LVAL_TYPE(res) == LVAL_ERR) {
        valk_lval_println(res);
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
