#define _POSIX_C_SOURCE 200809L
#include <editline/readline.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aio/aio.h"
#include "coverage.h"
#include "gc.h"
#include "log.h"
#include "memory.h"
#include "parser.h"

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
  u64 const SCRATCH_ARENA_BYTES = 4 * 1024 * 1024;

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

  valk_gc_heap_t* gc_heap = sys->heap;

  valk_mem_arena_t* scratch = malloc(SCRATCH_ARENA_BYTES);
  valk_mem_arena_init(scratch, SCRATCH_ARENA_BYTES - sizeof(*scratch));

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

  // Set root environment for GC marking and checkpoint evacuation
  valk_gc_set_root(gc_heap, env);
  valk_thread_ctx.root_env = env;

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
      if (strcmp(argv[i], "--script") == 0) {
        script_mode = true;
        continue;
      }
      if (strcmp(argv[i], "--repl") == 0) {
        force_repl = true;
        continue;
      }
      script_mode = true;  // Any file argument implies script mode
      valk_lval_t* res;
      // Parse into GC heap (persistent - AST must survive checkpoints)
      VALK_WITH_ALLOC((void*)gc_heap) { res = valk_parse_file(argv[i]); }
      if (LVAL_TYPE(res) == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        while (valk_lval_list_count(res) > 0) {
          // Evaluate in scratch arena - checkpoint will evacuate survivors
          valk_lval_t* x;
          VALK_WITH_ALLOC((void*)scratch) {
            x = valk_lval_eval(env, valk_lval_pop(res, 0));
          }

          if (LVAL_TYPE(x) == LVAL_ERR) {
            valk_lval_println(x);
            break;
          }

          // Checkpoint at safe point: between top-level expressions
          // This evacuates any values stored in env (via def) to GC heap
          valk_checkpoint(scratch, gc_heap, env);

          // GC safe point: expression evaluated, env and remaining AST (res) are live
          if (valk_gc_should_collect(gc_heap)) {
            valk_gc_heap_collect(gc_heap);  // Mark res as additional root
          }
        }
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

    // Wait for any running AIO systems to complete before exiting
    // This stops, joins threads, and frees all registered AIO systems
    valk_aio_wait_for_all_systems();

    if (valk_coverage_enabled()) {
      valk_coverage_report(valk_coverage_output_path());
      valk_coverage_reset();
    }

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
      // Parse and evaluate each expression in the input
      while (input[pos] != '\0') {
        // Skip whitespace
        while (input[pos] && strchr(" \t\n\r", input[pos])) pos++;
        if (input[pos] == '\0') break;

        valk_lval_t* expr = valk_lval_read(&pos, input);
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

    // Checkpoint: evacuate any values stored in env (via def) to GC heap,
    // then reset scratch arena. This replaces the simple arena reset.
    valk_checkpoint(scratch, gc_heap, env);

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

  // Gracefully stop AIO on REPL exit if present
  valk_lval_t* sym = valk_lval_sym("aio");
  valk_lval_t* val = valk_lenv_get(env, sym);
  if (LVAL_TYPE(val) != LVAL_ERR && LVAL_TYPE(val) == LVAL_REF &&
      strcmp(val->ref.type, "aio_system") == 0) {
    valk_aio_stop((valk_aio_system_t*)val->ref.ptr);
  }

  free(scratch);
  valk_system_shutdown(sys, 5000);
  valk_system_destroy(sys);

  return EXIT_SUCCESS;
}
