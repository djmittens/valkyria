#include <editline.h>
#include <errno.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aio.h"
#include "gc.h"
#include "log.h"
#include "memory.h"
#include "parser.h"

static void __aio_free(void* system) { valk_aio_stop(system); }

int main(int argc, char* argv[]) {
  char* input;
  // GC heap + scratch arena approach (Phase 5 complete with forwarding)
  // - GC heap for persistent values (managed by mark & sweep)
  // - Scratch arena for temporary values during evaluation
  // - Forwarding pointers allow scratch values to be promoted to GC heap
  size_t const GC_THRESHOLD_BYTES = 16 * 1024 * 1024;  // 16 MiB GC threshold
  size_t const SCRATCH_ARENA_BYTES =
      4 * 1024 * 1024;  // 4 MiB scratch (REPL only)

  // Check for hard limit env var, default to threshold * 2
  size_t hard_limit = 0;
  const char* hard_limit_env = getenv("VALK_HEAP_HARD_LIMIT");
  if (hard_limit_env && hard_limit_env[0] != '\0') {
    hard_limit = strtoull(hard_limit_env, NULL, 10);
  }

  valk_gc_malloc_heap_t* gc_heap = valk_gc_malloc_heap_init(GC_THRESHOLD_BYTES, hard_limit);

  valk_mem_arena_t* scratch = malloc(SCRATCH_ARENA_BYTES);
  valk_mem_arena_init(scratch, SCRATCH_ARENA_BYTES - sizeof(*scratch));

  // Set thread allocator to GC heap for persistent structures
  valk_thread_ctx.allocator = (void*)gc_heap;
  valk_thread_ctx.heap = gc_heap;  // Also set as fallback for arena overflow
  valk_thread_ctx.scratch = scratch;
  valk_thread_ctx.checkpoint_threshold = VALK_CHECKPOINT_THRESHOLD_DEFAULT;
  valk_thread_ctx.checkpoint_enabled = true;

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // Set root environment for GC marking and checkpoint evacuation
  valk_gc_malloc_set_root(gc_heap, env);
  valk_thread_ctx.root_env = env;

  // If we got here, we processed files but did not request exit; drop into
  // REPL. Set mode to repl now so shutdown inside REPL performs teardown.
  valk_lenv_put(env, valk_lval_sym("VALK_MODE"), valk_lval_str("init"));

  // Default: enable AIO/event loop in REPL so async/network builtins are
  // usable. Opt-out by setting VALK_DISABLE_AIO to a non-empty value.
  const char* disable_aio = getenv("VALK_DISABLE_AIO");
  if (!(disable_aio && disable_aio[0] != '\0')) {
    valk_aio_system_t* aio = valk_aio_start();
    valk_lenv_put(env, valk_lval_sym("aio"),
                  valk_lval_ref("aio_system", aio, __aio_free));
  }

  bool script_mode = false;
  if (argc >= 2) {
    for (int i = 1; i < argc; ++i) {
      if (strcmp(argv[i], "--script") == 0) {
        script_mode = true;
        continue;
      }
      script_mode = true;  // Any file argument implies script mode
      valk_lval_t* res;
      // Parse into GC heap (persistent)
      VALK_WITH_ALLOC((void*)gc_heap) { res = valk_parse_file(argv[i]); }
      if (res->flags == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        while (valk_lval_list_count(res) > 0) {
          valk_lval_t* x = valk_lval_eval(env, valk_lval_pop(res, 0));

          if (x->flags == LVAL_ERR) {
            valk_lval_println(x);
            break;
          }

          // Checkpoint if scratch arena usage exceeds threshold
          if (valk_thread_ctx.checkpoint_enabled &&
              valk_should_checkpoint(scratch,
                                     valk_thread_ctx.checkpoint_threshold)) {
            valk_checkpoint(scratch, gc_heap, env);
          }

          // GC safe point: expression evaluated, only env is live
          if (valk_gc_malloc_should_collect(gc_heap)) {
            valk_gc_malloc_collect(gc_heap);
          }
        }
      }
    }
  }

  // If script mode, cleanup and exit instead of entering REPL
  if (script_mode) {
    valk_lval_t* sym = valk_lval_sym("aio");
    valk_lval_t* val = valk_lenv_get(env, sym);
    if (val->flags != LVAL_ERR && val->flags &&
        strcmp(val->ref.type, "aio_system") == 0) {
      valk_aio_stop((valk_aio_system_t*)val->ref.ptr);
    }

    // Clean up GC heap for LeakSanitizer
    valk_gc_malloc_heap_destroy(gc_heap);
    free(scratch);

    return EXIT_SUCCESS;
  }

  // If we got here, we processed no files; drop into REPL.
  // Set mode to repl now so shutdown inside REPL performs teardown.
  valk_lenv_put(env, valk_lval_sym("VALK_MODE"), valk_lval_str("repl"));

  // This is the L in repL
  while ((input = readline("valkyria> ")) != NULL) {
    int pos = 0;
    add_history(input);

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

    // GC safe point: all evaluation done, scratch reset, only environment is
    // live Classic Lisp approach - collect between expressions, never during
    // evaluation
    if (valk_gc_malloc_should_collect(gc_heap)) {
      valk_gc_malloc_collect(gc_heap);
    }
  }

  // Gracefully stop AIO on REPL exit if present
  valk_lval_t* sym = valk_lval_sym("aio");
  valk_lval_t* val = valk_lenv_get(env, sym);
  if (val->flags != LVAL_ERR && val->flags &&
      strcmp(val->ref.type, "aio_system") == 0) {
    valk_aio_stop((valk_aio_system_t*)val->ref.ptr);
  }

  // Clean up GC heap for LeakSanitizer
  valk_gc_malloc_heap_destroy(gc_heap);
  free(scratch);

  return EXIT_SUCCESS;
}
