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

static void __aio_free(void *system) { valk_aio_stop(system); }

int main(int argc, char *argv[]) {
  char *input;
  // GC heap + scratch arena approach (Phase 5 complete with forwarding)
  // - GC heap for persistent values (managed by mark & sweep)
  // - Scratch arena for temporary values during evaluation
  // - Forwarding pointers allow scratch values to be promoted to GC heap
  size_t const GC_THRESHOLD_BYTES = 16 * 1024 * 1024;  // 16 MiB GC threshold
  size_t const SCRATCH_ARENA_BYTES = 4 * 1024 * 1024;  // 4 MiB scratch (REPL only)

  valk_gc_malloc_heap_t *gc_heap = valk_gc_malloc_heap_init(GC_THRESHOLD_BYTES);

  valk_mem_arena_t *scratch = malloc(SCRATCH_ARENA_BYTES);
  valk_mem_arena_init(scratch, SCRATCH_ARENA_BYTES - sizeof(*scratch));

  // Set thread allocator to GC heap for persistent structures
  valk_thread_ctx.allocator = (void *)gc_heap;

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // Set root environment for GC marking
  valk_gc_malloc_set_root(gc_heap, env);

  // If we got here, we processed files but did not request exit; drop into REPL.
  // Set mode to repl now so shutdown inside REPL performs teardown.
  valk_lenv_put(env, valk_lval_sym("VALK_MODE"), valk_lval_str("init"));

  // Default: enable AIO/event loop in REPL so async/network builtins are usable.
  // Opt-out by setting VALK_DISABLE_AIO to a non-empty value.
  const char *disable_aio = getenv("VALK_DISABLE_AIO");
  if (!(disable_aio && disable_aio[0] != '\0')) {
    valk_aio_system_t *aio = valk_aio_start();
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
      valk_lval_t *res;
      // Parse into GC heap (persistent)
      VALK_WITH_ALLOC((void *)gc_heap) { res = valk_parse_file(argv[i]); }
      if (res->flags == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        while (valk_lval_list_count(res) > 0) {
          valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(res, 0));

          if (x->flags == LVAL_ERR) {
            valk_lval_println(x);
            break;
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
    valk_lval_t *sym = valk_lval_sym("aio");
    valk_lval_t *val = valk_lenv_get(env, sym);
    if (val->flags != LVAL_ERR && val->flags && strcmp(val->ref.type, "aio_system") == 0) {
      valk_aio_stop((valk_aio_system_t *)val->ref.ptr);
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

    valk_lval_t *expr;
    VALK_WITH_ALLOC((void *)scratch) {
      expr = valk_lval_sexpr_empty();
      valk_lval_t *tmp;
      do {
        tmp = valk_lval_read(&pos, input);
        valk_lval_add(expr, tmp);
      } while ((tmp->flags != LVAL_ERR) && (input[pos] != '\0'));

      if (valk_log_would_log(VALK_LOG_TRACE)) {
        fprintf(stdout, "AST: ");
        valk_lval_println(expr);
      }

      expr = valk_lval_eval(env, expr);
    }
    valk_lval_println(expr);

    free(input);
    valk_mem_arena_reset(scratch);

    // GC safe point: all evaluation done, scratch reset, only environment is live
    // Classic Lisp approach - collect between expressions, never during evaluation
    if (valk_gc_malloc_should_collect(gc_heap)) {
      valk_gc_malloc_collect(gc_heap);
    }
  }

  // Gracefully stop AIO on REPL exit if present
  valk_lval_t *sym = valk_lval_sym("aio");
  valk_lval_t *val = valk_lenv_get(env, sym);
  if (val->flags != LVAL_ERR && val->flags && strcmp(val->ref.type, "aio_system") == 0) {
    valk_aio_stop((valk_aio_system_t *)val->ref.ptr);
  }

  // Clean up GC heap for LeakSanitizer
  valk_gc_malloc_heap_destroy(gc_heap);
  free(scratch);

  return EXIT_SUCCESS;
}
