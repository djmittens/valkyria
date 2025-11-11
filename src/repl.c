#include <editline.h>
#include <errno.h>
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
  // Initialize global arena (persistent) and scratch arena (ephemeral)
  // TODO(arena-gc): Global arena needs GC or better reclamation - currently accumulates
  // garbage from map/filter/join intermediate allocations during script execution
  size_t const GLOBAL_ARENA_BYTES = 64 * 1024 * 1024;   // 64 MiB
  size_t const SCRATCH_ARENA_BYTES = 16 * 1024 * 1024;  // 16 MiB

  valk_mem_arena_t *global_arena = malloc(GLOBAL_ARENA_BYTES);
  valk_mem_arena_init(global_arena, GLOBAL_ARENA_BYTES - sizeof(*global_arena));

  valk_mem_arena_t *scratch = malloc(SCRATCH_ARENA_BYTES);
  valk_mem_arena_init(scratch, SCRATCH_ARENA_BYTES - sizeof(*scratch));

  // Set thread allocator to global for persistent structures
  valk_thread_ctx.allocator = (void *)global_arena;

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

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

  if (argc >= 2) {
    for (int i = 1; i < argc; ++i) {
      if (strcmp(argv[i], "--script") == 0) {
        continue;
      }
      valk_lval_t *res;
      // Use global arena for script execution - values persist across expressions
      VALK_WITH_ALLOC((void *)global_arena) { res = valk_parse_file(argv[i]); }
      if (res->flags == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        while (valk_lval_list_count(res) > 0) {
          valk_lval_t *x;
          VALK_WITH_ALLOC((void *)global_arena) {
            x = valk_lval_eval(env, valk_lval_pop(res, 0));
          }

          if (x->flags == LVAL_ERR) {
            valk_lval_println(x);
            break;
          }
        }
      }
    }
  }

  // If we got here, we processed files but did not request exit; drop into REPL.
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

    // Check if we should run GC
    if (valk_gc_should_collect(global_arena)) {
      size_t reclaimed = valk_gc_collect(env, global_arena);
      if (reclaimed > 0) {
        fprintf(stderr, "GC: Collected %zu bytes\n", reclaimed);
      }
    }
  }

  // No frees for arena-backed data; OS reclaim on exit.
  // Gracefully stop AIO on REPL exit if present
  valk_lval_t *sym = valk_lval_sym("aio");
  valk_lval_t *val = valk_lenv_get(env, sym);
  if (val->flags != LVAL_ERR && val->flags && strcmp(val->ref.type, "aio_system") == 0) {
    valk_aio_stop((valk_aio_system_t *)val->ref.ptr);
  }
  return EXIT_SUCCESS;
}
