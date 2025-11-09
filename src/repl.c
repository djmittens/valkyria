#include <editline.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aio.h"
#include "log.h"
#include "memory.h"
#include "parser.h"

static void __aio_free(void *system) { valk_aio_stop(system); }

int main(int argc, char *argv[]) {
  char *input;
  // Initialize global arena (persistent) and scratch arena (ephemeral)
  size_t const GLOBAL_ARENA_BYTES = 16 * 1024 * 1024;   // 16 MiB
  size_t const SCRATCH_ARENA_BYTES = 4 * 1024 * 1024;   // 4 MiB

  valk_mem_arena_t *global_arena = malloc(GLOBAL_ARENA_BYTES);
  valk_mem_arena_init(global_arena, GLOBAL_ARENA_BYTES - sizeof(*global_arena));

  valk_mem_arena_t *scratch = malloc(SCRATCH_ARENA_BYTES);
  valk_mem_arena_init(scratch, SCRATCH_ARENA_BYTES - sizeof(*scratch));

  // Set thread allocator to global for persistent structures
  valk_thread_ctx.allocator = (void *)global_arena;

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  const char *enable_aio = getenv("VALK_ENABLE_AIO");
  if (enable_aio && enable_aio[0] != '\0') {
    valk_aio_system_t *aio = valk_aio_start();
    valk_lenv_put(env, valk_lval_sym("aio"),
                  valk_lval_ref("aio_system", aio, __aio_free));
  }

  if (argc >= 2) {
    for (int i = 1; i < argc; ++i) {
      valk_lval_t *res;
      VALK_WITH_ALLOC((void *)scratch) { res = valk_parse_file(argv[i]); }
      if (res->flags == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        while (res->expr.count) {
          valk_lval_t *x;
          VALK_WITH_ALLOC((void *)scratch) {
            x = valk_lval_eval(env, valk_lval_pop(res, 0));
          }

          if (x->flags == LVAL_ERR) {
            valk_lval_println(x);
          }
        }
      }
      valk_mem_arena_reset(scratch);
    }
  }

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
  }
  // No frees for arena-backed data; OS reclaim on exit.
  return EXIT_SUCCESS;
}
