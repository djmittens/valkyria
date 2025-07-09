#include <editline.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "aio.h"
#include "memory.h"
#include "parser.h"

static void __aio_free(void *system) { valk_aio_stop(system); }

int main(int argc, char *argv[]) {
  char *input;

  valk_mem_init_malloc();

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  valk_aio_system_t *aio = valk_aio_start();
  valk_lenv_put(env, valk_lval_sym("aio"),
                valk_lval_ref("aio_system", aio, __aio_free));

  if (argc >= 2) {
    for (int i = 1; i < argc; ++i) {
      valk_lval_t *res = valk_parse_file(argv[i]);
      if (res->flags == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        while (res->expr.count) {
          valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(res, 0));

          if (x->flags == LVAL_ERR) {
            valk_lval_println(x);
          }
        }
      }

    }
  }

  // This is the L in repL
  while ((input = readline("valkyria> ")) != NULL) {
    int pos = 0;
    add_history(input);

    valk_lval_t *expr = valk_lval_sexpr_empty();
    valk_lval_t *tmp;
    do {
      tmp = valk_lval_read(&pos, input);
      valk_lval_add(expr, tmp);
    } while ((tmp->flags != LVAL_ERR) && (input[pos] != '\0'));

    printf("AST: ");
    valk_lval_println(expr);

    expr = valk_lval_eval(env, expr);
    valk_lval_println(expr);

    free(input);
  }
  free(env);
  return EXIT_SUCCESS;
}
