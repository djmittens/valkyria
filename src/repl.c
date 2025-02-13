#include "parser.h"
#include <editline.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char *argv[]) {
  char *input;

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  if (argc >= 2) {
    for (int i = 1; i < argc; ++i) {
      valk_lval_t *res = valk_parse_file(argv[i]);
      if (res->type == LVAL_ERR) {
        valk_lval_println(res);
      } else {
        while (res->expr.count) {
          valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(res, 0));

          if (x->type == LVAL_ERR) {
            valk_lval_println(x);
          }
          valk_lval_free(x);
        }
      }

      valk_lval_free(res);
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
    } while ((tmp->type != LVAL_ERR) && (input[pos] != '\0'));

    printf("AST: ");
    valk_lval_println(expr);

    expr = valk_lval_eval(env, expr);
    valk_lval_println(expr);

    free(input);
    valk_lval_free(expr);
  }
  free(env);
  return EXIT_SUCCESS;
}

valk_lval_t *read_num(char *num) {
  errno = 0;
  long x = strtol(num, NULL, 10);
  return errno != ERANGE ? valk_lval_num(x)
                         : valk_lval_err("Number outside long range");
}
