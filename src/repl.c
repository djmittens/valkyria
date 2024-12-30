#include <editline.h>
#include <mpc.h>
#include <stdio.h>
#include <stdlib.h>

long eval(mpc_ast_t *ast);

int main(int argc, char *argv[]) {
  printf("Hello World\n");
  char *input;

  mpc_parser_t *number = mpc_new("number");
  mpc_parser_t *operator= mpc_new("operator");
  mpc_parser_t *expr = mpc_new("expr");
  mpc_parser_t *repl = mpc_new("repl");

  mpca_lang(MPCA_LANG_DEFAULT,
            "number : /-?[0-9]+/;\n"
            "operator : '+' | '-' | '*' | '/';\n"
            "expr : <number> | '(' <operator> <expr>+ ')';\n"
            "repl : /^/ <operator> <expr>+ /$/;\n",

            number, operator, expr, repl);
  // This is the L in repL
  while ((input = readline("valkyria> ")) != NULL) {
    add_history(input);
    mpc_result_t res;
    if (mpc_parse("<stdin>", input, repl, &res)) {
      mpc_ast_print(res.output);

      printf("Result: %li\n", eval(res.output));

      mpc_ast_delete(res.output);
    } else {
      mpc_err_print(res.error);
      mpc_err_delete(res.error);
    }

    free(input);
  }
  mpc_cleanup(4, number, operator, expr, repl);
  return EXIT_SUCCESS;
}

long eval_op(char *op, long x, long y) {
  if (strcmp(op, "+") == 0) {
    return x + y;
  }
  if (strcmp(op, "-") == 0) {
    return x - y;
  }
  if (strcmp(op, "*") == 0) {
    return x * y;
  }
  if (strcmp(op, "/") == 0) {
    return x / y;
  }
  return 0;
}

long eval(mpc_ast_t *ast) {
  if (strstr(ast->tag, "number")) {
    return atoi(ast->contents);
  }

  char *op = ast->children[1]->contents;

  long x = eval(ast->children[2]);

  // mpc_ast_t *child = ast->children[3];
  int i = 3;
  while (strstr(ast->children[i]->tag, "expr")) {
    x = eval_op(op, x, eval(ast->children[i]));
    i++;
  }
  return x;
}
