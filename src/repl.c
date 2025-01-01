#include "parser.h"
#include <editline.h>
#include <mpc.h>
#include <stdio.h>
#include <stdlib.h>

valk_lval_t *eval(mpc_ast_t *ast);
valk_lval_t *read_ast(const mpc_ast_t *ast);

int main(int argc, char *argv[]) {
  printf("Hello World\n");
  char *input;

  mpc_parser_t *number = mpc_new("number");
  mpc_parser_t *symbol = mpc_new("symbol");
  mpc_parser_t *sexpr = mpc_new("sexpr");
  mpc_parser_t *expr = mpc_new("expr");
  mpc_parser_t *repl = mpc_new("repl");

  mpca_lang(
      MPCA_LANG_DEFAULT,
      "number : /-?[0-9]+/;\n"
      "symbol : '+' | '-' | '*' | '/';\n"
      // s-expressions, or symbolic expressions, which is a list of expressions
      "sexpr : '(' <expr>* ')';\n"
      "expr : <number> | <symbol> | <sexpr>;\n"
      "repl : /^/<expr>*/$/;\n",

      number, symbol, sexpr, expr, repl);

  // This is the L in repL
  while ((input = readline("valkyria> ")) != NULL) {
    add_history(input);
    mpc_result_t res;
    if (mpc_parse("<stdin>", input, repl, &res)) {
      mpc_ast_print(res.output);

      valk_lval_t *finalRes = read_ast(res.output);
      printf("AST: ");
      valk_lval_print(finalRes);
      printf("\n");

      finalRes = valk_lval_eval(finalRes);
      printf("Result: ");
      valk_lval_print(finalRes);
      printf("\n");

      // valk_lval_free(finalRes);
      mpc_ast_delete(res.output);
    } else {
      mpc_err_print(res.error);
      mpc_err_delete(res.error);
    }

    free(input);
  }
  mpc_cleanup(5, number, symbol, sexpr, expr, repl);
  return EXIT_SUCCESS;
}

valk_lval_t *read_num(char *num) {
  errno = 0;
  long x = strtol(num, NULL, 10);
  return errno != ERANGE ? valk_lval_num(x)
                         : valk_lval_err("Number outside long range");
}

valk_lval_t *read_ast(const mpc_ast_t *ast) {
  if (strstr(ast->tag, "number")) {
    return read_num(ast->contents);
  }
  if (strstr(ast->tag, "symbol")) {
    return valk_lval_sym(ast->contents);
  }

  valk_lval_t *x = NULL;
  if (strstr(ast->tag, "sexpr") || (strcmp(ast->tag, ">") == 0)) {
    x = valk_lval_sexpr_empty();
  } else {
    return valk_lval_err("Incorrect node type");
  }

  mpc_ast_t *child;
  valk_lval_t *tChild;
  for (int i = 0; i < ast->children_num; ++i) {
    child = ast->children[i];
    if (strcmp(child->contents, "(") == 0) {
      continue;
    }
    if (strcmp(child->contents, ")") == 0) {
      continue;
    }
    if (strcmp(child->tag, "regex") == 0) {
      continue;
    }
    tChild = read_ast(child);
    if (tChild) {
      valk_lval_sexpr_add(x, tChild);
    } else {
      valk_lval_sexpr_add(x, valk_lval_err("Invalid expression"));
      printf("Warn: Skipping unhandled token: %s\n", child->tag);
    }
  }
  return x;
}
