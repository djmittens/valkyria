#include "parser.h"
#include <editline.h>
#include <mpc.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

valk_lval_t *eval(mpc_ast_t *ast);
valk_lval_t *read_ast(const mpc_ast_t *ast);

int main(int argc, char *argv[]) {
  printf("Hello World %ld\n", sizeof(valk_lval_t));
  char *input;

  mpc_parser_t *number = mpc_new("number");
  mpc_parser_t *string = mpc_new("string");
  mpc_parser_t *symbol = mpc_new("symbol");
  mpc_parser_t *comment = mpc_new("comment");
  mpc_parser_t *sexpr = mpc_new("sexpr");
  mpc_parser_t *qexpr = mpc_new("qexpr");
  mpc_parser_t *expr = mpc_new("expr");
  mpc_parser_t *repl = mpc_new("repl");

  mpc_err_t *err =
      mpca_lang(MPCA_LANG_DEFAULT,
                "number: /-?[0-9]+/;\n"
                "string: /\"(\\\\.|[^\"])*\"/;\n"
                "symbol: /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/;\n"
                "comment: /;[^\\r\\n]*/;\n"
                // "symbol : \"list\" | \"head\" | \"tail\" | \"init\" "
                // "| \"join\" | \"eval\" | \"cons\" | \"len\" "
                // "| '+' | '-' | '*' | '/';\n"
                // q-expresions arent real(other lisps have Macross qith a '
                // macro being the same as a q-expression). That being said its
                // a quote macro, and therefore a quote expression
                "qexpr : '{' <expr>* '}';\n"
                // s-expressions, or symbolic expressions, which is a list of
                // expressions and symbols, this list can be evaluated to
                // produce new expressions
                "sexpr : '(' <expr>* ')';\n"
                "expr : <number> | <string> | <symbol> | <comment> | <qexpr> | <sexpr> ;\n"
                "repl : /^/<expr>*/$/;\n",

                number, string, symbol, comment, qexpr, sexpr, expr, repl);

  if (err) {
    printf("Error constructing mpca_lang: %s\n", mpc_err_string(err));
  }
  valk_lenv_t *env = valk_lenv_new();
  valk_lenv_builtins(env);

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

      finalRes = valk_lval_eval(env, finalRes);
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
  free(env);
  mpc_cleanup(8, number, string, symbol, comment, qexpr, sexpr, expr, repl);
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
  } else if (strstr(ast->tag, "symbol")) {
    return valk_lval_sym(ast->contents);
  } else if (strstr(ast->tag, "string")) {
    // Lets cutoff the bullshit
    int len = strlen(ast->contents);
    ast->contents[len - 1] = '\0';
    char *unescaped = malloc(len - 1);
    strcpy(unescaped, ast->contents + 1);
    unescaped = mpcf_unescape(unescaped);
    valk_lval_t *res;
    res = valk_lval_str(unescaped);
    free(unescaped);
    return res;
  }
  valk_lval_t *x = NULL;
  if (strstr(ast->tag, "qexpr")) {
    x = valk_lval_qexpr_empty();
  } else if (strstr(ast->tag, "sexpr") || (strcmp(ast->tag, ">") == 0)) {
    x = valk_lval_sexpr_empty();
  } else {
    return valk_lval_err("Incorrect node type");
  }

  mpc_ast_t *child;
  valk_lval_t *tChild;
  for (int i = 0; i < ast->children_num; ++i) {
    child = ast->children[i];
    if (strcmp(child->contents, "{") == 0) {
      continue;
    }
    if (strcmp(child->contents, "}") == 0) {
      continue;
    }
    if (strcmp(child->contents, "(") == 0) {
      continue;
    }
    if (strcmp(child->contents, ")") == 0) {
      continue;
    }
    if (strcmp(child->tag, "regex") == 0) {
      continue;
    }
    if (strstr(child->tag, "comment")) {
      continue;
    }

    tChild = read_ast(child);
    if (tChild) {
      x = valk_lval_add(x, tChild);
      if (x->type == LVAL_ERR) {
        // This operation can fail
        // In which case we should discard the child
        valk_lval_free(tChild);
        break;
      }
    } else {
      x = valk_lval_add(x, valk_lval_err("Invalid expression"));
      printf("Warn: Skipping unhandled token: %s\n", child->tag);
    }
  }
  return x;
}
