#include "parser.h"
#include "testing.h"

valk_lval_t *find_error(valk_lval_t *ast) {
  switch (ast->type) {
  case LVAL_ERR:
    return ast;
  case LVAL_QEXPR:
  case LVAL_SEXPR: {
    for (int i = 0; i < ast->expr.count; i++) {
      if (find_error(ast->expr.cell[i])) {
        return ast->expr.cell[i];
      }
    }
  }
  case LVAL_STR:
  case LVAL_FUN:
  case LVAL_NUM:
  case LVAL_SYM:
    return NULL;
  }
}

void test_parsing_prelude(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *ast = valk_parse_file("../src/prelude.valk");
  printf("Read the file as ");
  valk_lval_println(ast);

  valk_lval_t *err = find_error(ast);
  if (err) {
    VALK_FAIL("Encountered %s, %s", valk_ltype_name(err->type), err->str);

  } else {
    VALK_PASS();
  }
  valk_lval_free(ast);
}

void test_always_failing(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_FAIL("This is an expected failure :%s, %s", "haaah", "ehhhhe");
}

int main(int argc, const char **argv) {
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_parsing_prelude", test_parsing_prelude);
  if (0) {
    valk_testsuite_add_test(suite, "test_always_failing", test_always_failing);
  }

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
