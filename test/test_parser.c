#include "parser.h"
#include "testing.h"

void test_parsing_prelude(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *ast = valk_parse_file("../src/prelude.valk");
  printf("Read the file as ");
  valk_lval_println(ast);

  if (ast->type == LVAL_ERR) {
    VALK_FAIL("encountered a parsing error %s", ast->str);
  } else {
    VALK_PASS();
  }
  valk_lval_free(ast);
}

void test_always_failing(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_FAIL("This is an expected failure :%s", "haaah");
}

int main(int argc, const char **argv) {
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "test_always_failing", test_always_failing);
  valk_testsuite_add_test(suite, "test_parsing_prelude", test_parsing_prelude);

  int res = valk_testsuite_run(suite);

  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return res;
}
