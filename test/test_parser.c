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
  valk_lval_t *ast = VALK_FIXTURE("prelude");

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

void test_prelude_not(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  int pos = 0;
  valk_lval_t *res = valk_lval_eval(env, valk_lval_read(&pos, "(not 1)"));

  valk_lval_println(res);

  valk_lval_t *err = find_error(res);
  if (err) {
    VALK_FAIL("Encountered %s, %s", valk_ltype_name(err->type), err->str);

  } else {
    VALK_PASS();
  }
  valk_lenv_free(env);
  valk_lval_free(res);
}

// TODO(main):  ny way to avoid this boilerplate???
static void valk_lval_free_void(void *lval) { valk_lval_free(lval); }
static void *valk_lval_copy_void(void *lval) { return valk_lval_copy(lval); }

static void valk_lenv_free_void(void *lenv) { valk_lenv_free(lenv); }
static void *valk_lenv_copy_void(void *lenv) { return valk_lenv_copy(lenv); }

int main(int argc, const char **argv) {
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_parsing_prelude", test_parsing_prelude);
  if (1) {
    valk_testsuite_add_test(suite, "test_always_failing", test_always_failing);
  }
  valk_testsuite_add_test(suite, "test_prelude_not", test_prelude_not);

  // load fixtures
  valk_lval_t *ast = valk_parse_file("../src/prelude.valk");
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env); // load the builtins
  valk_lval_t *r = valk_lval_eval(env, valk_lval_copy(ast));
  valk_lval_free(r);

  valk_testsuite_fixture_add(suite, "prelude", ast, valk_lval_copy_void,
                             valk_lval_free_void);
  valk_testsuite_fixture_add(suite, "env", env, valk_lenv_copy_void,
                             valk_lenv_free_void);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
