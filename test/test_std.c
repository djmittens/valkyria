#include "test_std.h"
#include "common.h"
#include "parser.h"

void test_parsing_prelude(VALK_TEST_ARGS()) {
  valk_lval_t *ast = VALK_FIXTURE("prelude");
  VALK_TEST();

  VALK_EXPECT_SUCCESS(ast);
  VALK_PASS();
  valk_lval_free(ast);
}

void test_always_failing(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_FAIL("This is an expected failure :%s, %s", "haaah", "ehhhhe");
}

void test_prelude_fun(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "(fun {add a b} {+ a b})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_SEXPR);
  VALK_ASSERT(res->expr.count == 0,
              "Defining a new function must result in an empty sexpr [%d]",
              res->num);
  valk_lval_free(res);

  res = valk_eval(env, "(add 10 100)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 110, "Defined function must be callable [%ld]",
              res->num);
  valk_lval_free(res);

  res = valk_eval(env, "(fun {_add a b} {+ a undefined})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_SEXPR);
  VALK_ASSERT(res->expr.count == 0,
              "Defining a new function must result in an empty sexpr [%d]",
              res->num);
  valk_lval_free(res);

  res = valk_eval(env, "(_add 10 100)");
  VALK_EXPECT_ERROR(res, "LEnv: Symbol `undefined` is not bound");
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_prelude_curry(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "((curry +) {1 2 3})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(
      res->num == 6,
      "Currying + should result in a new function that takes a list [%d]",
      res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_prelude_uncurry(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "((uncurry (curry +)) 1 2 3)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 6,
              "Uncurrying a curried function should apply to several  "
              "arguments [result: %d]",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
}

void test_prelude_do(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "(do (= {a} 2) (+ 1 2 3) (+ 1 a))");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 3,
              "Do operation should let you preform several actions returning "
              "the last result [result: %d]",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_prelude_let(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res =
      valk_eval(env, "(do (do (= {a} 2) (+ 1 2 3) (+ 1 a)) (a))");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 2, "Do operations will leak scope [result: %d]",
              res->num);
  valk_lval_free(res);

  res = valk_eval(env, "(do (let {do (= {b} 2) (+ 1 2 3) (+ 1 b)}) (b))");
  // Let opens a new scope, which is not shared with the outside do
  // therefore the last expression (b) should result in an error, as its bound
  // inside a let now
  VALK_EXPECT_ERROR(res, "LEnv: Symbol `b` is not bound");
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_prelude_nth(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "(nth 1 {1 2 3})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 1, "first element should return 1 [result: %d]",
              res->num);
  valk_lval_free(res);

  res = valk_eval(env, "(nth 0 {1 2 3})");
  VALK_EXPECT_ERROR(res, "Invalid array index (should start with 1)");
  valk_lval_free(res);

  res = valk_eval(env, "(nth 4 {99 2 3 40 5 6})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 40, "4th of array should return 40 [result: %d]",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_prelude_split(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "(split 0 {1 2 3 4 5 6 7 8})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR);
  VALK_ASSERT(
      res->expr.count == 2,
      "splitting at anything less than 1 should still work [result: %d]",
      res->expr.count);
  valk_lval_free(res);

  res = valk_eval(env, "(split 3 {1 2 3 4 5 6 7 8})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR);
  VALK_ASSERT(
      res->expr.count == 2,
      "splitting at 3rd index should yield lhs and rhs in a list [result: %d]",
      res->expr.count);
  VALK_ASSERT(res->expr.cell[0]->expr.count == 3,
              "lhs should have 3 things in it [result: %d]",
              res->expr.cell[0]->expr.count);
  VALK_ASSERT(res->expr.cell[1]->expr.count == 5,
              "rhs should have 5 things in it [result: %d]",
              res->expr.cell[1]->expr.count);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_prelude_map(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res =
      valk_eval(env, "(== (map (\\ {x} {* 2 x}) { 1 2 3} ) {2 4 6 })");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(
      res->num == 1,
      "using map with a lambda should double the elements numbers [result: %d]",
      res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_prelude_not(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "(not true)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 0, "Not true is false [%ld]", res->num);
  valk_lval_free(res);

  res = valk_eval(env, "(not false)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 1, "Not false is true [%ld]", res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_parsing_prelude", test_parsing_prelude);
  valk_testsuite_add_test(suite, "test_prelude_fun", test_prelude_fun);
  valk_testsuite_add_test(suite, "test_prelude_curry", test_prelude_curry);
  valk_testsuite_add_test(suite, "test_prelude_uncurry", test_prelude_uncurry);
  valk_testsuite_add_test(suite, "test_prelude_do", test_prelude_do);
  valk_testsuite_add_test(suite, "test_prelude_let", test_prelude_let);
  valk_testsuite_add_test(suite, "test_prelude_nth", test_prelude_nth);
  valk_testsuite_add_test(suite, "test_prelude_split", test_prelude_split);
  valk_testsuite_add_test(suite, "test_prelude_map", test_prelude_map);

  if (0) {
    valk_testsuite_add_test(suite, "test_always_failing", test_always_failing);
  }

  valk_testsuite_add_test(suite, "test_prelude_not", test_prelude_not);

  // load fixtures
  valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env); // load the builtins
  valk_lval_t *r = valk_lval_eval(env, valk_lval_copy(ast));
  valk_lval_free(r);

  valk_testsuite_fixture_add(suite, "prelude", ast,
                             (_fixture_copy_f *)valk_lval_copy,
                             (_fixture_free_f *)valk_lval_free);
  valk_testsuite_fixture_add(suite, "env", env,
                             (_fixture_copy_f *)valk_lenv_copy,
                             (_fixture_free_f *)valk_lenv_free);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

valk_lval_t *valk_lval_find_error(valk_lval_t *ast) {
  switch (ast->type) {
  case LVAL_ERR:
    return ast;
  case LVAL_QEXPR:
  case LVAL_SEXPR: {
    for (size_t i = 0; i < ast->expr.count; i++) {
      if (valk_lval_find_error(ast->expr.cell[i])) {
        return ast->expr.cell[i];
      }
    }
  }
  case LVAL_STR:
  case LVAL_FUN:
  case LVAL_NUM:
  case LVAL_SYM:
    return nullptr;
  }
}

valk_lval_t *valk_eval(valk_lenv_t *env, const char *expr) {
  int pos = 0;
  return valk_lval_eval(env, valk_lval_read(&pos, expr));
}
