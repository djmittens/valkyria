#include "test_std.h"

#include "collections.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

void test_parsing_prelude(VALK_TEST_ARGS()) {
  valk_lval_t *ast = VALK_FIXTURE("prelude");
  VALK_TEST();

  VALK_EXPECT_SUCCESS(ast);
  VALK_PASS();
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
  VALK_TEST_ASSERT(
      valk_lval_list_count(res) == 0,
      "Defining a new function must result in an empty sexpr [%ld]", res->num);

  res = valk_eval(env, "(add 10 100)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 110, "Defined function must be callable [%ld]",
                   res->num);

  res = valk_eval(env, "(fun {_add a b} {+ a undefined})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_SEXPR);
  VALK_TEST_ASSERT(
      valk_lval_list_count(res) == 0,
      "Defining a new function must result in an empty sexpr [%ld]", res->num);

  res = valk_eval(env, "(_add 10 100)");
  VALK_EXPECT_ERROR(res, "LEnv: Symbol `undefined` is not bound");

  VALK_PASS();
}

void test_prelude_curry(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "((curry +) {1 2 3})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(
      res->num == 6,
      "Currying + should result in a new function that takes a list [%ld != %ld]",
      res->num, 6L);

  VALK_PASS();
}

void test_prelude_uncurry(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "((uncurry (curry +)) 1 2 3)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 6,
              "Uncurrying a curried function should apply to several  "
              "arguments [result: %ld]",
              res->num);

  VALK_PASS();
}

void test_prelude_do(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "(do (= {a} 2) (+ 1 2 3) (+ 1 a))");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 3,
              "Do operation should let you preform several actions returning "
              "the last result [result: %ld]",
              res->num);

  VALK_PASS();
}

void test_prelude_let(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res =
      valk_eval(env, "(do (do (= {a} 2) (+ 1 2 3) (+ 1 a)) (a))");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 2, "Do operations will leak scope [result: %ld]",
              res->num);

  res = valk_eval(env, "(do (let {do (= {b} 2) (+ 1 2 3) (+ 1 b)}) (b))");
  // Let opens a new scope, which is not shared with the outside do
  // therefore the last expression (b) should result in an error, as its bound
  // inside a let now
  VALK_EXPECT_ERROR(res, "LEnv: Symbol `b` is not bound");

  VALK_PASS();
}

void test_prelude_nth(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "(nth 1 {1 2 3})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1, "first element should return 1 [result: %ld]",
              res->num);

  res = valk_eval(env, "(nth 0 {1 2 3})");
  VALK_EXPECT_ERROR(res, "Invalid array index (should start with 1)");

  res = valk_eval(env, "(nth 4 {99 2 3 40 5 6})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 40, "4th of array should return 40 [result: %ld]",
              res->num);

  VALK_PASS();
}

void test_prelude_split(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "(split 0 {1 2 3 4 5 6 7 8})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR);
  VALK_TEST_ASSERT(
      valk_lval_list_count(res) == 2,
      "splitting at anything less than 1 should still work [result: %zu]",
      valk_lval_list_count(res));

  res = valk_eval(env, "(split 3 {1 2 3 4 5 6 7 8})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR);
  VALK_TEST_ASSERT(
      valk_lval_list_count(res) == 2,
      "splitting at 3rd index should yield lhs and rhs in a list [result: %zu]",
      valk_lval_list_count(res));
  VALK_TEST_ASSERT(valk_lval_list_count(valk_lval_list_nth(res, 0)) == 3,
              "lhs should have 3 things in it [result: %zu]",
              valk_lval_list_count(valk_lval_list_nth(res, 0)));
  VALK_TEST_ASSERT(valk_lval_list_count(valk_lval_list_nth(res, 1)) == 5,
              "rhs should have 5 things in it [result: %zu]",
              valk_lval_list_count(valk_lval_list_nth(res, 1)));

  VALK_PASS();
}

void test_prelude_map(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res =
      valk_eval(env, "(== (map (\\ {x} {* 2 x}) { 1 2 3} ) {2 4 6 })");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1,
              "using map with a lambda should double the elements numbers "
              "[result: %ld]",
              res->num);

  VALK_PASS();
}

void test_prelude_not(VALK_TEST_ARGS()) {
  valk_lenv_t *env = VALK_FIXTURE("env");
  VALK_TEST();

  valk_lval_t *res = valk_eval(env, "(not true)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 0, "Not true is false [%ld]", res->num);

  res = valk_eval(env, "(not false)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1, "Not false is true [%ld]", res->num);

  VALK_PASS();
}

void test_dynamic_lists(VALK_TEST_ARGS()) {
  VALK_TEST();
  struct node {
    struct node *next;
    struct node *prev;
    size_t val;
  };

  constexpr size_t size = 100;
  struct node buf[size] = {0};

  struct node *head = &buf[0];
  struct node *end = nullptr;

  {  // init list
    for (size_t i = 0; i < size; i++) {
      buf[i].val = i;
      valk_dll_insert_after(end, &buf[i]);
      end = &buf[i];
    }

    size_t count = valk_dll_count(head);

    VALK_TEST_ASSERT(count == size,
                     "Expected linked list count to be %d, but was %d", size,
                     count);

    valk_dll_foreach(head) {
      if (item->prev != nullptr) {
        VALK_TEST_ASSERT(item->prev->val == (item->val - 1),
                         "Items are out of order: %d < %d", item->prev->val,
                         item->val);
      }
    }
  }

  {  // test removing nodes
    size_t start = 15;
    size_t popNum = 25;

    size_t numPop = 0;
    while (true) {
      if (popNum == numPop) {
        break;
      }
      valk_dll_pop(valk_dll_at(head, start));
      numPop++;
    }

    VALK_TEST_ASSERT(
        popNum == numPop,
        "Expected to pop the exact number of elements  %d, but was %d", popNum,
        numPop);

    size_t count = valk_dll_count(head);

    VALK_TEST_ASSERT(count == (size - popNum),
                     "Expected linked list count to be %d, but was %d",
                     (size - popNum), count);

    valk_dll_foreach(head) {
      // check values pre-deletion
      if (item->val > (start)) {
        break;
      }
      if (item->prev != nullptr) {
        VALK_TEST_ASSERT(item->prev->val == (item->val - 1),
                         "Items are out of order: %d < %d", item->prev->val,
                         item->val);
      }
    }

    valk_dll_foreach(head) {
      // check remaining values after deletion ()
      if (item->val <= start || item->prev->val == (start - 1)) {
        continue;
      }
      if (item->prev != nullptr) {
        VALK_TEST_ASSERT(item->prev->val == (item->val - 1),
                         "Items are out of order: %d < %d", item->prev->val,
                         item->val);
      }
    }
  }

  {  // test inserting nodes
    struct node item = {0};
    item.val = 9999;

    size_t pos = 40;
    valk_dll_insert_after(valk_dll_at(head, pos), &item);

    struct node item2 = {0};
    item2.val = 8888;
    valk_dll_insert_after(valk_dll_at(head, pos), &item2);

    VALK_TEST_ASSERT(valk_dll_at(head, pos + 1)->val == item2.val,
                     "Inserted item is not in the expected position expected, "
                     "%d , but was %d",
                     valk_dll_at(head, pos + 1)->val, item2.val);

    VALK_TEST_ASSERT(valk_dll_at(head, pos + 2)->val == item.val,
                     "Inserted item is not in the expected position expected, "
                     "%d , but was %d",
                     valk_dll_at(head, pos + 2)->val, item.val);
  }
  VALK_PASS();
}

static void *__lval_retain(void *lval) { return (valk_lval_t *)lval; }

static void __lval_release(void *lval) { UNUSED(lval); }

static void *__lenv_retain(void *lenv) { return (valk_lenv_t *)lenv; }

static void __lenv_release(void *lenv) { UNUSED(lenv); }

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);
  valk_mem_init_malloc();
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
  valk_testsuite_add_test(suite, "test_prelude_not", test_prelude_not);

  if (0) {
    valk_testsuite_add_test(suite, "test_always_failing", test_always_failing);
  }

  valk_testsuite_add_test(suite, "test_dynamic_lists", test_dynamic_lists);

  // load fixtures
  valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);  // load the builtins

  // Evaluate prelude sequentially (program semantics)
  while (valk_lval_list_count(ast)) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(ast, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      // Stop early if prelude fails; tests will surface the error
      break;
    }
  }

  valk_testsuite_fixture_add(suite, "prelude", ast, __lval_retain,
                             __lval_release);
  valk_testsuite_fixture_add(suite, "env", env, __lenv_retain, __lenv_release);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

valk_lval_t *valk_lval_find_error(valk_lval_t *ast) {
  switch (LVAL_TYPE(ast)) {
    case LVAL_ERR:
      return ast;
    case LVAL_QEXPR:
    case LVAL_SEXPR: {
      for (size_t i = 0; i < valk_lval_list_count(ast); i++) {
        valk_lval_t* child = valk_lval_list_nth(ast, i);
        if (valk_lval_find_error(child)) {
          return child;
        }
      }
      return nullptr;
    }
    case LVAL_CONS: {
      valk_lval_t *err = valk_lval_find_error(ast->cons.head);
      if (err) return err;
      return valk_lval_find_error(ast->cons.tail);
    }
    case LVAL_NIL:
    case LVAL_STR:
    case LVAL_FUN:
    case LVAL_NUM:
    case LVAL_REF:
    case LVAL_SYM:
    case LVAL_ENV:
    case LVAL_UNDEFINED:
      return nullptr;
  }
  return nullptr;
}

valk_lval_t *valk_eval(valk_lenv_t *env, const char *expr) {
  int pos = 0;
  return valk_lval_eval(env, valk_lval_read(&pos, expr));
}
