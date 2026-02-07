#include "test_std.h"

#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

void test_bug_string_equality_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "(== \"hello\" \"hello\")");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1,
              "BUG: Identical strings should be equal (==). "
              "Expected 1, got %ld. "
              "Root cause: parser.c:313 returns strcmp() directly instead of "
              "!strcmp() or (strcmp() == 0)",
              res->num);

  VALK_PASS();
}

void test_bug_string_equality_different(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "(== \"hello\" \"world\")");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 0,
              "BUG: Different strings should NOT be equal. "
              "Expected 0, got %ld. "
              "Root cause: parser.c:313 inverted strcmp logic",
              res->num);

  VALK_PASS();
}

void test_bug_string_inequality(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "(!= \"same\" \"same\")");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 0,
              "BUG: Identical strings with != should return 0. "
              "Expected 0, got %ld",
              res->num);

  VALK_PASS();
}

void test_bug_env_copy_with_many_bindings(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (= {a} 1) "
      "  (= {b} 2) "
      "  (= {c} 3) "
      "  (= {d} 4) "
      "  (= {e} 5) "
      "  (= {f} 6) "
      "  (= {g} 7) "
      "  (= {h} 8) "
      "  ((\\ {x} {+ x a b c d e f g h}) 100)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 136,
              "BUG: Lambda with many env bindings returns wrong result. "
              "Expected 136, got %ld. "
              "Root cause: parser.c:815,820-821 wrong sizeof in env copy",
              res->num);

  VALK_PASS();
}

void test_bug_nested_lambda_env_copy(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {add-n} (\\ {n x} {+ x n})) "
      "  (def {add5} (add-n 5)) "
      "  (def {add10} (add-n 10)) "
      "  (+ (add5 100) (add10 100))"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 215,
              "BUG: Curried function returns wrong result. "
              "Expected 215, got %ld. "
              "Root cause: Environment copy corrupts partial application",
              res->num);

  VALK_PASS();
}

void test_bug_lambda_parent_mutation_reuse(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {base-val} 100) "
      "  (def {my-fn} (\\ {x} {+ x base-val})) "
      "  (def {r1} (my-fn 1)) "
      "  (def {r2} (my-fn 2)) "
      "  (+ r1 r2)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 203,
              "BUG: Lambda with dynamic scoping returns wrong result. "
              "Expected 203, got %ld. "
              "Root cause: Environment not properly copied between calls",
              res->num);

  VALK_PASS();
}

void test_bug_lambda_multiple_calls_different_contexts(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {counter} (\\ {n} {+ n 1})) "
      "  (def {result1} (counter 10)) "
      "  (def {result2} (counter 20)) "
      "  (def {result3} (counter 30)) "
      "  (+ result1 result2 result3)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 63,
              "BUG: Multiple lambda calls return inconsistent results. "
              "Expected 63, got %ld",
              res->num);

  VALK_PASS();
}

void test_bug_cons_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "(list 1 2 3 4)");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR, LVAL_CONS, LVAL_NIL);
  size_t count = valk_lval_list_count(res);
  VALK_TEST_ASSERT(count == 4,
              "BUG: list should create list of 4 elements. "
              "Expected 4, got %zu",
              count);

  VALK_PASS();
}

void test_bug_cons_chained(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(cons 1 (cons 2 (cons 3 (cons 4 {}))))");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR, LVAL_CONS);
  size_t count = valk_lval_list_count(res);
  VALK_TEST_ASSERT(count == 4,
              "BUG: Chained cons should create list of 4 elements. "
              "Expected 4, got %zu. "
              "Root cause: parser.c:939-942 wrong sizeof in realloc/memmove",
              count);

  VALK_PASS();
}

void test_bug_cons_equality_check(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(== (list 1 2 3) {1 2 3})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1,
              "BUG: list result should equal literal list. "
              "Expected 1 (true), got %ld",
              res->num);

  VALK_PASS();
}

void test_bug_lval_copy_large_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {big-list} {1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16}) "
      "  (head big-list)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1,
              "BUG: head of list should return 1. "
              "Expected 1, got %ld.",
              res->num);

  VALK_PASS();
}

void test_bug_map_creates_many_copies(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(== (map (\\ {x} {* x 2}) {1 2 3 4 5 6 7 8}) "
      "    {2 4 6 8 10 12 14 16})");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1,
              "BUG: map result should equal expected list. "
              "Expected 1 (true), got %ld. "
              "Root cause: Memory corruption in copy operations",
              res->num);

  VALK_PASS();
}

void test_bug_many_sequential_bindings(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (= {v1} 1) (= {v2} 2) (= {v3} 3) (= {v4} 4) "
      "  (= {v5} 5) (= {v6} 6) (= {v7} 7) (= {v8} 8) "
      "  (= {v9} 9) (= {v10} 10) (= {v11} 11) (= {v12} 12) "
      "  (+ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 78,
              "BUG: Sum of many bindings is wrong. "
              "Expected 78, got %ld. "
              "Root cause: parser.c:861-862 wrong sizeof in realloc",
              res->num);

  VALK_PASS();
}

void test_stress_multi_client_scenario(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {on-timer} (\\ {tick} {+ tick 1})) "
      "  (def {client1-result} (on-timer 100)) "
      "  (def {client2-result} (on-timer 200)) "
      "  (def {client3-result} (on-timer 300)) "
      "  (if (== client1-result 101) "
      "      {if (== client2-result 201) "
      "          {if (== client3-result 301) "
      "              {1} "
      "              {0}} "
      "          {0}} "
      "      {0})"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 1,
              "BUG: Multi-client timer simulation failed. "
              "This indicates the lambda parent mutation bug (parser.c:452) "
              "is causing SSE events to fail in multi-tab scenarios. "
              "Expected 1, got %ld",
              res->num);

  VALK_PASS();
}

void test_stress_recursive_with_closures(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {fib} (\\ {n} "
      "    {if (<= n 1) "
      "        {n} "
      "        {+ (fib (- n 1)) (fib (- n 2))}}))"
      "  (fib 10)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_TEST_ASSERT(res->num == 55,
              "BUG: Recursive fibonacci returns wrong result. "
              "Expected 55, got %ld. "
              "Root cause: Memory corruption in recursive lambda calls",
              res->num);

  VALK_PASS();
}

static void *__lval_retain(void *lval) { return (valk_lval_t *)lval; }
static void __lval_release(void *lval) { UNUSED(lval); }

static void *__lenv_retain(void *lenv) { return (valk_lenv_t *)lenv; }
static void __lenv_release(void *lenv) { UNUSED(lenv); }

valk_lval_t *valk_lval_find_error(valk_lval_t *ast) {
  switch (LVAL_TYPE(ast)) {
    case LVAL_ERR:
      return ast;
    case LVAL_CONS: {
      if(valk_lval_list_is_empty(ast)) return nullptr;
      valk_lval_t *err = valk_lval_find_error(ast->cons.head);
      if (err) return err;
      if (ast->cons.tail == nullptr) return nullptr;
      return valk_lval_find_error(ast->cons.tail);
    }
    case LVAL_NIL:
    case LVAL_STR:
    case LVAL_FUN:
    case LVAL_NUM:
    case LVAL_REF:
    case LVAL_SYM:
    case LVAL_UNDEFINED:
    case LVAL_HANDLE:
      return nullptr;
  }
  return nullptr;
}

valk_lval_t *valk_eval(valk_lenv_t *env, const char *expr) {
  int pos = 0;
  return valk_lval_eval(env, valk_lval_read(&pos, expr));
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_gc_malloc_heap_t *gc_heap = valk_gc_malloc_heap_init(0);
  valk_thread_ctx.allocator = (void *)gc_heap;
  valk_thread_ctx.heap = gc_heap;
  valk_gc_thread_register();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_bug_string_equality_basic",
                          test_bug_string_equality_basic);
  valk_testsuite_add_test(suite, "test_bug_string_equality_different",
                          test_bug_string_equality_different);
  valk_testsuite_add_test(suite, "test_bug_string_inequality",
                          test_bug_string_inequality);

  valk_testsuite_add_test(suite, "test_bug_env_copy_with_many_bindings",
                          test_bug_env_copy_with_many_bindings);
  valk_testsuite_add_test(suite, "test_bug_nested_lambda_env_copy",
                          test_bug_nested_lambda_env_copy);

  valk_testsuite_add_test(suite, "test_bug_lambda_parent_mutation_reuse",
                          test_bug_lambda_parent_mutation_reuse);
  valk_testsuite_add_test(suite, "test_bug_lambda_multiple_calls_different_contexts",
                          test_bug_lambda_multiple_calls_different_contexts);

  valk_testsuite_add_test(suite, "test_bug_cons_basic", test_bug_cons_basic);
  valk_testsuite_add_test(suite, "test_bug_cons_chained", test_bug_cons_chained);
  valk_testsuite_add_test(suite, "test_bug_cons_equality_check",
                          test_bug_cons_equality_check);

  valk_testsuite_add_test(suite, "test_bug_lval_copy_large_list",
                          test_bug_lval_copy_large_list);
  valk_testsuite_add_test(suite, "test_bug_map_creates_many_copies",
                          test_bug_map_creates_many_copies);

  valk_testsuite_add_test(suite, "test_bug_many_sequential_bindings",
                          test_bug_many_sequential_bindings);

  valk_testsuite_add_test(suite, "test_stress_multi_client_scenario",
                          test_stress_multi_client_scenario);
  valk_testsuite_add_test(suite, "test_stress_recursive_with_closures",
                          test_stress_recursive_with_closures);

  valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  size_t expr_count = 0;
  while (valk_lval_list_count(ast)) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(ast, 0));
    expr_count++;
    if (LVAL_TYPE(x) == LVAL_ERR) {
      fprintf(stderr, "Prelude failed at expression %zu: ", expr_count);
      valk_lval_println(x);
      break;
    }
  }
  fprintf(stderr, "Prelude loaded %zu expressions successfully\n", expr_count);

  valk_testsuite_fixture_add(suite, "prelude", ast, __lval_retain,
                             __lval_release);
  valk_testsuite_fixture_add(suite, "env", env, __lenv_retain, __lenv_release);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_testsuite_free(suite);

  valk_gc_malloc_set_root(gc_heap, nullptr);
  valk_gc_malloc_collect(gc_heap, nullptr);
  valk_gc_thread_unregister();
  valk_gc_malloc_heap_destroy(gc_heap);

  return res;
}
