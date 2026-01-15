/**
 * Regression Tests for Timer/SSE Multi-Client Bugs
 *
 * These tests expose critical bugs in the Valkyria interpreter that cause
 * issues when multiple clients (e.g., debug dashboard tabs) interact with
 * the system concurrently. The bugs relate to:
 *
 * 1. String equality comparison (inverted logic)
 * 2. Memory corruption in environment copying
 * 3. Lambda parent environment mutation (race condition)
 * 4. Memory corruption in cons operation
 * 5. Memory corruption in lval copy for expressions
 */

#include "test_std.h"
#include "parser.h"
#include <string.h>

// ============================================================================
// BUG #1: Inverted String Equality (parser.c:313)
// ============================================================================
// The valk_lval_eq function returns strcmp() result directly for strings.
// strcmp() returns 0 when strings ARE equal, but valk_lval_eq should return
// non-zero (true) when equal. This breaks all string/symbol comparisons.
// ============================================================================

void test_bug_string_equality_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Test: Two identical strings should be equal (== returns 1)
  valk_lval_t *res = valk_eval(env, "(== \"hello\" \"hello\")");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 1,
              "BUG: Identical strings should be equal (==). "
              "Expected 1, got %ld. "
              "Root cause: parser.c:313 returns strcmp() directly instead of "
              "!strcmp() or (strcmp() == 0)",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_bug_string_equality_different(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Test: Two different strings should NOT be equal (== returns 0)
  valk_lval_t *res = valk_eval(env, "(== \"hello\" \"world\")");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 0,
              "BUG: Different strings should NOT be equal. "
              "Expected 0, got %ld. "
              "Root cause: parser.c:313 inverted strcmp logic",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_bug_string_inequality(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Test: != on identical strings should return 0 (they ARE equal)
  valk_lval_t *res = valk_eval(env, "(!= \"same\" \"same\")");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 0,
              "BUG: Identical strings with != should return 0. "
              "Expected 0, got %ld",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

// ============================================================================
// BUG #2: Environment Copy Memory Corruption (parser.c:815, 820-821)
// ============================================================================
// valk_lenv_copy() has THREE bugs:
//   - Line 815: malloc(sizeof(valk_lval_t)) instead of sizeof(valk_lenv_t)
//   - Line 820: sizeof(env->symbols) returns pointer size, not element size
//   - Line 821: sizeof(env->vals) returns pointer size, not element size
// This causes heap corruption when environments are copied (e.g., for lambdas)
// ============================================================================

void test_bug_env_copy_with_many_bindings(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Create an environment with multiple bindings to stress the copy
  // The memory corruption is more likely to manifest with more bindings
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
  // 100 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 = 136
  VALK_ASSERT(res->num == 136,
              "BUG: Lambda with many env bindings returns wrong result. "
              "Expected 136, got %ld. "
              "Root cause: parser.c:815,820-821 wrong sizeof in env copy",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_bug_nested_lambda_env_copy(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // This language uses dynamic scoping, not lexical closures.
  // Nested lambdas work when the binding is in global scope.
  // This test verifies currying works with global definitions.
  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {add-n} (\\ {n x} {+ x n})) "
      "  (def {add5} (add-n 5)) "
      "  (def {add10} (add-n 10)) "
      "  (+ (add5 100) (add10 100))"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  // (100 + 5) + (100 + 10) = 215
  VALK_ASSERT(res->num == 215,
              "BUG: Curried function returns wrong result. "
              "Expected 215, got %ld. "
              "Root cause: Environment copy corrupts partial application",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

// ============================================================================
// BUG #3: Lambda Parent Mutation - Multi-Client Race Condition (parser.c:452)
// ============================================================================
// In valk_lval_eval_call(), line 452 does:
//   func->fun.env->parent = env;
// This MUTATES the lambda's captured environment's parent pointer directly.
// When multiple clients/contexts evaluate the same lambda, they overwrite
// each other's parent context, causing:
//   - Race conditions in concurrent scenarios (timers, SSE events)
//   - Wrong values returned when lambda is reused
//   - Potential use-after-free if parent env is freed
// ============================================================================

void test_bug_lambda_parent_mutation_reuse(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // This language uses dynamic scoping: lambdas see the calling scope.
  // This test verifies that the lambda correctly accesses global bindings
  // and that multiple calls don't corrupt state.

  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {base-val} 100) "
      "  (def {my-fn} (\\ {x} {+ x base-val})) "
      "  (def {r1} (my-fn 1)) "   // 1 + 100 = 101
      "  (def {r2} (my-fn 2)) "   // 2 + 100 = 102
      "  (+ r1 r2)"               // 101 + 102 = 203
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 203,
              "BUG: Lambda with dynamic scoping returns wrong result. "
              "Expected 203, got %ld. "
              "Root cause: Environment not properly copied between calls",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_bug_lambda_multiple_calls_different_contexts(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Simulate timer/SSE scenario: same lambda called multiple times
  // from contexts that might have different local bindings
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
  // 11 + 21 + 31 = 63
  VALK_ASSERT(res->num == 63,
              "BUG: Multiple lambda calls return inconsistent results. "
              "Expected 63, got %ld",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

// ============================================================================
// BUG #4: Cons Operation Memory Corruption (parser.c:939-942)
// ============================================================================
// valk_builtin_cons() uses:
//   sizeof(tail->expr.cell) instead of sizeof(valk_lval_t *)
// This allocates wrong size and corrupts memory on cons operations.
// ============================================================================

void test_bug_cons_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  valk_lval_t *res = valk_eval(env, "(cons 1 {2 3 4})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR);
  VALK_ASSERT(res->expr.count == 4,
              "BUG: cons should create list of 4 elements. "
              "Expected 4, got %zu",
              res->expr.count);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_bug_cons_chained(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Chained cons operations stress the memory allocation bug
  valk_lval_t *res = valk_eval(env,
      "(cons 1 (cons 2 (cons 3 (cons 4 {}))))");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR);
  VALK_ASSERT(res->expr.count == 4,
              "BUG: Chained cons should create list of 4 elements. "
              "Expected 4, got %zu. "
              "Root cause: parser.c:939-942 wrong sizeof in realloc/memmove",
              res->expr.count);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_bug_cons_equality_check(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Test that cons'd list equals expected list
  // This combines the cons bug and equality bug
  valk_lval_t *res = valk_eval(env,
      "(== (cons 1 {2 3}) {1 2 3})");
  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 1,
              "BUG: cons'd list should equal literal list. "
              "Expected 1 (true), got %ld",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

// ============================================================================
// BUG #5: lval_copy Expression Cell Corruption (parser.c:248)
// ============================================================================
// valk_lval_copy() for QEXPR/SEXPR uses:
//   sizeof(res->expr.cell) instead of sizeof(valk_lval_t *)
// This causes buffer overflow when copying expressions.
// ============================================================================

void test_bug_lval_copy_large_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Create and copy a large list to trigger memory corruption
  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (def {big-list} {1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16}) "
      "  (head big-list)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_QEXPR);
  VALK_ASSERT(res->expr.count == 1,
              "BUG: head of list should have 1 element. "
              "Expected 1, got %zu. "
              "Root cause: parser.c:248 wrong sizeof in expr.cell allocation",
              res->expr.count);

  VALK_ASSERT(res->expr.cell[0]->num == 1,
              "BUG: head element should be 1. "
              "Expected 1, got %ld",
              res->expr.cell[0]->num);

  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_bug_map_creates_many_copies(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // map creates copies of the lambda and list elements
  // This stresses the copy functions
  valk_lval_t *res = valk_eval(env,
      "(== (map (\\ {x} {* x 2}) {1 2 3 4 5 6 7 8}) "
      "    {2 4 6 8 10 12 14 16})");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 1,
              "BUG: map result should equal expected list. "
              "Expected 1 (true), got %ld. "
              "Root cause: Memory corruption in copy operations",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

// ============================================================================
// BUG #6: Environment Put Memory Corruption (parser.c:861-862)
// ============================================================================
// valk_lenv_put() uses:
//   sizeof(env->symbols) and sizeof(env->vals) instead of pointer element sizes
// This causes buffer overflow when adding new bindings.
// ============================================================================

void test_bug_many_sequential_bindings(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Add many bindings to trigger multiple reallocs
  valk_lval_t *res = valk_eval(env,
      "(do "
      "  (= {v1} 1) (= {v2} 2) (= {v3} 3) (= {v4} 4) "
      "  (= {v5} 5) (= {v6} 6) (= {v7} 7) (= {v8} 8) "
      "  (= {v9} 9) (= {v10} 10) (= {v11} 11) (= {v12} 12) "
      "  (+ v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12)"
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  // 1+2+3+4+5+6+7+8+9+10+11+12 = 78
  VALK_ASSERT(res->num == 78,
              "BUG: Sum of many bindings is wrong. "
              "Expected 78, got %ld. "
              "Root cause: parser.c:861-862 wrong sizeof in realloc",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

// ============================================================================
// COMBINED STRESS TEST - Simulates Multi-Tab Debug Dashboard
// ============================================================================

void test_stress_multi_client_scenario(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // This test simulates what happens when multiple debug dashboard tabs
  // trigger SSE events and timers that evaluate shared lambdas
  valk_lval_t *res = valk_eval(env,
      "(do "
      // Define a "timer callback" that would be triggered by SSE
      "  (def {on-timer} (\\ {tick} {+ tick 1})) "
      // Simulate multiple "clients" calling the same callback
      "  (def {client1-result} (on-timer 100)) "
      "  (def {client2-result} (on-timer 200)) "
      "  (def {client3-result} (on-timer 300)) "
      // Verify all clients got correct results
      "  (if (== client1-result 101) "
      "      {if (== client2-result 201) "
      "          {if (== client3-result 301) "
      "              {1} "   // All correct
      "              {0}} "  // client3 wrong
      "          {0}} "      // client2 wrong
      "      {0})"           // client1 wrong
      ")");

  VALK_EXPECT_SUCCESS(res);
  VALK_ASSERT_TYPE(res, LVAL_NUM);
  VALK_ASSERT(res->num == 1,
              "BUG: Multi-client timer simulation failed. "
              "This indicates the lambda parent mutation bug (parser.c:452) "
              "is causing SSE events to fail in multi-tab scenarios. "
              "Expected 1, got %ld",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

void test_stress_recursive_with_closures(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Recursive functions with closures stress all the memory bugs
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
  // fib(10) = 55
  VALK_ASSERT(res->num == 55,
              "BUG: Recursive fibonacci returns wrong result. "
              "Expected 55, got %ld. "
              "Root cause: Memory corruption in recursive lambda calls",
              res->num);
  valk_lval_free(res);

  VALK_PASS();
  valk_lenv_free(env);
}

// ============================================================================
// Test Runner
// ============================================================================

static void valk_lval_free_void(void *lval) { valk_lval_free(lval); }
static void *valk_lval_copy_void(void *lval) { return valk_lval_copy(lval); }
static void valk_lenv_free_void(void *lenv) { valk_lenv_free(lenv); }
static void *valk_lenv_copy_void(void *lenv) { return valk_lenv_copy(lenv); }

int main(int argc, const char **argv) {
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // Bug #1: String equality
  valk_testsuite_add_test(suite, "test_bug_string_equality_basic",
                          test_bug_string_equality_basic);
  valk_testsuite_add_test(suite, "test_bug_string_equality_different",
                          test_bug_string_equality_different);
  valk_testsuite_add_test(suite, "test_bug_string_inequality",
                          test_bug_string_inequality);

  // Bug #2: Environment copy
  valk_testsuite_add_test(suite, "test_bug_env_copy_with_many_bindings",
                          test_bug_env_copy_with_many_bindings);
  valk_testsuite_add_test(suite, "test_bug_nested_lambda_env_copy",
                          test_bug_nested_lambda_env_copy);

  // Bug #3: Lambda parent mutation
  valk_testsuite_add_test(suite, "test_bug_lambda_parent_mutation_reuse",
                          test_bug_lambda_parent_mutation_reuse);
  valk_testsuite_add_test(suite, "test_bug_lambda_multiple_calls_different_contexts",
                          test_bug_lambda_multiple_calls_different_contexts);

  // Bug #4: Cons operation
  valk_testsuite_add_test(suite, "test_bug_cons_basic", test_bug_cons_basic);
  valk_testsuite_add_test(suite, "test_bug_cons_chained", test_bug_cons_chained);
  valk_testsuite_add_test(suite, "test_bug_cons_equality_check",
                          test_bug_cons_equality_check);

  // Bug #5: lval_copy corruption
  valk_testsuite_add_test(suite, "test_bug_lval_copy_large_list",
                          test_bug_lval_copy_large_list);
  valk_testsuite_add_test(suite, "test_bug_map_creates_many_copies",
                          test_bug_map_creates_many_copies);

  // Bug #6: Environment put corruption
  valk_testsuite_add_test(suite, "test_bug_many_sequential_bindings",
                          test_bug_many_sequential_bindings);

  // Combined stress tests (multi-client/SSE simulation)
  valk_testsuite_add_test(suite, "test_stress_multi_client_scenario",
                          test_stress_multi_client_scenario);
  valk_testsuite_add_test(suite, "test_stress_recursive_with_closures",
                          test_stress_recursive_with_closures);

  // Load fixtures
  valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
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

valk_lval_t *valk_lval_find_error(valk_lval_t *ast) {
  switch (ast->type) {
  case LVAL_ERR:
    return ast;
  case LVAL_QEXPR:
  case LVAL_SEXPR: {
    for (int i = 0; i < ast->expr.count; i++) {
      if (valk_lval_find_error(ast->expr.cell[i])) {
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

valk_lval_t *valk_eval(valk_lenv_t *env, const char *expr) {
  int pos = 0;
  return valk_lval_eval(env, valk_lval_read(&pos, expr));
}
