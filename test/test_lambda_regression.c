/**
 * Regression tests for lambda functionality
 * Tests basic lambda features to prevent bytecode compilation bugs
 */

#include "../src/parser.h"
#include "../src/compiler.h"
#include "../src/bc_vm.h"
#include "../src/memory.h"
#include "testing.h"

// Test: Identity function - parameter passthrough
static void test_lambda_identity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // (def {id} (\ {x} {x}))
  // (id 42)
  const char* code = "(do (def {id} (\\ {x} {x})) (id 42))";
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, code);
  valk_lval_t* result = valk_lval_eval(env, expr);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 42, "Identity function should return input");
  VALK_PASS();
}

// Test: Lambda with arithmetic - local variable in expression
static void test_lambda_arithmetic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // (def {add5} (\ {x} {+ x 5}))
  // (add5 10)
  const char* code = "(do (def {add5} (\\ {x} {+ x 5})) (add5 10))";
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, code);
  valk_lval_t* result = valk_lval_eval(env, expr);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 15, "Should compute x + 5 = 10 + 5 = 15");
  VALK_PASS();
}

// Test: Multi-parameter lambda
static void test_lambda_multiple_params(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // (def {mul} (\ {x y} {* x y}))
  // (mul 6 7)
  const char* code = "(do (def {mul} (\\ {x y} {* x y})) (mul 6 7))";
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, code);
  valk_lval_t* result = valk_lval_eval(env, expr);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 42, "Should compute 6 * 7 = 42");
  VALK_PASS();
}

// Test: Lambda with nested expression
static void test_lambda_nested_expr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // (def {f} (\ {x} {+ (* x 2) 1}))
  // (f 5) should be 11
  const char* code = "(do (def {f} (\\ {x} {+ (* x 2) 1})) (f 5))";
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, code);
  valk_lval_t* result = valk_lval_eval(env, expr);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 11, "Should compute (5 * 2) + 1 = 11");
  VALK_PASS();
}

// Test: Lambda returning another lambda (closure)
static void test_lambda_closure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // (def {make-adder} (\ {n} {\ {x} {+ x n}}))
  // (def {add3} (make-adder 3))
  // (add3 10) should be 13
  const char* code = "(do (def {make-adder} (\\ {n} {\\ {x} {+ x n}})) (def {add3} (make-adder 3)) (add3 10))";
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, code);
  valk_lval_t* result = valk_lval_eval(env, expr);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 13, "Closure should capture n=3 and add to x=10");
  VALK_PASS();
}

// Test: Recursive lambda (factorial)
static void test_lambda_recursion(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // (def {fact} (\ {n} {if (<= n 1) {1} {* n (fact (- n 1))}}))
  // (fact 5) should be 120
  const char* code = "(do (def {fact} (\\ {n} {if (<= n 1) {1} {* n (fact (- n 1))}})) (fact 5))";
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, code);
  valk_lval_t* result = valk_lval_eval(env, expr);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 120, "5! = 120");
  VALK_PASS();
}

int main() {
  valk_mem_init_malloc();
  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_lambda_identity", test_lambda_identity);
  valk_testsuite_add_test(suite, "test_lambda_arithmetic", test_lambda_arithmetic);
  valk_testsuite_add_test(suite, "test_lambda_multiple_params", test_lambda_multiple_params);
  valk_testsuite_add_test(suite, "test_lambda_nested_expr", test_lambda_nested_expr);
  valk_testsuite_add_test(suite, "test_lambda_closure", test_lambda_closure);
  valk_testsuite_add_test(suite, "test_lambda_recursion", test_lambda_recursion);

  valk_testsuite_run(suite);
  valk_testsuite_free(suite);

  return 0;
}
