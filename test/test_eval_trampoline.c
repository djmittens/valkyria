#include "common.h"
#include "eval_trampoline.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

#include <string.h>

// ============================================================================
// Test Fixtures
// ============================================================================

static valk_gc_malloc_heap_t *g_heap = NULL;
static valk_lenv_t *g_env = NULL;

static void setup_test_env(void) {
  // Initialize GC heap
  g_heap = valk_gc_malloc_heap_init(64 * 1024 * 1024, 128 * 1024 * 1024);
  valk_thread_ctx.allocator = (valk_mem_allocator_t *)g_heap;

  // Create environment with builtins
  g_env = valk_lenv_empty();
  valk_lenv_builtins(g_env);
  valk_gc_malloc_set_root(g_heap, g_env);
}

static void teardown_test_env(void) {
  if (g_heap) {
    valk_gc_malloc_heap_destroy(g_heap);
    g_heap = NULL;
  }
  g_env = NULL;
  valk_thread_ctx.allocator = NULL;
}

// Helper: Parse and evaluate an expression using trampoline
static valk_lval_t *eval_expr(const char *code) {
  int pos = 0;
  valk_lval_t *ast = valk_lval_read(&pos, code);
  if (LVAL_TYPE(ast) == LVAL_ERR) {
    return ast;
  }
  return valk_eval_trampoline(g_env, ast);
}

// Helper: Compare result with expected value
static bool result_is_num(valk_lval_t *result, long expected) {
  return result != NULL && LVAL_TYPE(result) == LVAL_NUM &&
         result->num == expected;
}

static bool result_is_str(valk_lval_t *result, const char *expected) {
  return result != NULL && LVAL_TYPE(result) == LVAL_STR &&
         strcmp(result->str, expected) == 0;
}

static bool result_is_nil(valk_lval_t *result) {
  return result != NULL && LVAL_TYPE(result) == LVAL_NIL;
}

static bool result_is_err(valk_lval_t *result) {
  return result != NULL && LVAL_TYPE(result) == LVAL_ERR;
}

// ============================================================================
// Stack Operations Tests
// ============================================================================

void test_stack_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  VALK_TEST_ASSERT(valk_eval_stack_empty(&stack), "Stack should be empty");
  VALK_TEST_ASSERT(valk_eval_stack_top(&stack) == NULL,
                   "Top of empty stack should be NULL");

  valk_eval_stack_free(&stack);
  VALK_PASS();
}

void test_stack_push_pop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  valk_eval_frame_t frame1 = {.type = FRAME_EVAL, .env = NULL};
  valk_eval_frame_t frame2 = {.type = FRAME_IF_COND, .env = NULL};

  valk_eval_stack_push(&stack, frame1);
  VALK_TEST_ASSERT(!valk_eval_stack_empty(&stack), "Stack should not be empty");
  VALK_TEST_ASSERT(valk_eval_stack_top(&stack)->type == FRAME_EVAL,
                   "Top should be FRAME_EVAL");

  valk_eval_stack_push(&stack, frame2);
  VALK_TEST_ASSERT(valk_eval_stack_top(&stack)->type == FRAME_IF_COND,
                   "Top should be FRAME_IF_COND");

  valk_eval_stack_pop(&stack);
  VALK_TEST_ASSERT(valk_eval_stack_top(&stack)->type == FRAME_EVAL,
                   "Top should be FRAME_EVAL after pop");

  valk_eval_stack_pop(&stack);
  VALK_TEST_ASSERT(valk_eval_stack_empty(&stack),
                   "Stack should be empty after pops");

  valk_eval_stack_free(&stack);
  VALK_PASS();
}

void test_stack_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_stack_t stack;
  valk_eval_stack_init(&stack);

  valk_eval_frame_t frame1 = {.type = FRAME_EVAL, .env = NULL};
  valk_eval_frame_t frame2 = {.type = FRAME_IF_COND, .env = NULL};

  valk_eval_stack_push(&stack, frame1);
  valk_eval_stack_push(&stack, frame2);

  valk_eval_stack_t *copy = valk_eval_stack_copy(&stack);
  VALK_TEST_ASSERT(copy != NULL, "Copy should not be NULL");
  VALK_TEST_ASSERT(copy->count == 2, "Copy should have 2 frames");
  VALK_TEST_ASSERT(copy->frames[0].type == FRAME_EVAL,
                   "First frame should be FRAME_EVAL");
  VALK_TEST_ASSERT(copy->frames[1].type == FRAME_IF_COND,
                   "Second frame should be FRAME_IF_COND");

  // Modify original, copy should be unchanged
  valk_eval_stack_pop(&stack);
  VALK_TEST_ASSERT(copy->count == 2, "Copy should still have 2 frames");

  valk_eval_stack_free(&stack);
  valk_eval_stack_free(copy);
  free(copy);
  VALK_PASS();
}

// ============================================================================
// Self-Evaluating Forms Tests
// ============================================================================

void test_trampoline_self_eval_num(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("42");
  VALK_TEST_ASSERT(result_is_num(result, 42), "42 should evaluate to 42");

  result = eval_expr("-17");
  VALK_TEST_ASSERT(result_is_num(result, -17), "-17 should evaluate to -17");

  result = eval_expr("0");
  VALK_TEST_ASSERT(result_is_num(result, 0), "0 should evaluate to 0");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_self_eval_str(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("\"hello\"");
  VALK_TEST_ASSERT(result_is_str(result, "hello"),
                   "\"hello\" should evaluate to \"hello\"");

  result = eval_expr("\"\"");
  VALK_TEST_ASSERT(result_is_str(result, ""), "\"\" should evaluate to \"\"");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_self_eval_nil(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("()");
  VALK_TEST_ASSERT(result_is_nil(result), "() should evaluate to nil");

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Builtin Function Tests
// ============================================================================

void test_trampoline_builtin_add(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(+ 1 2)");
  VALK_TEST_ASSERT(result_is_num(result, 3), "(+ 1 2) should evaluate to 3");

  result = eval_expr("(+ 1 2 3 4)");
  VALK_TEST_ASSERT(result_is_num(result, 10),
                   "(+ 1 2 3 4) should evaluate to 10");

  result = eval_expr("(+ 100 -50)");
  VALK_TEST_ASSERT(result_is_num(result, 50),
                   "(+ 100 -50) should evaluate to 50");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_builtin_subtract(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(- 10 3)");
  VALK_TEST_ASSERT(result_is_num(result, 7), "(- 10 3) should evaluate to 7");

  result = eval_expr("(- 5)");
  VALK_TEST_ASSERT(result_is_num(result, -5), "(- 5) should evaluate to -5");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_builtin_multiply(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(* 3 4)");
  VALK_TEST_ASSERT(result_is_num(result, 12), "(* 3 4) should evaluate to 12");

  result = eval_expr("(* 2 3 4)");
  VALK_TEST_ASSERT(result_is_num(result, 24),
                   "(* 2 3 4) should evaluate to 24");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_builtin_divide(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(/ 10 2)");
  VALK_TEST_ASSERT(result_is_num(result, 5), "(/ 10 2) should evaluate to 5");

  result = eval_expr("(/ 100 4 5)");
  VALK_TEST_ASSERT(result_is_num(result, 5),
                   "(/ 100 4 5) should evaluate to 5");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_nested_arithmetic(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(+ (* 2 3) (- 10 4))");
  VALK_TEST_ASSERT(result_is_num(result, 12),
                   "(+ (* 2 3) (- 10 4)) should evaluate to 12");

  result = eval_expr("(* (+ 1 2) (+ 3 4))");
  VALK_TEST_ASSERT(result_is_num(result, 21),
                   "(* (+ 1 2) (+ 3 4)) should evaluate to 21");

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Special Forms Tests
// ============================================================================

void test_trampoline_quote(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(quote foo)");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_SYM &&
                       strcmp(result->str, "foo") == 0,
                   "(quote foo) should return the symbol foo");

  result = eval_expr("(quote (1 2 3))");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS,
                   "(quote (1 2 3)) should return a list");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_if_true(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(if 1 10 20)");
  VALK_TEST_ASSERT(result_is_num(result, 10),
                   "(if 1 10 20) should evaluate to 10");

  result = eval_expr("(if 42 {100} {200})");
  VALK_TEST_ASSERT(result_is_num(result, 100),
                   "(if 42 {100} {200}) should evaluate to 100");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_if_false(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(if 0 10 20)");
  VALK_TEST_ASSERT(result_is_num(result, 20),
                   "(if 0 10 20) should evaluate to 20");

  result = eval_expr("(if 0 {100} {200})");
  VALK_TEST_ASSERT(result_is_num(result, 200),
                   "(if 0 {100} {200}) should evaluate to 200");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_do_sequence(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(do 1 2 3)");
  VALK_TEST_ASSERT(result_is_num(result, 3), "(do 1 2 3) should evaluate to 3");

  result = eval_expr("(do (+ 1 1) (+ 2 2) (+ 3 3))");
  VALK_TEST_ASSERT(result_is_num(result, 6),
                   "(do (+ 1 1) (+ 2 2) (+ 3 3)) should evaluate to 6");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_do_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(do)");
  VALK_TEST_ASSERT(result_is_nil(result), "(do) should evaluate to nil");

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Lambda Tests
// ============================================================================

void test_trampoline_lambda_simple(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Define and call a simple lambda
  valk_lval_t *result = eval_expr("((\\ {x} {x}) 42)");
  VALK_TEST_ASSERT(result_is_num(result, 42),
                   "Identity lambda should return 42");

  result = eval_expr("((\\ {x y} {+ x y}) 3 5)");
  VALK_TEST_ASSERT(result_is_num(result, 8),
                   "Add lambda should return 8");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_lambda_nested(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Test currying: outer lambda returns inner lambda
  valk_lval_t *result1 = eval_expr("((\\ {x} {\\ {y} {x}}) 10)");
  VALK_TEST_ASSERT(LVAL_TYPE(result1) == LVAL_FUN,
                   "Curried function should return a function");

  // Call the curried function
  valk_lval_t *result2 = eval_expr("(((\\ {x} {\\ {y} {x}}) 10) 20)");
  VALK_TEST_ASSERT(result_is_num(result2, 10),
                   "Curry returning x should return 10");

  // Test with addition
  valk_lval_t *result3 = eval_expr("(((\\ {x} {\\ {y} {+ x y}}) 10) 20)");
  VALK_TEST_ASSERT(result_is_num(result3, 30),
                   "Nested lambda should return 30");

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Error Handling Tests
// ============================================================================

void test_trampoline_error_unknown_symbol(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("unknown_symbol");
  VALK_TEST_ASSERT(result_is_err(result),
                   "Unknown symbol should produce error");

  teardown_test_env();
  VALK_PASS();
}

void test_trampoline_error_type_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  valk_lval_t *result = eval_expr("(+ 1 \"not a number\")");
  VALK_TEST_ASSERT(result_is_err(result),
                   "Type mismatch in + should produce error");

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Comparison with Recursive Eval
// ============================================================================

void test_trampoline_matches_recursive(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Note: if/do are special forms in trampoline vs builtins in recursive eval
  // So we only test expressions that don't rely on if/do semantics
  const char *expressions[] = {
      "42",
      "(+ 1 2 3)",
      "(* (+ 1 2) (- 10 5))",
      "((\\ {x} {x}) 99)",
      "((\\ {x y} {+ x y}) 3 5)",
  };
  size_t count = sizeof(expressions) / sizeof(expressions[0]);

  for (size_t i = 0; i < count; i++) {
    const char *expr = expressions[i];

    // Evaluate with trampoline
    int pos1 = 0;
    valk_lval_t *ast1 = valk_lval_read(&pos1, expr);
    valk_lval_t *tramp_result = valk_eval_trampoline(g_env, ast1);

    // Evaluate with recursive eval
    int pos2 = 0;
    valk_lval_t *ast2 = valk_lval_read(&pos2, expr);
    valk_lval_t *recur_result = valk_lval_eval(g_env, ast2);

    // Compare results
    VALK_TEST_ASSERT(valk_lval_eq(tramp_result, recur_result),
                     "Expression '%s' should produce same result", expr);
  }

  teardown_test_env();
  VALK_PASS();
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // Stack operations tests
  valk_testsuite_add_test(suite, "test_stack_init", test_stack_init);
  valk_testsuite_add_test(suite, "test_stack_push_pop", test_stack_push_pop);
  valk_testsuite_add_test(suite, "test_stack_copy", test_stack_copy);

  // Self-evaluating forms
  valk_testsuite_add_test(suite, "test_trampoline_self_eval_num",
                          test_trampoline_self_eval_num);
  valk_testsuite_add_test(suite, "test_trampoline_self_eval_str",
                          test_trampoline_self_eval_str);
  valk_testsuite_add_test(suite, "test_trampoline_self_eval_nil",
                          test_trampoline_self_eval_nil);

  // Builtin functions
  valk_testsuite_add_test(suite, "test_trampoline_builtin_add",
                          test_trampoline_builtin_add);
  valk_testsuite_add_test(suite, "test_trampoline_builtin_subtract",
                          test_trampoline_builtin_subtract);
  valk_testsuite_add_test(suite, "test_trampoline_builtin_multiply",
                          test_trampoline_builtin_multiply);
  valk_testsuite_add_test(suite, "test_trampoline_builtin_divide",
                          test_trampoline_builtin_divide);
  valk_testsuite_add_test(suite, "test_trampoline_nested_arithmetic",
                          test_trampoline_nested_arithmetic);

  // Special forms
  valk_testsuite_add_test(suite, "test_trampoline_quote", test_trampoline_quote);
  valk_testsuite_add_test(suite, "test_trampoline_if_true",
                          test_trampoline_if_true);
  valk_testsuite_add_test(suite, "test_trampoline_if_false",
                          test_trampoline_if_false);
  valk_testsuite_add_test(suite, "test_trampoline_do_sequence",
                          test_trampoline_do_sequence);
  valk_testsuite_add_test(suite, "test_trampoline_do_empty",
                          test_trampoline_do_empty);

  // Lambda tests
  valk_testsuite_add_test(suite, "test_trampoline_lambda_simple",
                          test_trampoline_lambda_simple);
  valk_testsuite_add_test(suite, "test_trampoline_lambda_nested",
                          test_trampoline_lambda_nested);

  // Error handling
  valk_testsuite_add_test(suite, "test_trampoline_error_unknown_symbol",
                          test_trampoline_error_unknown_symbol);
  valk_testsuite_add_test(suite, "test_trampoline_error_type_mismatch",
                          test_trampoline_error_type_mismatch);

  // Comparison with recursive eval
  valk_testsuite_add_test(suite, "test_trampoline_matches_recursive",
                          test_trampoline_matches_recursive);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
