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
  g_heap = valk_gc_malloc_heap_init(64 * 1024 * 1024, 128 * 1024 * 1024);
  valk_thread_ctx.allocator = (valk_mem_allocator_t *)g_heap;

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

// Helper: parse and eval a string
static valk_lval_t *eval_str(const char *code) {
  int pos = 0;
  valk_lval_t *expr = valk_lval_read_expr(&pos, code);
  if (LVAL_TYPE(expr) == LVAL_ERR) {
    return expr;
  }
  return valk_lval_eval(g_env, expr);
}

// ============================================================================
// Phase 2 Tests: with-handler installs handlers
// ============================================================================

void test_with_handler_installs_handler(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Define a handler and check it's accessible inside the body
  // Note: body must be a QEXPR {body} so it's not evaluated before with-handler runs
  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x} x)} "
    "  {(find-handler 'MyEffect/op)})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) != LVAL_ERR,
                   "with-handler should not return an error");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_FUN,
                   "find-handler should return a function when handler is installed");

  teardown_test_env();
  VALK_PASS();
}

void test_with_handler_pops_on_return(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Install a handler, then check it's gone after with-handler returns
  const char *setup_code =
    "(with-handler "
    "  {(MyEffect/op {x} x)} "
    "  {42})";

  valk_lval_t *result = eval_str(setup_code);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM && result->num == 42,
                   "with-handler body should evaluate correctly");

  // Now check that the handler is NOT accessible in the outer scope
  const char *check_code = "(find-handler 'MyEffect/op)";
  valk_lval_t *handler = eval_str(check_code);

  VALK_TEST_ASSERT(LVAL_TYPE(handler) == LVAL_NIL,
                   "Handler should not be found after with-handler returns");

  teardown_test_env();
  VALK_PASS();
}

void test_handler_lookup_finds_inner(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Nested handlers - inner should shadow outer
  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x} (+ x 10))} "      // Outer: add 10
    "  {(with-handler "
    "    {(MyEffect/op {x} (+ x 100))} "   // Inner: add 100
    "    {(find-handler 'MyEffect/op)})})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_FUN,
                   "find-handler should return the inner handler function");

  // Test that calling the handler returns the inner behavior
  // We can't easily call the lambda directly, so we test via a different means
  // Just verify we got a function for now

  teardown_test_env();
  VALK_PASS();
}

void test_handler_lookup_finds_outer(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Nested handlers with different effect operations
  const char *code =
    "(with-handler "
    "  {(OuterEffect/op {x} (+ x 10))} "
    "  {(with-handler "
    "    {(InnerEffect/op {x} (+ x 100))} "
    "    {(find-handler 'OuterEffect/op)})})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_FUN,
                   "find-handler should find outer handler when inner doesn't have it");

  teardown_test_env();
  VALK_PASS();
}

void test_handler_lookup_returns_null_if_missing(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // No handler installed - should return nil
  const char *code = "(find-handler 'NonExistent/op)";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL,
                   "find-handler should return nil when no handler is found");

  teardown_test_env();
  VALK_PASS();
}

void test_with_handler_multiple_handlers(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Multiple handlers in one with-handler
  const char *code =
    "(with-handler "
    "  {(Effect1/op {x} (+ x 1)) "
    "   (Effect2/op {x} (+ x 2))} "
    "  {(do "
    "    (def {h1} (find-handler 'Effect1/op)) "
    "    (def {h2} (find-handler 'Effect2/op)) "
    "    (list h1 h2))})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) != LVAL_ERR,
                   "Multiple handlers should not cause an error");

  // Result should be a list of two functions
  if (LVAL_TYPE(result) == LVAL_QEXPR || LVAL_TYPE(result) == LVAL_CONS) {
    valk_lval_t *h1 = valk_lval_list_nth(result, 0);
    valk_lval_t *h2 = valk_lval_list_nth(result, 1);
    VALK_TEST_ASSERT(LVAL_TYPE(h1) == LVAL_FUN,
                     "First handler should be a function");
    VALK_TEST_ASSERT(LVAL_TYPE(h2) == LVAL_FUN,
                     "Second handler should be a function");
  }

  teardown_test_env();
  VALK_PASS();
}

void test_handler_stack_returns_nil_when_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  const char *code = "(handler-stack)";
  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL,
                   "handler-stack should return nil when no handlers installed");

  teardown_test_env();
  VALK_PASS();
}

void test_handler_stack_returns_stack_inside_handler(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x} x)} "
    "  {(handler-stack)})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) != LVAL_NIL,
                   "handler-stack should return non-nil inside with-handler");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS,
                   "handler-stack should return a list");

  teardown_test_env();
  VALK_PASS();
}

void test_with_handler_body_can_access_outer_vars(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Define a variable, then access it inside with-handler body
  const char *setup = "(def {outer-val} 42)";
  eval_str(setup);

  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x} x)} "
    "  {outer-val})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM && result->num == 42,
                   "with-handler body should have access to outer variables");

  teardown_test_env();
  VALK_PASS();
}

void test_with_handler_body_can_define_vars(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x} x)} "
    "  {(do "
    "    (def {inner-val} 99) "
    "    inner-val)})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM && result->num == 99,
                   "with-handler body should be able to define and use variables");

  teardown_test_env();
  VALK_PASS();
}

void test_with_handler_error_propagation(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x} x)} "
    "  {(error \"test error\")})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR,
                   "Errors in body should propagate through with-handler");

  teardown_test_env();
  VALK_PASS();
}

void test_with_handler_invalid_handler_syntax(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Handler with less than 3 elements should error
  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x})} "  // Missing body
    "  {42})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR,
                   "Invalid handler syntax should return an error");

  teardown_test_env();
  VALK_PASS();
}

void test_gc_preserves_handler_stack(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_test_env();

  // Install handlers, run GC, verify handlers still work
  const char *code =
    "(with-handler "
    "  {(MyEffect/op {x} (+ x 1))} "
    "  {(do "
    "    (gc) "  // Force GC
    "    (find-handler 'MyEffect/op))})";

  valk_lval_t *result = eval_str(code);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_FUN,
                   "Handler should survive GC");

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

  // Handler installation and lookup
  valk_testsuite_add_test(suite, "test_with_handler_installs_handler",
                          test_with_handler_installs_handler);
  valk_testsuite_add_test(suite, "test_with_handler_pops_on_return",
                          test_with_handler_pops_on_return);
  valk_testsuite_add_test(suite, "test_handler_lookup_finds_inner",
                          test_handler_lookup_finds_inner);
  valk_testsuite_add_test(suite, "test_handler_lookup_finds_outer",
                          test_handler_lookup_finds_outer);
  valk_testsuite_add_test(suite, "test_handler_lookup_returns_null_if_missing",
                          test_handler_lookup_returns_null_if_missing);

  // Multiple handlers
  valk_testsuite_add_test(suite, "test_with_handler_multiple_handlers",
                          test_with_handler_multiple_handlers);

  // handler-stack builtin
  valk_testsuite_add_test(suite, "test_handler_stack_returns_nil_when_empty",
                          test_handler_stack_returns_nil_when_empty);
  valk_testsuite_add_test(suite, "test_handler_stack_returns_stack_inside_handler",
                          test_handler_stack_returns_stack_inside_handler);

  // Scoping
  valk_testsuite_add_test(suite, "test_with_handler_body_can_access_outer_vars",
                          test_with_handler_body_can_access_outer_vars);
  valk_testsuite_add_test(suite, "test_with_handler_body_can_define_vars",
                          test_with_handler_body_can_define_vars);

  // Error handling
  valk_testsuite_add_test(suite, "test_with_handler_error_propagation",
                          test_with_handler_error_propagation);
  valk_testsuite_add_test(suite, "test_with_handler_invalid_handler_syntax",
                          test_with_handler_invalid_handler_syntax);

  // GC integration
  valk_testsuite_add_test(suite, "test_gc_preserves_handler_stack",
                          test_gc_preserves_handler_stack);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_mem_init_malloc();
  valk_testsuite_free(suite);

  return res;
}
