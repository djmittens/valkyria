// test/test_eval_metrics.c
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#define _POSIX_C_SOURCE 200809L

#include "testing.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "gc.h"

//-----------------------------------------------------------------------------
// Helper: Set up GC heap for test
//-----------------------------------------------------------------------------
typedef struct {
  valk_gc_heap_t* heap;
  valk_thread_context_t old_ctx;
  valk_lenv_t* env;
} test_gc_ctx_t;

static test_gc_ctx_t test_setup_gc(void) {
  test_gc_ctx_t ctx;
  ctx.heap = valk_gc_heap_create(0);
  ctx.old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)ctx.heap;
  valk_thread_ctx.heap = ctx.heap;
  ctx.env = valk_lenv_empty();
  valk_gc_set_root(ctx.heap, ctx.env);
  return ctx;
}

static void test_teardown_gc(test_gc_ctx_t* ctx) {
  valk_thread_ctx = ctx->old_ctx;
  valk_gc_heap_destroy(ctx->heap);
}

//-----------------------------------------------------------------------------
// Test: Metrics Initialization
//-----------------------------------------------------------------------------

void test_eval_metrics_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_metrics_init();

  // Verify all metrics initialize to zero
  u64 evals, func_calls, builtin_calls, closures, lookups;
  u32 stack_max;

  valk_eval_metrics_get(&evals, &func_calls, &builtin_calls, &stack_max,
                        &closures, &lookups);

  VALK_TEST_ASSERT(evals == 0, "evals_total should be 0");
  VALK_TEST_ASSERT(func_calls == 0, "function_calls should be 0");
  VALK_TEST_ASSERT(builtin_calls == 0, "builtin_calls should be 0");
  VALK_TEST_ASSERT(stack_max == 0, "stack_depth_max should be 0");
  VALK_TEST_ASSERT(closures == 0, "closures_created should be 0");
  VALK_TEST_ASSERT(lookups == 0, "env_lookups should be 0");

  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Eval Counter
//-----------------------------------------------------------------------------

void test_eval_counter(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_metrics_init();
  test_gc_ctx_t gc = test_setup_gc();
  valk_lenv_builtins(gc.env);

  u64 evals_before = 0;
  valk_eval_metrics_get(&evals_before, nullptr, nullptr, nullptr, nullptr, nullptr);

  // Evaluate a simple number (should increment eval counter)
  valk_lval_t* num = valk_lval_num(42);
  valk_lval_t* result = valk_lval_eval(gc.env, num);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");

  u64 evals_after = 0;
  valk_eval_metrics_get(&evals_after, nullptr, nullptr, nullptr, nullptr, nullptr);

  VALK_TEST_ASSERT(evals_after > evals_before,
                   "Eval counter should increment");

  test_teardown_gc(&gc);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Builtin Calls
//-----------------------------------------------------------------------------

void test_builtin_calls(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_metrics_init();
  test_gc_ctx_t gc = test_setup_gc();
  valk_lenv_builtins(gc.env);

  u64 builtin_before = 0;
  valk_eval_metrics_get(nullptr, nullptr, &builtin_before, nullptr, nullptr, nullptr);

  // Call a builtin function (e.g., +)
  valk_lval_t* plus_sym = valk_lval_sym("+");
  valk_lval_t* arg1 = valk_lval_num(1);
  valk_lval_t* arg2 = valk_lval_num(2);

  valk_lval_t* expr = valk_lval_list(
      (valk_lval_t*[]){plus_sym, arg1, arg2}, 3);

  valk_lval_t* result = valk_lval_eval(gc.env, expr);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 3, "Result should be 3");

  u64 builtin_after = 0;
  valk_eval_metrics_get(nullptr, nullptr, &builtin_after, nullptr, nullptr, nullptr);

  VALK_TEST_ASSERT(builtin_after > builtin_before,
                   "Builtin call counter should increment");

  test_teardown_gc(&gc);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Stack Depth Tracking
//-----------------------------------------------------------------------------

void test_stack_depth(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_metrics_init();
  test_gc_ctx_t gc = test_setup_gc();
  valk_lenv_builtins(gc.env);

  u32 stack_before = 0;
  valk_eval_metrics_get(nullptr, nullptr, nullptr, &stack_before, nullptr, nullptr);

  // Create a simple nested function call: (+ (+ 1 2) 3)
  valk_lval_t* plus1 = valk_lval_sym("+");
  valk_lval_t* one = valk_lval_num(1);
  valk_lval_t* two = valk_lval_num(2);
  valk_lval_t* inner_call = valk_lval_list(
      (valk_lval_t*[]){plus1, one, two}, 3);

  valk_lval_t* plus2 = valk_lval_sym("+");
  valk_lval_t* three = valk_lval_num(3);
  valk_lval_t* outer_call = valk_lval_list(
      (valk_lval_t*[]){plus2, inner_call, three}, 3);

  valk_lval_t* result = valk_lval_eval(gc.env, outer_call);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be a number");
  VALK_TEST_ASSERT(result->num == 6, "Result should be 6");

  u32 stack_after = 0;
  valk_eval_metrics_get(nullptr, nullptr, nullptr, &stack_after, nullptr, nullptr);

  VALK_TEST_ASSERT(stack_after > stack_before,
                   "Stack depth max should increase after nested calls");

  test_teardown_gc(&gc);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Closure Counting
//-----------------------------------------------------------------------------

void test_closure_counting(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_metrics_init();
  test_gc_ctx_t gc = test_setup_gc();
  valk_lenv_builtins(gc.env);

  u64 closures_before = 0;
  valk_eval_metrics_get(nullptr, nullptr, nullptr, nullptr, &closures_before, nullptr);

  // Create a lambda: \ {x} {x}
  valk_lval_t* param_x = valk_lval_sym("x");
  valk_lval_t* formals = valk_lval_qlist((valk_lval_t*[]){param_x}, 1);

  valk_lval_t* x_sym = valk_lval_sym("x");
  valk_lval_t* body = valk_lval_qlist((valk_lval_t*[]){x_sym}, 1);

  valk_lval_t* lambda = valk_lval_lambda(gc.env, formals, body);
  VALK_TEST_ASSERT(LVAL_TYPE(lambda) == LVAL_FUN,
                   "Lambda should be a function");

  u64 closures_after = 0;
  valk_eval_metrics_get(nullptr, nullptr, nullptr, nullptr, &closures_after, nullptr);

  VALK_TEST_ASSERT(closures_after > closures_before,
                   "Closure counter should increment");

  test_teardown_gc(&gc);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Environment Lookups
//-----------------------------------------------------------------------------

void test_env_lookups(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_eval_metrics_init();
  test_gc_ctx_t gc = test_setup_gc();
  valk_lenv_builtins(gc.env);

  u64 lookups_before = 0;
  valk_eval_metrics_get(nullptr, nullptr, nullptr, nullptr, nullptr, &lookups_before);

  // Lookup a symbol (e.g., +)
  valk_lval_t* plus_sym = valk_lval_sym("+");
  valk_lval_t* result = valk_lval_eval(gc.env, plus_sym);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_FUN,
                   "Result should be a function");

  u64 lookups_after = 0;
  valk_eval_metrics_get(nullptr, nullptr, nullptr, nullptr, nullptr, &lookups_after);

  VALK_TEST_ASSERT(lookups_after > lookups_before,
                   "Lookup counter should increment");

  test_teardown_gc(&gc);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Main
//-----------------------------------------------------------------------------

int main(int argc, const char** argv) {
  UNUSED(argc);
  UNUSED(argv);

  // Initialize memory allocator
  valk_mem_init_malloc();

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_eval_metrics_init",
                          test_eval_metrics_init);
  valk_testsuite_add_test(suite, "test_eval_counter",
                          test_eval_counter);
  valk_testsuite_add_test(suite, "test_builtin_calls",
                          test_builtin_calls);
  valk_testsuite_add_test(suite, "test_stack_depth",
                          test_stack_depth);
  valk_testsuite_add_test(suite, "test_closure_counting",
                          test_closure_counting);
  valk_testsuite_add_test(suite, "test_env_lookups",
                          test_env_lookups);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
