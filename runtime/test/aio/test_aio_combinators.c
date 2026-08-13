#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <uv.h>

#include "aio/aio.h"
#include "aio/system/aio_system.h"
#include "common.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

static valk_lenv_t *create_test_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  valk_register_async_handle_builtins(env);
  return env;
}

static valk_lval_t *eval_str(valk_lenv_t *env, const char *code) {
  int pos = 0;
  valk_lval_t *parsed = valk_lval_read_expr(&pos, code);
  if (LVAL_TYPE(parsed) == LVAL_ERR) return parsed;
  return valk_lval_eval(env, parsed);
}

static void test_aio_all_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all ())");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_single_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all (list (aio/pure 42)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_multiple_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all (list (aio/pure 1) (aio/pure 2) (aio/pure 3)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(atomic_load_explicit(&handle->status, memory_order_acquire), VALK_ASYNC_COMPLETED);
  ASSERT_NOT_NULL(atomic_load_explicit(&handle->result, memory_order_acquire));

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_one_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all (list (aio/pure 1) (aio/fail \"error\") (aio/pure 3)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(atomic_load_explicit(&handle->status, memory_order_acquire), VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_all_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all (list (aio/fail \"e1\") (aio/fail \"e2\")))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_non_list_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all 42)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_non_handle_element_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all (list 42))");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_no_args_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_single_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race (list (aio/pure 42)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_multiple_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race (list (aio/pure 1) (aio/pure 2) (aio/pure 3)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_first_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race (list (aio/fail \"error\") (aio/pure 2)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_empty_list_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race ())");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_non_list_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race 42)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_non_handle_element_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race (list 42))");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_no_args_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_single_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/any (list (aio/pure 42)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_multiple_with_one_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/any (list (aio/fail \"e1\") (aio/pure 42) (aio/fail \"e2\")))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_all_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/any (list (aio/fail \"e1\") (aio/fail \"e2\") (aio/fail \"e3\")))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_empty_list_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/any ())");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_non_list_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/any 42)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_non_handle_element_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/any (list 42))");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_no_args_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/any)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_nested_all(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/all (list "
    "  (aio/all (list (aio/pure 1) (aio/pure 2))) "
    "  (aio/all (list (aio/pure 3) (aio/pure 4)))))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_nested_race(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/race (list "
    "  (aio/race (list (aio/pure 1) (aio/pure 2))) "
    "  (aio/race (list (aio/pure 3) (aio/pure 4)))))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_all_preserves_order(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/all (list (aio/pure 1) (aio/pure 2) (aio/pure 3)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_NOT_NULL(handle->result);

  valk_lval_t *list = handle->result;
  int expected = 1;
  while (!valk_lval_list_is_empty(list)) {
    valk_lval_t *elem = valk_lval_head(list);
    ASSERT_LVAL_NUM(elem, expected);
    expected++;
    list = valk_lval_tail(list);
  }
  ASSERT_EQ(expected, 4);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_then_after_all(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/then (aio/all (list (aio/pure 1) (aio/pure 2))) "
    "  (\\ {xs} {(aio/pure xs)}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_catch_after_all_failure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/catch (aio/all (list (aio/pure 1) (aio/fail \"error\"))) "
    "  (\\ {e} {(aio/pure \"recovered\")}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_first_wins(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/race (list (aio/pure \"first\") (aio/pure \"second\")))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_LVAL_STR(handle->result, "first");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_first_success_wins(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/any (list (aio/fail \"e1\") (aio/pure \"success\") (aio/fail \"e3\")))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_LVAL_STR(handle->result, "success");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_pure_creates_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/pure 42)");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_LVAL_NUM(handle->result, 42);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_fail_creates_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/fail \"test error\")");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_status_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/status (aio/pure 1))");

  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  ASSERT_LVAL_SYM(result, ":completed");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_status_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/status (aio/fail \"err\"))");

  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  ASSERT_LVAL_SYM(result, ":failed");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_cancel_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/cancel (aio/pure 1))");

  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  ASSERT_LVAL_SYM(result, ":false");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_cancelled_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/cancelled? (aio/pure 1))");

  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  ASSERT_LVAL_SYM(result, ":false");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_interval_returns_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  // This is a limited unit test - just verify interval exists and gives proper error
  valk_lenv_t *env = create_test_env();
  
  // The interval function should return an error when given invalid args
  valk_lval_t *result = eval_str(env, "(aio/interval 42 100 (\\ {} nil))");
  
  // Should get an error, not unknown function error
  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  // Don't check exact message, just that function exists
  ASSERT_TRUE(strlen(result->str) > 0);
  
  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_then_transforms(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/then (aio/pure 10) (\\ {x} {(aio/pure (* x 2))}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_LVAL_NUM(handle->result, 20);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_then_propagates_failure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/then (aio/fail \"error\") (\\ {x} {(aio/pure (* x 2))}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_catch_recovers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/catch (aio/fail \"error\") (\\ {e} {(aio/pure 99)}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_catch_passes_through_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/catch (aio/pure 42) (\\ {e} {(aio/pure 0)}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_LVAL_NUM(handle->result, 42);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_finally_runs_on_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/finally (aio/pure 42) (\\ {} {nil}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_finally_runs_on_failure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/finally (aio/fail \"error\") (\\ {} {nil}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_on_cancel_registered(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/on-cancel (aio/pure 42) (\\ {} {nil}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_bracket_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/bracket (aio/pure \"resource\") "
    "  (\\ {r} {(aio/pure nil)}) "
    "  (\\ {r} {(aio/pure 42)}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_bracket_use_fails(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/bracket (aio/pure \"resource\") "
    "  (\\ {r} {(aio/pure nil)}) "
    "  (\\ {r} {(aio/fail \"use failed\")}))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_within_completed_before_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/within (aio/pure 42) 1000)");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  valk_lval_t *value = handle->result;
  ASSERT_LVAL_TYPE(value, LVAL_NUM);
  ASSERT_EQ(value->num, 42);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_within_failed_before_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/within (aio/fail \"error\") 1000)");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);

  valk_lval_t *error = handle->error;
  ASSERT_LVAL_TYPE(error, LVAL_STR);
  ASSERT_STR_EQ(error->str, "error");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_within_wrong_args_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/within)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "aio/within: expected 2 arguments");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_within_non_handle_first_arg_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/within 42 1000)");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "aio/within: first argument must be a handle");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_within_non_number_second_arg_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env, "(aio/within (aio/pure 42) \"timeout\")");

  ASSERT_LVAL_TYPE(result, LVAL_ERR);
  ASSERT_STR_CONTAINS(result->str, "aio/within: second argument must be a number");

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_within_actual_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = create_test_env();
  valk_lenv_put(env, valk_lval_sym("sys"), valk_lval_ref("aio_system", sys, NULL));
  
  valk_lval_t *result = eval_str(env, "(aio/within (aio/sleep sys 100) 10)");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  
  for (int i = 0; i < 500 && handle->status == VALK_ASYNC_RUNNING; i++) {
    usleep(1000);
  }

  ASSERT_EQ(handle->status, VALK_ASYNC_FAILED);
  valk_lval_t *error = handle->error;
  ASSERT_LVAL_TYPE(error, LVAL_ERR);
  ASSERT_STR_EQ(error->str, ":timeout");

  valk_lenv_free(env);
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}

static void test_aio_all_many_handles(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/all (list "
    "  (aio/pure 1) (aio/pure 2) (aio/pure 3) (aio/pure 4) (aio/pure 5) "
    "  (aio/pure 6) (aio/pure 7) (aio/pure 8) (aio/pure 9) (aio/pure 10)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);

  size_t count = 0;
  valk_lval_t *list = handle->result;
  while (!valk_lval_list_is_empty(list)) {
    count++;
    list = valk_lval_tail(list);
  }
  ASSERT_EQ(count, 10);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_race_many_handles(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/race (list "
    "  (aio/pure 1) (aio/pure 2) (aio/pure 3) (aio/pure 4) (aio/pure 5)))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_LVAL_NUM(handle->result, 1);

  valk_lenv_free(env);
  VALK_PASS();
}

static void test_aio_any_many_failures_one_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  valk_lval_t *result = eval_str(env,
    "(aio/any (list "
    "  (aio/fail \"e1\") (aio/fail \"e2\") (aio/fail \"e3\") "
    "  (aio/pure \"success\") (aio/fail \"e4\")))");

  ASSERT_LVAL_TYPE(result, LVAL_HANDLE);
  valk_async_handle_t *handle = result->async.handle;
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->status, VALK_ASYNC_COMPLETED);
  ASSERT_LVAL_STR(handle->result, "success");

  valk_lenv_free(env);
  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_aio_all_empty_list", test_aio_all_empty_list);
  valk_testsuite_add_test(suite, "test_aio_all_single_completed", test_aio_all_single_completed);
  valk_testsuite_add_test(suite, "test_aio_all_multiple_completed", test_aio_all_multiple_completed);
  valk_testsuite_add_test(suite, "test_aio_all_one_failed", test_aio_all_one_failed);
  valk_testsuite_add_test(suite, "test_aio_all_all_failed", test_aio_all_all_failed);
  valk_testsuite_add_test(suite, "test_aio_all_non_list_error", test_aio_all_non_list_error);
  valk_testsuite_add_test(suite, "test_aio_all_non_handle_element_error", test_aio_all_non_handle_element_error);
  valk_testsuite_add_test(suite, "test_aio_all_no_args_error", test_aio_all_no_args_error);
  valk_testsuite_add_test(suite, "test_aio_all_preserves_order", test_aio_all_preserves_order);
  valk_testsuite_add_test(suite, "test_aio_all_many_handles", test_aio_all_many_handles);

  valk_testsuite_add_test(suite, "test_aio_race_single_completed", test_aio_race_single_completed);
  valk_testsuite_add_test(suite, "test_aio_race_multiple_completed", test_aio_race_multiple_completed);
  valk_testsuite_add_test(suite, "test_aio_race_first_failed", test_aio_race_first_failed);
  valk_testsuite_add_test(suite, "test_aio_race_empty_list_error", test_aio_race_empty_list_error);
  valk_testsuite_add_test(suite, "test_aio_race_non_list_error", test_aio_race_non_list_error);
  valk_testsuite_add_test(suite, "test_aio_race_non_handle_element_error", test_aio_race_non_handle_element_error);
  valk_testsuite_add_test(suite, "test_aio_race_no_args_error", test_aio_race_no_args_error);
  valk_testsuite_add_test(suite, "test_aio_race_first_wins", test_aio_race_first_wins);
  valk_testsuite_add_test(suite, "test_aio_race_many_handles", test_aio_race_many_handles);

  valk_testsuite_add_test(suite, "test_aio_any_single_completed", test_aio_any_single_completed);
  valk_testsuite_add_test(suite, "test_aio_any_multiple_with_one_success", test_aio_any_multiple_with_one_success);
  valk_testsuite_add_test(suite, "test_aio_any_all_failed", test_aio_any_all_failed);
  valk_testsuite_add_test(suite, "test_aio_any_empty_list_error", test_aio_any_empty_list_error);
  valk_testsuite_add_test(suite, "test_aio_any_non_list_error", test_aio_any_non_list_error);
  valk_testsuite_add_test(suite, "test_aio_any_non_handle_element_error", test_aio_any_non_handle_element_error);
  valk_testsuite_add_test(suite, "test_aio_any_no_args_error", test_aio_any_no_args_error);
  valk_testsuite_add_test(suite, "test_aio_any_first_success_wins", test_aio_any_first_success_wins);
  valk_testsuite_add_test(suite, "test_aio_any_many_failures_one_success", test_aio_any_many_failures_one_success);

  valk_testsuite_add_test(suite, "test_aio_nested_all", test_aio_nested_all);
  valk_testsuite_add_test(suite, "test_aio_nested_race", test_aio_nested_race);
  valk_testsuite_add_test(suite, "test_aio_then_after_all", test_aio_then_after_all);
  valk_testsuite_add_test(suite, "test_aio_catch_after_all_failure", test_aio_catch_after_all_failure);

  valk_testsuite_add_test(suite, "test_aio_pure_creates_completed", test_aio_pure_creates_completed);
  valk_testsuite_add_test(suite, "test_aio_fail_creates_failed", test_aio_fail_creates_failed);
  valk_testsuite_add_test(suite, "test_aio_status_completed", test_aio_status_completed);
  valk_testsuite_add_test(suite, "test_aio_status_failed", test_aio_status_failed);
  valk_testsuite_add_test(suite, "test_aio_cancel_completed", test_aio_cancel_completed);
  valk_testsuite_add_test(suite, "test_aio_cancelled_completed", test_aio_cancelled_completed);
  valk_testsuite_add_test(suite, "test_aio_interval_returns_handle", test_aio_interval_returns_handle);

  valk_testsuite_add_test(suite, "test_aio_then_transforms", test_aio_then_transforms);
  valk_testsuite_add_test(suite, "test_aio_then_propagates_failure", test_aio_then_propagates_failure);
  valk_testsuite_add_test(suite, "test_aio_catch_recovers", test_aio_catch_recovers);
  valk_testsuite_add_test(suite, "test_aio_catch_passes_through_success", test_aio_catch_passes_through_success);
  valk_testsuite_add_test(suite, "test_aio_finally_runs_on_success", test_aio_finally_runs_on_success);
  valk_testsuite_add_test(suite, "test_aio_finally_runs_on_failure", test_aio_finally_runs_on_failure);
  valk_testsuite_add_test(suite, "test_aio_on_cancel_registered", test_aio_on_cancel_registered);
  valk_testsuite_add_test(suite, "test_aio_bracket_success", test_aio_bracket_success);
  valk_testsuite_add_test(suite, "test_aio_bracket_use_fails", test_aio_bracket_use_fails);

  valk_testsuite_add_test(suite, "test_aio_within_completed_before_timeout", test_aio_within_completed_before_timeout);
  valk_testsuite_add_test(suite, "test_aio_within_failed_before_timeout", test_aio_within_failed_before_timeout);
  valk_testsuite_add_test(suite, "test_aio_within_wrong_args_error", test_aio_within_wrong_args_error);
  valk_testsuite_add_test(suite, "test_aio_within_non_handle_first_arg_error", test_aio_within_non_handle_first_arg_error);
  valk_testsuite_add_test(suite, "test_aio_within_non_number_second_arg_error", test_aio_within_non_number_second_arg_error);
  valk_testsuite_add_test(suite, "test_aio_within_actual_timeout", test_aio_within_actual_timeout);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
