#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"
#include "../../src/aio/aio.h"
#include "../../src/aio/aio_async.h"
#include "../../src/aio/aio_request_ctx.h"
#include "../../src/aio/aio_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern u64 g_async_handle_id;

void test_async_handle_new_null_sys_and_region(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->sys, NULL);
  ASSERT_EQ(handle->env, NULL);
  ASSERT_EQ(handle->region, NULL);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_PENDING);
  ASSERT_EQ(handle->refcount, 1);

  valk_async_handle_free(handle);
  VALK_PASS();
}

void test_async_handle_new_with_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_aio_system_t fake_sys = {0};
  valk_mem_arena_t arena = {0};
  valk_mem_arena_init(&arena, 4096);
  valk_region_init(&fake_sys.system_region, VALK_LIFETIME_REQUEST, NULL, &arena);

  valk_async_handle_t *handle = valk_async_handle_new(&fake_sys, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->sys, &fake_sys);
  ASSERT_EQ(handle->region, &fake_sys.system_region);

  valk_mem_arena_reset(&arena);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_free(NULL);

  VALK_PASS();
}

void test_async_handle_free_with_region_does_nothing(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_region_t region = {0};

  valk_async_handle_t handle = {0};
  handle.region = &region;

  valk_async_handle_free(&handle);

  VALK_PASS();
}

void test_async_handle_ref_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *result = valk_async_handle_ref(NULL);
  ASSERT_NULL(result);

  VALK_PASS();
}

void test_async_handle_ref_increments(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(handle->refcount, 1);

  valk_async_handle_t *ref = valk_async_handle_ref(handle);
  ASSERT_EQ(ref, handle);
  ASSERT_EQ(handle->refcount, 2);

  valk_async_handle_unref(handle);
  ASSERT_EQ(handle->refcount, 1);

  valk_async_handle_free(handle);
  VALK_PASS();
}

void test_async_handle_unref_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_unref(NULL);

  VALK_PASS();
}

void test_async_handle_unref_frees_at_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_async_handle_unref(handle);

  VALK_PASS();
}

void test_async_handle_refcount_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  u32 count = valk_async_handle_refcount(NULL);
  ASSERT_EQ(count, 0);

  VALK_PASS();
}

void test_async_handle_refcount_returns_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(valk_async_handle_refcount(handle), 1);

  valk_async_handle_ref(handle);
  ASSERT_EQ(valk_async_handle_refcount(handle), 2);

  valk_async_handle_unref(handle);
  valk_async_handle_free(handle);
  VALK_PASS();
}

static int g_cleanup_called = 0;
static void* g_cleanup_ctx = NULL;

static void test_cleanup_fn(void *ctx) {
  g_cleanup_called = 1;
  g_cleanup_ctx = ctx;
}

static int g_on_done_called = 0;
static void* g_on_done_ctx = NULL;
static valk_async_handle_t* g_on_done_handle = NULL;

static void test_on_done_fn(valk_async_handle_t *handle, void *ctx) {
  g_on_done_called = 1;
  g_on_done_ctx = ctx;
  g_on_done_handle = handle;
}

void test_async_handle_on_cleanup_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_on_cleanup(NULL, test_cleanup_fn, NULL);

  valk_async_handle_t handle = {0};
  valk_async_handle_on_cleanup(&handle, NULL, NULL);

  VALK_PASS();
}

void test_async_handle_on_cleanup_invoked_on_unref(VALK_TEST_ARGS()) {
  VALK_TEST();

  g_cleanup_called = 0;
  g_cleanup_ctx = NULL;

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  int ctx_value = 42;
  valk_async_handle_on_cleanup(handle, test_cleanup_fn, &ctx_value);

  valk_async_handle_unref(handle);

  ASSERT_EQ(g_cleanup_called, 1);
  ASSERT_EQ(g_cleanup_ctx, &ctx_value);

  VALK_PASS();
}

void test_async_handle_complete_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_complete(NULL, NULL);

  VALK_PASS();
}

void test_async_handle_complete_transitions_pending_to_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_PENDING);

  valk_lval_t *result = valk_lval_num(42);
  valk_async_handle_complete(handle, result);

  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_COMPLETED);
  ASSERT_EQ(handle->result, result);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_complete_already_terminal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_lval_t *result1 = valk_lval_num(1);
  valk_lval_t *result2 = valk_lval_num(2);

  valk_async_handle_complete(handle, result1);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_COMPLETED);
  ASSERT_EQ(handle->result, result1);

  valk_async_handle_complete(handle, result2);
  ASSERT_EQ(handle->result, result1);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_fail_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_fail(NULL, NULL);

  VALK_PASS();
}

void test_async_handle_fail_transitions_pending_to_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_PENDING);

  valk_lval_t *err = valk_lval_err("test error");
  valk_async_handle_fail(handle, err);

  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_FAILED);
  ASSERT_EQ(handle->error, err);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_fail_already_terminal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_lval_t *result = valk_lval_num(42);
  valk_async_handle_complete(handle, result);

  valk_lval_t *err = valk_lval_err("test error");
  valk_async_handle_fail(handle, err);

  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_COMPLETED);
  ASSERT_NULL(handle->error);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_cancel_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool result = valk_async_handle_cancel(NULL);
  ASSERT_FALSE(result);

  VALK_PASS();
}

void test_async_handle_cancel_already_terminal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_lval_t *result = valk_lval_num(42);
  valk_async_handle_complete(handle, result);

  bool cancelled = valk_async_handle_cancel(handle);
  ASSERT_FALSE(cancelled);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_COMPLETED);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_cancel_pending_no_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_PENDING);

  bool cancelled = valk_async_handle_cancel(handle);
  ASSERT_TRUE(cancelled);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_CANCELLED);

  valk_async_handle_free(handle);
  VALK_PASS();
}

void test_async_handle_add_child_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t handle = {0};
  valk_async_handle_add_child(NULL, &handle);
  valk_async_handle_add_child(&handle, NULL);

  VALK_PASS();
}

void test_async_handle_add_child_sets_parent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *parent = valk_async_handle_new_in_region(NULL, NULL, NULL);
  valk_async_handle_t *child = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(parent);
  ASSERT_NOT_NULL(child);

  valk_async_handle_add_child(parent, child);
  ASSERT_EQ(child->parent, parent);

  valk_async_handle_free(child);
  valk_async_handle_free(parent);
  VALK_PASS();
}

void test_async_handle_add_child_propagates_request_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *parent = valk_async_handle_new_in_region(NULL, NULL, NULL);
  valk_async_handle_t *child = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(parent);
  ASSERT_NOT_NULL(child);

  valk_request_ctx_t ctx = {0};
  parent->request_ctx = &ctx;

  valk_async_handle_add_child(parent, child);
  ASSERT_EQ(child->request_ctx, &ctx);

  valk_async_handle_free(child);
  valk_async_handle_free(parent);
  VALK_PASS();
}

void test_async_is_resource_closed_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool closed = valk_async_is_resource_closed(NULL);
  ASSERT_FALSE(closed);

  VALK_PASS();
}

void test_async_is_resource_closed_no_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t handle = {0};
  bool closed = valk_async_is_resource_closed(&handle);
  ASSERT_FALSE(closed);

  VALK_PASS();
}

static bool test_is_closed_result = false;
static bool test_is_closed_callback(void *ctx) {
  (void)ctx;
  return test_is_closed_result;
}

void test_async_is_resource_closed_with_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t handle = {0};
  handle.is_closed = test_is_closed_callback;

  test_is_closed_result = false;
  ASSERT_FALSE(valk_async_is_resource_closed(&handle));

  test_is_closed_result = true;
  ASSERT_TRUE(valk_async_is_resource_closed(&handle));

  VALK_PASS();
}

void test_async_propagate_region_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_propagate_region(NULL, NULL, NULL);

  VALK_PASS();
}

void test_async_propagate_region_sets_region(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);
  ASSERT_NULL(handle->region);

  valk_region_t region = {0};
  valk_async_propagate_region(handle, &region, NULL);
  ASSERT_EQ(handle->region, &region);

  valk_async_handle_free(handle);
  VALK_PASS();
}

void test_async_propagate_context_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_propagate_context(NULL, NULL, NULL, NULL);

  VALK_PASS();
}

void test_async_propagate_context_sets_all(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_region_t region = {0};
  valk_lenv_t env = {0};
  valk_request_ctx_t ctx = {0};

  valk_async_propagate_context(handle, &region, &env, &ctx);
  ASSERT_EQ(handle->region, &region);
  ASSERT_EQ(handle->env, &env);
  ASSERT_EQ(handle->request_ctx, &ctx);

  valk_async_handle_free(handle);
  VALK_PASS();
}

void test_async_status_to_sym(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_lval_t *pending = valk_async_status_to_sym(VALK_ASYNC_PENDING);
  ASSERT_EQ(pending->flags & LVAL_TYPE_MASK, LVAL_SYM);
  ASSERT_STR_EQ(pending->str, ":pending");

  valk_lval_t *running = valk_async_status_to_sym(VALK_ASYNC_RUNNING);
  ASSERT_STR_EQ(running->str, ":running");

  valk_lval_t *completed = valk_async_status_to_sym(VALK_ASYNC_COMPLETED);
  ASSERT_STR_EQ(completed->str, ":completed");

  valk_lval_t *failed = valk_async_status_to_sym(VALK_ASYNC_FAILED);
  ASSERT_STR_EQ(failed->str, ":failed");

  valk_lval_t *cancelled = valk_async_status_to_sym(VALK_ASYNC_CANCELLED);
  ASSERT_STR_EQ(cancelled->str, ":cancelled");

  valk_lval_t *unknown = valk_async_status_to_sym((valk_async_status_t)99);
  ASSERT_STR_EQ(unknown->str, ":unknown");

  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_await_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_lval_t *result = valk_async_handle_await(NULL);
  ASSERT_EQ(result->flags & LVAL_TYPE_MASK, LVAL_ERR);

  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_await_already_completed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_lval_t *result = valk_lval_num(42);
  valk_async_handle_complete(handle, result);

  valk_lval_t *awaited = valk_async_handle_await(handle);
  ASSERT_EQ(awaited, result);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_await_already_failed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_lval_t *err = valk_lval_err("test error");
  valk_async_handle_fail(handle, err);

  valk_lval_t *awaited = valk_async_handle_await(handle);
  ASSERT_EQ(awaited, err);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_handle_await_already_cancelled(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_async_handle_cancel(handle);
  ASSERT_EQ(valk_async_handle_get_status(handle), VALK_ASYNC_CANCELLED);

  valk_lval_t *awaited = valk_async_handle_await(handle);
  ASSERT_EQ(awaited->flags & LVAL_TYPE_MASK, LVAL_ERR);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_lval_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_async_handle_t *handle = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(handle);

  valk_lval_t *lval = valk_lval_handle(handle);
  ASSERT_NOT_NULL(lval);
  ASSERT_EQ(lval->flags & LVAL_TYPE_MASK, LVAL_HANDLE);
  ASSERT_EQ(lval->async.handle, handle);

  valk_async_handle_free(handle);
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_async_notify_done_calls_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  g_on_done_called = 0;
  g_on_done_ctx = NULL;
  g_on_done_handle = NULL;

  valk_async_handle_t handle = {0};
  handle.on_done = test_on_done_fn;
  handle.on_done_ctx = (void*)0xDEADBEEF;

  valk_async_notify_done(&handle);

  ASSERT_EQ(g_on_done_called, 1);
  ASSERT_EQ(g_on_done_ctx, (void*)0xDEADBEEF);
  ASSERT_EQ(g_on_done_handle, &handle);
  ASSERT_NULL(handle.on_done);
  ASSERT_NULL(handle.on_done_ctx);

  VALK_PASS();
}

void test_async_notify_done_no_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  g_cleanup_called = 0;
  valk_async_handle_t handle = {0};

  valk_async_notify_done(&handle);

  ASSERT_EQ(g_cleanup_called, 0);

  VALK_PASS();
}

void test_async_handle_unref_with_children(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_async_handle_t *parent = valk_async_handle_new_in_region(NULL, NULL, NULL);
  valk_async_handle_t *child1 = valk_async_handle_new_in_region(NULL, NULL, NULL);
  valk_async_handle_t *child2 = valk_async_handle_new_in_region(NULL, NULL, NULL);
  ASSERT_NOT_NULL(parent);
  ASSERT_NOT_NULL(child1);
  ASSERT_NOT_NULL(child2);

  valk_async_handle_add_child(parent, child1);
  valk_async_handle_add_child(parent, child2);

  valk_async_handle_unref(parent);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "async_handle_new_null_sys_and_region", test_async_handle_new_null_sys_and_region);
  valk_testsuite_add_test(suite, "async_handle_new_with_sys", test_async_handle_new_with_sys);
  valk_testsuite_add_test(suite, "async_handle_free_null", test_async_handle_free_null);
  valk_testsuite_add_test(suite, "async_handle_free_with_region_does_nothing", test_async_handle_free_with_region_does_nothing);
  valk_testsuite_add_test(suite, "async_handle_ref_null", test_async_handle_ref_null);
  valk_testsuite_add_test(suite, "async_handle_ref_increments", test_async_handle_ref_increments);
  valk_testsuite_add_test(suite, "async_handle_unref_null", test_async_handle_unref_null);
  valk_testsuite_add_test(suite, "async_handle_unref_frees_at_zero", test_async_handle_unref_frees_at_zero);
  valk_testsuite_add_test(suite, "async_handle_refcount_null", test_async_handle_refcount_null);
  valk_testsuite_add_test(suite, "async_handle_refcount_returns_count", test_async_handle_refcount_returns_count);
  valk_testsuite_add_test(suite, "async_handle_on_cleanup_null", test_async_handle_on_cleanup_null);
  valk_testsuite_add_test(suite, "async_handle_on_cleanup_invoked_on_unref", test_async_handle_on_cleanup_invoked_on_unref);
  valk_testsuite_add_test(suite, "async_handle_complete_null", test_async_handle_complete_null);
  valk_testsuite_add_test(suite, "async_handle_complete_transitions", test_async_handle_complete_transitions_pending_to_completed);
  valk_testsuite_add_test(suite, "async_handle_complete_already_terminal", test_async_handle_complete_already_terminal);
  valk_testsuite_add_test(suite, "async_handle_fail_null", test_async_handle_fail_null);
  valk_testsuite_add_test(suite, "async_handle_fail_transitions", test_async_handle_fail_transitions_pending_to_failed);
  valk_testsuite_add_test(suite, "async_handle_fail_already_terminal", test_async_handle_fail_already_terminal);
  valk_testsuite_add_test(suite, "async_handle_cancel_null", test_async_handle_cancel_null);
  valk_testsuite_add_test(suite, "async_handle_cancel_already_terminal", test_async_handle_cancel_already_terminal);
  valk_testsuite_add_test(suite, "async_handle_cancel_pending_no_sys", test_async_handle_cancel_pending_no_sys);
  valk_testsuite_add_test(suite, "async_handle_add_child_null", test_async_handle_add_child_null);
  valk_testsuite_add_test(suite, "async_handle_add_child_sets_parent", test_async_handle_add_child_sets_parent);
  valk_testsuite_add_test(suite, "async_handle_add_child_propagates_ctx", test_async_handle_add_child_propagates_request_ctx);
  valk_testsuite_add_test(suite, "async_is_resource_closed_null", test_async_is_resource_closed_null);
  valk_testsuite_add_test(suite, "async_is_resource_closed_no_callback", test_async_is_resource_closed_no_callback);
  valk_testsuite_add_test(suite, "async_is_resource_closed_with_callback", test_async_is_resource_closed_with_callback);
  valk_testsuite_add_test(suite, "async_propagate_region_null", test_async_propagate_region_null);
  valk_testsuite_add_test(suite, "async_propagate_region_sets_region", test_async_propagate_region_sets_region);
  valk_testsuite_add_test(suite, "async_propagate_context_null", test_async_propagate_context_null);
  valk_testsuite_add_test(suite, "async_propagate_context_sets_all", test_async_propagate_context_sets_all);
  valk_testsuite_add_test(suite, "async_status_to_sym", test_async_status_to_sym);
  valk_testsuite_add_test(suite, "async_handle_await_null", test_async_handle_await_null);
  valk_testsuite_add_test(suite, "async_handle_await_already_completed", test_async_handle_await_already_completed);
  valk_testsuite_add_test(suite, "async_handle_await_already_failed", test_async_handle_await_already_failed);
  valk_testsuite_add_test(suite, "async_handle_await_already_cancelled", test_async_handle_await_already_cancelled);
  valk_testsuite_add_test(suite, "lval_handle", test_lval_handle);
  valk_testsuite_add_test(suite, "async_notify_done_calls_callback", test_async_notify_done_calls_callback);
  valk_testsuite_add_test(suite, "async_notify_done_no_callback", test_async_notify_done_no_callback);
  valk_testsuite_add_test(suite, "async_handle_unref_with_children", test_async_handle_unref_with_children);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
