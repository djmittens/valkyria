#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/aio.h"
#include "../../src/aio/aio_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static _Atomic int g_timer_fired = 0;
static _Atomic int g_timer_close_count = 0;

static void timer_test_callback(uv_timer_t *timer) {
  (void)timer;
  atomic_fetch_add(&g_timer_fired, 1);
}

static void close_cb(uv_handle_t *handle) {
  (void)handle;
  atomic_fetch_add(&g_timer_close_count, 1);
}

void test_timer_alloc_null_system(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *handle = valk_aio_timer_alloc(NULL);
  ASSERT_NULL(handle);

  VALK_PASS();
}

void test_timer_alloc_null_handle_slab(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t fake_sys = {0};
  fake_sys.handleSlab = NULL;

  valk_aio_handle_t *handle = valk_aio_timer_alloc(&fake_sys);
  ASSERT_NULL(handle);

  VALK_PASS();
}

void test_timer_init_null_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_timer_init(NULL);

  VALK_PASS();
}

void test_timer_init_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t fake_handle = {0};
  fake_handle.sys = NULL;

  valk_aio_timer_init(&fake_handle);

  VALK_PASS();
}

void test_timer_start_null_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_timer_start(NULL, 100, 0, timer_test_callback);

  VALK_PASS();
}

void test_timer_stop_null_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_timer_stop(NULL);

  VALK_PASS();
}

void test_timer_close_null_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_timer_close(NULL, close_cb);

  VALK_PASS();
}

void test_timer_set_data_null_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  int data = 42;
  valk_aio_timer_set_data(NULL, &data);

  VALK_PASS();
}

void test_timer_free_null_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_timer_free(NULL);

  VALK_PASS();
}

void test_timer_free_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t fake_handle = {0};
  fake_handle.sys = NULL;

  valk_aio_timer_free(&fake_handle);

  VALK_PASS();
}

void test_timer_full_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);
  ASSERT_EQ(timer->kind, VALK_HNDL_TIMER);
  ASSERT_EQ(timer->magic, VALK_AIO_HANDLE_MAGIC);
  ASSERT_EQ(timer->sys, sys);

  valk_aio_timer_init(timer);

  int test_data = 42;
  valk_aio_timer_set_data(timer, &test_data);

  valk_aio_timer_start(timer, 10, 0, timer_test_callback);

  usleep(50000);

  valk_aio_timer_stop(timer);

  valk_aio_timer_close(timer, close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_timer_repeating(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);
  valk_aio_timer_start(timer, 5, 10, timer_test_callback);

  usleep(80000);

  valk_aio_timer_stop(timer);
  valk_aio_timer_close(timer, close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_timer_double_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);
  valk_aio_timer_close(timer, close_cb);
  valk_aio_timer_close(timer, close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_timer_stop_before_fire(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);
  valk_aio_timer_start(timer, 10000, 0, timer_test_callback);
  valk_aio_timer_stop(timer);

  usleep(20000);

  valk_aio_timer_close(timer, close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_timer_free_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);
  ASSERT_EQ(timer->kind, VALK_HNDL_TIMER);

  valk_aio_timer_free(timer);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_timer_free_wrong_kind(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  timer->kind = VALK_HNDL_TCP;
  valk_aio_timer_free(timer);

  timer->kind = VALK_HNDL_TIMER;
  valk_aio_timer_free(timer);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "timer_alloc_null_system", test_timer_alloc_null_system);
  valk_testsuite_add_test(suite, "timer_alloc_null_handle_slab", test_timer_alloc_null_handle_slab);
  valk_testsuite_add_test(suite, "timer_init_null_handle", test_timer_init_null_handle);
  valk_testsuite_add_test(suite, "timer_init_null_sys", test_timer_init_null_sys);
  valk_testsuite_add_test(suite, "timer_start_null_handle", test_timer_start_null_handle);
  valk_testsuite_add_test(suite, "timer_stop_null_handle", test_timer_stop_null_handle);
  valk_testsuite_add_test(suite, "timer_close_null_handle", test_timer_close_null_handle);
  valk_testsuite_add_test(suite, "timer_set_data_null_handle", test_timer_set_data_null_handle);
  valk_testsuite_add_test(suite, "timer_free_null_handle", test_timer_free_null_handle);
  valk_testsuite_add_test(suite, "timer_free_null_sys", test_timer_free_null_sys);
  valk_testsuite_add_test(suite, "timer_full_lifecycle", test_timer_full_lifecycle);
  valk_testsuite_add_test(suite, "timer_repeating", test_timer_repeating);
  valk_testsuite_add_test(suite, "timer_double_close", test_timer_double_close);
  valk_testsuite_add_test(suite, "timer_stop_before_fire", test_timer_stop_before_fire);
  valk_testsuite_add_test(suite, "timer_free_lifecycle", test_timer_free_lifecycle);
  valk_testsuite_add_test(suite, "timer_free_wrong_kind", test_timer_free_wrong_kind);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
