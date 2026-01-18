#include "../testing.h"
#include "aio/io/io_timer_ops.h"
#include "aio/aio.h"
#include "aio/aio_internal.h"
#include "memory.h"
#include <string.h>
#include <unistd.h>

static _Atomic int g_uv_callback_count = 0;
static _Atomic int g_uv_close_count = 0;

static void uv_timer_callback(valk_io_timer_t *timer) {
  (void)timer;
  atomic_fetch_add(&g_uv_callback_count, 1);
}

static void uv_close_callback(void *handle) {
  (void)handle;
  atomic_fetch_add(&g_uv_close_count, 1);
}

void test_uv_timer_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  char timer_buf[512];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;
  int res = valk_io_timer_ops_uv.init(sys, timer);
  ASSERT_EQ(res, 0);

  valk_io_timer_ops_uv.close(timer, uv_close_callback);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_uv_timer_start_stop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  char timer_buf[512];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;
  int res = valk_io_timer_ops_uv.init(sys, timer);
  ASSERT_EQ(res, 0);

  atomic_store(&g_uv_callback_count, 0);
  res = valk_io_timer_ops_uv.start(timer, uv_timer_callback, 10, 0);
  ASSERT_EQ(res, 0);

  usleep(100000);

  res = valk_io_timer_ops_uv.stop(timer);
  ASSERT_EQ(res, 0);

  valk_io_timer_ops_uv.close(timer, uv_close_callback);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_uv_timer_repeating(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  char timer_buf[512];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;
  int res = valk_io_timer_ops_uv.init(sys, timer);
  ASSERT_EQ(res, 0);

  res = valk_io_timer_ops_uv.start(timer, uv_timer_callback, 5, 10);
  ASSERT_EQ(res, 0);

  usleep(80000);

  res = valk_io_timer_ops_uv.stop(timer);
  ASSERT_EQ(res, 0);

  valk_io_timer_ops_uv.close(timer, uv_close_callback);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_uv_timer_is_closing(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  char timer_buf[512];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;
  int res = valk_io_timer_ops_uv.init(sys, timer);
  ASSERT_EQ(res, 0);

  bool closing = valk_io_timer_ops_uv.is_closing(timer);
  ASSERT_FALSE(closing);

  valk_io_timer_ops_uv.close(timer, uv_close_callback);

  closing = valk_io_timer_ops_uv.is_closing(timer);
  ASSERT_TRUE(closing);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_uv_timer_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  char timer_buf[512];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;
  int res = valk_io_timer_ops_uv.init(sys, timer);
  ASSERT_EQ(res, 0);

  int test_value = 12345;
  valk_io_timer_ops_uv.set_data(timer, &test_value);

  void *data = valk_io_timer_ops_uv.get_data(timer);
  ASSERT_EQ(data, &test_value);
  ASSERT_EQ(*(int*)data, 12345);

  valk_io_timer_ops_uv.close(timer, uv_close_callback);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_uv_timer_null_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  char timer_buf[512];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;
  int res = valk_io_timer_ops_uv.init(sys, timer);
  ASSERT_EQ(res, 0);

  res = valk_io_timer_ops_uv.start(timer, NULL, 10, 0);
  ASSERT_EQ(res, 0);

  usleep(100000);

  res = valk_io_timer_ops_uv.stop(timer);
  ASSERT_EQ(res, 0);

  valk_io_timer_ops_uv.close(timer, uv_close_callback);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "uv_timer_init", test_uv_timer_init);
  valk_testsuite_add_test(suite, "uv_timer_start_stop", test_uv_timer_start_stop);
  valk_testsuite_add_test(suite, "uv_timer_repeating", test_uv_timer_repeating);
  valk_testsuite_add_test(suite, "uv_timer_is_closing", test_uv_timer_is_closing);
  valk_testsuite_add_test(suite, "uv_timer_data", test_uv_timer_data);
  valk_testsuite_add_test(suite, "uv_timer_null_callback", test_uv_timer_null_callback);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
