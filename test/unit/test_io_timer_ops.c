#include "../testing.h"
#include "aio/io/io_timer_ops.h"
#include <string.h>

static valk_test_timer_state_t g_timer_state;
static int g_callback_count = 0;

static void reset_state(void) {
  memset(&g_timer_state, 0, sizeof(g_timer_state));
  g_callback_count = 0;
  valk_test_timer_init_state(&g_timer_state);
}

static void test_callback(valk_io_timer_t *timer) {
  (void)timer;
  g_callback_count++;
}

void test_timer_ops_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_io_timer_ops_test.timer_size > 0, "Timer size should be positive");
  VALK_TEST_ASSERT(valk_io_timer_ops_uv.timer_size > 0, "UV timer size should be positive");

  VALK_PASS();
}

void test_timer_test_double_start_fires(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  valk_io_timer_ops_test.start(timer, test_callback, 100, 0);

  VALK_TEST_ASSERT(g_callback_count == 0, "Callback should not fire immediately");
  VALK_TEST_ASSERT(valk_test_timer_pending_count() == 1, "Should have 1 pending timer");

  valk_test_timer_advance(50);
  VALK_TEST_ASSERT(g_callback_count == 0, "Callback should not fire before timeout");

  valk_test_timer_advance(50);
  VALK_TEST_ASSERT(g_callback_count == 1, "Callback should fire at timeout");

  VALK_PASS();
}

void test_timer_test_double_repeat(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  valk_io_timer_ops_test.start(timer, test_callback, 100, 100);

  valk_test_timer_advance(100);
  VALK_TEST_ASSERT(g_callback_count == 1, "First callback");

  valk_test_timer_advance(100);
  VALK_TEST_ASSERT(g_callback_count == 2, "Second callback");

  valk_test_timer_advance(100);
  VALK_TEST_ASSERT(g_callback_count == 3, "Third callback");

  VALK_PASS();
}

void test_timer_test_double_stop(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  valk_io_timer_ops_test.start(timer, test_callback, 100, 100);

  valk_test_timer_advance(100);
  VALK_TEST_ASSERT(g_callback_count == 1, "First callback before stop");

  valk_io_timer_ops_test.stop(timer);

  valk_test_timer_advance(100);
  VALK_TEST_ASSERT(g_callback_count == 1, "No more callbacks after stop");

  VALK_PASS();
}

void test_timer_test_double_data(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);

  int test_data = 42;
  valk_io_timer_ops_test.set_data(timer, &test_data);

  int *retrieved = valk_io_timer_ops_test.get_data(timer);
  VALK_TEST_ASSERT(retrieved == &test_data, "Data pointer should match");
  VALK_TEST_ASSERT(*retrieved == 42, "Data value should match");

  VALK_PASS();
}

void test_timer_test_double_now(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  uint64_t t0 = valk_io_timer_ops_test.now(nullptr);
  VALK_TEST_ASSERT(t0 == 0, "Initial time should be 0");

  valk_test_timer_advance(500);

  uint64_t t1 = valk_io_timer_ops_test.now(nullptr);
  VALK_TEST_ASSERT(t1 == 500, "Time should advance to 500");

  VALK_PASS();
}

void test_timer_test_double_hrtime(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  uint64_t t0 = valk_io_timer_ops_test.hrtime();
  VALK_TEST_ASSERT(t0 == 0, "Initial hrtime should be 0");

  valk_test_timer_advance(500);

  uint64_t t1 = valk_io_timer_ops_test.hrtime();
  VALK_TEST_ASSERT(t1 == 500 * 1000000ULL, "hrtime should be in nanoseconds");

  VALK_PASS();
}

void test_timer_test_double_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  valk_io_timer_ops_test.start(timer, test_callback, 100, 0);

  VALK_TEST_ASSERT(!valk_io_timer_ops_test.is_closing(timer), "Not closing initially");

  valk_io_timer_ops_test.close(timer, nullptr);

  VALK_TEST_ASSERT(valk_io_timer_ops_test.is_closing(timer), "Should be closing after close()");

  valk_test_timer_advance(100);
  VALK_TEST_ASSERT(g_callback_count == 0, "No callbacks after close");

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "timer_ops_size", test_timer_ops_size);
  valk_testsuite_add_test(suite, "timer_test_double_start_fires", test_timer_test_double_start_fires);
  valk_testsuite_add_test(suite, "timer_test_double_repeat", test_timer_test_double_repeat);
  valk_testsuite_add_test(suite, "timer_test_double_stop", test_timer_test_double_stop);
  valk_testsuite_add_test(suite, "timer_test_double_data", test_timer_test_double_data);
  valk_testsuite_add_test(suite, "timer_test_double_now", test_timer_test_double_now);
  valk_testsuite_add_test(suite, "timer_test_double_hrtime", test_timer_test_double_hrtime);
  valk_testsuite_add_test(suite, "timer_test_double_close", test_timer_test_double_close);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
