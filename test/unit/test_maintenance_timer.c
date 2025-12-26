#include "../testing.h"
#include "aio/io/io_timer_ops.h"
#include <string.h>

static valk_test_timer_state_t g_timer_state;
static int g_callback_count = 0;
static valk_io_timer_t *g_last_timer = nullptr;

static void reset_state(void) {
  memset(&g_timer_state, 0, sizeof(g_timer_state));
  g_callback_count = 0;
  g_last_timer = nullptr;
  valk_test_timer_init_state(&g_timer_state);
}

static void test_callback(valk_io_timer_t *timer) {
  g_last_timer = timer;
  g_callback_count++;
}

void test_maintenance_timer_starts(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  
  ASSERT_EQ(valk_test_timer_pending_count(), 0);

  uint64_t maintenance_interval_ms = 1000;
  valk_io_timer_ops_test.start(timer, test_callback, 
    maintenance_interval_ms, maintenance_interval_ms);

  ASSERT_EQ(valk_test_timer_pending_count(), 1);

  VALK_PASS();
}

void test_maintenance_timer_fires_at_interval(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  
  uint64_t maintenance_interval_ms = 1000;
  valk_io_timer_ops_test.start(timer, test_callback,
    maintenance_interval_ms, maintenance_interval_ms);

  ASSERT_EQ(g_callback_count, 0);

  valk_test_timer_advance(500);
  ASSERT_EQ(g_callback_count, 0);

  valk_test_timer_advance(500);
  ASSERT_EQ(g_callback_count, 1);

  valk_test_timer_advance(1000);
  ASSERT_EQ(g_callback_count, 2);

  valk_test_timer_advance(1000);
  ASSERT_EQ(g_callback_count, 3);

  VALK_PASS();
}

void test_maintenance_timer_stop(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  
  valk_io_timer_ops_test.start(timer, test_callback, 100, 100);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_callback_count, 1);

  valk_io_timer_ops_test.stop(timer);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_callback_count, 1);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_callback_count, 1);

  VALK_PASS();
}

void test_maintenance_timer_data_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);

  int test_data = 42;
  valk_io_timer_ops_test.set_data(timer, &test_data);

  int *retrieved = valk_io_timer_ops_test.get_data(timer);
  ASSERT_EQ(retrieved, &test_data);
  ASSERT_EQ(*retrieved, 42);

  VALK_PASS();
}

void test_maintenance_timer_close(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  valk_io_timer_ops_test.start(timer, test_callback, 100, 100);

  ASSERT_FALSE(valk_io_timer_ops_test.is_closing(timer));

  valk_io_timer_ops_test.close(timer, nullptr);

  ASSERT_TRUE(valk_io_timer_ops_test.is_closing(timer));

  valk_test_timer_advance(100);
  ASSERT_EQ(g_callback_count, 0);

  VALK_PASS();
}

void test_maintenance_timer_now_advances(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  uint64_t t0 = valk_io_timer_ops_test.now(nullptr);
  ASSERT_EQ(t0, 0);

  valk_test_timer_advance(500);

  uint64_t t1 = valk_io_timer_ops_test.now(nullptr);
  ASSERT_EQ(t1, 500);

  valk_test_timer_advance(250);

  uint64_t t2 = valk_io_timer_ops_test.now(nullptr);
  ASSERT_EQ(t2, 750);

  VALK_PASS();
}

void test_maintenance_timer_one_shot(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();

  char timer_buf[256];
  valk_io_timer_t *timer = (valk_io_timer_t *)timer_buf;

  valk_io_timer_ops_test.init(nullptr, timer);
  
  valk_io_timer_ops_test.start(timer, test_callback, 100, 0);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_callback_count, 1);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_callback_count, 1);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_callback_count, 1);

  VALK_PASS();
}

static int g_cb1_count = 0;
static int g_cb2_count = 0;

static void timer_cb1(valk_io_timer_t *t) {
  (void)t;
  g_cb1_count++;
}

static void timer_cb2(valk_io_timer_t *t) {
  (void)t;
  g_cb2_count++;
}

void test_maintenance_timer_multiple_timers(VALK_TEST_ARGS()) {
  VALK_TEST();
  reset_state();
  g_cb1_count = 0;
  g_cb2_count = 0;

  char timer_buf1[256];
  char timer_buf2[256];
  valk_io_timer_t *timer1 = (valk_io_timer_t *)timer_buf1;
  valk_io_timer_t *timer2 = (valk_io_timer_t *)timer_buf2;

  valk_io_timer_ops_test.init(nullptr, timer1);
  valk_io_timer_ops_test.init(nullptr, timer2);

  valk_io_timer_ops_test.start(timer1, timer_cb1, 100, 100);
  valk_io_timer_ops_test.start(timer2, timer_cb2, 150, 150);

  ASSERT_EQ(valk_test_timer_pending_count(), 2);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_cb1_count, 1);
  ASSERT_EQ(g_cb2_count, 0);

  valk_test_timer_advance(50);
  ASSERT_EQ(g_cb1_count, 1);
  ASSERT_EQ(g_cb2_count, 1);

  valk_test_timer_advance(50);
  ASSERT_EQ(g_cb1_count, 2);
  ASSERT_EQ(g_cb2_count, 1);

  valk_test_timer_advance(100);
  ASSERT_EQ(g_cb1_count, 3);
  ASSERT_EQ(g_cb2_count, 2);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "maintenance_timer_starts", 
    test_maintenance_timer_starts);
  valk_testsuite_add_test(suite, "maintenance_timer_fires_at_interval",
    test_maintenance_timer_fires_at_interval);
  valk_testsuite_add_test(suite, "maintenance_timer_stop",
    test_maintenance_timer_stop);
  valk_testsuite_add_test(suite, "maintenance_timer_data_roundtrip",
    test_maintenance_timer_data_roundtrip);
  valk_testsuite_add_test(suite, "maintenance_timer_close",
    test_maintenance_timer_close);
  valk_testsuite_add_test(suite, "maintenance_timer_now_advances",
    test_maintenance_timer_now_advances);
  valk_testsuite_add_test(suite, "maintenance_timer_one_shot",
    test_maintenance_timer_one_shot);
  valk_testsuite_add_test(suite, "maintenance_timer_multiple_timers",
    test_maintenance_timer_multiple_timers);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
