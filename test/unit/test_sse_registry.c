#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio_sse_stream_registry.h"

#include <string.h>

void test_registry_init_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_init(NULL, NULL);

  valk_sse_stream_registry_t registry;
  valk_sse_registry_init(&registry, NULL);

  VALK_PASS();
}

void test_registry_shutdown_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_shutdown(NULL);

  VALK_PASS();
}

void test_registry_stream_count_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t count = valk_sse_registry_stream_count(NULL);
  ASSERT_EQ(count, 0);

  VALK_PASS();
}

void test_registry_stats_json_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buf[256];
  size_t len = valk_sse_registry_stats_json(NULL, buf, sizeof(buf));
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_stats_json_null_buf(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  size_t len = valk_sse_registry_stats_json(&registry, NULL, 256);
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_stats_json_zero_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  char buf[256];
  size_t len = valk_sse_registry_stats_json(&registry, buf, 0);
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_stats_json_valid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  registry.stream_count = 5;
  registry.timer_running = true;
  registry.events_pushed_total = 100;
  registry.bytes_pushed_total = 10000;

  char buf[256];
  size_t len = valk_sse_registry_stats_json(&registry, buf, sizeof(buf));
  ASSERT_GT(len, 0);
  ASSERT_STR_CONTAINS(buf, "stream_count");
  ASSERT_STR_CONTAINS(buf, "timer_running");
  ASSERT_STR_CONTAINS(buf, "events_pushed_total");
  ASSERT_STR_CONTAINS(buf, "bytes_pushed_total");
  ASSERT_STR_CONTAINS(buf, "\"stream_count\":5");
  ASSERT_STR_CONTAINS(buf, "\"timer_running\":true");

  VALK_PASS();
}

void test_registry_stats_json_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  char buf[10];
  size_t len = valk_sse_registry_stats_json(&registry, buf, sizeof(buf));
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

void test_registry_subscribe_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      NULL, NULL, NULL, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_subscribe_null_data_prd(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      &registry, (valk_aio_handle_t *)1, (nghttp2_session *)1, 1,
      VALK_SSE_SUB_DIAGNOSTICS, NULL);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_unsubscribe_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_unsubscribe(NULL, NULL);

  valk_sse_stream_registry_t registry = {0};
  valk_sse_registry_unsubscribe(&registry, NULL);

  VALK_PASS();
}

void test_registry_unsubscribe_connection_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t count = valk_sse_registry_unsubscribe_connection(NULL, NULL);
  ASSERT_EQ(count, 0);

  valk_sse_stream_registry_t registry = {0};
  count = valk_sse_registry_unsubscribe_connection(&registry, NULL);
  ASSERT_EQ(count, 0);

  VALK_PASS();
}

void test_registry_find_by_stream_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(NULL, NULL, 0);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_find_by_stream_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(
      &registry, (valk_aio_handle_t *)1, 1);
  ASSERT_NULL(entry);

  VALK_PASS();
}

void test_registry_timer_start_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_timer_start(NULL);

  VALK_PASS();
}

void test_registry_timer_start_no_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  valk_sse_registry_timer_start(&registry);

  VALK_PASS();
}

void test_registry_timer_stop_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_timer_stop(NULL);

  VALK_PASS();
}

void test_registry_timer_stop_not_running(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t registry = {0};
  registry.timer_running = false;
  valk_sse_registry_timer_stop(&registry);

  VALK_PASS();
}

void test_subscription_type_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_EQ(VALK_SSE_SUB_DIAGNOSTICS, 0);
  ASSERT_EQ(VALK_SSE_SUB_METRICS_ONLY, 1);
  ASSERT_EQ(VALK_SSE_SUB_MEMORY_ONLY, 2);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_registry_init_null_args", test_registry_init_null_args);
  valk_testsuite_add_test(suite, "test_registry_shutdown_null", test_registry_shutdown_null);
  valk_testsuite_add_test(suite, "test_registry_stream_count_null", test_registry_stream_count_null);
  valk_testsuite_add_test(suite, "test_registry_stats_json_null", test_registry_stats_json_null);
  valk_testsuite_add_test(suite, "test_registry_stats_json_null_buf", test_registry_stats_json_null_buf);
  valk_testsuite_add_test(suite, "test_registry_stats_json_zero_size", test_registry_stats_json_zero_size);
  valk_testsuite_add_test(suite, "test_registry_stats_json_valid", test_registry_stats_json_valid);
  valk_testsuite_add_test(suite, "test_registry_stats_json_small_buffer", test_registry_stats_json_small_buffer);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null_args", test_registry_subscribe_null_args);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null_data_prd", test_registry_subscribe_null_data_prd);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_null", test_registry_unsubscribe_null);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_connection_null", test_registry_unsubscribe_connection_null);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_null", test_registry_find_by_stream_null);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_empty", test_registry_find_by_stream_empty);
  valk_testsuite_add_test(suite, "test_registry_timer_start_null", test_registry_timer_start_null);
  valk_testsuite_add_test(suite, "test_registry_timer_start_no_aio", test_registry_timer_start_no_aio);
  valk_testsuite_add_test(suite, "test_registry_timer_stop_null", test_registry_timer_stop_null);
  valk_testsuite_add_test(suite, "test_registry_timer_stop_not_running", test_registry_timer_stop_not_running);
  valk_testsuite_add_test(suite, "test_subscription_type_enum", test_subscription_type_enum);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
