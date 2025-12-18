#include "../testing.h"
#include "../../src/memory.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/aio_sse_stream_registry.h"
#include "../../src/metrics_v2.h"

void test_registry_init_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_init(NULL, NULL);

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
  VALK_TEST_ASSERT(count == 0, "NULL registry should return 0 count");

  VALK_PASS();
}

void test_registry_stats_json_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buf[256];
  size_t len = valk_sse_registry_stats_json(NULL, buf, sizeof(buf));
  VALK_TEST_ASSERT(len == 0, "NULL registry should return 0 length");

  valk_sse_stream_registry_t reg = {0};
  len = valk_sse_registry_stats_json(&reg, NULL, 100);
  VALK_TEST_ASSERT(len == 0, "NULL buffer should return 0 length");

  len = valk_sse_registry_stats_json(&reg, buf, 0);
  VALK_TEST_ASSERT(len == 0, "Zero buffer size should return 0 length");

  VALK_PASS();
}

void test_registry_unsubscribe_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_unsubscribe(NULL, NULL);

  valk_sse_stream_registry_t reg = {0};
  valk_sse_registry_unsubscribe(&reg, NULL);

  VALK_PASS();
}

void test_registry_subscribe_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;
  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(NULL, NULL, NULL, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);
  VALK_TEST_ASSERT(entry == NULL, "NULL registry should return NULL entry");

  valk_sse_stream_registry_t reg = {0};
  entry = valk_sse_registry_subscribe(&reg, NULL, NULL, 1, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);
  VALK_TEST_ASSERT(entry == NULL, "NULL handle should return NULL entry");

  VALK_PASS();
}

void test_registry_unsubscribe_connection_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t count = valk_sse_registry_unsubscribe_connection(NULL, NULL);
  VALK_TEST_ASSERT(count == 0, "NULL arguments should return 0");

  VALK_PASS();
}

void test_registry_find_by_stream_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(NULL, NULL, 1);
  VALK_TEST_ASSERT(entry == NULL, "NULL registry should return NULL");

  VALK_PASS();
}

void test_registry_timer_start_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_timer_start(NULL);

  valk_sse_stream_registry_t reg = {0};
  valk_sse_registry_timer_start(&reg);

  VALK_PASS();
}

void test_registry_timer_stop_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_timer_stop(NULL);

  valk_sse_stream_registry_t reg = {0};
  valk_sse_registry_timer_stop(&reg);

  VALK_PASS();
}

void test_subscription_type_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_SSE_SUB_DIAGNOSTICS == 0, "DIAGNOSTICS should be 0");
  VALK_TEST_ASSERT(VALK_SSE_SUB_METRICS_ONLY == 1, "METRICS_ONLY should be 1");
  VALK_TEST_ASSERT(VALK_SSE_SUB_MEMORY_ONLY == 2, "MEMORY_ONLY should be 2");

  VALK_PASS();
}

void test_registry_stats_json_format(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.stream_count = 5;
  reg.timer_running = true;
  reg.events_pushed_total = 100;
  reg.bytes_pushed_total = 50000;

  char buf[256];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON output");
  VALK_TEST_ASSERT(strstr(buf, "\"stream_count\":5") != NULL, "Missing stream_count");
  VALK_TEST_ASSERT(strstr(buf, "\"timer_running\":true") != NULL, "Missing timer_running");
  VALK_TEST_ASSERT(strstr(buf, "\"events_pushed_total\":100") != NULL, "Missing events_pushed_total");
  VALK_TEST_ASSERT(strstr(buf, "\"bytes_pushed_total\":50000") != NULL, "Missing bytes_pushed_total");

  VALK_PASS();
}

void test_registry_stats_json_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.stream_count = 5;

  char buf[10];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));
  VALK_TEST_ASSERT(len == 0, "Too small buffer should return 0");

  VALK_PASS();
}

void test_registry_stream_count_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  size_t count = valk_sse_registry_stream_count(&reg);
  VALK_TEST_ASSERT(count == 0, "Empty registry should have 0 streams");

  VALK_PASS();
}

void test_registry_find_by_stream_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(&reg, NULL, 1);
  VALK_TEST_ASSERT(entry == NULL, "Empty registry should return NULL");

  VALK_PASS();
}

void test_registry_stats_json_all_fields(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.stream_count = 10;
  reg.timer_running = false;
  reg.events_pushed_total = 500;
  reg.bytes_pushed_total = 123456;

  char buf[512];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON output");
  VALK_TEST_ASSERT(strstr(buf, "\"stream_count\":10") != NULL, "Should contain stream_count");
  VALK_TEST_ASSERT(strstr(buf, "\"timer_running\":false") != NULL, "timer_running should be false");
  VALK_TEST_ASSERT(strstr(buf, "\"events_pushed_total\":500") != NULL, "Should contain events_pushed_total");
  VALK_TEST_ASSERT(strstr(buf, "\"bytes_pushed_total\":123456") != NULL, "Should contain bytes_pushed_total");

  VALK_PASS();
}

void test_registry_unsubscribe_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  size_t count = valk_sse_registry_unsubscribe_connection(&reg, (valk_aio_handle_t *)0x1234);
  VALK_TEST_ASSERT(count == 0, "Unsubscribe on empty registry should return 0");

  VALK_PASS();
}

void test_registry_stats_json_large_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.stream_count = 1000;
  reg.timer_running = true;
  reg.events_pushed_total = 1ULL << 40;
  reg.bytes_pushed_total = 1ULL << 50;

  char buf[512];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON output with large values");
  VALK_TEST_ASSERT(strstr(buf, "\"stream_count\":1000") != NULL, "Should contain stream_count");

  VALK_PASS();
}

void test_registry_stats_json_exact_buffer_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.stream_count = 1;
  reg.timer_running = true;
  reg.events_pushed_total = 1;
  reg.bytes_pushed_total = 1;

  char buf[256];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should succeed with adequate buffer");
  VALK_TEST_ASSERT(len < sizeof(buf), "Length should be less than buffer size");

  VALK_PASS();
}

void test_registry_stats_json_timer_false(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.stream_count = 0;
  reg.timer_running = false;
  reg.events_pushed_total = 0;
  reg.bytes_pushed_total = 0;

  char buf[256];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON output");
  VALK_TEST_ASSERT(strstr(buf, "\"timer_running\":false") != NULL, "timer_running should be false");

  VALK_PASS();
}

void test_registry_unsubscribe_nonexistent_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  size_t count = valk_sse_registry_unsubscribe_connection(&reg, (valk_aio_handle_t *)0xDEADBEEF);
  VALK_TEST_ASSERT(count == 0, "Unsubscribing nonexistent handle should return 0");

  VALK_PASS();
}

void test_registry_find_by_stream_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(&reg, (valk_aio_handle_t *)0x1234, 999);
  VALK_TEST_ASSERT(entry == NULL, "Should return NULL when stream not found");

  VALK_PASS();
}

void test_registry_stream_count_after_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  VALK_TEST_ASSERT(valk_sse_registry_stream_count(&reg) == 0, "Initial stream count should be 0");

  reg.stream_count = 5;
  VALK_TEST_ASSERT(valk_sse_registry_stream_count(&reg) == 5, "Stream count should be 5");

  VALK_PASS();
}

void test_registry_stats_json_boundary(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.stream_count = 999999;
  reg.timer_running = true;
  reg.events_pushed_total = 0xFFFFFFFFULL;
  reg.bytes_pushed_total = 0xFFFFFFFFFFFFFFFFULL;

  char buf[512];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON output with boundary values");
  VALK_TEST_ASSERT(strstr(buf, "\"stream_count\":999999") != NULL, "Should contain stream_count");

  VALK_PASS();
}

void test_registry_subscribe_null_data_prd(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(&reg, (valk_aio_handle_t *)0x1234, NULL, 1, VALK_SSE_SUB_DIAGNOSTICS, NULL);
  VALK_TEST_ASSERT(entry == NULL, "NULL data_prd should return NULL entry");

  VALK_PASS();
}

void test_registry_timer_operations_uninitialized(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};
  reg.timer_running = false;
  reg.timer_handle = NULL;

  valk_sse_registry_timer_stop(&reg);

  VALK_PASS();
}

void test_subscription_types_all(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT((int)VALK_SSE_SUB_DIAGNOSTICS == 0, "DIAGNOSTICS should be 0");
  VALK_TEST_ASSERT((int)VALK_SSE_SUB_METRICS_ONLY == 1, "METRICS_ONLY should be 1");
  VALK_TEST_ASSERT((int)VALK_SSE_SUB_MEMORY_ONLY == 2, "MEMORY_ONLY should be 2");

  VALK_PASS();
}

void test_registry_stats_json_minimum_valid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_registry_t reg = {0};

  char buf[200];
  size_t len = valk_sse_registry_stats_json(&reg, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce output for zeroed registry");
  VALK_TEST_ASSERT(buf[0] == '{', "Should start with {");
  VALK_TEST_ASSERT(buf[len-1] == '}', "Should end with }");

  VALK_PASS();
}

#else

void test_sse_registry_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("SSE registry tests require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_registry_init_null", test_registry_init_null);
  valk_testsuite_add_test(suite, "test_registry_shutdown_null", test_registry_shutdown_null);
  valk_testsuite_add_test(suite, "test_registry_stream_count_null", test_registry_stream_count_null);
  valk_testsuite_add_test(suite, "test_registry_stats_json_null", test_registry_stats_json_null);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_null", test_registry_unsubscribe_null);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null", test_registry_subscribe_null);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_connection_null", test_registry_unsubscribe_connection_null);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_null", test_registry_find_by_stream_null);
  valk_testsuite_add_test(suite, "test_registry_timer_start_null", test_registry_timer_start_null);
  valk_testsuite_add_test(suite, "test_registry_timer_stop_null", test_registry_timer_stop_null);
  valk_testsuite_add_test(suite, "test_subscription_type_enum", test_subscription_type_enum);
  valk_testsuite_add_test(suite, "test_registry_stats_json_format", test_registry_stats_json_format);
  valk_testsuite_add_test(suite, "test_registry_stats_json_small_buffer", test_registry_stats_json_small_buffer);
  valk_testsuite_add_test(suite, "test_registry_stream_count_empty", test_registry_stream_count_empty);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_empty", test_registry_find_by_stream_empty);
  valk_testsuite_add_test(suite, "test_registry_stats_json_all_fields", test_registry_stats_json_all_fields);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_empty", test_registry_unsubscribe_empty);
  valk_testsuite_add_test(suite, "test_registry_stats_json_large_values", test_registry_stats_json_large_values);
  valk_testsuite_add_test(suite, "test_registry_stats_json_exact_buffer_size", test_registry_stats_json_exact_buffer_size);
  valk_testsuite_add_test(suite, "test_registry_stats_json_timer_false", test_registry_stats_json_timer_false);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_nonexistent_handle", test_registry_unsubscribe_nonexistent_handle);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_not_found", test_registry_find_by_stream_not_found);
  valk_testsuite_add_test(suite, "test_registry_stream_count_after_init", test_registry_stream_count_after_init);
  valk_testsuite_add_test(suite, "test_registry_stats_json_boundary", test_registry_stats_json_boundary);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null_data_prd", test_registry_subscribe_null_data_prd);
  valk_testsuite_add_test(suite, "test_registry_timer_operations_uninitialized", test_registry_timer_operations_uninitialized);
  valk_testsuite_add_test(suite, "test_subscription_types_all", test_subscription_types_all);
  valk_testsuite_add_test(suite, "test_registry_stats_json_minimum_valid", test_registry_stats_json_minimum_valid);
#else
  valk_testsuite_add_test(suite, "test_sse_registry_disabled", test_sse_registry_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
