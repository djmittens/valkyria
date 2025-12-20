#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/common.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef VALK_METRICS_ENABLED
#include "../../src/aio.h"
#include "../../src/aio_sse_stream_registry.h"

static valk_aio_system_t *create_test_aio_system(void) {
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  return valk_aio_start_with_config(&cfg);
}

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

void test_registry_timer_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_timer_start(NULL);
  valk_sse_registry_timer_stop(NULL);

  VALK_PASS();
}

void test_registry_subscribe_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;
  
  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      NULL, NULL, NULL, 0, VALK_SSE_SUB_DIAGNOSTICS, &data_prd);
  VALK_TEST_ASSERT(entry == NULL, "NULL registry should return NULL");

  VALK_PASS();
}

void test_registry_subscribe_null_data_prd(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  VALK_TEST_ASSERT(registry != NULL, "Registry should exist");

  valk_sse_stream_entry_t *entry = valk_sse_registry_subscribe(
      registry, NULL, NULL, 0, VALK_SSE_SUB_DIAGNOSTICS, NULL);
  VALK_TEST_ASSERT(entry == NULL, "NULL data_prd should return NULL");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_unsubscribe_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_registry_unsubscribe(NULL, NULL);

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  valk_sse_registry_unsubscribe(registry, NULL);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_unsubscribe_connection_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t count = valk_sse_registry_unsubscribe_connection(NULL, NULL);
  VALK_TEST_ASSERT(count == 0, "NULL registry should return 0");

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  count = valk_sse_registry_unsubscribe_connection(registry, NULL);
  VALK_TEST_ASSERT(count == 0, "NULL handle should return 0");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_find_by_stream_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_entry_t *entry = valk_sse_registry_find_by_stream(NULL, NULL, 0);
  VALK_TEST_ASSERT(entry == NULL, "NULL registry should return NULL");

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  entry = valk_sse_registry_find_by_stream(registry, NULL, 999);
  VALK_TEST_ASSERT(entry == NULL, "Non-existent stream should return NULL");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_stream_count_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t count = valk_sse_registry_stream_count(NULL);
  VALK_TEST_ASSERT(count == 0, "NULL registry should return 0");

  VALK_PASS();
}

void test_registry_stats_json_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t len = valk_sse_registry_stats_json(NULL, NULL, 0);
  VALK_TEST_ASSERT(len == 0, "NULL args should return 0");

  char buf[256];
  len = valk_sse_registry_stats_json(NULL, buf, sizeof(buf));
  VALK_TEST_ASSERT(len == 0, "NULL registry should return 0");

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  len = valk_sse_registry_stats_json(registry, NULL, 0);
  VALK_TEST_ASSERT(len == 0, "NULL buf should return 0");

  len = valk_sse_registry_stats_json(registry, buf, 0);
  VALK_TEST_ASSERT(len == 0, "Zero buf_size should return 0");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_stats_json_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);

  char tiny_buf[5];
  size_t len = valk_sse_registry_stats_json(registry, tiny_buf, sizeof(tiny_buf));
  VALK_TEST_ASSERT(len == 0, "Tiny buffer should return 0");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_stats_json_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);

  char buf[256];
  size_t len = valk_sse_registry_stats_json(registry, buf, sizeof(buf));
  VALK_TEST_ASSERT(len > 0, "Should succeed with proper buffer");
  VALK_TEST_ASSERT(strstr(buf, "\"stream_count\":0") != NULL, "Should show 0 streams");
  VALK_TEST_ASSERT(strstr(buf, "\"timer_running\":") != NULL, "Should have timer_running field");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_timer_start_already_running(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);

  valk_sse_registry_timer_start(registry);

  char buf[256];
  valk_sse_registry_stats_json(registry, buf, sizeof(buf));
  VALK_TEST_ASSERT(strstr(buf, "\"timer_running\":true") != NULL, "Timer should be running");

  valk_sse_registry_timer_start(registry);
  valk_sse_registry_stats_json(registry, buf, sizeof(buf));
  VALK_TEST_ASSERT(strstr(buf, "\"timer_running\":true") != NULL, "Timer still should be running");

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_timer_stop_not_running(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);

  valk_sse_registry_timer_stop(registry);
  valk_sse_registry_timer_stop(registry);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_registry_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_aio_system();
  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);

  VALK_TEST_ASSERT(valk_sse_registry_stream_count(registry) == 0, "Initial count should be 0");

  valk_sse_registry_timer_start(registry);
  valk_sse_registry_timer_stop(registry);

  valk_aio_stop(sys);
  VALK_PASS();
}

void test_subscription_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_SSE_SUB_DIAGNOSTICS == 0, "DIAGNOSTICS should be 0");
  VALK_TEST_ASSERT(VALK_SSE_SUB_METRICS_ONLY == 1, "METRICS_ONLY should be 1");
  VALK_TEST_ASSERT(VALK_SSE_SUB_MEMORY_ONLY == 2, "MEMORY_ONLY should be 2");

  VALK_PASS();
}

#else

void test_sse_registry_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("SSE registry requires VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_registry_init_null_args", test_registry_init_null_args);
  valk_testsuite_add_test(suite, "test_registry_shutdown_null", test_registry_shutdown_null);
  valk_testsuite_add_test(suite, "test_registry_timer_null", test_registry_timer_null);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null_args", test_registry_subscribe_null_args);
  valk_testsuite_add_test(suite, "test_registry_subscribe_null_data_prd", test_registry_subscribe_null_data_prd);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_null_args", test_registry_unsubscribe_null_args);
  valk_testsuite_add_test(suite, "test_registry_unsubscribe_connection_null", test_registry_unsubscribe_connection_null);
  valk_testsuite_add_test(suite, "test_registry_find_by_stream_null", test_registry_find_by_stream_null);
  valk_testsuite_add_test(suite, "test_registry_stream_count_null", test_registry_stream_count_null);
  valk_testsuite_add_test(suite, "test_registry_stats_json_null_args", test_registry_stats_json_null_args);
  valk_testsuite_add_test(suite, "test_registry_stats_json_small_buffer", test_registry_stats_json_small_buffer);
  valk_testsuite_add_test(suite, "test_registry_stats_json_success", test_registry_stats_json_success);
  valk_testsuite_add_test(suite, "test_registry_timer_start_already_running", test_registry_timer_start_already_running);
  valk_testsuite_add_test(suite, "test_registry_timer_stop_not_running", test_registry_timer_stop_not_running);
  valk_testsuite_add_test(suite, "test_registry_lifecycle", test_registry_lifecycle);
  valk_testsuite_add_test(suite, "test_subscription_types", test_subscription_types);
#else
  valk_testsuite_add_test(suite, "test_sse_registry_disabled", test_sse_registry_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
