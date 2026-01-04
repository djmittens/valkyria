#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/aio.h"
#include "../../src/aio/aio_alloc.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_system_config_default(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  ASSERT_EQ(cfg.max_connections, 0);
  ASSERT_EQ(cfg.max_concurrent_streams, 0);
  ASSERT_EQ(cfg.arena_size, 0);

  VALK_PASS();
}

void test_system_config_demo_preset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  ASSERT_EQ(cfg.max_connections, 8);
  ASSERT_EQ(cfg.max_concurrent_streams, 8);
  ASSERT_EQ(cfg.max_handles, 128);
  ASSERT_EQ(cfg.max_servers, 3);
  ASSERT_EQ(cfg.max_clients, 3);
  ASSERT_EQ(cfg.arena_size, 4 * 1024 * 1024);
  ASSERT_EQ(cfg.arena_pool_size, 24);
  ASSERT_EQ(cfg.max_request_body_size, 1 * 1024 * 1024);

  VALK_PASS();
}

void test_system_config_production_preset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_production();
  ASSERT_EQ(cfg.max_connections, 100);
  ASSERT_EQ(cfg.max_concurrent_streams, 100);
  ASSERT_EQ(cfg.max_handles, 4096);
  ASSERT_EQ(cfg.arena_pool_size, 1000);

  VALK_PASS();
}

void test_system_config_minimal_preset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_minimal();
  ASSERT_EQ(cfg.max_connections, 4);
  ASSERT_EQ(cfg.max_concurrent_streams, 4);
  ASSERT_EQ(cfg.max_handles, 64);
  ASSERT_EQ(cfg.arena_size, 1 * 1024 * 1024);

  VALK_PASS();
}

void test_system_config_api_preset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_api();
  ASSERT_EQ(cfg.max_connections, 50);
  ASSERT_EQ(cfg.max_concurrent_streams, 256);
  ASSERT_EQ(cfg.arena_size, 1 * 1024 * 1024);

  VALK_PASS();
}

void test_system_config_large_payload_preset(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_large_payload();
  ASSERT_EQ(cfg.max_connections, 20);
  ASSERT_EQ(cfg.max_concurrent_streams, 16);
  ASSERT_EQ(cfg.arena_size, 64 * 1024 * 1024);
  ASSERT_EQ(cfg.max_request_body_size, 128 * 1024 * 1024);

  VALK_PASS();
}

void test_server_config_default(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http_server_config_t cfg = valk_http_server_config_default();
  ASSERT_EQ(cfg.max_response_body_size, 64 * 1024 * 1024);
  ASSERT_NULL(cfg.error_503_body);
  ASSERT_EQ(cfg.error_503_body_len, 0);
  ASSERT_EQ(cfg.sse_buffer_size, 64 * 1024);
  ASSERT_EQ(cfg.sse_queue_max, 1000);

  VALK_PASS();
}

void test_server_config_demo(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http_server_config_t cfg = valk_http_server_config_demo();
  ASSERT_EQ(cfg.max_response_body_size, 8 * 1024 * 1024);
  ASSERT_EQ(cfg.sse_buffer_size, 32 * 1024);
  ASSERT_EQ(cfg.sse_queue_max, 100);

  VALK_PASS();
}

void test_client_config_default(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http_client_config_t cfg = valk_http_client_config_default();
  ASSERT_EQ(cfg.max_concurrent_streams, 100);
  ASSERT_EQ(cfg.max_response_body_size, 64 * 1024 * 1024);
  ASSERT_EQ(cfg.connect_timeout_ms, 30000);
  ASSERT_EQ(cfg.request_timeout_ms, 60000);
  ASSERT_EQ(cfg.max_idle_connections, 0);
  ASSERT_EQ(cfg.keepalive_ms, 0);

  VALK_PASS();
}

void test_config_validate_demo(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NULL(err);

  VALK_PASS();
}

void test_config_validate_production(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_production();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NULL(err);

  VALK_PASS();
}

void test_config_validate_api_resolved(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_api();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NULL(err);

  VALK_PASS();
}

void test_config_validate_zero_connections_fails(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  cfg.max_connections = 0;

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "max_connections");

  VALK_PASS();
}

void test_config_validate_zero_streams_fails(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  cfg.max_concurrent_streams = 0;

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "max_concurrent_streams");

  VALK_PASS();
}

void test_config_validate_zero_arena_size_fails(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  cfg.arena_size = 0;

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "arena_size");

  VALK_PASS();
}

void test_config_validate_invalid_watermarks(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.95f;
  cfg.buffer_critical_watermark = 0.80f;
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, -1);

  VALK_PASS();
}

void test_config_resolve_fills_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  ASSERT_GT(cfg.max_connections, 0);
  ASSERT_GT(cfg.max_concurrent_streams, 0);
  ASSERT_GT(cfg.arena_size, 0);
  ASSERT_GT(cfg.tcp_buffer_pool_size, 0);
  ASSERT_GT(cfg.arena_pool_size, 0);

  VALK_PASS();
}

void test_config_resolve_respects_custom_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  cfg.max_connections = 50;
  cfg.max_concurrent_streams = 64;
  cfg.arena_size = 8 * 1024 * 1024;

  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  ASSERT_EQ(cfg.max_connections, 50);
  ASSERT_EQ(cfg.max_concurrent_streams, 64);
  ASSERT_EQ(cfg.arena_size, 8 * 1024 * 1024);

  VALK_PASS();
}

void test_aio_active_system_initially_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  // This test was checking for a global that no longer exists
  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
void test_owner_registry_null_system(VALK_TEST_ARGS()) {
  VALK_TEST();

  u16 idx = valk_owner_register(nullptr, "test", 0, nullptr);
  ASSERT_EQ(idx, UINT16_MAX);

  const char *name = valk_owner_get_name(nullptr, 0);
  ASSERT_NULL(name);

  size_t count = valk_owner_get_count(nullptr);
  ASSERT_EQ(count, 0);

  VALK_PASS();
}

void test_aio_get_metrics_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t *metrics = valk_aio_get_metrics(nullptr);
  ASSERT_NULL(metrics);

  VALK_PASS();
}

void test_aio_get_system_stats_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_stats_t *stats = valk_aio_get_system_stats(nullptr);
  ASSERT_NULL(stats);

  VALK_PASS();
}

void test_aio_get_http_clients_registry_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http_clients_registry_t *registry = valk_aio_get_http_clients_registry(nullptr);
  ASSERT_NULL(registry);

  VALK_PASS();
}

void test_aio_get_gc_heap_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_aio_get_gc_heap(nullptr);
  ASSERT_NULL(heap);

  VALK_PASS();
}

void test_aio_get_scratch_arena_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = valk_aio_get_scratch_arena(nullptr);
  ASSERT_NULL(arena);

  VALK_PASS();
}

void test_aio_get_tcp_buffer_slab_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_aio_get_tcp_buffer_slab(nullptr);
  ASSERT_NULL(slab);

  VALK_PASS();
}
#endif

void test_aio_get_event_loop_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  struct uv_loop_s *loop = valk_aio_get_event_loop(nullptr);
  ASSERT_NULL(loop);

  VALK_PASS();
}

void test_aio_get_name_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *name = valk_aio_get_name(nullptr);
  ASSERT_STR_EQ(name, "unknown");

  VALK_PASS();
}

void test_aio_set_name_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_set_name(nullptr, "test");
  VALK_PASS();
}

void test_aio_is_shutting_down_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool result = valk_aio_is_shutting_down(nullptr);
  ASSERT_TRUE(result);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_system_config_default", test_system_config_default);
  valk_testsuite_add_test(suite, "test_system_config_demo_preset", test_system_config_demo_preset);
  valk_testsuite_add_test(suite, "test_system_config_production_preset", test_system_config_production_preset);
  valk_testsuite_add_test(suite, "test_system_config_minimal_preset", test_system_config_minimal_preset);
  valk_testsuite_add_test(suite, "test_system_config_api_preset", test_system_config_api_preset);
  valk_testsuite_add_test(suite, "test_system_config_large_payload_preset", test_system_config_large_payload_preset);
  valk_testsuite_add_test(suite, "test_server_config_default", test_server_config_default);
  valk_testsuite_add_test(suite, "test_server_config_demo", test_server_config_demo);
  valk_testsuite_add_test(suite, "test_client_config_default", test_client_config_default);
  valk_testsuite_add_test(suite, "test_config_validate_demo", test_config_validate_demo);
  valk_testsuite_add_test(suite, "test_config_validate_production", test_config_validate_production);
  valk_testsuite_add_test(suite, "test_config_validate_api_resolved", test_config_validate_api_resolved);
  valk_testsuite_add_test(suite, "test_config_validate_zero_connections_fails", test_config_validate_zero_connections_fails);
  valk_testsuite_add_test(suite, "test_config_validate_zero_streams_fails", test_config_validate_zero_streams_fails);
  valk_testsuite_add_test(suite, "test_config_validate_zero_arena_size_fails", test_config_validate_zero_arena_size_fails);
  valk_testsuite_add_test(suite, "test_config_validate_invalid_watermarks", test_config_validate_invalid_watermarks);
  valk_testsuite_add_test(suite, "test_config_resolve_fills_defaults", test_config_resolve_fills_defaults);
  valk_testsuite_add_test(suite, "test_config_resolve_respects_custom_values", test_config_resolve_respects_custom_values);
  valk_testsuite_add_test(suite, "test_aio_active_system_initially_null", test_aio_active_system_initially_null);
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_owner_registry_null_system", test_owner_registry_null_system);
  valk_testsuite_add_test(suite, "test_aio_get_metrics_null", test_aio_get_metrics_null);
  valk_testsuite_add_test(suite, "test_aio_get_system_stats_null", test_aio_get_system_stats_null);
  valk_testsuite_add_test(suite, "test_aio_get_http_clients_registry_null", test_aio_get_http_clients_registry_null);
  valk_testsuite_add_test(suite, "test_aio_get_gc_heap_null", test_aio_get_gc_heap_null);
  valk_testsuite_add_test(suite, "test_aio_get_scratch_arena_null", test_aio_get_scratch_arena_null);
  valk_testsuite_add_test(suite, "test_aio_get_tcp_buffer_slab_null", test_aio_get_tcp_buffer_slab_null);
#endif
  valk_testsuite_add_test(suite, "test_aio_get_event_loop_null", test_aio_get_event_loop_null);
  valk_testsuite_add_test(suite, "test_aio_get_name_null", test_aio_get_name_null);
  valk_testsuite_add_test(suite, "test_aio_set_name_null", test_aio_set_name_null);
  valk_testsuite_add_test(suite, "test_aio_is_shutting_down_null", test_aio_is_shutting_down_null);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
