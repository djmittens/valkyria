#include "testing.h"
#include "aio/aio.h"
#include "common.h"
#include "memory.h"
#include <stdio.h>

void test_config_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  valk_aio_system_config_resolve(&cfg);

  VALK_TEST_ASSERT(cfg.max_connections == 100,
                   "Default max_connections should be 100, got %u", cfg.max_connections);
  VALK_TEST_ASSERT(cfg.max_concurrent_streams == 100,
                   "Default max_concurrent_streams should be 100, got %u", cfg.max_concurrent_streams);
  VALK_TEST_ASSERT(cfg.max_connections_per_client == 2,
                   "Default max_connections_per_client should be 2, got %u", cfg.max_connections_per_client);

  size_t server_conns = cfg.max_servers * cfg.max_connections;
  size_t client_conns = cfg.max_clients * cfg.max_connections_per_client;
  u32 expected_tcp = (u32)((server_conns + client_conns) * 4);
  VALK_TEST_ASSERT(cfg.tcp_buffer_pool_size == expected_tcp,
                   "Default tcp_buffer_pool_size should be %u, got %u", expected_tcp, cfg.tcp_buffer_pool_size);

  VALK_TEST_ASSERT(cfg.arena_size == 64 * 1024 * 1024,
                   "Default arena_size should be 64MB, got %zu", cfg.arena_size);
  VALK_TEST_ASSERT(cfg.max_request_body_size == 8 * 1024 * 1024,
                   "Default max_request_body_size should be 8MB, got %zu", cfg.max_request_body_size);

  VALK_TEST_ASSERT(cfg.connection_idle_timeout_ms == 60000,
                   "Default connection_idle_timeout_ms should be 60000, got %u", cfg.connection_idle_timeout_ms);
  VALK_TEST_ASSERT(cfg.maintenance_interval_ms == 1000,
                   "Default maintenance_interval_ms should be 1000, got %u", cfg.maintenance_interval_ms);

  VALK_PASS();
}

void test_config_derivation_streams(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 500;
  cfg.max_concurrent_streams = 50;

  valk_aio_system_config_resolve(&cfg);

  size_t server_conns = cfg.max_servers * cfg.max_connections;
  size_t client_conns = cfg.max_clients * cfg.max_connections_per_client;
  u32 expected_tcp = (u32)((server_conns + client_conns) * 4);
  VALK_TEST_ASSERT(cfg.tcp_buffer_pool_size == expected_tcp,
                   "tcp_buffer_pool_size should be %u, got %u", expected_tcp, cfg.tcp_buffer_pool_size);

  VALK_TEST_ASSERT(cfg.arena_pool_size >= 64 && cfg.arena_pool_size <= 1024,
                   "arena_pool_size should be in range [64, 1024], got %u", cfg.arena_pool_size);

  VALK_PASS();
}

void test_config_override(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 500;

  valk_aio_system_config_resolve(&cfg);

  VALK_TEST_ASSERT(cfg.tcp_buffer_pool_size == 500,
                   "tcp_buffer_pool_size should keep override value 500, got %u", cfg.tcp_buffer_pool_size);

  VALK_PASS();
}

void test_config_validation_limits(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  valk_aio_system_config_resolve(&cfg);

  cfg.max_connections = 0;
  const char *err1 = valk_aio_system_config_validate(&cfg);
  VALK_TEST_ASSERT(err1 != nullptr,
                   "Validation should fail for max_connections = 0");

  cfg.max_connections = 100001;
  const char *err2 = valk_aio_system_config_validate(&cfg);
  VALK_TEST_ASSERT(err2 != nullptr,
                   "Validation should fail for max_connections = 100001");

  cfg.max_connections = 100;
  const char *err3 = valk_aio_system_config_validate(&cfg);
  VALK_TEST_ASSERT(err3 == nullptr,
                   "Validation should pass for max_connections = 100, got: %s", err3 ? err3 : "nullptr");

  VALK_PASS();
}

void test_config_validation_relationships(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  valk_aio_system_config_resolve(&cfg);

  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 50;
  const char *err1 = valk_aio_system_config_validate(&cfg);
  VALK_TEST_ASSERT(err1 != nullptr,
                   "Validation should fail when tcp_buffer_pool_size < max_connections");

  cfg.tcp_buffer_pool_size = 100;
  const char *err2 = valk_aio_system_config_validate(&cfg);
  VALK_TEST_ASSERT(err2 == nullptr,
                   "Validation should pass when tcp_buffer_pool_size >= max_connections, got: %s",
                   err2 ? err2 : "nullptr");

  VALK_PASS();
}

void test_system_start_with_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 50;
  cfg.max_concurrent_streams = 50;

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  VALK_TEST_ASSERT(sys != nullptr,
                   "System should start with valid config");

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_system_start_invalid_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 50;

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  VALK_TEST_ASSERT(sys == nullptr,
                   "System should fail to start with invalid config");

  VALK_PASS();
}

void test_config_presets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t demo = valk_aio_config_demo();
  VALK_TEST_ASSERT(demo.max_connections == 8,
                   "Demo preset max_connections should be 8, got %u", demo.max_connections);

  valk_aio_system_config_t prod = valk_aio_config_production();
  VALK_TEST_ASSERT(prod.max_connections == 100,
                   "Production preset max_connections should be 100, got %u", prod.max_connections);

  valk_aio_system_config_t minimal = valk_aio_config_minimal();
  VALK_TEST_ASSERT(minimal.max_connections == 4,
                   "Minimal preset max_connections should be 4, got %u", minimal.max_connections);

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_config_defaults", test_config_defaults);
  valk_testsuite_add_test(suite, "test_config_derivation_streams", test_config_derivation_streams);
  valk_testsuite_add_test(suite, "test_config_override", test_config_override);
  valk_testsuite_add_test(suite, "test_config_validation_limits", test_config_validation_limits);
  valk_testsuite_add_test(suite, "test_config_validation_relationships", test_config_validation_relationships);
  valk_testsuite_add_test(suite, "test_system_start_with_config", test_system_start_with_config);
  valk_testsuite_add_test(suite, "test_system_start_invalid_config", test_system_start_invalid_config);
  valk_testsuite_add_test(suite, "test_config_presets", test_config_presets);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
