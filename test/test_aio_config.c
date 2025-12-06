#include "testing.h"
#include "aio.h"
#include "common.h"
#include <stdio.h>
#include <stdint.h>

// NOTE: This test file is prepared for the AIO_CONFIG_PLAN.md implementation.
// Tests are currently skipped until the plan is fully implemented in aio.h and aio_uv.c.
// See docs/AIO_CONFIG_PLAN.md for details on the planned configuration system.

// Test that default configuration is correctly set
void test_config_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_system_config_default();

  // Current implementation - test what exists now
  VALK_TEST_ASSERT(cfg.arena_pool_size == 256,
                   "Default arena_pool_size should be 256, got %u", cfg.arena_pool_size);
  VALK_TEST_ASSERT(cfg.arena_size == 4 * 1024 * 1024,
                   "Default arena_size should be 4MB, got %zu", cfg.arena_size);
  VALK_TEST_ASSERT(cfg.tcp_buffer_pool_size == 2048,
                   "Default tcp_buffer_pool_size should be 2048, got %u", cfg.tcp_buffer_pool_size);

  // TODO(networking): Once AIO_CONFIG_PLAN.md is implemented, uncomment these tests:
  //
  // Apply default resolution
  // valk_aio_system_config_resolve(&cfg);
  //
  // Primary parameters - defaults from plan
  // VALK_TEST_ASSERT(cfg.max_connections == 100,
  //                  "Default max_connections should be 100, got %u", cfg.max_connections);
  // VALK_TEST_ASSERT(cfg.max_concurrent_streams == 100,
  //                  "Default max_concurrent_streams should be 100, got %u", cfg.max_concurrent_streams);
  //
  // Derived values - formulas from plan:
  // tcp_buffer_pool_size = max_connections × (2 + max_concurrent_streams / 8)
  // = 100 × (2 + 100/8) = 100 × 14.5 = 1450
  // VALK_TEST_ASSERT(cfg.tcp_buffer_pool_size == 1450,
  //                  "Default tcp_buffer_pool_size should be 1450, got %u", cfg.tcp_buffer_pool_size);
  //
  // arena_pool_size = max_connections × 2 = 100 × 2 = 200
  // VALK_TEST_ASSERT(cfg.arena_pool_size == 200,
  //                  "Default arena_pool_size should be 200, got %u", cfg.arena_pool_size);
  //
  // Memory sizing
  // VALK_TEST_ASSERT(cfg.arena_size == 64 * 1024 * 1024,
  //                  "Default arena_size should be 64MB, got %zu", cfg.arena_size);
  // VALK_TEST_ASSERT(cfg.max_request_body_size == 8 * 1024 * 1024,
  //                  "Default max_request_body_size should be 8MB, got %zu", cfg.max_request_body_size);

  VALK_PASS();
}

// Test auto-derivation with custom streams
void test_config_derivation_streams(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};

  // Set primary parameters (from plan - not yet implemented)
  // cfg.max_connections = 500;
  // cfg.max_concurrent_streams = 50;

  // valk_aio_system_config_resolve(&cfg);

  // Expected: tcp_buffer_pool_size = 500 × (2 + 50/8) = 500 × 8.25 = 4125
  // VALK_TEST_ASSERT(cfg.tcp_buffer_pool_size == 4125,
  //                  "tcp_buffer_pool_size should be 4125, got %u", cfg.tcp_buffer_pool_size);

  // Expected: arena_pool_size = 500 × 2 = 1000
  // VALK_TEST_ASSERT(cfg.arena_pool_size == 1000,
  //                  "arena_pool_size should be 1000, got %u", cfg.arena_pool_size);

  // Skip this test until config resolution is implemented
  VALK_SKIP("Config resolution not yet implemented");
}

// Test that explicit overrides are preserved
void test_config_override(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};

  // Set primary parameter and explicit override (from plan - not yet implemented)
  // cfg.max_connections = 100;
  // cfg.tcp_buffer_pool_size = 500;  // Override auto-derivation

  // valk_aio_system_config_resolve(&cfg);

  // Should preserve the override
  // VALK_TEST_ASSERT(cfg.tcp_buffer_pool_size == 500,
  //                  "tcp_buffer_pool_size should keep override value 500, got %u", cfg.tcp_buffer_pool_size);

  // Skip this test until config resolution is implemented
  VALK_SKIP("Config resolution not yet implemented");
}

// Test hard limit validation
void test_config_validation_limits(VALK_TEST_ARGS()) {
  VALK_TEST();

  // valk_aio_system_config_t cfg = valk_aio_system_config_default();
  // valk_aio_system_config_resolve(&cfg);

  // Test max_connections bounds (from plan: min=1, max=100,000)
  // cfg.max_connections = 0;
  // const char *err1 = valk_aio_system_config_validate(&cfg);
  // VALK_TEST_ASSERT(err1 != NULL,
  //                  "Validation should fail for max_connections = 0");

  // cfg.max_connections = 100001;
  // const char *err2 = valk_aio_system_config_validate(&cfg);
  // VALK_TEST_ASSERT(err2 != NULL,
  //                  "Validation should fail for max_connections = 100001");

  // cfg.max_connections = 100;
  // const char *err3 = valk_aio_system_config_validate(&cfg);
  // VALK_TEST_ASSERT(err3 == NULL,
  //                  "Validation should pass for max_connections = 100");

  // Skip this test until validation is implemented
  VALK_SKIP("Config validation not yet implemented");
}

// Test relationship validations
void test_config_validation_relationships(VALK_TEST_ARGS()) {
  VALK_TEST();

  // valk_aio_system_config_t cfg = valk_aio_system_config_default();
  // valk_aio_system_config_resolve(&cfg);

  // Test: tcp_buffer_pool_size < max_connections should fail
  // cfg.max_connections = 100;
  // cfg.tcp_buffer_pool_size = 50;
  // const char *err1 = valk_aio_system_config_validate(&cfg);
  // VALK_TEST_ASSERT(err1 != NULL,
  //                  "Validation should fail when tcp_buffer_pool_size < max_connections");

  // Test: tcp_buffer_pool_size >= max_connections should pass
  // cfg.tcp_buffer_pool_size = 100;
  // const char *err2 = valk_aio_system_config_validate(&cfg);
  // VALK_TEST_ASSERT(err2 == NULL,
  //                  "Validation should pass when tcp_buffer_pool_size >= max_connections");

  // Skip this test until validation is implemented
  VALK_SKIP("Config validation not yet implemented");
}

// Test starting system with config
void test_system_start_with_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  // valk_aio_system_config_t cfg = {0};
  // cfg.max_connections = 50;
  // cfg.max_concurrent_streams = 50;

  // valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  // VALK_TEST_ASSERT(sys != NULL,
  //                  "System should start with valid config");

  // Verify config was applied
  // VALK_TEST_ASSERT(sys->config.max_connections == 50,
  //                  "System config max_connections should be 50, got %u", sys->config.max_connections);

  // Expected: tcp_buffer_pool_size = 50 × (2 + 50/8) = 50 × 8.25 = 412
  // VALK_TEST_ASSERT(sys->config.tcp_buffer_pool_size == 412,
  //                  "System config tcp_buffer_pool_size should be 412, got %u", sys->config.tcp_buffer_pool_size);

  // valk_aio_stop(sys);

  // Skip this test until valk_aio_start_with_config is implemented
  VALK_SKIP("valk_aio_start_with_config not yet implemented");
}

// Test that invalid config returns NULL
void test_system_start_invalid_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  // valk_aio_system_config_t cfg = {0};
  // cfg.max_connections = 100;
  // cfg.tcp_buffer_pool_size = 10;  // Invalid: < max_connections

  // valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  // VALK_TEST_ASSERT(sys == NULL,
  //                  "System should fail to start with invalid config");

  // Skip this test until valk_aio_start_with_config is implemented
  VALK_SKIP("valk_aio_start_with_config not yet implemented");
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // Add all test cases from the plan
  valk_testsuite_add_test(suite, "test_config_defaults", test_config_defaults);
  valk_testsuite_add_test(suite, "test_config_derivation_streams", test_config_derivation_streams);
  valk_testsuite_add_test(suite, "test_config_override", test_config_override);
  valk_testsuite_add_test(suite, "test_config_validation_limits", test_config_validation_limits);
  valk_testsuite_add_test(suite, "test_config_validation_relationships", test_config_validation_relationships);
  valk_testsuite_add_test(suite, "test_system_start_with_config", test_system_start_with_config);
  valk_testsuite_add_test(suite, "test_system_start_invalid_config", test_system_start_invalid_config);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
