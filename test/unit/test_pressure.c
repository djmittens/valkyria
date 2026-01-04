#include "../testing.h"
#include "../../src/aio/http2/overload/aio_overload_state.h"
#include "../../src/memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_config_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_config_t cfg = valk_pressure_config_default();

  ASSERT_DOUBLE_EQ(cfg.high_watermark, 0.85f, 0.001f);
  ASSERT_DOUBLE_EQ(cfg.critical_watermark, 0.95f, 0.001f);
  ASSERT_EQ(cfg.backpressure_max, 1000);
  ASSERT_EQ(cfg.backpressure_timeout_ms, 30000);

  VALK_PASS();
}

void test_normal_accepts_all(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.3f,
    .arena_slab_usage = 0.4f,
    .handle_slab_usage = 0.5f,
    .active_connections = 10,
    .backpressure_queue_len = 0,
    .oldest_backpressure_age_ms = 0,
  };
  valk_pressure_config_t cfg = valk_pressure_config_default();

  valk_pressure_decision_t d = valk_pressure_evaluate(&state, &cfg);

  ASSERT_EQ(d.level, VALK_PRESSURE_NORMAL);
  ASSERT_TRUE(d.accept_connection);
  ASSERT_DOUBLE_EQ(d.connection_shed_probability, 0.0f, 0.001f);
  ASSERT_TRUE(d.accept_stream);
  ASSERT_FALSE(d.drop_oldest_backpressure);

  VALK_PASS();
}

void test_elevated_gradual_shedding(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.75f,
    .arena_slab_usage = 0.4f,
    .handle_slab_usage = 0.3f,
    .active_connections = 50,
    .backpressure_queue_len = 0,
    .oldest_backpressure_age_ms = 0,
  };
  valk_pressure_config_t cfg = valk_pressure_config_default();

  valk_pressure_decision_t d = valk_pressure_evaluate(&state, &cfg);

  ASSERT_EQ(d.level, VALK_PRESSURE_ELEVATED);
  ASSERT_TRUE(d.accept_connection);
  ASSERT_GT(d.connection_shed_probability, 0.0f);
  ASSERT_LT(d.connection_shed_probability, 0.35f);
  ASSERT_TRUE(d.accept_stream);

  VALK_PASS();
}

void test_high_rejects_connections(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.90f,
    .arena_slab_usage = 0.4f,
    .handle_slab_usage = 0.3f,
    .active_connections = 80,
    .backpressure_queue_len = 100,
    .oldest_backpressure_age_ms = 5000,
  };
  valk_pressure_config_t cfg = valk_pressure_config_default();

  valk_pressure_decision_t d = valk_pressure_evaluate(&state, &cfg);

  ASSERT_EQ(d.level, VALK_PRESSURE_HIGH);
  ASSERT_FALSE(d.accept_connection);
  ASSERT_DOUBLE_EQ(d.connection_shed_probability, 1.0f, 0.001f);

  VALK_PASS();
}

void test_critical_drops_queued(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.96f,
    .arena_slab_usage = 0.97f,
    .handle_slab_usage = 0.95f,
    .active_connections = 100,
    .backpressure_queue_len = 500,
    .oldest_backpressure_age_ms = 25000,
  };
  valk_pressure_config_t cfg = valk_pressure_config_default();

  valk_pressure_decision_t d = valk_pressure_evaluate(&state, &cfg);

  ASSERT_EQ(d.level, VALK_PRESSURE_CRITICAL);
  ASSERT_FALSE(d.accept_connection);
  ASSERT_DOUBLE_EQ(d.connection_shed_probability, 1.0f, 0.001f);
  ASSERT_TRUE(d.drop_oldest_backpressure);
  ASSERT_FALSE(d.accept_stream);

  VALK_PASS();
}

void test_arena_pressure_blocks_streams(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.3f,
    .arena_slab_usage = 0.96f,
    .handle_slab_usage = 0.3f,
    .active_connections = 50,
    .backpressure_queue_len = 0,
    .oldest_backpressure_age_ms = 0,
  };
  valk_pressure_config_t cfg = valk_pressure_config_default();

  valk_pressure_decision_t d = valk_pressure_evaluate(&state, &cfg);

  ASSERT_FALSE(d.accept_stream);

  VALK_PASS();
}

void test_timeout_triggers_drop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.3f,
    .arena_slab_usage = 0.4f,
    .handle_slab_usage = 0.3f,
    .active_connections = 10,
    .backpressure_queue_len = 10,
    .oldest_backpressure_age_ms = 35000,
  };
  valk_pressure_config_t cfg = valk_pressure_config_default();

  valk_pressure_decision_t d = valk_pressure_evaluate(&state, &cfg);

  ASSERT_TRUE(d.drop_oldest_backpressure);

  VALK_PASS();
}

void test_tcp_buffer_determines_connection_level(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state_high_tcp = {
    .tcp_write_slab_usage = 0.96f,
    .arena_slab_usage = 0.3f,
    .handle_slab_usage = 0.3f,
    .active_connections = 10,
    .backpressure_queue_len = 0,
    .oldest_backpressure_age_ms = 0,
  };

  valk_pressure_state_t state_low_tcp_high_others = {
    .tcp_write_slab_usage = 0.3f,
    .arena_slab_usage = 0.96f,
    .handle_slab_usage = 0.96f,
    .active_connections = 10,
    .backpressure_queue_len = 0,
    .oldest_backpressure_age_ms = 0,
  };

  valk_pressure_config_t cfg = valk_pressure_config_default();

  valk_pressure_decision_t d1 = valk_pressure_evaluate(&state_high_tcp, &cfg);
  valk_pressure_decision_t d2 = valk_pressure_evaluate(&state_low_tcp_high_others, &cfg);

  ASSERT_EQ(d1.level, VALK_PRESSURE_CRITICAL);
  ASSERT_EQ(d2.level, VALK_PRESSURE_NORMAL);
  ASSERT_TRUE(d2.accept_connection);

  VALK_PASS();
}

void test_shed_probability_in_range(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_config_t cfg = valk_pressure_config_default();

  for (int i = 0; i <= 100; i++) {
    valk_pressure_state_t state = {
      .tcp_write_slab_usage = (float)i / 100.0f,
      .arena_slab_usage = 0.0f,
      .handle_slab_usage = 0.0f,
      .active_connections = 10,
      .backpressure_queue_len = 0,
      .oldest_backpressure_age_ms = 0,
    };

    valk_pressure_decision_t d = valk_pressure_evaluate(&state, &cfg);

    ASSERT_GE(d.connection_shed_probability, 0.0f);
    ASSERT_LE(d.connection_shed_probability, 1.0f);
  }

  VALK_PASS();
}

void test_level_str(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_STR_EQ(valk_pressure_level_str(VALK_PRESSURE_NORMAL), "NORMAL");
  ASSERT_STR_EQ(valk_pressure_level_str(VALK_PRESSURE_ELEVATED), "ELEVATED");
  ASSERT_STR_EQ(valk_pressure_level_str(VALK_PRESSURE_HIGH), "HIGH");
  ASSERT_STR_EQ(valk_pressure_level_str(VALK_PRESSURE_CRITICAL), "CRITICAL");
  // NOLINTNEXTLINE(clang-analyzer-optin.core.EnumCastOutOfRange)
  ASSERT_STR_EQ(valk_pressure_level_str((valk_pressure_level_e)999), "UNKNOWN");

  VALK_PASS();
}

int main(int argc, const char *argv[]) {
  (void)argc;
  (void)argv;

  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_config_defaults", test_config_defaults);
  valk_testsuite_add_test(suite, "test_normal_accepts_all", test_normal_accepts_all);
  valk_testsuite_add_test(suite, "test_elevated_gradual_shedding", test_elevated_gradual_shedding);
  valk_testsuite_add_test(suite, "test_high_rejects_connections", test_high_rejects_connections);
  valk_testsuite_add_test(suite, "test_critical_drops_queued", test_critical_drops_queued);
  valk_testsuite_add_test(suite, "test_arena_pressure_blocks_streams", test_arena_pressure_blocks_streams);
  valk_testsuite_add_test(suite, "test_timeout_triggers_drop", test_timeout_triggers_drop);
  valk_testsuite_add_test(suite, "test_tcp_buffer_determines_connection_level", test_tcp_buffer_determines_connection_level);
  valk_testsuite_add_test(suite, "test_shed_probability_in_range", test_shed_probability_in_range);
  valk_testsuite_add_test(suite, "test_level_str", test_level_str);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
