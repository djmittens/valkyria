#include "../testing.h"
#include "../../src/aio/aio_conn_admission.h"
#include "../../src/memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_admission_init_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  ASSERT_DOUBLE_EQ(ctx.config.high_watermark, 0.85f, 0.001f);
  ASSERT_DOUBLE_EQ(ctx.config.critical_watermark, 0.95f, 0.001f);
  ASSERT_NE(ctx.random_state, 0);

  VALK_PASS();
}

void test_admission_init_custom_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_config_t custom = {
    .high_watermark = 0.70f,
    .critical_watermark = 0.90f,
    .backpressure_max = 500,
    .backpressure_timeout_ms = 15000,
    .pending_stream_max = 32,
    .pending_stream_timeout_ms = 5000,
  };

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, &custom);

  ASSERT_DOUBLE_EQ(ctx.config.high_watermark, 0.70f, 0.001f);
  ASSERT_DOUBLE_EQ(ctx.config.critical_watermark, 0.90f, 0.001f);
  ASSERT_EQ(ctx.config.backpressure_max, 500);

  VALK_PASS();
}

void test_admission_init_from_system_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init_from_config(&ctx, 0.80f, 0.92f, 20000);

  ASSERT_DOUBLE_EQ(ctx.config.high_watermark, 0.80f, 0.001f);
  ASSERT_DOUBLE_EQ(ctx.config.critical_watermark, 0.92f, 0.001f);
  ASSERT_EQ(ctx.config.backpressure_timeout_ms, 20000);

  VALK_PASS();
}

void test_admission_check_connection_normal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.3f,
    .arena_slab_usage = 0.4f,
    .pending_stream_usage = 0.2f,
    .handle_slab_usage = 0.5f,
  };

  valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &state);

  ASSERT_TRUE(result.accept);
  ASSERT_EQ(result.level, VALK_PRESSURE_NORMAL);
  ASSERT_TRUE(result.reason == nullptr);

  VALK_PASS();
}

void test_admission_check_connection_critical_rejects(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.96f,
    .arena_slab_usage = 0.4f,
    .pending_stream_usage = 0.2f,
    .handle_slab_usage = 0.5f,
  };

  valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &state);

  ASSERT_FALSE(result.accept);
  ASSERT_EQ(result.level, VALK_PRESSURE_CRITICAL);
  ASSERT_TRUE(result.reason != nullptr);

  VALK_PASS();
}

void test_admission_check_connection_high_rejects(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.90f,
    .arena_slab_usage = 0.4f,
    .pending_stream_usage = 0.2f,
    .handle_slab_usage = 0.5f,
  };

  valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &state);

  ASSERT_FALSE(result.accept);
  ASSERT_EQ(result.level, VALK_PRESSURE_HIGH);

  VALK_PASS();
}

void test_admission_random_deterministic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);
  valk_conn_admission_seed(&ctx, 42);

  float r1 = valk_conn_admission_random(&ctx);
  float r2 = valk_conn_admission_random(&ctx);
  float r3 = valk_conn_admission_random(&ctx);

  valk_conn_admission_seed(&ctx, 42);

  ASSERT_DOUBLE_EQ(valk_conn_admission_random(&ctx), r1, 0.0001f);
  ASSERT_DOUBLE_EQ(valk_conn_admission_random(&ctx), r2, 0.0001f);
  ASSERT_DOUBLE_EQ(valk_conn_admission_random(&ctx), r3, 0.0001f);

  VALK_PASS();
}

void test_admission_random_in_range(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  for (int i = 0; i < 1000; i++) {
    float r = valk_conn_admission_random(&ctx);
    ASSERT_GE(r, 0.0f);
    ASSERT_LT(r, 2.0f);
  }

  VALK_PASS();
}

void test_admission_probabilistic_shedding(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);
  valk_conn_admission_seed(&ctx, 12345);

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.75f,
    .arena_slab_usage = 0.4f,
    .pending_stream_usage = 0.2f,
    .handle_slab_usage = 0.3f,
  };

  int accepted = 0;
  int rejected = 0;

  for (int i = 0; i < 1000; i++) {
    valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &state);
    if (result.accept) {
      accepted++;
    } else {
      rejected++;
    }
  }

  ASSERT_GT(accepted, 0);
  ASSERT_GT(rejected, 0);
  ASSERT_GT(accepted, rejected);

  VALK_PASS();
}

void test_admission_check_stream_normal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.3f,
    .arena_slab_usage = 0.4f,
    .pending_stream_usage = 0.2f,
    .handle_slab_usage = 0.5f,
  };

  valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &state);

  ASSERT_TRUE(result.accept);
  ASSERT_EQ(result.level, VALK_PRESSURE_NORMAL);

  VALK_PASS();
}

void test_admission_check_stream_arena_pressure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_pressure_state_t state = {
    .tcp_write_slab_usage = 0.3f,
    .arena_slab_usage = 0.90f,
    .pending_stream_usage = 0.2f,
    .handle_slab_usage = 0.5f,
  };

  valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &state);

  ASSERT_FALSE(result.accept);
  ASSERT_TRUE(result.reason != nullptr);

  VALK_PASS();
}

void test_admission_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_init(nullptr, nullptr);

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_conn_admission_result_t r1 = valk_conn_admission_check(nullptr, nullptr);
  ASSERT_TRUE(r1.accept);

  valk_conn_admission_result_t r2 = valk_conn_admission_check(&ctx, nullptr);
  ASSERT_TRUE(r2.accept);

  valk_conn_admission_result_t r3 = valk_conn_admission_check(nullptr, nullptr);
  ASSERT_TRUE(r3.accept);

  VALK_PASS();
}

void test_admission_snapshot_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pressure_state_t state = valk_conn_admission_snapshot(nullptr, 1000);

  ASSERT_DOUBLE_EQ(state.tcp_write_slab_usage, 0.0f, 0.001f);
  ASSERT_DOUBLE_EQ(state.arena_slab_usage, 0.0f, 0.001f);
  ASSERT_EQ(state.backpressure_queue_len, 0);

  VALK_PASS();
}

int main(int argc, const char *argv[]) {
  (void)argc;
  (void)argv;

  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_admission_init_defaults", test_admission_init_defaults);
  valk_testsuite_add_test(suite, "test_admission_init_custom_config", test_admission_init_custom_config);
  valk_testsuite_add_test(suite, "test_admission_init_from_system_config", test_admission_init_from_system_config);
  valk_testsuite_add_test(suite, "test_admission_check_connection_normal", test_admission_check_connection_normal);
  valk_testsuite_add_test(suite, "test_admission_check_connection_critical_rejects", test_admission_check_connection_critical_rejects);
  valk_testsuite_add_test(suite, "test_admission_check_connection_high_rejects", test_admission_check_connection_high_rejects);
  valk_testsuite_add_test(suite, "test_admission_random_deterministic", test_admission_random_deterministic);
  valk_testsuite_add_test(suite, "test_admission_random_in_range", test_admission_random_in_range);
  valk_testsuite_add_test(suite, "test_admission_probabilistic_shedding", test_admission_probabilistic_shedding);
  valk_testsuite_add_test(suite, "test_admission_check_stream_normal", test_admission_check_stream_normal);
  valk_testsuite_add_test(suite, "test_admission_check_stream_arena_pressure", test_admission_check_stream_arena_pressure);
  valk_testsuite_add_test(suite, "test_admission_null_args", test_admission_null_args);
  valk_testsuite_add_test(suite, "test_admission_snapshot_null_sys", test_admission_snapshot_null_sys);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
