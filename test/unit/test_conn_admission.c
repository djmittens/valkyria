#include "../testing.h"
#include "../../src/aio/http2/overload/aio_overload_admission.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static valk_aio_system_t *create_test_system_with_slabs(sz slab_item_size, sz slab_num_items) {
  valk_aio_system_t *sys = calloc(1, sizeof(valk_aio_system_t));
  sys->tcpBufferSlab = valk_slab_new(slab_item_size, slab_num_items);
  sys->httpStreamArenas = valk_slab_new(slab_item_size, slab_num_items);
  sys->handleSlab = valk_slab_new(slab_item_size, slab_num_items);
  valk_backpressure_list_init(&sys->backpressure, 1000, 30000);
  return sys;
}

static void free_test_system_with_slabs(valk_aio_system_t *sys) {
  if (sys->tcpBufferSlab) valk_slab_free(sys->tcpBufferSlab);
  if (sys->httpStreamArenas) valk_slab_free(sys->httpStreamArenas);
  if (sys->handleSlab) valk_slab_free(sys->handleSlab);
  free(sys);
}

static valk_aio_handle_t *create_test_handle(u64 backpressure_start_time) {
  valk_aio_handle_t *h = calloc(1, sizeof(valk_aio_handle_t));
  h->http.backpressure_start_time = backpressure_start_time;
  h->http.backpressure_next = nullptr;
  return h;
}

static void free_test_handle(valk_aio_handle_t *h) {
  free(h);
}

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
    .handle_slab_usage = 0.5f,
  };

  valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &state);

  ASSERT_TRUE(result.accept);
  ASSERT_EQ(result.level, VALK_PRESSURE_NORMAL);

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

void test_admission_snapshot_empty_slabs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_system_with_slabs(64, 10);

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_DOUBLE_EQ(state.tcp_write_slab_usage, 0.0f, 0.001f);
  ASSERT_DOUBLE_EQ(state.arena_slab_usage, 0.0f, 0.001f);
  ASSERT_DOUBLE_EQ(state.handle_slab_usage, 0.0f, 0.001f);
  ASSERT_EQ(state.backpressure_queue_len, 0);
  ASSERT_EQ(state.oldest_backpressure_age_ms, 0);

  free_test_system_with_slabs(sys);
  VALK_PASS();
}

void test_admission_snapshot_partial_slab_usage(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_system_with_slabs(64, 10);

  valk_slab_item_t *items[5];
  for (int i = 0; i < 5; i++) {
    items[i] = valk_slab_aquire(sys->tcpBufferSlab);
  }

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_DOUBLE_EQ(state.tcp_write_slab_usage, 0.5f, 0.001f);
  ASSERT_DOUBLE_EQ(state.arena_slab_usage, 0.0f, 0.001f);

  for (int i = 0; i < 5; i++) {
    valk_slab_release(sys->tcpBufferSlab, items[i]);
  }

  free_test_system_with_slabs(sys);
  VALK_PASS();
}

void test_admission_snapshot_full_slab_usage(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_system_with_slabs(64, 10);

  valk_slab_item_t *items[10];
  for (int i = 0; i < 10; i++) {
    items[i] = valk_slab_aquire(sys->tcpBufferSlab);
  }

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_DOUBLE_EQ(state.tcp_write_slab_usage, 1.0f, 0.001f);

  for (int i = 0; i < 10; i++) {
    valk_slab_release(sys->tcpBufferSlab, items[i]);
  }

  free_test_system_with_slabs(sys);
  VALK_PASS();
}

void test_admission_snapshot_with_backpressure_list(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_system_with_slabs(64, 10);

  valk_aio_handle_t *h1 = create_test_handle(500);
  valk_aio_handle_t *h2 = create_test_handle(300);
  valk_aio_handle_t *h3 = create_test_handle(800);

  sys->backpressure.head = h1;
  h1->http.backpressure_next = h2;
  h2->http.backpressure_next = h3;
  h3->http.backpressure_next = nullptr;
  sys->backpressure.size = 3;

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_EQ(state.backpressure_queue_len, 3);
  ASSERT_EQ(state.oldest_backpressure_age_ms, 700);

  free_test_handle(h1);
  free_test_handle(h2);
  free_test_handle(h3);
  free_test_system_with_slabs(sys);
  VALK_PASS();
}

void test_admission_snapshot_backpressure_future_timestamp(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_system_with_slabs(64, 10);

  valk_aio_handle_t *h1 = create_test_handle(2000);

  sys->backpressure.head = h1;
  h1->http.backpressure_next = nullptr;
  sys->backpressure.size = 1;

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_EQ(state.backpressure_queue_len, 1);
  ASSERT_EQ(state.oldest_backpressure_age_ms, 0);

  free_test_handle(h1);
  free_test_system_with_slabs(sys);
  VALK_PASS();
}

void test_admission_snapshot_backpressure_zero_start_time(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_system_with_slabs(64, 10);

  valk_aio_handle_t *h1 = create_test_handle(0);

  sys->backpressure.head = h1;
  h1->http.backpressure_next = nullptr;
  sys->backpressure.size = 1;

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_EQ(state.backpressure_queue_len, 1);
  ASSERT_EQ(state.oldest_backpressure_age_ms, 0);

  free_test_handle(h1);
  free_test_system_with_slabs(sys);
  VALK_PASS();
}

void test_admission_snapshot_null_slabs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = calloc(1, sizeof(valk_aio_system_t));
  sys->tcpBufferSlab = nullptr;
  sys->httpStreamArenas = nullptr;
  sys->handleSlab = nullptr;

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_DOUBLE_EQ(state.tcp_write_slab_usage, 0.0f, 0.001f);
  ASSERT_DOUBLE_EQ(state.arena_slab_usage, 0.0f, 0.001f);
  ASSERT_DOUBLE_EQ(state.handle_slab_usage, 0.0f, 0.001f);

  free(sys);
  VALK_PASS();
}

void test_admission_seed_null_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_seed(nullptr, 42);

  VALK_PASS();
}

void test_admission_init_from_config_null_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_init_from_config(nullptr, 0.8f, 0.9f, 10000);

  VALK_PASS();
}

void test_admission_init_from_config_zero_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init_from_config(&ctx, 0.0f, 0.0f, 0);

  ASSERT_DOUBLE_EQ(ctx.config.high_watermark, 0.85f, 0.001f);
  ASSERT_DOUBLE_EQ(ctx.config.critical_watermark, 0.95f, 0.001f);

  VALK_PASS();
}

void test_admission_check_reason_strings(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_pressure_state_t critical_state = {
    .tcp_write_slab_usage = 0.96f,
    .arena_slab_usage = 0.4f,
    .handle_slab_usage = 0.5f,
  };

  valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &critical_state);
  ASSERT_FALSE(result.accept);
  ASSERT_TRUE(strcmp(result.reason, "critical pressure") == 0);

  valk_pressure_state_t high_state = {
    .tcp_write_slab_usage = 0.90f,
    .arena_slab_usage = 0.4f,
    .handle_slab_usage = 0.5f,
  };

  result = valk_conn_admission_check(&ctx, &high_state);
  ASSERT_FALSE(result.accept);
  ASSERT_TRUE(strcmp(result.reason, "high pressure") == 0);

  VALK_PASS();
}

void test_admission_probabilistic_shed_reason(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_admission_ctx_t ctx;
  valk_conn_admission_init(&ctx, nullptr);

  valk_pressure_state_t elevated_state = {
    .tcp_write_slab_usage = 0.75f,
    .arena_slab_usage = 0.4f,
    .handle_slab_usage = 0.3f,
  };

  bool found_probabilistic_shed = false;
  for (int i = 0; i < 1000 && !found_probabilistic_shed; i++) {
    valk_conn_admission_result_t result = valk_conn_admission_check(&ctx, &elevated_state);
    if (!result.accept && result.reason && strcmp(result.reason, "probabilistic shed") == 0) {
      found_probabilistic_shed = true;
    }
  }

  ASSERT_TRUE(found_probabilistic_shed);

  VALK_PASS();
}

void test_admission_snapshot_multiple_slabs_different_usage(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = create_test_system_with_slabs(64, 10);

  valk_slab_item_t *tcp_items[3];
  for (int i = 0; i < 3; i++) {
    tcp_items[i] = valk_slab_aquire(sys->tcpBufferSlab);
  }

  valk_slab_item_t *arena_items[7];
  for (int i = 0; i < 7; i++) {
    arena_items[i] = valk_slab_aquire(sys->httpStreamArenas);
  }

  valk_slab_item_t *handle_item = valk_slab_aquire(sys->handleSlab);

  valk_pressure_state_t state = valk_conn_admission_snapshot(sys, 1000);

  ASSERT_DOUBLE_EQ(state.tcp_write_slab_usage, 0.3f, 0.001f);
  ASSERT_DOUBLE_EQ(state.arena_slab_usage, 0.7f, 0.001f);
  ASSERT_DOUBLE_EQ(state.handle_slab_usage, 0.1f, 0.001f);

  for (int i = 0; i < 3; i++) {
    valk_slab_release(sys->tcpBufferSlab, tcp_items[i]);
  }
  for (int i = 0; i < 7; i++) {
    valk_slab_release(sys->httpStreamArenas, arena_items[i]);
  }
  valk_slab_release(sys->handleSlab, handle_item);

  free_test_system_with_slabs(sys);
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
  valk_testsuite_add_test(suite, "test_admission_snapshot_empty_slabs", test_admission_snapshot_empty_slabs);
  valk_testsuite_add_test(suite, "test_admission_snapshot_partial_slab_usage", test_admission_snapshot_partial_slab_usage);
  valk_testsuite_add_test(suite, "test_admission_snapshot_full_slab_usage", test_admission_snapshot_full_slab_usage);
  valk_testsuite_add_test(suite, "test_admission_snapshot_with_backpressure_list", test_admission_snapshot_with_backpressure_list);
  valk_testsuite_add_test(suite, "test_admission_snapshot_backpressure_future_timestamp", test_admission_snapshot_backpressure_future_timestamp);
  valk_testsuite_add_test(suite, "test_admission_snapshot_backpressure_zero_start_time", test_admission_snapshot_backpressure_zero_start_time);
  valk_testsuite_add_test(suite, "test_admission_snapshot_null_slabs", test_admission_snapshot_null_slabs);
  valk_testsuite_add_test(suite, "test_admission_seed_null_ctx", test_admission_seed_null_ctx);
  valk_testsuite_add_test(suite, "test_admission_init_from_config_null_ctx", test_admission_init_from_config_null_ctx);
  valk_testsuite_add_test(suite, "test_admission_init_from_config_zero_values", test_admission_init_from_config_zero_values);
  valk_testsuite_add_test(suite, "test_admission_check_reason_strings", test_admission_check_reason_strings);
  valk_testsuite_add_test(suite, "test_admission_probabilistic_shed_reason", test_admission_probabilistic_shed_reason);
  valk_testsuite_add_test(suite, "test_admission_snapshot_multiple_slabs_different_usage", test_admission_snapshot_multiple_slabs_different_usage);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
