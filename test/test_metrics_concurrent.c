// test/test_metrics_concurrent.c
// Concurrent/race condition testing for metrics

#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "common.h"
#include "memory.h"
#include "metrics_v2.h"
#include "metrics_delta.h"
#include "testing.h"

// ============================================================================
// Thread Context Structures
// ============================================================================

typedef struct {
  valk_counter_v2_t *counter;
  int iterations;
  int thread_id;
} counter_thread_ctx_t;

typedef struct {
  valk_gauge_v2_t *gauge;
  int iterations;
  int thread_id;
} gauge_thread_ctx_t;

typedef struct {
  valk_histogram_v2_t *histogram;
  int iterations;
  int thread_id;
} histogram_thread_ctx_t;

typedef struct {
  const char *name;
  int iterations;
  int thread_id;
} create_thread_ctx_t;

typedef struct {
  int iterations;
  int thread_id;
} snapshot_thread_ctx_t;

// ============================================================================
// Counter Concurrent Tests
// ============================================================================

static void *counter_increment_many(void *arg) {
  counter_thread_ctx_t *ctx = (counter_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_counter_v2_inc(ctx->counter);
  }

  return nullptr;
}

static void *counter_add_many(void *arg) {
  counter_thread_ctx_t *ctx = (counter_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_counter_v2_add(ctx->counter, ctx->thread_id + 1);
  }

  return nullptr;
}

static void test_counter_concurrent_inc_high_contention(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("high_contention_counter", nullptr, &labels);
  ASSERT_NOT_NULL(c);

  const int NUM_THREADS = 16;
  const int ITERATIONS = 50000;
  pthread_t threads[NUM_THREADS];
  counter_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (counter_thread_ctx_t){
      .counter = c,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, counter_increment_many, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  u64 expected = (u64)NUM_THREADS * ITERATIONS;
  u64 actual = atomic_load(&c->value);
  ASSERT_EQ(actual, expected);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

static void test_counter_concurrent_add_varied(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("varied_add_counter", nullptr, &labels);
  ASSERT_NOT_NULL(c);

  const int NUM_THREADS = 8;
  const int ITERATIONS = 10000;
  pthread_t threads[NUM_THREADS];
  counter_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (counter_thread_ctx_t){
      .counter = c,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, counter_add_many, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  u64 expected = 0;
  for (int i = 0; i < NUM_THREADS; i++) {
    expected += (u64)ITERATIONS * (i + 1);
  }
  u64 actual = atomic_load(&c->value);
  ASSERT_EQ(actual, expected);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Gauge Concurrent Tests
// ============================================================================

static void *gauge_set_many(void *arg) {
  gauge_thread_ctx_t *ctx = (gauge_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_gauge_v2_set(ctx->gauge, ctx->thread_id * 1000 + i);
  }

  return nullptr;
}

static void *gauge_inc_dec_many(void *arg) {
  gauge_thread_ctx_t *ctx = (gauge_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_gauge_v2_inc(ctx->gauge);
    valk_gauge_v2_dec(ctx->gauge);
  }

  return nullptr;
}

static void *gauge_add_many(void *arg) {
  gauge_thread_ctx_t *ctx = (gauge_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_gauge_v2_add(ctx->gauge, 1);
    valk_gauge_v2_add(ctx->gauge, -1);
  }

  return nullptr;
}

static void test_gauge_concurrent_set(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *g = valk_gauge_get_or_create("concurrent_set_gauge", nullptr, &labels);
  ASSERT_NOT_NULL(g);

  const int NUM_THREADS = 8;
  const int ITERATIONS = 10000;
  pthread_t threads[NUM_THREADS];
  gauge_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (gauge_thread_ctx_t){
      .gauge = g,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, gauge_set_many, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  i64 actual = atomic_load(&g->value);
  ASSERT_GE(actual, 0);
  ASSERT_LT(actual, NUM_THREADS * 1000 + ITERATIONS);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

static void test_gauge_concurrent_inc_dec_balanced(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *g = valk_gauge_get_or_create("balanced_gauge", nullptr, &labels);
  ASSERT_NOT_NULL(g);

  valk_gauge_v2_set(g, 0);

  const int NUM_THREADS = 8;
  const int ITERATIONS = 50000;
  pthread_t threads[NUM_THREADS];
  gauge_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (gauge_thread_ctx_t){
      .gauge = g,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, gauge_inc_dec_many, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  i64 actual = atomic_load(&g->value);
  ASSERT_EQ(actual, 0);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

static void test_gauge_concurrent_add_balanced(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *g = valk_gauge_get_or_create("add_balanced_gauge", nullptr, &labels);
  ASSERT_NOT_NULL(g);

  valk_gauge_v2_set(g, 0);

  const int NUM_THREADS = 8;
  const int ITERATIONS = 50000;
  pthread_t threads[NUM_THREADS];
  gauge_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (gauge_thread_ctx_t){
      .gauge = g,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, gauge_add_many, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  i64 actual = atomic_load(&g->value);
  ASSERT_EQ(actual, 0);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Histogram Concurrent Tests
// ============================================================================

static void *histogram_observe_many(void *arg) {
  histogram_thread_ctx_t *ctx = (histogram_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    u64 value = (ctx->thread_id * 10000 + i) % 1000000;
    valk_histogram_v2_observe_us(ctx->histogram, value);
  }

  return nullptr;
}

static void test_histogram_concurrent_observe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  double bounds[] = {0.001, 0.01, 0.1, 0.5, 1.0};
  valk_label_set_v2_t labels = {0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create(
      "concurrent_histogram", nullptr, bounds, 5, &labels);
  ASSERT_NOT_NULL(h);

  const int NUM_THREADS = 8;
  const int ITERATIONS = 10000;
  pthread_t threads[NUM_THREADS];
  histogram_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (histogram_thread_ctx_t){
      .histogram = h,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, histogram_observe_many, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  u64 expected_count = (u64)NUM_THREADS * ITERATIONS;
  u64 actual_count = atomic_load(&h->count);
  ASSERT_EQ(actual_count, expected_count);

  u64 total_bucket_count = 0;
  for (int i = 0; i <= h->bucket_count; i++) {
    total_bucket_count += atomic_load(&h->buckets[i]);
  }
  ASSERT_EQ(total_bucket_count, expected_count);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Concurrent Metric Creation Tests
// ============================================================================

static void *create_counter_many(void *arg) {
  create_thread_ctx_t *ctx = (create_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    char name[64];
    snprintf(name, sizeof(name), "%s_%d_%d", ctx->name, ctx->thread_id, i);

    valk_label_set_v2_t labels = {
      .labels = {{.key = "thread", .value = "test"}},
      .count = 1
    };

    valk_counter_v2_t *c = valk_counter_get_or_create(name, nullptr, &labels);
    if (c) {
      valk_counter_v2_inc(c);
    }
  }

  return nullptr;
}

static void test_concurrent_counter_creation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  const int NUM_THREADS = 4;
  const int ITERATIONS = 500;
  pthread_t threads[NUM_THREADS];
  create_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (create_thread_ctx_t){
      .name = "concurrent_counter",
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, create_counter_many, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  size_t total_counters = atomic_load(&g_metrics.counter_count);
  ASSERT_GE(total_counters, 1);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

static void *get_same_counter(void *arg) {
  create_thread_ctx_t *ctx = (create_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_label_set_v2_t labels = {0};
    valk_counter_v2_t *c = valk_counter_get_or_create("shared_counter", nullptr, &labels);
    if (c) {
      valk_counter_v2_inc(c);
    }
  }

  return nullptr;
}

static void test_concurrent_same_counter_get_or_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  const int NUM_THREADS = 8;
  const int ITERATIONS = 5000;
  pthread_t threads[NUM_THREADS];
  create_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (create_thread_ctx_t){
      .name = "shared",
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, get_same_counter, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  size_t total_counters = atomic_load(&g_metrics.counter_count);
  ASSERT_EQ(total_counters, 1);

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("shared_counter", nullptr, &labels);
  u64 expected = (u64)NUM_THREADS * ITERATIONS;
  u64 actual = atomic_load(&c->value);
  ASSERT_EQ(actual, expected);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Concurrent Delta Collection Tests
// ============================================================================

static void *collect_snapshot(void *arg) {
  snapshot_thread_ctx_t *ctx = (snapshot_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_delta_snapshot_t snap;
    valk_delta_snapshot_init(&snap);
    valk_delta_snapshot_collect(&snap, &g_metrics);
    valk_delta_snapshot_free(&snap);
  }

  return nullptr;
}

static void *update_metrics_while_collecting(void *arg) {
  counter_thread_ctx_t *ctx = (counter_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_counter_v2_inc(ctx->counter);
  }

  return nullptr;
}

static void test_concurrent_snapshot_and_update(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("snapshot_test", nullptr, &labels);
  ASSERT_NOT_NULL(c);

  const int NUM_UPDATERS = 4;
  const int NUM_COLLECTORS = 2;
  const int ITERATIONS = 5000;

  pthread_t updaters[NUM_UPDATERS];
  pthread_t collectors[NUM_COLLECTORS];
  counter_thread_ctx_t updater_contexts[NUM_UPDATERS];
  snapshot_thread_ctx_t collector_contexts[NUM_COLLECTORS];

  for (int i = 0; i < NUM_UPDATERS; i++) {
    updater_contexts[i] = (counter_thread_ctx_t){
      .counter = c,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&updaters[i], nullptr, update_metrics_while_collecting, &updater_contexts[i]);
  }

  for (int i = 0; i < NUM_COLLECTORS; i++) {
    collector_contexts[i] = (snapshot_thread_ctx_t){
      .iterations = ITERATIONS / 10,
      .thread_id = i
    };
    pthread_create(&collectors[i], nullptr, collect_snapshot, &collector_contexts[i]);
  }

  for (int i = 0; i < NUM_UPDATERS; i++) {
    pthread_join(updaters[i], nullptr);
  }
  for (int i = 0; i < NUM_COLLECTORS; i++) {
    pthread_join(collectors[i], nullptr);
  }

  u64 expected = (u64)NUM_UPDATERS * ITERATIONS;
  u64 actual = atomic_load(&c->value);
  ASSERT_EQ(actual, expected);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Concurrent Eviction Tests
// ============================================================================

static void *evict_stale_loop(void *arg) {
  int *iterations = (int *)arg;

  for (int i = 0; i < *iterations; i++) {
    valk_metrics_evict_stale();
    for (volatile int j = 0; j < 100; j++) {}
  }

  return nullptr;
}

static void *create_and_update_counters(void *arg) {
  create_thread_ctx_t *ctx = (create_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    char name[64];
    snprintf(name, sizeof(name), "evict_test_%d_%d", ctx->thread_id, i % 10);

    valk_label_set_v2_t labels = {
      .labels = {{.key = "iteration", .value = "test"}},
      .count = 1
    };

    valk_counter_v2_t *c = valk_counter_get_or_create(name, nullptr, &labels);
    if (c) {
      valk_counter_v2_inc(c);
    }
  }

  return nullptr;
}

static void test_concurrent_eviction_and_creation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();
  g_metrics.eviction_threshold_us = 1;

  const int NUM_CREATORS = 4;
  const int ITERATIONS = 1000;
  const int EVICTION_ITERATIONS = 200;

  pthread_t creators[NUM_CREATORS];
  pthread_t evictor;
  create_thread_ctx_t creator_contexts[NUM_CREATORS];

  for (int i = 0; i < NUM_CREATORS; i++) {
    creator_contexts[i] = (create_thread_ctx_t){
      .name = "evict_test",
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&creators[i], nullptr, create_and_update_counters, &creator_contexts[i]);
  }

  int evict_iters = EVICTION_ITERATIONS;
  pthread_create(&evictor, nullptr, evict_stale_loop, &evict_iters);

  for (int i = 0; i < NUM_CREATORS; i++) {
    pthread_join(creators[i], nullptr);
  }
  pthread_join(evictor, nullptr);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Mixed Metric Type Concurrent Tests
// ============================================================================

typedef struct {
  int thread_id;
  int iterations;
} mixed_thread_ctx_t;

static void *mixed_metric_operations(void *arg) {
  mixed_thread_ctx_t *ctx = (mixed_thread_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    char name[64];
    snprintf(name, sizeof(name), "mixed_counter_%d", ctx->thread_id);
    valk_label_set_v2_t labels = {0};
    valk_counter_v2_t *c = valk_counter_get_or_create(name, nullptr, &labels);
    if (c) valk_counter_v2_inc(c);

    snprintf(name, sizeof(name), "mixed_gauge_%d", ctx->thread_id);
    valk_gauge_v2_t *g = valk_gauge_get_or_create(name, nullptr, &labels);
    if (g) valk_gauge_v2_set(g, i);

    double bounds[] = {0.1, 1.0};
    snprintf(name, sizeof(name), "mixed_hist_%d", ctx->thread_id);
    valk_histogram_v2_t *h = valk_histogram_get_or_create(name, nullptr, bounds, 2, &labels);
    if (h) valk_histogram_v2_observe_us(h, i * 1000);
  }

  return nullptr;
}

static void test_mixed_metric_types_concurrent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  const int NUM_THREADS = 8;
  const int ITERATIONS = 500;
  pthread_t threads[NUM_THREADS];
  mixed_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (mixed_thread_ctx_t){
      .thread_id = i,
      .iterations = ITERATIONS
    };
    pthread_create(&threads[i], nullptr, mixed_metric_operations, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  ASSERT_GT(atomic_load(&g_metrics.counter_count), 0);
  ASSERT_GT(atomic_load(&g_metrics.gauge_count), 0);
  ASSERT_GT(atomic_load(&g_metrics.histogram_count), 0);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Handle Deref Under Contention
// ============================================================================

static void *handle_deref_loop(void *arg) {
  counter_thread_ctx_t *ctx = (counter_thread_ctx_t *)arg;

  valk_metric_handle_t handle = valk_counter_handle(ctx->counter);

  for (int i = 0; i < ctx->iterations; i++) {
    valk_counter_v2_t *c = valk_counter_deref(handle);
    if (c) {
      valk_counter_v2_inc(c);
    }
  }

  return nullptr;
}

static void test_handle_deref_under_contention(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("handle_test", nullptr, &labels);
  ASSERT_NOT_NULL(c);

  const int NUM_THREADS = 8;
  const int ITERATIONS = 10000;
  pthread_t threads[NUM_THREADS];
  counter_thread_ctx_t contexts[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    contexts[i] = (counter_thread_ctx_t){
      .counter = c,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&threads[i], nullptr, handle_deref_loop, &contexts[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  u64 expected = (u64)NUM_THREADS * ITERATIONS;
  u64 actual = atomic_load(&c->value);
  ASSERT_EQ(actual, expected);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Registry Stats Under Contention
// ============================================================================

static void *registry_stats_loop(void *arg) {
  int *iterations = (int *)arg;

  for (int i = 0; i < *iterations; i++) {
    valk_registry_stats_t stats;
    valk_registry_stats_collect(&stats);

    char buf[4096];
    valk_registry_stats_to_json(&stats, buf, sizeof(buf));
  }

  return nullptr;
}

static void test_registry_stats_under_contention(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("stats_test", nullptr, &labels);

  const int NUM_UPDATERS = 4;
  const int NUM_STATS_READERS = 2;
  const int ITERATIONS = 5000;

  pthread_t updaters[NUM_UPDATERS];
  pthread_t stats_readers[NUM_STATS_READERS];
  counter_thread_ctx_t updater_contexts[NUM_UPDATERS];

  for (int i = 0; i < NUM_UPDATERS; i++) {
    updater_contexts[i] = (counter_thread_ctx_t){
      .counter = c,
      .iterations = ITERATIONS,
      .thread_id = i
    };
    pthread_create(&updaters[i], nullptr, counter_increment_many, &updater_contexts[i]);
  }

  int stats_iters = ITERATIONS / 10;
  for (int i = 0; i < NUM_STATS_READERS; i++) {
    pthread_create(&stats_readers[i], nullptr, registry_stats_loop, &stats_iters);
  }

  for (int i = 0; i < NUM_UPDATERS; i++) {
    pthread_join(updaters[i], nullptr);
  }
  for (int i = 0; i < NUM_STATS_READERS; i++) {
    pthread_join(stats_readers[i], nullptr);
  }

  u64 expected = (u64)NUM_UPDATERS * ITERATIONS;
  u64 actual = atomic_load(&c->value);
  ASSERT_EQ(actual, expected);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_counter_concurrent_inc_high_contention",
                          test_counter_concurrent_inc_high_contention);
  valk_testsuite_add_test(suite, "test_counter_concurrent_add_varied",
                          test_counter_concurrent_add_varied);

  valk_testsuite_add_test(suite, "test_gauge_concurrent_set",
                          test_gauge_concurrent_set);
  valk_testsuite_add_test(suite, "test_gauge_concurrent_inc_dec_balanced",
                          test_gauge_concurrent_inc_dec_balanced);
  valk_testsuite_add_test(suite, "test_gauge_concurrent_add_balanced",
                          test_gauge_concurrent_add_balanced);

  valk_testsuite_add_test(suite, "test_histogram_concurrent_observe",
                          test_histogram_concurrent_observe);

  valk_testsuite_add_test(suite, "test_concurrent_counter_creation",
                          test_concurrent_counter_creation);
  valk_testsuite_add_test(suite, "test_concurrent_same_counter_get_or_create",
                          test_concurrent_same_counter_get_or_create);

  valk_testsuite_add_test(suite, "test_concurrent_snapshot_and_update",
                          test_concurrent_snapshot_and_update);

  valk_testsuite_add_test(suite, "test_concurrent_eviction_and_creation",
                          test_concurrent_eviction_and_creation);

  valk_testsuite_add_test(suite, "test_mixed_metric_types_concurrent",
                          test_mixed_metric_types_concurrent);

  valk_testsuite_add_test(suite, "test_handle_deref_under_contention",
                          test_handle_deref_under_contention);

  valk_testsuite_add_test(suite, "test_registry_stats_under_contention",
                          test_registry_stats_under_contention);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
