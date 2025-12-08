// test/test_metrics_v2.c
#include "testing.h"
#include "common.h"
#include "memory.h"

#ifdef VALK_METRICS_ENABLED

#include "metrics_v2.h"
#include "metrics_delta.h"
#include <string.h>
#include <pthread.h>

// Inline functions are defined in metrics_v2.h

// ============================================================================
// TEST: Registry Lifecycle
// ============================================================================

void test_metrics_v2_init_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Verify initial state
  VALK_TEST_ASSERT(atomic_load(&g_metrics.counter_count) == 0,
                   "Initial counter_count should be 0");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.gauge_count) == 0,
                   "Initial gauge_count should be 0");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.histogram_count) == 0,
                   "Initial histogram_count should be 0");
  VALK_TEST_ASSERT(g_metrics.string_pool_count == 0,
                   "Initial string_pool_count should be 0");
  VALK_TEST_ASSERT(g_metrics.start_time_us > 0,
                   "start_time_us should be set");
  VALK_TEST_ASSERT(g_metrics.snapshot_interval_us == 1000000,
                   "Default snapshot_interval_us should be 1s");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_metrics_v2_reinit(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Multiple init/destroy cycles
  for (int i = 0; i < 3; i++) {
    valk_metrics_registry_init();

    valk_label_set_v2_t labels = {0};
    valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", "Test", &labels);
    VALK_TEST_ASSERT(c != NULL, "Counter should be created");

    valk_counter_v2_inc(c);
    VALK_TEST_ASSERT(atomic_load(&c->value) == 1, "Counter value should be 1");

    valk_metrics_registry_destroy();
  }

  VALK_PASS();
}

// ============================================================================
// TEST: Counter V2 Operations
// ============================================================================

void test_counter_v2_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("requests_total", "Total requests", &labels);

  VALK_TEST_ASSERT(c != NULL, "Counter should be created");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.counter_count) == 1,
                   "counter_count should be 1");
  VALK_TEST_ASSERT(atomic_load(&c->value) == 0, "Initial value should be 0");
  VALK_TEST_ASSERT(strcmp(c->name, "requests_total") == 0,
                   "Counter name should match");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_counter_v2_inc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", NULL, &labels);
  VALK_TEST_ASSERT(c != NULL, "Counter should be created");

  // Test increment
  valk_counter_v2_inc(c);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 1, "Value should be 1 after inc");

  valk_counter_v2_inc(c);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 2, "Value should be 2 after inc");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_counter_v2_add(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", NULL, &labels);
  VALK_TEST_ASSERT(c != NULL, "Counter should be created");

  // Test add
  valk_counter_v2_add(c, 10);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 10, "Value should be 10 after add(10)");

  valk_counter_v2_add(c, 5);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 15, "Value should be 15 after add(5)");

  valk_counter_v2_add(c, 0);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 15, "Value should be 15 after add(0)");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_counter_v2_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create counter with labels
  valk_label_set_v2_t labels1 = {
    .labels = {
      {.key = "method", .value = "GET"},
      {.key = "status", .value = "200"}
    },
    .count = 2
  };

  valk_counter_v2_t *c1 = valk_counter_get_or_create("http_requests", "HTTP requests", &labels1);
  VALK_TEST_ASSERT(c1 != NULL, "Counter with labels should be created");
  VALK_TEST_ASSERT(c1->labels.count == 2, "Should have 2 labels");

  valk_counter_v2_inc(c1);
  VALK_TEST_ASSERT(atomic_load(&c1->value) == 1, "Value should be 1");

  // Different labels should create different counter
  valk_label_set_v2_t labels2 = {
    .labels = {
      {.key = "method", .value = "POST"},
      {.key = "status", .value = "200"}
    },
    .count = 2
  };

  valk_counter_v2_t *c2 = valk_counter_get_or_create("http_requests", "HTTP requests", &labels2);
  VALK_TEST_ASSERT(c2 != NULL && c2 != c1,
                   "Different labels should create different counter");
  VALK_TEST_ASSERT(atomic_load(&c2->value) == 0, "New counter value should be 0");

  valk_counter_v2_add(c2, 5);
  VALK_TEST_ASSERT(atomic_load(&c2->value) == 5, "c2 value should be 5");
  VALK_TEST_ASSERT(atomic_load(&c1->value) == 1, "c1 value should still be 1");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_counter_v2_dedup(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {
    .labels = {
      {.key = "env", .value = "prod"}
    },
    .count = 1
  };

  valk_counter_v2_t *c1 = valk_counter_get_or_create("test", "Test", &labels);
  valk_counter_v2_inc(c1);

  // Same name+labels should return same counter
  valk_counter_v2_t *c2 = valk_counter_get_or_create("test", "Test", &labels);
  VALK_TEST_ASSERT(c2 == c1, "Same name+labels should return same pointer");
  VALK_TEST_ASSERT(atomic_load(&c2->value) == 1, "Value should be 1");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.counter_count) == 1,
                   "counter_count should still be 1");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// TEST: Gauge V2 Operations
// ============================================================================

void test_gauge_v2_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *g = valk_gauge_get_or_create("memory_bytes", "Memory usage", &labels);

  VALK_TEST_ASSERT(g != NULL, "Gauge should be created");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.gauge_count) == 1,
                   "gauge_count should be 1");
  VALK_TEST_ASSERT(atomic_load(&g->value) == 0, "Initial value should be 0");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_gauge_v2_set_inc_dec(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *g = valk_gauge_get_or_create("test_gauge", NULL, &labels);
  VALK_TEST_ASSERT(g != NULL, "Gauge should be created");

  // Test set
  valk_gauge_v2_set(g, 100);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 100, "Value should be 100 after set");

  // Test increment
  valk_gauge_v2_inc(g);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 101, "Value should be 101 after inc");

  // Test decrement
  valk_gauge_v2_dec(g);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 100, "Value should be 100 after dec");

  // Test add (positive)
  valk_gauge_v2_add(g, 50);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 150, "Value should be 150 after add(50)");

  // Test add (negative)
  valk_gauge_v2_add(g, -30);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 120, "Value should be 120 after add(-30)");

  // Test set to negative
  valk_gauge_v2_set(g, -42);
  VALK_TEST_ASSERT(atomic_load(&g->value) == -42, "Value should be -42 after set");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// TEST: Histogram V2 Operations
// ============================================================================

void test_histogram_v2_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  double bounds[] = {0.001, 0.01, 0.1, 1.0};
  valk_label_set_v2_t labels = {0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create(
      "request_duration", "Request duration", bounds, 4, &labels);

  VALK_TEST_ASSERT(h != NULL, "Histogram should be created");
  VALK_TEST_ASSERT(h->bucket_count == 4, "Should have 4 buckets");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.histogram_count) == 1,
                   "histogram_count should be 1");

  // Verify bounds
  for (int i = 0; i < 4; i++) {
    VALK_TEST_ASSERT(h->bucket_bounds[i] == bounds[i],
                     "Bucket bound %d should match", i);
  }

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_histogram_v2_observe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  double bounds[] = {0.1, 0.5, 1.0, 5.0};
  valk_label_set_v2_t labels = {0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create(
      "request_duration", NULL, bounds, 4, &labels);
  VALK_TEST_ASSERT(h != NULL, "Histogram should be created");

  // Initial state
  VALK_TEST_ASSERT(atomic_load(&h->count) == 0, "Initial count should be 0");
  VALK_TEST_ASSERT(atomic_load(&h->sum_micros) == 0, "Initial sum should be 0");

  // Observe value in first bucket (0.05s = 50000us <= 0.1s)
  valk_histogram_v2_observe_us(h, 50000);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 1, "Count should be 1");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[0]) == 1, "Bucket 0 should be 1");
  VALK_TEST_ASSERT(atomic_load(&h->sum_micros) == 50000, "Sum should be 50000");

  // Observe value in second bucket (0.3s = 300000us <= 0.5s)
  valk_histogram_v2_observe_us(h, 300000);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 2, "Count should be 2");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[1]) == 1, "Bucket 1 should be 1");

  // Observe value in third bucket (0.75s = 750000us <= 1.0s)
  valk_histogram_v2_observe_us(h, 750000);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 3, "Count should be 3");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[2]) == 1, "Bucket 2 should be 1");

  // Observe value in +Inf bucket (10.0s = 10000000us > 5.0s)
  valk_histogram_v2_observe_us(h, 10000000);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 4, "Count should be 4");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[4]) == 1, "+Inf bucket should be 1");

  // Verify sum (50000 + 300000 + 750000 + 10000000 = 11100000 us)
  uint64_t expected_sum = 11100000;
  uint64_t actual_sum = atomic_load(&h->sum_micros);
  VALK_TEST_ASSERT(actual_sum == expected_sum,
                   "Sum should be %lu, got %lu", expected_sum, actual_sum);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_histogram_v2_custom_buckets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Custom buckets for latency measurement
  double bounds[] = {0.001, 0.002, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0};
  valk_label_set_v2_t labels = {0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create(
      "latency", "Latency distribution", bounds, 10, &labels);

  VALK_TEST_ASSERT(h != NULL, "Histogram should be created");
  VALK_TEST_ASSERT(h->bucket_count == 10, "Should have 10 buckets");

  // Observe some values
  valk_histogram_v2_observe_us(h, 500);    // 0.0005s -> bucket 0
  valk_histogram_v2_observe_us(h, 1500);   // 0.0015s -> bucket 1
  valk_histogram_v2_observe_us(h, 7500);   // 0.0075s -> bucket 3

  VALK_TEST_ASSERT(atomic_load(&h->buckets[0]) == 1, "Bucket 0 should have 1");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[1]) == 1, "Bucket 1 should have 1");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[3]) == 1, "Bucket 3 should have 1");
  VALK_TEST_ASSERT(atomic_load(&h->count) == 3, "Total count should be 3");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// TEST: Delta Collection
// ============================================================================

void test_delta_snapshot_init_free(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  // Implementation pre-allocates with default capacity
  VALK_TEST_ASSERT(snap.deltas != NULL, "Deltas should be allocated initially");
  VALK_TEST_ASSERT(snap.delta_count == 0, "delta_count should be 0");
  VALK_TEST_ASSERT(snap.delta_capacity == 256, "delta_capacity should be 256 (default)");

  valk_delta_snapshot_free(&snap);
  VALK_PASS();
}

void test_delta_counter_change(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create and increment counter
  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", NULL, &labels);
  valk_counter_v2_add(c, 10);

  // Collect delta
  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(changed > 0, "Should detect counter change");
  VALK_TEST_ASSERT(snap.counters_changed > 0, "counters_changed should be > 0");

  valk_delta_snapshot_free(&snap);
  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_delta_gauge_threshold(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create gauge and set value
  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *g = valk_gauge_get_or_create("test_gauge", NULL, &labels);
  valk_gauge_v2_set(g, 100);

  // Collect delta
  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(changed > 0, "Should detect gauge change");
  VALK_TEST_ASSERT(snap.gauges_changed > 0, "gauges_changed should be > 0");

  valk_delta_snapshot_free(&snap);
  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_delta_histogram_buckets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create histogram and observe values
  double bounds[] = {0.1, 1.0};
  valk_label_set_v2_t labels = {0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create(
      "test_histogram", NULL, bounds, 2, &labels);

  valk_histogram_v2_observe_us(h, 50000);  // 0.05s
  valk_histogram_v2_observe_us(h, 500000); // 0.5s

  // Collect delta
  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(changed > 0, "Should detect histogram change");
  VALK_TEST_ASSERT(snap.histograms_changed > 0, "histograms_changed should be > 0");

  valk_delta_snapshot_free(&snap);
  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// TEST: JSON Encoding
// ============================================================================

void test_delta_to_json(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create some metrics
  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", NULL, &labels);
  valk_counter_v2_add(c, 42);

  valk_gauge_v2_t *g = valk_gauge_get_or_create("test_gauge", NULL, &labels);
  valk_gauge_v2_set(g, 100);

  // Collect delta
  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  // Encode to JSON
  char buf[4096];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "JSON output should be non-empty");
  VALK_TEST_ASSERT(len < sizeof(buf), "JSON output should fit in buffer");

  // Verify JSON contains expected fields
  VALK_TEST_ASSERT(strstr(buf, "\"ts\"") != NULL, "Should contain timestamp");
  VALK_TEST_ASSERT(strstr(buf, "\"deltas\"") != NULL, "Should contain deltas array");

  valk_delta_snapshot_free(&snap);
  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_delta_to_sse(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create metric
  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", NULL, &labels);
  valk_counter_v2_add(c, 10);

  // Collect delta
  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  // Encode to SSE
  char buf[4096];
  size_t len = valk_delta_to_sse(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "SSE output should be non-empty");
  VALK_TEST_ASSERT(strstr(buf, "event:") != NULL, "Should contain event type");
  VALK_TEST_ASSERT(strstr(buf, "data:") != NULL, "Should contain data field");

  valk_delta_snapshot_free(&snap);
  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// TEST: Concurrency
// ============================================================================

typedef struct {
  valk_counter_v2_t *counter;
  int iterations;
} thread_test_ctx_t;

static void *counter_increment_thread(void *arg) {
  thread_test_ctx_t *ctx = (thread_test_ctx_t *)arg;

  for (int i = 0; i < ctx->iterations; i++) {
    valk_counter_v2_inc(ctx->counter);
  }

  return NULL;
}

void test_counter_concurrent_inc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("concurrent_counter", NULL, &labels);
  VALK_TEST_ASSERT(c != NULL, "Counter should be created");

  // Spawn multiple threads
  const int NUM_THREADS = 4;
  const int ITERATIONS = 10000;
  pthread_t threads[NUM_THREADS];
  thread_test_ctx_t ctx = {.counter = c, .iterations = ITERATIONS};

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_create(&threads[i], NULL, counter_increment_thread, &ctx);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], NULL);
  }

  // Verify total
  uint64_t expected = NUM_THREADS * ITERATIONS;
  uint64_t actual = atomic_load(&c->value);
  VALK_TEST_ASSERT(actual == expected,
                   "Counter should be %lu, got %lu", expected, actual);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// MAIN
// ============================================================================

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  // Initialize memory allocator
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // Registry lifecycle tests
  valk_testsuite_add_test(suite, "test_metrics_v2_init_destroy",
                          test_metrics_v2_init_destroy);
  valk_testsuite_add_test(suite, "test_metrics_v2_reinit",
                          test_metrics_v2_reinit);

  // Counter V2 tests
  valk_testsuite_add_test(suite, "test_counter_v2_create",
                          test_counter_v2_create);
  valk_testsuite_add_test(suite, "test_counter_v2_inc",
                          test_counter_v2_inc);
  valk_testsuite_add_test(suite, "test_counter_v2_add",
                          test_counter_v2_add);
  valk_testsuite_add_test(suite, "test_counter_v2_labels",
                          test_counter_v2_labels);
  valk_testsuite_add_test(suite, "test_counter_v2_dedup",
                          test_counter_v2_dedup);

  // Gauge V2 tests
  valk_testsuite_add_test(suite, "test_gauge_v2_create",
                          test_gauge_v2_create);
  valk_testsuite_add_test(suite, "test_gauge_v2_set_inc_dec",
                          test_gauge_v2_set_inc_dec);

  // Histogram V2 tests
  valk_testsuite_add_test(suite, "test_histogram_v2_create",
                          test_histogram_v2_create);
  valk_testsuite_add_test(suite, "test_histogram_v2_observe",
                          test_histogram_v2_observe);
  valk_testsuite_add_test(suite, "test_histogram_v2_custom_buckets",
                          test_histogram_v2_custom_buckets);

  // Delta collection tests
  valk_testsuite_add_test(suite, "test_delta_snapshot_init_free",
                          test_delta_snapshot_init_free);
  valk_testsuite_add_test(suite, "test_delta_counter_change",
                          test_delta_counter_change);
  valk_testsuite_add_test(suite, "test_delta_gauge_threshold",
                          test_delta_gauge_threshold);
  valk_testsuite_add_test(suite, "test_delta_histogram_buckets",
                          test_delta_histogram_buckets);

  // JSON encoding tests
  valk_testsuite_add_test(suite, "test_delta_to_json",
                          test_delta_to_json);
  valk_testsuite_add_test(suite, "test_delta_to_sse",
                          test_delta_to_sse);

  // Concurrency tests
  valk_testsuite_add_test(suite, "test_counter_concurrent_inc",
                          test_counter_concurrent_inc);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

#else

// ============================================================================
// METRICS DISABLED - Skip Tests
// ============================================================================

#include <stdio.h>

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  fprintf(stderr, "SKIP: Metrics V2 tests disabled (VALK_METRICS not enabled)\n");
  return 0;
}

#endif // VALK_METRICS_ENABLED
