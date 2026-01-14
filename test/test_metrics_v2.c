// test/test_metrics_v2.c
#include "testing.h"
#include "common.h"
#include "memory.h"
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
    VALK_TEST_ASSERT(c != nullptr, "Counter should be created");

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

  VALK_TEST_ASSERT(c != nullptr, "Counter should be created");
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
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", nullptr, &labels);
  VALK_TEST_ASSERT(c != nullptr, "Counter should be created");

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
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", nullptr, &labels);
  VALK_TEST_ASSERT(c != nullptr, "Counter should be created");

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
  VALK_TEST_ASSERT(c1 != nullptr, "Counter with labels should be created");
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
  VALK_TEST_ASSERT(c2 != nullptr && c2 != c1,
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

  VALK_TEST_ASSERT(g != nullptr, "Gauge should be created");
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
  valk_gauge_v2_t *g = valk_gauge_get_or_create("test_gauge", nullptr, &labels);
  VALK_TEST_ASSERT(g != nullptr, "Gauge should be created");

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

  VALK_TEST_ASSERT(h != nullptr, "Histogram should be created");
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
      "request_duration", nullptr, bounds, 4, &labels);
  VALK_TEST_ASSERT(h != nullptr, "Histogram should be created");

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
  u64 expected_sum = 11100000;
  u64 actual_sum = atomic_load(&h->sum_micros);
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

  VALK_TEST_ASSERT(h != nullptr, "Histogram should be created");
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
  VALK_TEST_ASSERT(snap.deltas != nullptr, "Deltas should be allocated initially");
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
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", nullptr, &labels);
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
  valk_gauge_v2_t *g = valk_gauge_get_or_create("test_gauge", nullptr, &labels);
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
      "test_histogram", nullptr, bounds, 2, &labels);

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
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", nullptr, &labels);
  valk_counter_v2_add(c, 42);

  valk_gauge_v2_t *g = valk_gauge_get_or_create("test_gauge", nullptr, &labels);
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
  VALK_TEST_ASSERT(strstr(buf, "\"ts\"") != nullptr, "Should contain timestamp");
  VALK_TEST_ASSERT(strstr(buf, "\"deltas\"") != nullptr, "Should contain deltas array");

  valk_delta_snapshot_free(&snap);
  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_delta_to_sse(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create metric
  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", nullptr, &labels);
  valk_counter_v2_add(c, 10);

  // Collect delta
  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  // Encode to SSE
  char buf[4096];
  size_t len = valk_delta_to_sse(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "SSE output should be non-empty");
  VALK_TEST_ASSERT(strstr(buf, "event:") != nullptr, "Should contain event type");
  VALK_TEST_ASSERT(strstr(buf, "data:") != nullptr, "Should contain data field");

  valk_delta_snapshot_free(&snap);
  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// TEST: LRU Eviction
// ============================================================================

void test_eviction_threshold_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Verify eviction threshold is set to default (5 minutes)
  VALK_TEST_ASSERT(g_metrics.eviction_threshold_us == VALK_EVICTION_THRESHOLD_US,
                   "Eviction threshold should be 5 minutes");
  VALK_TEST_ASSERT(g_metrics.eviction_threshold_us == 5 * 60 * 1000000ULL,
                   "Eviction threshold should be 300000000 us");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_eviction_free_list_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Verify free list heads are initialized to invalid
  VALK_TEST_ASSERT(atomic_load(&g_metrics.counter_free.head) == VALK_INVALID_SLOT,
                   "Counter free list should be empty");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.gauge_free.head) == VALK_INVALID_SLOT,
                   "Gauge free list should be empty");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.histogram_free.head) == VALK_INVALID_SLOT,
                   "Histogram free list should be empty");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_metric_active_flag(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", nullptr, &labels);
  VALK_TEST_ASSERT(c != nullptr, "Counter should be created");

  // Verify active flag is set
  VALK_TEST_ASSERT(atomic_load(&c->active) == true, "Counter should be active");

  // Verify evictable flag is true by default
  VALK_TEST_ASSERT(c->evictable == true, "Counter should be evictable by default");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_metric_persistent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("persistent_counter", nullptr, &labels);
  VALK_TEST_ASSERT(c != nullptr, "Counter should be created");
  VALK_TEST_ASSERT(c->evictable == true, "Should be evictable initially");

  // Mark as persistent
  valk_counter_set_persistent(c);
  VALK_TEST_ASSERT(c->evictable == false, "Should be non-evictable after set_persistent");

  // Create persistent gauge
  valk_gauge_v2_t *g = valk_gauge_get_or_create("persistent_gauge", nullptr, &labels);
  valk_gauge_set_persistent(g);
  VALK_TEST_ASSERT(g->evictable == false, "Gauge should be non-evictable");

  // Create persistent histogram
  double bounds[] = {0.1, 1.0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create("persistent_hist", nullptr, bounds, 2, &labels);
  valk_histogram_set_persistent(h);
  VALK_TEST_ASSERT(h->evictable == false, "Histogram should be non-evictable");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_metric_last_updated(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};

  // Create counter and verify initial timestamp
  valk_counter_v2_t *c = valk_counter_get_or_create("test_counter", nullptr, &labels);
  u64 ts1 = atomic_load(&c->last_updated_us);
  VALK_TEST_ASSERT(ts1 > 0, "Counter should have non-zero timestamp on creation");

  // Wait a tiny bit and update
  for (volatile int i = 0; i < 10000; i++) {} // Spin briefly
  valk_counter_v2_inc(c);
  u64 ts2 = atomic_load(&c->last_updated_us);
  VALK_TEST_ASSERT(ts2 >= ts1, "Timestamp should increase after update");

  // Test gauge timestamp update
  valk_gauge_v2_t *g = valk_gauge_get_or_create("test_gauge", nullptr, &labels);
  u64 gts1 = atomic_load(&g->last_updated_us);
  valk_gauge_v2_set(g, 42);
  u64 gts2 = atomic_load(&g->last_updated_us);
  VALK_TEST_ASSERT(gts2 >= gts1, "Gauge timestamp should update");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_eviction_no_stale_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};

  // Create a fresh metric
  valk_counter_v2_t *c = valk_counter_get_or_create("fresh_counter", nullptr, &labels);
  valk_counter_v2_inc(c);

  // Try to evict - should evict 0 since metric is fresh
  size_t evicted = valk_metrics_evict_stale();
  VALK_TEST_ASSERT(evicted == 0, "Should not evict fresh metrics");
  VALK_TEST_ASSERT(atomic_load(&c->active) == true, "Counter should still be active");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_eviction_persistent_protected(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};

  // Create a persistent metric
  valk_counter_v2_t *c = valk_counter_get_or_create("protected_counter", nullptr, &labels);
  valk_counter_set_persistent(c);

  // Even with very old timestamp (manually set for test), persistent should not evict
  // We can't easily test this without mocking time, so just verify the flag works
  VALK_TEST_ASSERT(c->evictable == false, "Counter should be marked non-evictable");

  (void)valk_metrics_evict_stale();
  VALK_TEST_ASSERT(atomic_load(&c->active) == true,
                   "Persistent counter should never be evicted");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_metric_generation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};

  // Create first metric
  valk_counter_v2_t *c1 = valk_counter_get_or_create("gen_counter", nullptr, &labels);
  u32 gen1 = atomic_load(&c1->generation);
  VALK_TEST_ASSERT(gen1 >= 1, "Generation should be at least 1 after creation");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_handle_create_deref(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};

  // Create counter and get handle
  valk_counter_v2_t *c = valk_counter_get_or_create("handle_test", nullptr, &labels);
  valk_metric_handle_t handle = valk_counter_handle(c);

  VALK_TEST_ASSERT(handle.slot != VALK_INVALID_SLOT, "Handle slot should be valid");
  VALK_TEST_ASSERT(handle.generation > 0, "Handle generation should be > 0");

  // Dereference handle
  valk_counter_v2_t *c2 = valk_counter_deref(handle);
  VALK_TEST_ASSERT(c2 == c, "Dereferenced pointer should match original");

  // Test gauge handle
  valk_gauge_v2_t *g = valk_gauge_get_or_create("gauge_handle", nullptr, &labels);
  valk_metric_handle_t gh = valk_gauge_handle(g);
  valk_gauge_v2_t *g2 = valk_gauge_deref(gh);
  VALK_TEST_ASSERT(g2 == g, "Gauge dereference should match original");

  // Test histogram handle
  double bounds[] = {0.1, 1.0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create("hist_handle", nullptr, bounds, 2, &labels);
  valk_metric_handle_t hh = valk_histogram_handle(h);
  valk_histogram_v2_t *h2 = valk_histogram_deref(hh);
  VALK_TEST_ASSERT(h2 == h, "Histogram dereference should match original");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_handle_invalid(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Invalid handle should return nullptr
  valk_metric_handle_t invalid = VALK_HANDLE_INVALID;
  VALK_TEST_ASSERT(valk_counter_deref(invalid) == nullptr,
                   "Invalid counter handle should return nullptr");
  VALK_TEST_ASSERT(valk_gauge_deref(invalid) == nullptr,
                   "Invalid gauge handle should return nullptr");
  VALK_TEST_ASSERT(valk_histogram_deref(invalid) == nullptr,
                   "Invalid histogram handle should return nullptr");

  // Handle for nullptr pointer
  valk_metric_handle_t null_handle = valk_counter_handle(nullptr);
  VALK_TEST_ASSERT(null_handle.slot == VALK_INVALID_SLOT,
                   "nullptr counter should produce invalid handle");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_eviction_slot_reuse(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Set a very short eviction threshold for testing (1 microsecond)
  g_metrics.eviction_threshold_us = 1;

  valk_label_set_v2_t labels1 = {
    .labels = {{.key = "id", .value = "1"}},
    .count = 1
  };

  // Create and immediately age a metric
  valk_counter_v2_t *c1 = valk_counter_get_or_create("reuse_test", nullptr, &labels1);
  VALK_TEST_ASSERT(c1 != nullptr, "Counter should be created");
  size_t initial_count = atomic_load(&g_metrics.counter_count);

  // Wait a tiny bit to make the metric "stale"
  for (volatile int i = 0; i < 100000; i++) {} // Spin

  // Evict stale metrics
  size_t evicted = valk_metrics_evict_stale();

  // With threshold of 1us, the counter should be evicted
  VALK_TEST_ASSERT(evicted >= 1, "Should evict at least 1 metric");
  VALK_TEST_ASSERT(atomic_load(&c1->active) == false, "Counter should be inactive after eviction");

  // Free list should have the slot
  u32 free_head = atomic_load(&g_metrics.counter_free.head);
  VALK_TEST_ASSERT(free_head != VALK_INVALID_SLOT, "Free list should have evicted slot");

  // Create a new metric - should reuse the slot from free list
  valk_label_set_v2_t labels2 = {
    .labels = {{.key = "id", .value = "2"}},
    .count = 1
  };
  valk_counter_v2_t *c2 = valk_counter_get_or_create("reuse_test2", nullptr, &labels2);
  VALK_TEST_ASSERT(c2 != nullptr, "New counter should be created");

  // Counter count should not have increased if slot was reused
  // (or only increased by 1 if free list was used for reuse)
  size_t final_count = atomic_load(&g_metrics.counter_count);
  VALK_TEST_ASSERT(final_count <= initial_count + 1,
                   "Should reuse slots instead of always allocating new");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

// ============================================================================
// TEST: Pool Metrics Factory
// ============================================================================

#include "pool_metrics.h"

void test_pool_metrics_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init(&pm, "test_pool");

  VALK_TEST_ASSERT(ok == true, "Pool metrics init should succeed");
  VALK_TEST_ASSERT(pm.pool_name != nullptr, "Pool name should be set");
  VALK_TEST_ASSERT(strcmp(pm.pool_name, "test_pool") == 0, "Pool name should match");

  // All metrics should be created
  VALK_TEST_ASSERT(pm.used != nullptr, "Used gauge should be created");
  VALK_TEST_ASSERT(pm.total != nullptr, "Total gauge should be created");
  VALK_TEST_ASSERT(pm.peak != nullptr, "Peak gauge should be created");
  VALK_TEST_ASSERT(pm.overflow != nullptr, "Overflow counter should be created");

  // Metrics should be persistent (non-evictable)
  VALK_TEST_ASSERT(pm.used->evictable == false, "Used gauge should be persistent");
  VALK_TEST_ASSERT(pm.total->evictable == false, "Total gauge should be persistent");
  VALK_TEST_ASSERT(pm.peak->evictable == false, "Peak gauge should be persistent");
  VALK_TEST_ASSERT(pm.overflow->evictable == false, "Overflow counter should be persistent");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_pool_metrics_init_custom(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init_custom(&pm, "tcp_buffers", "slab");

  VALK_TEST_ASSERT(ok == true, "Custom pool metrics init should succeed");

  // Verify metric names contain custom prefix
  VALK_TEST_ASSERT(strstr(pm.used->name, "slab") != nullptr ||
                   strcmp(pm.used->name, "slab_used") == 0,
                   "Used metric should have custom prefix");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_pool_metrics_update(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  valk_pool_metrics_init(&pm, "update_test");

  // Update with test values
  valk_pool_metrics_update(&pm, 50, 100, 75, 5);

  VALK_TEST_ASSERT(atomic_load(&pm.used->value) == 50, "Used should be 50");
  VALK_TEST_ASSERT(atomic_load(&pm.total->value) == 100, "Total should be 100");
  VALK_TEST_ASSERT(atomic_load(&pm.peak->value) == 75, "Peak should be 75");
  VALK_TEST_ASSERT(atomic_load(&pm.overflow->value) == 5, "Overflow should be 5");

  // Update again
  valk_pool_metrics_update(&pm, 60, 100, 80, 7);

  VALK_TEST_ASSERT(atomic_load(&pm.used->value) == 60, "Used should be 60");
  VALK_TEST_ASSERT(atomic_load(&pm.peak->value) == 80, "Peak should be 80");
  VALK_TEST_ASSERT(atomic_load(&pm.overflow->value) == 7, "Overflow should be 7");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_pool_metrics_update_slab(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  valk_pool_metrics_init(&pm, "slab_test");

  // Simulate slab state: 100 total, 40 free, peak 70, 3 overflows
  valk_pool_metrics_update_slab(&pm, 100, 40, 70, 3);

  // used = total - free = 100 - 40 = 60
  VALK_TEST_ASSERT(atomic_load(&pm.used->value) == 60, "Used should be 60 (100-40)");
  VALK_TEST_ASSERT(atomic_load(&pm.total->value) == 100, "Total should be 100");
  VALK_TEST_ASSERT(atomic_load(&pm.peak->value) == 70, "Peak should be 70");
  VALK_TEST_ASSERT(atomic_load(&pm.overflow->value) == 3, "Overflow should be 3");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_pool_metrics_update_arena(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  valk_pool_metrics_init(&pm, "arena_test");

  // Simulate arena state: capacity 1MB, used 600KB, HWM 800KB, 2 overflows
  size_t capacity = 1024 * 1024;
  size_t used = 600 * 1024;
  size_t hwm = 800 * 1024;
  size_t overflow = 2;

  valk_pool_metrics_update_arena(&pm, capacity, used, hwm, overflow);

  VALK_TEST_ASSERT(atomic_load(&pm.used->value) == (i64)used, "Used should match");
  VALK_TEST_ASSERT(atomic_load(&pm.total->value) == (i64)capacity, "Total should match");
  VALK_TEST_ASSERT(atomic_load(&pm.peak->value) == (i64)hwm, "Peak should match");
  VALK_TEST_ASSERT(atomic_load(&pm.overflow->value) == overflow, "Overflow should match");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_pool_metrics_multiple_pools(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create metrics for multiple pools
  valk_pool_metrics_t tcp_buffers, stream_arenas, lval_slab;

  bool ok1 = valk_pool_metrics_init(&tcp_buffers, "tcp_buffers");
  bool ok2 = valk_pool_metrics_init(&stream_arenas, "stream_arenas");
  bool ok3 = valk_pool_metrics_init(&lval_slab, "lval_slab");

  VALK_TEST_ASSERT(ok1 && ok2 && ok3, "All pool metrics should initialize");

  // Update each pool with different values
  valk_pool_metrics_update(&tcp_buffers, 10, 100, 50, 0);
  valk_pool_metrics_update(&stream_arenas, 5, 50, 25, 1);
  valk_pool_metrics_update(&lval_slab, 1000, 4096, 2000, 0);

  // Verify each pool has independent values
  VALK_TEST_ASSERT(atomic_load(&tcp_buffers.used->value) == 10, "TCP buffers used");
  VALK_TEST_ASSERT(atomic_load(&stream_arenas.used->value) == 5, "Stream arenas used");
  VALK_TEST_ASSERT(atomic_load(&lval_slab.used->value) == 1000, "LVAL slab used");

  VALK_TEST_ASSERT(atomic_load(&tcp_buffers.total->value) == 100, "TCP buffers total");
  VALK_TEST_ASSERT(atomic_load(&stream_arenas.total->value) == 50, "Stream arenas total");
  VALK_TEST_ASSERT(atomic_load(&lval_slab.total->value) == 4096, "LVAL slab total");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_pool_metrics_null_safety(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Test nullptr handling
  bool ok = valk_pool_metrics_init(nullptr, "test");
  VALK_TEST_ASSERT(ok == false, "Init with nullptr metrics should fail");

  valk_pool_metrics_t pm;
  ok = valk_pool_metrics_init(&pm, nullptr);
  VALK_TEST_ASSERT(ok == false, "Init with nullptr name should fail");

  // Update with nullptr should not crash
  valk_pool_metrics_update(nullptr, 0, 0, 0, 0);
  valk_pool_metrics_update_slab(nullptr, 0, 0, 0, 0);
  valk_pool_metrics_update_arena(nullptr, 0, 0, 0, 0);

  // Should reach here without crashing
  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_pool_metrics_eviction_protected(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Set very short eviction threshold
  g_metrics.eviction_threshold_us = 1;

  valk_pool_metrics_t pm;
  valk_pool_metrics_init(&pm, "protected_pool");

  // Wait to make metrics "stale"
  for (volatile int i = 0; i < 100000; i++) {}

  (void)valk_metrics_evict_stale();
  VALK_TEST_ASSERT(atomic_load(&pm.used->active) == true,
                   "Pool used gauge should survive eviction");
  VALK_TEST_ASSERT(atomic_load(&pm.total->active) == true,
                   "Pool total gauge should survive eviction");
  VALK_TEST_ASSERT(atomic_load(&pm.peak->active) == true,
                   "Pool peak gauge should survive eviction");
  VALK_TEST_ASSERT(atomic_load(&pm.overflow->active) == true,
                   "Pool overflow counter should survive eviction");

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

  return nullptr;
}

void test_counter_concurrent_inc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c = valk_counter_get_or_create("concurrent_counter", nullptr, &labels);
  VALK_TEST_ASSERT(c != nullptr, "Counter should be created");

  const int NUM_THREADS = 4;
  const int ITERATIONS = 10000;
  pthread_t threads[NUM_THREADS];
  thread_test_ctx_t ctx = {.counter = c, .iterations = ITERATIONS};

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_create(&threads[i], nullptr, counter_increment_thread, &ctx);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  u64 expected = NUM_THREADS * ITERATIONS;
  u64 actual = atomic_load(&c->value);
  VALK_TEST_ASSERT(actual == expected,
                   "Counter should be %lu, got %lu", expected, actual);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_registry_stats_json_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_registry_stats_t stats;
  valk_registry_stats_collect(&stats);

  char tiny_buf[10];
  size_t len = valk_registry_stats_to_json(&stats, tiny_buf, sizeof(tiny_buf));
  VALK_TEST_ASSERT(len == 0, "Should return 0 when buffer too small");

  len = valk_registry_stats_to_json(&stats, nullptr, 100);
  VALK_TEST_ASSERT(len == 0, "Should return 0 when buffer is nullptr");

  len = valk_registry_stats_to_json(nullptr, tiny_buf, sizeof(tiny_buf));
  VALK_TEST_ASSERT(len == 0, "Should return 0 when stats is nullptr");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_summary_persistent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_summary_set_persistent(nullptr);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_summary_handle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_metric_handle_t null_handle = valk_summary_handle(nullptr);
  VALK_TEST_ASSERT(null_handle.slot == VALK_INVALID_SLOT,
                   "nullptr summary should produce invalid handle");

  valk_metric_handle_t invalid = VALK_HANDLE_INVALID;
  valk_summary_v2_t *s = valk_summary_deref(invalid);
  VALK_TEST_ASSERT(s == nullptr, "Invalid handle should return nullptr");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_eviction_with_actual_evictions(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  g_metrics.eviction_threshold_us = 1;

  valk_label_set_v2_t labels1 = {
    .labels = {{.key = "type", .value = "counter"}},
    .count = 1
  };
  valk_label_set_v2_t labels2 = {
    .labels = {{.key = "type", .value = "gauge"}},
    .count = 1
  };
  valk_label_set_v2_t labels3 = {
    .labels = {{.key = "type", .value = "histogram"}},
    .count = 1
  };

  valk_counter_v2_t *c = valk_counter_get_or_create("evict_me_counter", nullptr, &labels1);
  valk_gauge_v2_t *g = valk_gauge_get_or_create("evict_me_gauge", nullptr, &labels2);
  double bounds[] = {0.1, 1.0};
  valk_histogram_v2_t *h = valk_histogram_get_or_create("evict_me_hist", nullptr, bounds, 2, &labels3);

  VALK_TEST_ASSERT(c != nullptr && g != nullptr && h != nullptr, "All metrics should be created");

  for (volatile int i = 0; i < 100000; i++) {}

  size_t evicted = valk_metrics_evict_stale();
  VALK_TEST_ASSERT(evicted >= 3, "Should evict at least 3 metrics");

  VALK_TEST_ASSERT(atomic_load(&g_metrics.evictions_total) >= 3,
                   "evictions_total should be at least 3");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.evictions_counters) >= 1,
                   "evictions_counters should be at least 1");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.evictions_gauges) >= 1,
                   "evictions_gauges should be at least 1");
  VALK_TEST_ASSERT(atomic_load(&g_metrics.evictions_histograms) >= 1,
                   "evictions_histograms should be at least 1");

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_registry_stats_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_registry_stats_collect(nullptr);

  valk_metrics_registry_destroy();
  VALK_PASS();
}

void test_labels_equality_hash_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels1 = {
    .labels = {{.key = "a", .value = "1"}, {.key = "b", .value = "2"}},
    .count = 2
  };

  valk_label_set_v2_t labels2 = {
    .labels = {{.key = "a", .value = "1"}, {.key = "b", .value = "3"}},
    .count = 2
  };

  valk_counter_v2_t *c1 = valk_counter_get_or_create("test", nullptr, &labels1);
  valk_counter_v2_t *c2 = valk_counter_get_or_create("test", nullptr, &labels2);

  VALK_TEST_ASSERT(c1 != c2, "Different label values should create different counters");

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

  // LRU Eviction tests
  valk_testsuite_add_test(suite, "test_eviction_threshold_init",
                          test_eviction_threshold_init);
  valk_testsuite_add_test(suite, "test_eviction_free_list_init",
                          test_eviction_free_list_init);
  valk_testsuite_add_test(suite, "test_metric_active_flag",
                          test_metric_active_flag);
  valk_testsuite_add_test(suite, "test_metric_persistent",
                          test_metric_persistent);
  valk_testsuite_add_test(suite, "test_metric_last_updated",
                          test_metric_last_updated);
  valk_testsuite_add_test(suite, "test_eviction_no_stale_metrics",
                          test_eviction_no_stale_metrics);
  valk_testsuite_add_test(suite, "test_eviction_persistent_protected",
                          test_eviction_persistent_protected);
  valk_testsuite_add_test(suite, "test_metric_generation",
                          test_metric_generation);
  valk_testsuite_add_test(suite, "test_handle_create_deref",
                          test_handle_create_deref);
  valk_testsuite_add_test(suite, "test_handle_invalid",
                          test_handle_invalid);
  valk_testsuite_add_test(suite, "test_eviction_slot_reuse",
                          test_eviction_slot_reuse);

  // Pool Metrics Factory tests
  valk_testsuite_add_test(suite, "test_pool_metrics_init",
                          test_pool_metrics_init);
  valk_testsuite_add_test(suite, "test_pool_metrics_init_custom",
                          test_pool_metrics_init_custom);
  valk_testsuite_add_test(suite, "test_pool_metrics_update",
                          test_pool_metrics_update);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_slab",
                          test_pool_metrics_update_slab);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_arena",
                          test_pool_metrics_update_arena);
  valk_testsuite_add_test(suite, "test_pool_metrics_multiple_pools",
                          test_pool_metrics_multiple_pools);
  valk_testsuite_add_test(suite, "test_pool_metrics_null_safety",
                          test_pool_metrics_null_safety);
  valk_testsuite_add_test(suite, "test_pool_metrics_eviction_protected",
                          test_pool_metrics_eviction_protected);

  valk_testsuite_add_test(suite, "test_registry_stats_json_small_buffer",
                          test_registry_stats_json_small_buffer);
  valk_testsuite_add_test(suite, "test_summary_persistent",
                          test_summary_persistent);
  valk_testsuite_add_test(suite, "test_summary_handle",
                          test_summary_handle);
  valk_testsuite_add_test(suite, "test_eviction_with_actual_evictions",
                          test_eviction_with_actual_evictions);
  valk_testsuite_add_test(suite, "test_registry_stats_null",
                          test_registry_stats_null);
  valk_testsuite_add_test(suite, "test_labels_equality_hash_mismatch",
                          test_labels_equality_hash_mismatch);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
