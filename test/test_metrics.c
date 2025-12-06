// test/test_metrics.c
#include "testing.h"
#include "common.h"
#include "memory.h"

#ifdef VALK_METRICS_ENABLED

#include "metrics.h"
#include <string.h>
#include <math.h>

//-----------------------------------------------------------------------------
// Test: Lifecycle
//-----------------------------------------------------------------------------

void test_metrics_init_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Verify initial state
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.counter_count) == 0,
                   "Initial counter_count should be 0");
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.gauge_count) == 0,
                   "Initial gauge_count should be 0");
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.histogram_count) == 0,
                   "Initial histogram_count should be 0");
  VALK_TEST_ASSERT(g_valk_metrics.label_pool_count == 0,
                   "Initial label_pool_count should be 0");
  VALK_TEST_ASSERT(g_valk_metrics.start_time_us > 0,
                   "start_time_us should be set");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_metrics_multiple_init_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Multiple init/destroy cycles
  for (int i = 0; i < 3; i++) {
    valk_metrics_init();

    valk_counter_t* c = valk_metric_counter("test_counter", NULL);
    VALK_TEST_ASSERT(c != NULL, "Counter should be created");
    valk_counter_inc(c);

    VALK_TEST_ASSERT(atomic_load(&c->value) == 1,
                     "Counter value should be 1");

    valk_metrics_destroy();
  }

  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Counter Operations
//-----------------------------------------------------------------------------

void test_counter_registration(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  valk_counter_t* c1 = valk_metric_counter("requests_total", NULL);
  VALK_TEST_ASSERT(c1 != NULL, "Counter should be created");
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.counter_count) == 1,
                   "counter_count should be 1");

  // Same name should return same pointer
  valk_counter_t* c2 = valk_metric_counter("requests_total", NULL);
  VALK_TEST_ASSERT(c2 == c1, "Same counter name should return same pointer");
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.counter_count) == 1,
                   "counter_count should still be 1");

  // Different name should create new counter
  valk_counter_t* c3 = valk_metric_counter("errors_total", NULL);
  VALK_TEST_ASSERT(c3 != NULL && c3 != c1,
                   "Different name should create new counter");
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.counter_count) == 2,
                   "counter_count should be 2");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_counter_inc_add(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  valk_counter_t* c = valk_metric_counter("test_counter", NULL);
  VALK_TEST_ASSERT(c != NULL, "Counter should be created");

  // Initial value should be 0
  VALK_TEST_ASSERT(atomic_load(&c->value) == 0, "Initial value should be 0");

  // Test increment
  valk_counter_inc(c);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 1, "Value should be 1 after inc");

  valk_counter_inc(c);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 2, "Value should be 2 after inc");

  // Test add
  valk_counter_add(c, 10);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 12, "Value should be 12 after add");

  valk_counter_add(c, 0);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 12, "Value should be 12 after add(0)");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_counter_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Create counter with labels
  valk_counter_t* c1 = valk_metric_counter("http_requests",
                                            "method", "GET",
                                            "status", "200",
                                            NULL);
  VALK_TEST_ASSERT(c1 != NULL, "Counter with labels should be created");
  VALK_TEST_ASSERT(c1->labels.count == 2, "Should have 2 labels");

  valk_counter_inc(c1);
  VALK_TEST_ASSERT(atomic_load(&c1->value) == 1, "Value should be 1");

  // Different labels should create different counter
  valk_counter_t* c2 = valk_metric_counter("http_requests",
                                            "method", "POST",
                                            "status", "200",
                                            NULL);
  VALK_TEST_ASSERT(c2 != NULL && c2 != c1,
                   "Different labels should create different counter");
  VALK_TEST_ASSERT(atomic_load(&c2->value) == 0, "New counter value should be 0");

  valk_counter_add(c2, 5);

  // Same name+labels should return same counter
  valk_counter_t* c3 = valk_metric_counter("http_requests",
                                            "method", "GET",
                                            "status", "200",
                                            NULL);
  VALK_TEST_ASSERT(c3 == c1, "Same name+labels should return same counter");
  VALK_TEST_ASSERT(atomic_load(&c3->value) == 1, "Value should still be 1");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_counter_labels_array(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  const char* keys[] = {"method", "path"};
  const char* vals[] = {"GET", "/api/users"};

  valk_counter_t* c = valk_metric_counter_labels("api_requests", keys, vals, 2);
  VALK_TEST_ASSERT(c != NULL, "Counter should be created");
  VALK_TEST_ASSERT(c->labels.count == 2, "Should have 2 labels");

  valk_counter_inc(c);
  VALK_TEST_ASSERT(atomic_load(&c->value) == 1, "Value should be 1");

  valk_metrics_destroy();
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Gauge Operations
//-----------------------------------------------------------------------------

void test_gauge_registration(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  valk_gauge_t* g1 = valk_metric_gauge("memory_bytes", NULL);
  VALK_TEST_ASSERT(g1 != NULL, "Gauge should be created");
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.gauge_count) == 1,
                   "gauge_count should be 1");

  // Same name should return same pointer
  valk_gauge_t* g2 = valk_metric_gauge("memory_bytes", NULL);
  VALK_TEST_ASSERT(g2 == g1, "Same gauge name should return same pointer");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_gauge_operations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  valk_gauge_t* g = valk_metric_gauge("test_gauge", NULL);
  VALK_TEST_ASSERT(g != NULL, "Gauge should be created");

  // Initial value should be 0
  VALK_TEST_ASSERT(atomic_load(&g->value) == 0, "Initial value should be 0");

  // Test set
  valk_gauge_set(g, 100);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 100, "Value should be 100 after set");

  // Test increment
  valk_gauge_inc(g);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 101, "Value should be 101 after inc");

  // Test decrement
  valk_gauge_dec(g);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 100, "Value should be 100 after dec");

  // Test add (positive)
  valk_gauge_add(g, 50);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 150, "Value should be 150 after add(50)");

  // Test add (negative)
  valk_gauge_add(g, -30);
  VALK_TEST_ASSERT(atomic_load(&g->value) == 120, "Value should be 120 after add(-30)");

  // Test set to negative
  valk_gauge_set(g, -42);
  VALK_TEST_ASSERT(atomic_load(&g->value) == -42, "Value should be -42 after set");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_gauge_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  valk_gauge_t* g1 = valk_metric_gauge("memory_bytes",
                                        "type", "heap",
                                        NULL);
  VALK_TEST_ASSERT(g1 != NULL, "Gauge with labels should be created");

  valk_gauge_set(g1, 1024);

  valk_gauge_t* g2 = valk_metric_gauge("memory_bytes",
                                        "type", "stack",
                                        NULL);
  VALK_TEST_ASSERT(g2 != NULL && g2 != g1,
                   "Different labels should create different gauge");

  valk_gauge_set(g2, 512);

  VALK_TEST_ASSERT(atomic_load(&g1->value) == 1024, "g1 value should be 1024");
  VALK_TEST_ASSERT(atomic_load(&g2->value) == 512, "g2 value should be 512");

  valk_metrics_destroy();
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Histogram Operations
//-----------------------------------------------------------------------------

void test_histogram_registration(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  double bounds[] = {0.001, 0.01, 0.1, 1.0};
  valk_histogram_t* h = valk_metric_histogram("request_duration",
                                               bounds, 4,
                                               NULL);
  VALK_TEST_ASSERT(h != NULL, "Histogram should be created");
  VALK_TEST_ASSERT(h->bucket_count == 4, "Should have 4 buckets");
  VALK_TEST_ASSERT(atomic_load(&g_valk_metrics.histogram_count) == 1,
                   "histogram_count should be 1");

  // Verify bounds
  for (int i = 0; i < 4; i++) {
    VALK_TEST_ASSERT(h->bucket_bounds[i] == bounds[i],
                     "Bucket bound %d should match", i);
  }

  valk_metrics_destroy();
  VALK_PASS();
}

void test_histogram_observe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  double bounds[] = {0.1, 0.5, 1.0, 5.0};
  valk_histogram_t* h = valk_metric_histogram("request_duration",
                                               bounds, 4,
                                               NULL);
  VALK_TEST_ASSERT(h != NULL, "Histogram should be created");

  // Initial state
  VALK_TEST_ASSERT(atomic_load(&h->count) == 0, "Initial count should be 0");
  VALK_TEST_ASSERT(atomic_load(&h->sum_us) == 0, "Initial sum should be 0");

  // Observe value in first bucket (0.05 <= 0.1)
  valk_histogram_observe(h, 0.05);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 1, "Count should be 1");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[0]) == 1, "Bucket 0 should be 1");
  VALK_TEST_ASSERT(atomic_load(&h->sum_us) == 50000, "Sum should be 50000 us");

  // Observe value in second bucket (0.3 <= 0.5)
  valk_histogram_observe(h, 0.3);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 2, "Count should be 2");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[1]) == 1, "Bucket 1 should be 1");

  // Observe value in third bucket (0.75 <= 1.0)
  valk_histogram_observe(h, 0.75);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 3, "Count should be 3");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[2]) == 1, "Bucket 2 should be 1");

  // Observe value in +Inf bucket (10.0 > 5.0)
  valk_histogram_observe(h, 10.0);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 4, "Count should be 4");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[4]) == 1, "+Inf bucket should be 1");

  // Verify sum (0.05 + 0.3 + 0.75 + 10.0 = 11.1 seconds = 11,100,000 us)
  uint64_t expected_sum = (uint64_t)(11.1 * 1e6);
  uint64_t actual_sum = atomic_load(&h->sum_us);
  VALK_TEST_ASSERT(actual_sum >= expected_sum - 100 && actual_sum <= expected_sum + 100,
                   "Sum should be approximately %lu, got %lu", expected_sum, actual_sum);

  valk_metrics_destroy();
  VALK_PASS();
}

void test_histogram_observe_us(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  double bounds[] = {0.001, 0.01};
  valk_histogram_t* h = valk_metric_histogram("latency",
                                               bounds, 2,
                                               NULL);
  VALK_TEST_ASSERT(h != NULL, "Histogram should be created");

  // Observe 500 microseconds (0.0005 seconds, <= 0.001)
  valk_histogram_observe_us(h, 500);
  VALK_TEST_ASSERT(atomic_load(&h->count) == 1, "Count should be 1");
  VALK_TEST_ASSERT(atomic_load(&h->buckets[0]) == 1, "Bucket 0 should be 1");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_histogram_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  double bounds[] = {0.1, 1.0};

  valk_histogram_t* h1 = valk_metric_histogram("http_duration",
                                                bounds, 2,
                                                "method", "GET",
                                                NULL);
  VALK_TEST_ASSERT(h1 != NULL, "Histogram with labels should be created");

  valk_histogram_observe(h1, 0.5);

  valk_histogram_t* h2 = valk_metric_histogram("http_duration",
                                                bounds, 2,
                                                "method", "POST",
                                                NULL);
  VALK_TEST_ASSERT(h2 != NULL && h2 != h1,
                   "Different labels should create different histogram");

  valk_histogram_observe(h2, 1.5);

  VALK_TEST_ASSERT(atomic_load(&h1->count) == 1, "h1 count should be 1");
  VALK_TEST_ASSERT(atomic_load(&h2->count) == 1, "h2 count should be 1");

  valk_metrics_destroy();
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Label Interning
//-----------------------------------------------------------------------------

void test_label_interning(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Create two counters with same label strings
  valk_counter_t* c1 = valk_metric_counter("test",
                                            "env", "prod",
                                            NULL);
  valk_counter_t* c2 = valk_metric_counter("test2",
                                            "env", "prod",
                                            NULL);

  // Label strings should be interned (same pointer)
  VALK_TEST_ASSERT(c1->labels.labels[0].key == c2->labels.labels[0].key,
                   "Interned label keys should have same pointer");
  VALK_TEST_ASSERT(c1->labels.labels[0].value == c2->labels.labels[0].value,
                   "Interned label values should have same pointer");

  // Same metric name should also be interned
  valk_counter_t* c3 = valk_metric_counter("test", NULL);
  VALK_TEST_ASSERT(c1->name == c3->name,
                   "Interned metric names should have same pointer");

  valk_metrics_destroy();
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Iteration
//-----------------------------------------------------------------------------

typedef struct {
  size_t count;
  uint64_t total_value;
} iter_ctx_t;

static void count_counters(const valk_counter_t* c, void* ctx) {
  UNUSED(c);
  iter_ctx_t* ictx = (iter_ctx_t*)ctx;
  ictx->count++;
  ictx->total_value += atomic_load(&c->value);
}

static void count_gauges(const valk_gauge_t* g, void* ctx) {
  UNUSED(g);
  iter_ctx_t* ictx = (iter_ctx_t*)ctx;
  ictx->count++;
}

static void count_histograms(const valk_histogram_t* h, void* ctx) {
  UNUSED(h);
  iter_ctx_t* ictx = (iter_ctx_t*)ctx;
  ictx->count++;
}

void test_iteration_counters(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Create several counters
  valk_counter_t* c1 = valk_metric_counter("c1", NULL);
  valk_counter_t* c2 = valk_metric_counter("c2", NULL);
  valk_counter_t* c3 = valk_metric_counter("c3", NULL);

  valk_counter_add(c1, 10);
  valk_counter_add(c2, 20);
  valk_counter_add(c3, 30);

  iter_ctx_t ctx = {0};
  valk_metrics_foreach_counter(count_counters, &ctx);

  VALK_TEST_ASSERT(ctx.count == 3, "Should iterate 3 counters");
  VALK_TEST_ASSERT(ctx.total_value == 60, "Total value should be 60");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_iteration_gauges(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  valk_metric_gauge("g1", NULL);
  valk_metric_gauge("g2", NULL);

  iter_ctx_t ctx = {0};
  valk_metrics_foreach_gauge(count_gauges, &ctx);

  VALK_TEST_ASSERT(ctx.count == 2, "Should iterate 2 gauges");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_iteration_histograms(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  double bounds[] = {0.1};
  valk_metric_histogram("h1", bounds, 1, NULL);
  valk_metric_histogram("h2", bounds, 1, NULL);
  valk_metric_histogram("h3", bounds, 1, NULL);

  iter_ctx_t ctx = {0};
  valk_metrics_foreach_histogram(count_histograms, &ctx);

  VALK_TEST_ASSERT(ctx.count == 3, "Should iterate 3 histograms");

  valk_metrics_destroy();
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Export
//-----------------------------------------------------------------------------

void test_export_prometheus(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Create some metrics
  valk_counter_t* c = valk_metric_counter("requests_total",
                                           "method", "GET",
                                           NULL);
  valk_counter_add(c, 42);

  valk_gauge_t* g = valk_metric_gauge("memory_bytes", NULL);
  valk_gauge_set(g, 1024);

  double bounds[] = {0.1, 1.0};
  valk_histogram_t* h = valk_metric_histogram("latency",
                                               bounds, 2,
                                               NULL);
  valk_histogram_observe(h, 0.5);
  valk_histogram_observe(h, 1.5);

  // Export to Prometheus format
  char buf[4096];
  size_t len = valk_metrics_prometheus(buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Prometheus export should produce output");
  VALK_TEST_ASSERT(len < sizeof(buf), "Output should fit in buffer");

  // Verify output contains expected metrics
  VALK_TEST_ASSERT(strstr(buf, "requests_total") != NULL,
                   "Should contain counter name");
  VALK_TEST_ASSERT(strstr(buf, "method=\"GET\"") != NULL,
                   "Should contain counter label");
  VALK_TEST_ASSERT(strstr(buf, "42") != NULL,
                   "Should contain counter value");
  VALK_TEST_ASSERT(strstr(buf, "memory_bytes") != NULL,
                   "Should contain gauge name");
  VALK_TEST_ASSERT(strstr(buf, "1024") != NULL,
                   "Should contain gauge value");
  VALK_TEST_ASSERT(strstr(buf, "latency_bucket") != NULL,
                   "Should contain histogram buckets");
  VALK_TEST_ASSERT(strstr(buf, "latency_sum") != NULL,
                   "Should contain histogram sum");
  VALK_TEST_ASSERT(strstr(buf, "latency_count") != NULL,
                   "Should contain histogram count");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_export_json(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Create some metrics
  valk_counter_t* c = valk_metric_counter("test_counter", NULL);
  valk_counter_add(c, 100);

  valk_gauge_t* g = valk_metric_gauge("test_gauge", NULL);
  valk_gauge_set(g, -50);

  // Export to JSON format
  char buf[4096];
  size_t len = valk_metrics_json(buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "JSON export should produce output");
  VALK_TEST_ASSERT(len < sizeof(buf), "Output should fit in buffer");

  // Verify JSON structure
  VALK_TEST_ASSERT(strstr(buf, "uptime_seconds") != NULL,
                   "Should contain uptime");
  VALK_TEST_ASSERT(strstr(buf, "\"counters\"") != NULL,
                   "Should contain counters array");
  VALK_TEST_ASSERT(strstr(buf, "\"gauges\"") != NULL,
                   "Should contain gauges array");
  VALK_TEST_ASSERT(strstr(buf, "\"histograms\"") != NULL,
                   "Should contain histograms array");
  VALK_TEST_ASSERT(strstr(buf, "test_counter") != NULL,
                   "Should contain counter name");
  VALK_TEST_ASSERT(strstr(buf, "test_gauge") != NULL,
                   "Should contain gauge name");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_export_values_match(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  valk_counter_t* c = valk_metric_counter("test", NULL);
  valk_counter_add(c, 123);

  // Export both formats
  char prom_buf[2048];
  char json_buf[2048];

  valk_metrics_prometheus(prom_buf, sizeof(prom_buf));
  valk_metrics_json(json_buf, sizeof(json_buf));

  // Both should contain the value 123
  VALK_TEST_ASSERT(strstr(prom_buf, "123") != NULL,
                   "Prometheus should contain value 123");
  VALK_TEST_ASSERT(strstr(json_buf, "123") != NULL,
                   "JSON should contain value 123");

  valk_metrics_destroy();
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Limits
//-----------------------------------------------------------------------------

void test_counter_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Fill up to limit
  for (size_t i = 0; i < VALK_METRICS_MAX_COUNTERS; i++) {
    char name[64];
    snprintf(name, sizeof(name), "counter_%zu", i);
    valk_counter_t* c = valk_metric_counter(name, NULL);
    VALK_TEST_ASSERT(c != NULL, "Counter %zu should be created", i);
  }

  // Next one should fail
  valk_counter_t* c = valk_metric_counter("overflow_counter", NULL);
  VALK_TEST_ASSERT(c == NULL, "Counter beyond limit should return NULL");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_max_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Create counter with maximum labels
  valk_counter_t* c = valk_metric_counter("test",
                                           "l1", "v1",
                                           "l2", "v2",
                                           "l3", "v3",
                                           "l4", "v4",
                                           "l5", "v5",
                                           "l6", "v6",
                                           "l7", "v7",
                                           "l8", "v8",
                                           NULL);
  VALK_TEST_ASSERT(c != NULL, "Counter with max labels should be created");
  VALK_TEST_ASSERT(c->labels.count == VALK_METRICS_MAX_LABELS,
                   "Should have max labels");

  valk_metrics_destroy();
  VALK_PASS();
}

void test_histogram_bucket_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_init();

  // Try to create histogram with more buckets than allowed
  double bounds[VALK_METRICS_MAX_BUCKETS + 5];
  for (size_t i = 0; i < VALK_METRICS_MAX_BUCKETS + 5; i++) {
    bounds[i] = (double)(i + 1) * 0.1;
  }

  valk_histogram_t* h = valk_metric_histogram("test",
                                               bounds,
                                               VALK_METRICS_MAX_BUCKETS + 5,
                                               NULL);
  VALK_TEST_ASSERT(h != NULL, "Histogram should be created");
  VALK_TEST_ASSERT(h->bucket_count == VALK_METRICS_MAX_BUCKETS,
                   "Bucket count should be capped at max");

  valk_metrics_destroy();
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Main
//-----------------------------------------------------------------------------

int main(int argc, const char** argv) {
  UNUSED(argc);
  UNUSED(argv);

  // Initialize memory allocator
  valk_mem_init_malloc();

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  // Lifecycle tests
  valk_testsuite_add_test(suite, "test_metrics_init_destroy",
                          test_metrics_init_destroy);
  valk_testsuite_add_test(suite, "test_metrics_multiple_init_destroy",
                          test_metrics_multiple_init_destroy);

  // Counter tests
  valk_testsuite_add_test(suite, "test_counter_registration",
                          test_counter_registration);
  valk_testsuite_add_test(suite, "test_counter_inc_add",
                          test_counter_inc_add);
  valk_testsuite_add_test(suite, "test_counter_with_labels",
                          test_counter_with_labels);
  valk_testsuite_add_test(suite, "test_counter_labels_array",
                          test_counter_labels_array);

  // Gauge tests
  valk_testsuite_add_test(suite, "test_gauge_registration",
                          test_gauge_registration);
  valk_testsuite_add_test(suite, "test_gauge_operations",
                          test_gauge_operations);
  valk_testsuite_add_test(suite, "test_gauge_with_labels",
                          test_gauge_with_labels);

  // Histogram tests
  valk_testsuite_add_test(suite, "test_histogram_registration",
                          test_histogram_registration);
  valk_testsuite_add_test(suite, "test_histogram_observe",
                          test_histogram_observe);
  valk_testsuite_add_test(suite, "test_histogram_observe_us",
                          test_histogram_observe_us);
  valk_testsuite_add_test(suite, "test_histogram_with_labels",
                          test_histogram_with_labels);

  // Label interning tests
  valk_testsuite_add_test(suite, "test_label_interning",
                          test_label_interning);

  // Iteration tests
  valk_testsuite_add_test(suite, "test_iteration_counters",
                          test_iteration_counters);
  valk_testsuite_add_test(suite, "test_iteration_gauges",
                          test_iteration_gauges);
  valk_testsuite_add_test(suite, "test_iteration_histograms",
                          test_iteration_histograms);

  // Export tests
  valk_testsuite_add_test(suite, "test_export_prometheus",
                          test_export_prometheus);
  valk_testsuite_add_test(suite, "test_export_json",
                          test_export_json);
  valk_testsuite_add_test(suite, "test_export_values_match",
                          test_export_values_match);

  // Limit tests
  valk_testsuite_add_test(suite, "test_counter_limit",
                          test_counter_limit);
  valk_testsuite_add_test(suite, "test_max_labels",
                          test_max_labels);
  valk_testsuite_add_test(suite, "test_histogram_bucket_limit",
                          test_histogram_bucket_limit);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

#else

//=============================================================================
// METRICS DISABLED - Skip Tests
//=============================================================================

#include <stdio.h>

int main(int argc, const char** argv) {
  UNUSED(argc);
  UNUSED(argv);

  fprintf(stderr, "SKIP: Metrics tests disabled (VALK_METRICS not enabled)\n");
  return 0;
}

#endif // VALK_METRICS_ENABLED
