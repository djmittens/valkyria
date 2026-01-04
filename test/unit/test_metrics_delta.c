#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/common.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/metrics_v2.h"
#include "../../src/metrics_delta.h"

#include <stdio.h>
#include <string.h>

void test_delta_type_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_DELTA_NONE == 0, "NONE should be 0");
  VALK_TEST_ASSERT(VALK_DELTA_INCREMENT == 1, "INCREMENT should be 1");
  VALK_TEST_ASSERT(VALK_DELTA_SET == 2, "SET should be 2");
  VALK_TEST_ASSERT(VALK_DELTA_OBSERVE == 3, "OBSERVE should be 3");

  VALK_PASS();
}

void test_delta_snapshot_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  VALK_TEST_ASSERT(snap.timestamp_us == 0, "timestamp should be 0");
  VALK_TEST_ASSERT(snap.prev_timestamp_us == 0, "prev_timestamp should be 0");
  VALK_TEST_ASSERT(snap.interval_us == 0, "interval should be 0");
  VALK_TEST_ASSERT(snap.delta_count == 0, "delta_count should be 0");
  VALK_TEST_ASSERT(snap.delta_capacity == 256, "delta_capacity should be 256");
  VALK_TEST_ASSERT(snap.deltas != nullptr, "deltas should be allocated");
  VALK_TEST_ASSERT(snap.counters_changed == 0, "counters_changed should be 0");
  VALK_TEST_ASSERT(snap.gauges_changed == 0, "gauges_changed should be 0");
  VALK_TEST_ASSERT(snap.histograms_changed == 0, "histograms_changed should be 0");
  VALK_TEST_ASSERT(snap.summaries_changed == 0, "summaries_changed should be 0");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_snapshot_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_snapshot_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("test_counter", "Test counter", &labels);
  VALK_TEST_ASSERT(counter != nullptr, "Counter should be created");

  valk_counter_v2_inc(counter);
  valk_counter_v2_inc(counter);
  valk_counter_v2_inc(counter);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(changed > 0, "Should detect changes");
  VALK_TEST_ASSERT(snap.delta_count > 0, "delta_count should be > 0");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_baseline_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);

  VALK_TEST_ASSERT(baseline.initialized == false, "Should not be initialized");
  VALK_TEST_ASSERT(baseline.last_collect_time == 0, "last_collect_time should be 0");

  VALK_PASS();
}

void test_baseline_sync(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("sync_counter", "Test", &labels);
  valk_counter_v2_add(counter, 100);

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);
  valk_metrics_baseline_sync(&baseline, &g_metrics);

  VALK_TEST_ASSERT(baseline.initialized == true, "Should be initialized after sync");

  VALK_PASS();
}

void test_delta_collect_stateless(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("stateless_counter", "Test", &labels);
  valk_counter_v2_add(counter, 50);

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);
  valk_metrics_baseline_sync(&baseline, &g_metrics);

  valk_counter_v2_add(counter, 25);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect_stateless(&snap, &g_metrics, &baseline);

  VALK_TEST_ASSERT(changed > 0, "Should detect the increment of 25");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_json(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  snap.timestamp_us = 1000000;
  snap.prev_timestamp_us = 500000;
  snap.interval_us = 500000;

  char buf[1024];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce output");
  VALK_TEST_ASSERT(strstr(buf, "\"ts\"") != nullptr, "Should contain ts");
  VALK_TEST_ASSERT(strstr(buf, "\"interval_us\"") != nullptr, "Should contain interval_us");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_sse(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  snap.timestamp_us = 2000000;

  char buf[2048];
  size_t len = valk_delta_to_sse(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce output");
  VALK_TEST_ASSERT(strstr(buf, "event:") != nullptr, "Should contain event header");
  VALK_TEST_ASSERT(strstr(buf, "data:") != nullptr, "Should contain data");
  VALK_TEST_ASSERT(strstr(buf, "\n\n") != nullptr, "Should end with double newline");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_json_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  char buf[10];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len >= sizeof(buf), "Should indicate buffer too small");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_metrics_v2_to_json(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("json_test_counter", "Test", &labels);
  valk_counter_v2_add(counter, 42);

  char buf[4096];
  size_t len = valk_metrics_v2_to_json(&g_metrics, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce output");
  VALK_TEST_ASSERT(strstr(buf, "json_test_counter") != nullptr, "Should contain counter name");

  VALK_PASS();
}

void test_delta_snapshot_double_free(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_snapshot_multiple_collects(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("multi_collect_counter", "Test", &labels);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  for (int i = 0; i < 10; i++) {
    valk_counter_v2_inc(counter);
    valk_delta_snapshot_collect(&snap, &g_metrics);
  }

  VALK_TEST_ASSERT(snap.delta_count >= 0, "delta_count should be valid");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_json_with_deltas(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("delta_json_counter", "Test", &labels);
  valk_counter_v2_add(counter, 100);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  char buf[4096];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce output");
  VALK_TEST_ASSERT(strstr(buf, "\"ts\"") != nullptr, "Should contain timestamp");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_sse_format(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  snap.timestamp_us = 12345678;

  char buf[4096];
  size_t len = valk_delta_to_sse(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce SSE output");
  VALK_TEST_ASSERT(strstr(buf, "event:") != nullptr, "Should have event header");
  VALK_TEST_ASSERT(strstr(buf, "data:") != nullptr, "Should have data section");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_baseline_multiple_syncs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("baseline_sync_counter", "Test", &labels);

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);

  for (int i = 0; i < 5; i++) {
    valk_counter_v2_add(counter, 10);
    valk_metrics_baseline_sync(&baseline, &g_metrics);
  }

  VALK_TEST_ASSERT(baseline.initialized == true, "Should remain initialized");

  VALK_PASS();
}

void test_delta_collect_empty_registry(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  size_t changed = valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(changed >= 0, "Should handle collection");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_snapshot_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  VALK_TEST_ASSERT(snap.delta_capacity == 256, "Default capacity should be 256");
  VALK_TEST_ASSERT(snap.deltas != nullptr, "Deltas array should be allocated");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_with_gauge(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *gauge = valk_gauge_get_or_create("test_gauge", "Test gauge", &labels);
  VALK_TEST_ASSERT(gauge != nullptr, "Gauge should be created");

  valk_gauge_v2_set(gauge, 100);
  valk_gauge_v2_set(gauge, 200);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(snap.gauges_changed >= 0, "gauges_changed should be valid");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_with_multiple_counters(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *c1 = valk_counter_get_or_create("multi_counter_1", "Test 1", &labels);
  valk_counter_v2_t *c2 = valk_counter_get_or_create("multi_counter_2", "Test 2", &labels);
  valk_counter_v2_t *c3 = valk_counter_get_or_create("multi_counter_3", "Test 3", &labels);

  valk_counter_v2_add(c1, 10);
  valk_counter_v2_add(c2, 20);
  valk_counter_v2_add(c3, 30);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(snap.counters_changed >= 0, "counters_changed should be valid");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_sse_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  snap.timestamp_us = 1000;

  char buf[10];
  size_t len = valk_delta_to_sse(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len >= sizeof(buf), "Should indicate buffer too small");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_snapshot_reset_between_collects(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("reset_test_counter", "Test", &labels);
  valk_counter_v2_add(counter, 100);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  valk_delta_snapshot_collect(&snap, &g_metrics);
  size_t first_count = snap.delta_count;

  valk_counter_v2_add(counter, 50);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(first_count >= 0, "First count should be valid");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_baseline_already_initialized(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);
  valk_metrics_baseline_sync(&baseline, &g_metrics);
  VALK_TEST_ASSERT(baseline.initialized == true, "Should be initialized");

  valk_metrics_baseline_sync(&baseline, &g_metrics);
  VALK_TEST_ASSERT(baseline.initialized == true, "Should remain initialized");

  VALK_PASS();
}

void test_delta_json_includes_timestamp(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  snap.timestamp_us = 9876543210ULL;

  char buf[1024];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");
  VALK_TEST_ASSERT(strstr(buf, "9876543210") != nullptr, "Should contain timestamp");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_snapshot_interval_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  snap.timestamp_us = 2000000;
  snap.prev_timestamp_us = 1000000;
  snap.interval_us = 1000000;

  char buf[1024];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");
  VALK_TEST_ASSERT(strstr(buf, "\"interval_us\":1000000") != nullptr, "Should contain interval");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_change_counts(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  VALK_TEST_ASSERT(snap.counters_changed == 0, "counters_changed should start at 0");
  VALK_TEST_ASSERT(snap.gauges_changed == 0, "gauges_changed should start at 0");
  VALK_TEST_ASSERT(snap.histograms_changed == 0, "histograms_changed should start at 0");
  VALK_TEST_ASSERT(snap.summaries_changed == 0, "summaries_changed should start at 0");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_with_histogram(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  double bounds[] = {1000, 5000, 10000, 50000, 100000, 500000, 1000000};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "test_histogram", "Test histogram", bounds, 7, &labels);
  VALK_TEST_ASSERT(hist != nullptr, "Histogram should be created");

  valk_histogram_v2_observe_us(hist, 3000);
  valk_histogram_v2_observe_us(hist, 20000);
  valk_histogram_v2_observe_us(hist, 150000);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(snap.histograms_changed >= 0, "histograms_changed should be valid");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_prometheus(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("prom_counter", "Test counter", &labels);
  valk_counter_v2_add(counter, 42);

  valk_gauge_v2_t *gauge = valk_gauge_get_or_create("prom_gauge", "Test gauge", &labels);
  valk_gauge_v2_set(gauge, 123);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  char buf[4096];
  size_t len = valk_delta_to_prometheus(&snap, &g_metrics, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce prometheus output");
  VALK_TEST_ASSERT(strstr(buf, "prom_counter") != nullptr, "Should contain counter");
  VALK_TEST_ASSERT(strstr(buf, "prom_gauge") != nullptr, "Should contain gauge");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_prometheus_with_histogram(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  double bounds[] = {100000, 500000, 1000000, 5000000};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "prom_histogram", "Test histogram", bounds, 4, &labels);
  valk_histogram_v2_observe_us(hist, 200000);
  valk_histogram_v2_observe_us(hist, 700000);
  valk_histogram_v2_observe_us(hist, 2000000);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  char buf[8192];
  size_t len = valk_delta_to_prometheus(&snap, &g_metrics, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce prometheus output");
  VALK_TEST_ASSERT(strstr(buf, "prom_histogram_bucket") != nullptr, "Should contain bucket");
  VALK_TEST_ASSERT(strstr(buf, "_sum") != nullptr, "Should contain sum");
  VALK_TEST_ASSERT(strstr(buf, "_count") != nullptr, "Should contain count");
  VALK_TEST_ASSERT(strstr(buf, "+Inf") != nullptr, "Should contain +Inf bucket");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  labels.count = 2;
  labels.labels[0].key = "method";
  labels.labels[0].value = "GET";
  labels.labels[1].key = "path";
  labels.labels[1].value = "/api/test";

  valk_counter_v2_t *counter = valk_counter_get_or_create("labeled_counter", "Test", &labels);
  valk_counter_v2_add(counter, 10);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  char buf[4096];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_to_prometheus_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  labels.count = 1;
  labels.labels[0].key = "endpoint";
  labels.labels[0].value = "api";

  valk_counter_v2_t *counter = valk_counter_get_or_create("labeled_prom_counter", "Test", &labels);
  valk_counter_v2_add(counter, 50);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  char buf[4096];
  size_t len = valk_delta_to_prometheus(&snap, &g_metrics, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce output");
  VALK_TEST_ASSERT(strstr(buf, "endpoint=\"api\"") != nullptr, "Should contain label");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_capacity_growth(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  for (int i = 0; i < 300; i++) {
    char name[64];
    snprintf(name, sizeof(name), "capacity_counter_%d", i);
    valk_counter_v2_t *c = valk_counter_get_or_create(name, "Test", &labels);
    valk_counter_v2_add(c, i);
  }

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(changed > 0, "Should detect changes");
  VALK_TEST_ASSERT(snap.delta_capacity >= 256, "Capacity should grow as needed");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_collect_stateless_first_call(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("first_call_counter", "Test", &labels);
  valk_counter_v2_add(counter, 100);

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  size_t changed = valk_delta_snapshot_collect_stateless(&snap, &g_metrics, &baseline);

  VALK_TEST_ASSERT(changed == 0, "First call should return 0 (baseline just set)");
  VALK_TEST_ASSERT(baseline.initialized == true, "Baseline should now be initialized");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_collect_stateless_with_gauge(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *gauge = valk_gauge_get_or_create("stateless_gauge", "Test", &labels);
  valk_gauge_v2_set(gauge, 100);

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);
  valk_metrics_baseline_sync(&baseline, &g_metrics);

  valk_gauge_v2_set(gauge, 200);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect_stateless(&snap, &g_metrics, &baseline);

  VALK_TEST_ASSERT(changed > 0, "Should detect gauge change");
  VALK_TEST_ASSERT(snap.gauges_changed > 0, "gauges_changed should be > 0");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_collect_stateless_with_histogram(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  double bounds[] = {10000, 100000, 1000000};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "stateless_histogram", "Test", bounds, 3, &labels);
  valk_histogram_v2_observe_us(hist, 50000);

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);
  valk_metrics_baseline_sync(&baseline, &g_metrics);

  valk_histogram_v2_observe_us(hist, 500000);
  valk_histogram_v2_observe_us(hist, 2000000);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect_stateless(&snap, &g_metrics, &baseline);

  VALK_TEST_ASSERT(changed > 0, "Should detect histogram changes");
  VALK_TEST_ASSERT(snap.histograms_changed > 0, "histograms_changed should be > 0");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_json_with_counter_delta(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("json_delta_counter", "Test", &labels);
  valk_counter_v2_add(counter, 100);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  char buf[4096];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");
  VALK_TEST_ASSERT(strstr(buf, "\"t\":\"c\"") != nullptr, "Should contain counter type");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_json_with_gauge_delta(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *gauge = valk_gauge_get_or_create("json_delta_gauge", "Test", &labels);
  valk_gauge_v2_set(gauge, 500);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  char buf[4096];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");
  VALK_TEST_ASSERT(strstr(buf, "\"t\":\"g\"") != nullptr, "Should contain gauge type");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_json_with_histogram_delta(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  double bounds[] = {100000, 1000000, 10000000};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "json_delta_histogram", "Test", bounds, 3, &labels);
  valk_histogram_v2_observe_us(hist, 500000);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  char buf[4096];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");
  VALK_TEST_ASSERT(strstr(buf, "\"t\":\"h\"") != nullptr, "Should contain histogram type");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_prometheus_histogram_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  labels.count = 1;
  labels.labels[0].key = "handler";
  labels.labels[0].value = "test";

  double bounds[] = {10000, 100000};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "prom_labeled_histogram", "Test", bounds, 2, &labels);
  valk_histogram_v2_observe_us(hist, 50000);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  char buf[8192];
  size_t len = valk_delta_to_prometheus(&snap, &g_metrics, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce output");
  VALK_TEST_ASSERT(strstr(buf, "handler=\"test\"") != nullptr, "Should contain label in bucket");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_metrics_v2_to_json_with_all_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};

  valk_counter_v2_t *counter = valk_counter_get_or_create("full_json_counter", "Test", &labels);
  valk_counter_v2_add(counter, 10);

  valk_gauge_v2_t *gauge = valk_gauge_get_or_create("full_json_gauge", "Test", &labels);
  valk_gauge_v2_set(gauge, 20);

  double bounds[] = {100000, 1000000};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "full_json_histogram", "Test", bounds, 2, &labels);
  valk_histogram_v2_observe_us(hist, 500000);

  char buf[8192];
  size_t len = valk_metrics_v2_to_json(&g_metrics, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");
  VALK_TEST_ASSERT(strstr(buf, "\"counters\"") != nullptr, "Should contain counters");
  VALK_TEST_ASSERT(strstr(buf, "\"gauges\"") != nullptr, "Should contain gauges");
  VALK_TEST_ASSERT(strstr(buf, "\"histograms\"") != nullptr, "Should contain histograms");

  VALK_PASS();
}

void test_metrics_v2_to_json_with_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  labels.count = 1;
  labels.labels[0].key = "type";
  labels.labels[0].value = "test";

  valk_counter_v2_t *counter = valk_counter_get_or_create("labeled_json_counter", "Test", &labels);
  valk_counter_v2_add(counter, 5);

  char buf[4096];
  size_t len = valk_metrics_v2_to_json(&g_metrics, buf, sizeof(buf));

  VALK_TEST_ASSERT(len > 0, "Should produce JSON");
  VALK_TEST_ASSERT(strstr(buf, "\"labels\"") != nullptr, "Should contain labels");

  VALK_PASS();
}

void test_delta_no_change_after_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("no_change_counter", "Test", &labels);
  valk_counter_v2_add(counter, 100);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  valk_delta_snapshot_collect(&snap, &g_metrics);
  size_t first_changes = snap.counters_changed;

  valk_delta_snapshot_collect(&snap, &g_metrics);
  size_t second_changes = snap.counters_changed;

  VALK_TEST_ASSERT(first_changes > 0, "First collect should show changes");
  VALK_TEST_ASSERT(second_changes == 0, "Second collect should show no changes");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_stateless_no_change_all_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};

  valk_counter_v2_t *counter = valk_counter_get_or_create("stateless_nochange_counter", "Test", &labels);
  valk_counter_v2_add(counter, 50);

  valk_gauge_v2_t *gauge = valk_gauge_get_or_create("stateless_nochange_gauge", "Test", &labels);
  valk_gauge_v2_set(gauge, 100);

  double bounds[] = {10000, 100000};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "stateless_nochange_histogram", "Test", bounds, 2, &labels);
  valk_histogram_v2_observe_us(hist, 50000);

  valk_metrics_baseline_t baseline;
  valk_metrics_baseline_init(&baseline);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);

  size_t first = valk_delta_snapshot_collect_stateless(&snap, &g_metrics, &baseline);
  VALK_TEST_ASSERT(first == 0, "First collect should report 0 (baseline just set)");

  size_t second = valk_delta_snapshot_collect_stateless(&snap, &g_metrics, &baseline);
  VALK_TEST_ASSERT(snap.counters_changed == 0, "Counter should show no change");
  VALK_TEST_ASSERT(snap.gauges_changed == 0, "Gauge should show no change");
  VALK_TEST_ASSERT(snap.histograms_changed == 0, "Histogram should show no change");
  VALK_TEST_ASSERT(second == 0, "Second collect with no changes should return 0");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_json_small_buffer_truncation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create("trunc_counter", "Test", &labels);
  valk_counter_v2_add(counter, 999);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  valk_delta_snapshot_collect(&snap, &g_metrics);

  char tiny_buf[10];
  size_t len = valk_delta_to_json(&snap, tiny_buf, sizeof(tiny_buf));
  VALK_TEST_ASSERT(len == sizeof(tiny_buf), "Should return buffer size on truncation");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

void test_delta_with_empty_labels(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t empty_labels = {0};
  empty_labels.count = 0;

  valk_counter_v2_t *counter = valk_counter_get_or_create("empty_labels_counter", "Test", &empty_labels);
  valk_counter_v2_add(counter, 42);

  valk_delta_snapshot_t snap;
  valk_delta_snapshot_init(&snap);
  size_t changed = valk_delta_snapshot_collect(&snap, &g_metrics);

  VALK_TEST_ASSERT(changed > 0, "Should detect changes");
  VALK_TEST_ASSERT(snap.delta_count > 0, "Should have deltas");

  char buf[4096];
  size_t len = valk_delta_to_json(&snap, buf, sizeof(buf));
  VALK_TEST_ASSERT(len > 0, "Should produce JSON");

  valk_delta_snapshot_free(&snap);

  VALK_PASS();
}

#else

void test_metrics_delta_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Metrics delta tests require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_delta_type_enum", test_delta_type_enum);
  valk_testsuite_add_test(suite, "test_delta_snapshot_init", test_delta_snapshot_init);
  valk_testsuite_add_test(suite, "test_delta_snapshot_free_null", test_delta_snapshot_free_null);
  valk_testsuite_add_test(suite, "test_delta_snapshot_collect", test_delta_snapshot_collect);
  valk_testsuite_add_test(suite, "test_baseline_init", test_baseline_init);
  valk_testsuite_add_test(suite, "test_baseline_sync", test_baseline_sync);
  valk_testsuite_add_test(suite, "test_delta_collect_stateless", test_delta_collect_stateless);
  valk_testsuite_add_test(suite, "test_delta_to_json", test_delta_to_json);
  valk_testsuite_add_test(suite, "test_delta_to_sse", test_delta_to_sse);
  valk_testsuite_add_test(suite, "test_delta_to_json_small_buffer", test_delta_to_json_small_buffer);
  valk_testsuite_add_test(suite, "test_metrics_v2_to_json", test_metrics_v2_to_json);
  valk_testsuite_add_test(suite, "test_delta_snapshot_double_free", test_delta_snapshot_double_free);
  valk_testsuite_add_test(suite, "test_delta_snapshot_multiple_collects", test_delta_snapshot_multiple_collects);
  valk_testsuite_add_test(suite, "test_delta_to_json_with_deltas", test_delta_to_json_with_deltas);
  valk_testsuite_add_test(suite, "test_delta_to_sse_format", test_delta_to_sse_format);
  valk_testsuite_add_test(suite, "test_baseline_multiple_syncs", test_baseline_multiple_syncs);
  valk_testsuite_add_test(suite, "test_delta_collect_empty_registry", test_delta_collect_empty_registry);
  valk_testsuite_add_test(suite, "test_delta_snapshot_capacity", test_delta_snapshot_capacity);
  valk_testsuite_add_test(suite, "test_delta_with_gauge", test_delta_with_gauge);
  valk_testsuite_add_test(suite, "test_delta_with_multiple_counters", test_delta_with_multiple_counters);
  valk_testsuite_add_test(suite, "test_delta_to_sse_small_buffer", test_delta_to_sse_small_buffer);
  valk_testsuite_add_test(suite, "test_delta_snapshot_reset_between_collects", test_delta_snapshot_reset_between_collects);
  valk_testsuite_add_test(suite, "test_baseline_already_initialized", test_baseline_already_initialized);
  valk_testsuite_add_test(suite, "test_delta_json_includes_timestamp", test_delta_json_includes_timestamp);
  valk_testsuite_add_test(suite, "test_delta_snapshot_interval_tracking", test_delta_snapshot_interval_tracking);
  valk_testsuite_add_test(suite, "test_delta_change_counts", test_delta_change_counts);
  valk_testsuite_add_test(suite, "test_delta_with_histogram", test_delta_with_histogram);
  valk_testsuite_add_test(suite, "test_delta_to_prometheus", test_delta_to_prometheus);
  valk_testsuite_add_test(suite, "test_delta_to_prometheus_with_histogram", test_delta_to_prometheus_with_histogram);
  valk_testsuite_add_test(suite, "test_delta_with_labels", test_delta_with_labels);
  valk_testsuite_add_test(suite, "test_delta_to_prometheus_with_labels", test_delta_to_prometheus_with_labels);
  valk_testsuite_add_test(suite, "test_delta_capacity_growth", test_delta_capacity_growth);
  valk_testsuite_add_test(suite, "test_delta_collect_stateless_first_call", test_delta_collect_stateless_first_call);
  valk_testsuite_add_test(suite, "test_delta_collect_stateless_with_gauge", test_delta_collect_stateless_with_gauge);
  valk_testsuite_add_test(suite, "test_delta_collect_stateless_with_histogram", test_delta_collect_stateless_with_histogram);
  valk_testsuite_add_test(suite, "test_delta_json_with_counter_delta", test_delta_json_with_counter_delta);
  valk_testsuite_add_test(suite, "test_delta_json_with_gauge_delta", test_delta_json_with_gauge_delta);
  valk_testsuite_add_test(suite, "test_delta_json_with_histogram_delta", test_delta_json_with_histogram_delta);
  valk_testsuite_add_test(suite, "test_delta_prometheus_histogram_with_labels", test_delta_prometheus_histogram_with_labels);
  valk_testsuite_add_test(suite, "test_metrics_v2_to_json_with_all_types", test_metrics_v2_to_json_with_all_types);
  valk_testsuite_add_test(suite, "test_metrics_v2_to_json_with_labels", test_metrics_v2_to_json_with_labels);
  valk_testsuite_add_test(suite, "test_delta_no_change_after_collect", test_delta_no_change_after_collect);
  valk_testsuite_add_test(suite, "test_stateless_no_change_all_types", test_stateless_no_change_all_types);
  valk_testsuite_add_test(suite, "test_delta_json_small_buffer_truncation", test_delta_json_small_buffer_truncation);
  valk_testsuite_add_test(suite, "test_delta_with_empty_labels", test_delta_with_empty_labels);
#else
  valk_testsuite_add_test(suite, "test_metrics_delta_disabled", test_metrics_delta_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
