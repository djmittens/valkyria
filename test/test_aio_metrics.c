#include "testing.h"

#ifdef VALK_METRICS_ENABLED

#include "../src/aio_metrics.h"
#include "../src/memory.h"
#include <string.h>
#include <stdio.h>

void test_metrics_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Verify all counters are zero
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 0,
                   "requests_total should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_active) == 0,
                   "requests_active should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_errors) == 0,
                   "requests_errors should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_total) == 0,
                   "connections_total should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_active) == 0,
                   "connections_active should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.streams_total) == 0,
                   "streams_total should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.streams_active) == 0,
                   "streams_active should be 0");
  VALK_TEST_ASSERT(metrics.start_time_us > 0,
                   "start_time_us should be set");

  VALK_PASS();
}

void test_metrics_connection_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Successful connection
  valk_aio_metrics_on_connection(&metrics, true);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_total) == 1,
                   "connections_total should be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_active) == 1,
                   "connections_active should be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_failed) == 0,
                   "connections_failed should be 0");

  // Failed connection
  valk_aio_metrics_on_connection(&metrics, false);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_total) == 2,
                   "connections_total should be 2");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_active) == 1,
                   "connections_active should still be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_failed) == 1,
                   "connections_failed should be 1");

  // Close connection
  valk_aio_metrics_on_close(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_active) == 0,
                   "connections_active should be 0 after close");

  VALK_PASS();
}

void test_metrics_stream_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Start stream
  valk_aio_metrics_on_stream_start(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.streams_total) == 1,
                   "streams_total should be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.streams_active) == 1,
                   "streams_active should be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_active) == 1,
                   "requests_active should be 1");

  // End stream successfully
  valk_aio_metrics_on_stream_end(&metrics, false, 1000, 512, 256);
  VALK_TEST_ASSERT(atomic_load(&metrics.streams_active) == 0,
                   "streams_active should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_active) == 0,
                   "requests_active should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 1,
                   "requests_total should be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_errors) == 0,
                   "requests_errors should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_sent) == 512,
                   "request_bytes_sent should be 512");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_recv) == 256,
                   "request_bytes_recv should be 256");
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_sent_total) == 512,
                   "bytes_sent_total should be 512");
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_recv_total) == 256,
                   "bytes_recv_total should be 256");

  // Start another stream and end with error
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, true, 2000, 1024, 512);
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 2,
                   "requests_total should be 2");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_errors) == 1,
                   "requests_errors should be 1");

  VALK_PASS();
}

void test_metrics_json_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Add some data
  valk_aio_metrics_on_connection(&metrics, true);
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 5000, 1024, 512);

  // Generate JSON
  char* json = valk_aio_metrics_to_json(&metrics, NULL);
  VALK_TEST_ASSERT(json != NULL, "JSON output should not be NULL");

  // Basic validation - check for expected keys
  VALK_TEST_ASSERT(strstr(json, "\"uptime_seconds\"") != NULL,
                   "JSON should contain uptime_seconds");
  VALK_TEST_ASSERT(strstr(json, "\"connections\"") != NULL,
                   "JSON should contain connections");
  VALK_TEST_ASSERT(strstr(json, "\"streams\"") != NULL,
                   "JSON should contain streams");
  VALK_TEST_ASSERT(strstr(json, "\"requests\"") != NULL,
                   "JSON should contain requests");
  VALK_TEST_ASSERT(strstr(json, "\"bytes\"") != NULL,
                   "JSON should contain bytes");

  // Check values
  VALK_TEST_ASSERT(strstr(json, "\"total\": 1") != NULL,
                   "JSON should show 1 connection/stream/request");

  free(json);
  VALK_PASS();
}

void test_metrics_prometheus_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Add some data
  valk_aio_metrics_on_connection(&metrics, true);
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 5000, 1024, 512);

  // Generate Prometheus format
  char* prom = valk_aio_metrics_to_prometheus(&metrics, NULL);
  VALK_TEST_ASSERT(prom != NULL, "Prometheus output should not be NULL");

  // Basic validation - check for expected metric names
  VALK_TEST_ASSERT(strstr(prom, "# HELP") != NULL,
                   "Prometheus should contain HELP annotations");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE") != NULL,
                   "Prometheus should contain TYPE annotations");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_uptime_seconds") != NULL,
                   "Prometheus should contain uptime metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_connections_total") != NULL,
                   "Prometheus should contain connections_total");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_streams_total") != NULL,
                   "Prometheus should contain streams_total");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_requests_total") != NULL,
                   "Prometheus should contain requests_total");

  // Check metric types
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_aio_connections_total counter") != NULL,
                   "connections_total should be a counter");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_aio_connections_active gauge") != NULL,
                   "connections_active should be a gauge");

  free(prom);
  VALK_PASS();
}

#else // !VALK_METRICS_ENABLED

void test_metrics_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Metrics not enabled (VALK_METRICS_ENABLED not defined)");
}

#endif // VALK_METRICS_ENABLED

int main(void) {
  // Initialize memory system required by test framework
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_metrics_init", test_metrics_init);
  valk_testsuite_add_test(suite, "test_metrics_connection_tracking",
                          test_metrics_connection_tracking);
  valk_testsuite_add_test(suite, "test_metrics_stream_tracking",
                          test_metrics_stream_tracking);
  valk_testsuite_add_test(suite, "test_metrics_json_output",
                          test_metrics_json_output);
  valk_testsuite_add_test(suite, "test_metrics_prometheus_output",
                          test_metrics_prometheus_output);
#else
  valk_testsuite_add_test(suite, "test_metrics_disabled", test_metrics_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
