#include "testing.h"

#ifdef VALK_METRICS_ENABLED

#include "../src/aio/aio_metrics.h"
#include "../src/memory.h"
#include "../src/gc.h"
#include "../src/parser.h"
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

  // Check values (compact JSON has no spaces after colons)
  VALK_TEST_ASSERT(strstr(json, "\"total\":1") != NULL,
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

void test_system_stats_prometheus_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_stats_t stats;
  valk_aio_system_stats_init(&stats, 64, 128, 256);

  // Add some test data
  valk_aio_system_stats_on_server_start(&stats);
  valk_aio_system_stats_on_client_start(&stats);
  valk_aio_system_stats_on_handle_create(&stats);
  valk_aio_system_stats_on_arena_acquire(&stats);

  // Generate Prometheus format
  char* prom = valk_aio_system_stats_to_prometheus(&stats, NULL);
  VALK_TEST_ASSERT(prom != NULL, "Prometheus output should not be NULL");

  // Basic validation - check for expected metric names
  VALK_TEST_ASSERT(strstr(prom, "# HELP") != NULL,
                   "Prometheus should contain HELP annotations");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE") != NULL,
                   "Prometheus should contain TYPE annotations");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_servers_count") != NULL,
                   "Prometheus should contain servers_count metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_clients_count") != NULL,
                   "Prometheus should contain clients_count metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_handles_count") != NULL,
                   "Prometheus should contain handles_count metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_arenas_used") != NULL,
                   "Prometheus should contain arenas_used metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_arenas_total") != NULL,
                   "Prometheus should contain arenas_total metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_tcp_buffers_used") != NULL,
                   "Prometheus should contain tcp_buffers_used metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_tcp_buffers_total") != NULL,
                   "Prometheus should contain tcp_buffers_total metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_queue_depth") != NULL,
                   "Prometheus should contain queue_depth metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_pending_requests") != NULL,
                   "Prometheus should contain pending_requests metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_pending_responses") != NULL,
                   "Prometheus should contain pending_responses metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_arena_pool_overflow_total") != NULL,
                   "Prometheus should contain arena_pool_overflow_total metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_tcp_buffer_overflow_total") != NULL,
                   "Prometheus should contain tcp_buffer_overflow_total metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_connections_rejected_load_total") != NULL,
                   "Prometheus should contain connections_rejected_load_total metric");

  // Check metric types
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_aio_servers_count gauge") != NULL,
                   "servers_count should be a gauge");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_aio_arena_pool_overflow_total counter") != NULL,
                   "arena_pool_overflow_total should be a counter");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_aio_tcp_buffer_overflow_total counter") != NULL,
                   "tcp_buffer_overflow_total should be a counter");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_aio_connections_rejected_load_total counter") != NULL,
                   "connections_rejected_load_total should be a counter");

  // Check actual values
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_servers_count 1") != NULL,
                   "servers_count should be 1");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_clients_count 1") != NULL,
                   "clients_count should be 1");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_handles_count 1") != NULL,
                   "handles_count should be 1");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_arenas_used 1") != NULL,
                   "arenas_used should be 1");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_arenas_total 64") != NULL,
                   "arenas_total should be 64");
  VALK_TEST_ASSERT(strstr(prom, "valk_aio_tcp_buffers_total 128") != NULL,
                   "tcp_buffers_total should be 128");

  free(prom);
  VALK_PASS();
}

void test_stream_metrics_with_duration(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Start a stream
  valk_aio_metrics_on_stream_start(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.streams_active) == 1,
                   "streams_active should be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_active) == 1,
                   "requests_active should be 1");

  // End stream with a 5ms (5000us) duration
  valk_aio_metrics_on_stream_end(&metrics, false, 5000, 256, 128);

  // Verify duration was recorded
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 5000,
                   "request_duration_us_sum should be 5000");
  VALK_TEST_ASSERT(atomic_load(&metrics.streams_active) == 0,
                   "streams_active should be 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 1,
                   "requests_total should be 1");

  // Add another stream with 10ms duration
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 10000, 512, 256);

  // Verify cumulative duration
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 15000,
                   "request_duration_us_sum should be 15000 (5000 + 10000)");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 2,
                   "requests_total should be 2");

  // Add a third stream with 2ms duration
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 2000, 1024, 512);

  // Verify final cumulative duration
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 17000,
                   "request_duration_us_sum should be 17000 (5000 + 10000 + 2000)");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 3,
                   "requests_total should be 3");

  VALK_PASS();
}

void test_request_duration_histogram(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Test various duration ranges to verify bucketing logic
  // Durations: 100us, 1ms, 10ms, 100ms, 1s
  u64 durations[] = {100, 1000, 10000, 100000, 1000000};
  size_t num_durations = sizeof(durations) / sizeof(durations[0]);

  for (size_t i = 0; i < num_durations; i++) {
    valk_aio_metrics_on_stream_start(&metrics);
    valk_aio_metrics_on_stream_end(&metrics, false, durations[i], 128, 64);
  }

  // Verify all requests were counted
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == num_durations,
                   "requests_total should match number of durations");

  // Verify total duration sum
  u64 expected_sum = 0;
  for (size_t i = 0; i < num_durations; i++) {
    expected_sum += durations[i];
  }
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == expected_sum,
                   "request_duration_us_sum should equal sum of all durations");

  // Verify average duration calculation
  u64 total_requests = atomic_load(&metrics.requests_total);
  u64 total_duration = atomic_load(&metrics.request_duration_us_sum);
  u64 avg_duration = total_duration / total_requests;

  // Average of the test durations: (100 + 1000 + 10000 + 100000 + 1000000) / 5 = 222220
  VALK_TEST_ASSERT(avg_duration == 222220,
                   "average duration should be 222220 microseconds");

  VALK_PASS();
}

void test_metrics_duration_microsecond_sum(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Verify initial state
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 0,
                   "request_duration_us_sum should start at 0");

  // Record first request: 1ms = 1000us
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 1000, 100, 50);
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 1000,
                   "duration sum should be 1000");

  // Record second request: 2ms = 2000us
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 2000, 200, 100);
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 3000,
                   "duration sum should be 3000 (1000 + 2000)");

  // Record third request: 3.5ms = 3500us
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 3500, 300, 150);
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 6500,
                   "duration sum should be 6500 (1000 + 2000 + 3500)");

  // Record fourth request: 500us
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 500, 400, 200);
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 7000,
                   "duration sum should be 7000 (1000 + 2000 + 3500 + 500)");

  // Record fifth request: 10ms = 10000us
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 10000, 500, 250);
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 17000,
                   "duration sum should be 17000 (1000 + 2000 + 3500 + 500 + 10000)");

  // Verify total request count matches
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 5,
                   "requests_total should be 5");

  // Verify that error requests also record duration
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, true, 5000, 600, 300);
  VALK_TEST_ASSERT(atomic_load(&metrics.request_duration_us_sum) == 22000,
                   "duration sum should be 22000 (includes error request duration)");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_errors) == 1,
                   "requests_errors should be 1");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 6,
                   "requests_total should be 6 (includes error request)");

  VALK_PASS();
}

void test_stream_metrics_bytes_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  // Verify initial state
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_sent_total) == 0,
                   "bytes_sent_total should start at 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_recv_total) == 0,
                   "bytes_recv_total should start at 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_sent) == 0,
                   "request_bytes_sent should start at 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_recv) == 0,
                   "request_bytes_recv should start at 0");

  // First stream: 1024 bytes sent, 512 bytes received
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 1000, 1024, 512);

  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_sent_total) == 1024,
                   "bytes_sent_total should be 1024");
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_recv_total) == 512,
                   "bytes_recv_total should be 512");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_sent) == 1024,
                   "request_bytes_sent should be 1024");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_recv) == 512,
                   "request_bytes_recv should be 512");

  // Second stream: 2048 bytes sent, 1024 bytes received
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 2000, 2048, 1024);

  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_sent_total) == 3072,
                   "bytes_sent_total should be 3072 (1024 + 2048)");
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_recv_total) == 1536,
                   "bytes_recv_total should be 1536 (512 + 1024)");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_sent) == 3072,
                   "request_bytes_sent should be 3072");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_recv) == 1536,
                   "request_bytes_recv should be 1536");

  // Third stream: 512 bytes sent, 256 bytes received
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 3000, 512, 256);

  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_sent_total) == 3584,
                   "bytes_sent_total should be 3584 (1024 + 2048 + 512)");
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_recv_total) == 1792,
                   "bytes_recv_total should be 1792 (512 + 1024 + 256)");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_sent) == 3584,
                   "request_bytes_sent should be 3584");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_recv) == 1792,
                   "request_bytes_recv should be 1792");

  // Fourth stream with error: 4096 bytes sent, 2048 bytes received
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, true, 4000, 4096, 2048);

  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_sent_total) == 7680,
                   "bytes_sent_total should be 7680 (includes error stream)");
  VALK_TEST_ASSERT(atomic_load(&metrics.bytes_recv_total) == 3840,
                   "bytes_recv_total should be 3840 (includes error stream)");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_sent) == 7680,
                   "request_bytes_sent should be 7680");
  VALK_TEST_ASSERT(atomic_load(&metrics.request_bytes_recv) == 3840,
                   "request_bytes_recv should be 3840");
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_errors) == 1,
                   "requests_errors should be 1");

  // Verify total request count
  VALK_TEST_ASSERT(atomic_load(&metrics.requests_total) == 4,
                   "requests_total should be 4");

  VALK_PASS();
}

void test_vm_metrics_collect_with_gc_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");

  // Set up thread context with heap pointer
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.heap = heap;

  // Do some allocations to generate non-zero metrics
  void* ptr1 = valk_gc_malloc_heap_alloc(heap, 512);
  void* ptr2 = valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(ptr1 != NULL, "Allocation 1 should succeed");
  VALK_TEST_ASSERT(ptr2 != NULL, "Allocation 2 should succeed");

  // Collect VM metrics
  valk_vm_metrics_t vm;
  valk_vm_metrics_collect(&vm, heap, NULL);

  // Verify that heap metrics are populated
  VALK_TEST_ASSERT(vm.gc_heap_total > 0,
                   "gc_heap_total should be > 0, got %zu", vm.gc_heap_total);
  VALK_TEST_ASSERT(vm.gc_heap_used > 0,
                   "gc_heap_used should be > 0 after allocations, got %zu", vm.gc_heap_used);
  VALK_TEST_ASSERT(vm.gc_heap_used <= vm.gc_heap_total,
                   "gc_heap_used should be <= gc_heap_total");

  // Restore thread context and cleanup
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

void test_vm_metrics_collect_null_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Collect VM metrics with NULL heap
  valk_vm_metrics_t vm;
  valk_vm_metrics_collect(&vm, NULL, NULL);

  // Verify that GC metrics are zero when heap is NULL
  VALK_TEST_ASSERT(vm.gc_cycles == 0,
                   "gc_cycles should be 0 with NULL heap");
  VALK_TEST_ASSERT(vm.gc_pause_us_total == 0,
                   "gc_pause_us_total should be 0 with NULL heap");
  VALK_TEST_ASSERT(vm.gc_pause_us_max == 0,
                   "gc_pause_us_max should be 0 with NULL heap");
  VALK_TEST_ASSERT(vm.gc_reclaimed_bytes == 0,
                   "gc_reclaimed_bytes should be 0 with NULL heap");
  VALK_TEST_ASSERT(vm.gc_heap_used == 0,
                   "gc_heap_used should be 0 with NULL heap");
  VALK_TEST_ASSERT(vm.gc_heap_total == 0,
                   "gc_heap_total should be 0 with NULL heap");

  VALK_PASS();
}

void test_vm_metrics_json_contains_heap_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.heap = heap;

  void* ptr1 = valk_gc_malloc_heap_alloc(heap, 512);
  void* ptr2 = valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(ptr1 != NULL, "Allocation 1 should succeed");
  VALK_TEST_ASSERT(ptr2 != NULL, "Allocation 2 should succeed");

  valk_vm_metrics_t vm;
  valk_vm_metrics_collect(&vm, heap, NULL);
  char* json = valk_vm_metrics_to_json(&vm, NULL);
  VALK_TEST_ASSERT(json != NULL, "JSON output should not be NULL");

  // Verify JSON contains heap fields
  VALK_TEST_ASSERT(strstr(json, "\"heap_used_bytes\"") != NULL,
                   "JSON should contain heap_used_bytes field");
  VALK_TEST_ASSERT(strstr(json, "\"heap_total_bytes\"") != NULL,
                   "JSON should contain heap_total_bytes field");

  // Verify the values are not zero (should have been populated)
  // We can't check exact values, but we can check they're present
  // The JSON format should be like: "heap_used_bytes": 1234,
  char* heap_used_line = strstr(json, "\"heap_used_bytes\"");
  VALK_TEST_ASSERT(heap_used_line != NULL, "Should find heap_used_bytes in JSON");

  // Basic sanity check - the line should contain a colon and a number
  char* colon = strchr(heap_used_line, ':');
  VALK_TEST_ASSERT(colon != NULL, "Should find colon after heap_used_bytes");

  // Cleanup
  free(json);
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

void test_vm_metrics_prometheus_contains_heap_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.heap = heap;
  void* ptr1 = valk_gc_malloc_heap_alloc(heap, 512);
  void* ptr2 = valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(ptr1 != NULL, "Allocation 1 should succeed");
  VALK_TEST_ASSERT(ptr2 != NULL, "Allocation 2 should succeed");

  // Collect and generate Prometheus format
  valk_vm_metrics_t vm;
  valk_vm_metrics_collect(&vm, heap, NULL);
  char* prom = valk_vm_metrics_to_prometheus(&vm, NULL);
  VALK_TEST_ASSERT(prom != NULL, "Prometheus output should not be NULL");

  // Verify Prometheus contains heap metrics
  VALK_TEST_ASSERT(strstr(prom, "valk_gc_heap_used_bytes") != NULL,
                   "Prometheus should contain valk_gc_heap_used_bytes metric");
  VALK_TEST_ASSERT(strstr(prom, "valk_gc_heap_total_bytes") != NULL,
                   "Prometheus should contain valk_gc_heap_total_bytes metric");

  // Check for HELP and TYPE annotations
  VALK_TEST_ASSERT(strstr(prom, "# HELP valk_gc_heap_used_bytes") != NULL,
                   "Prometheus should contain HELP for heap_used");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_gc_heap_used_bytes gauge") != NULL,
                   "heap_used should be a gauge");
  VALK_TEST_ASSERT(strstr(prom, "# HELP valk_gc_heap_total_bytes") != NULL,
                   "Prometheus should contain HELP for heap_total");
  VALK_TEST_ASSERT(strstr(prom, "# TYPE valk_gc_heap_total_bytes gauge") != NULL,
                   "heap_total should be a gauge");

  // Cleanup
  free(prom);
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

void test_connection_state_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  VALK_TEST_ASSERT(atomic_load(&metrics.connections_connecting) == 0,
                   "connections_connecting should start at 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_idle) == 0,
                   "connections_idle should start at 0");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_closing) == 0,
                   "connections_closing should start at 0");

  valk_aio_metrics_on_connecting(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_connecting) == 1,
                   "connections_connecting should be 1");

  valk_aio_metrics_on_connected(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_connecting) == 0,
                   "connections_connecting should be 0 after connected");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_active) == 1,
                   "connections_active should be 1 after connected");

  valk_aio_metrics_on_idle(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_active) == 0,
                   "connections_active should be 0 after idle");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_idle) == 1,
                   "connections_idle should be 1");

  valk_aio_metrics_on_reactivate(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_idle) == 0,
                   "connections_idle should be 0 after reactivate");
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_active) == 1,
                   "connections_active should be 1 after reactivate");

  valk_aio_metrics_on_closing(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_closing) == 1,
                   "connections_closing should be 1");

  valk_aio_metrics_on_closed(&metrics);
  VALK_TEST_ASSERT(atomic_load(&metrics.connections_closing) == 0,
                   "connections_closing should be 0 after closed");

  VALK_PASS();
}

void test_system_stats_full_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_stats_t stats;
  valk_aio_system_stats_init(&stats, 64, 128, 256);

  VALK_TEST_ASSERT(stats.arenas_total == 64, "arenas_total should be 64");
  VALK_TEST_ASSERT(stats.tcp_buffers_total == 128, "tcp_buffers_total should be 128");
  VALK_TEST_ASSERT(stats.queue_capacity == 256, "queue_capacity should be 256");

  valk_aio_system_stats_on_server_start(&stats);
  valk_aio_system_stats_on_server_start(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.servers_count) == 2, "servers_count should be 2");

  valk_aio_system_stats_on_server_stop(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.servers_count) == 1, "servers_count should be 1");

  valk_aio_system_stats_on_client_start(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.clients_count) == 1, "clients_count should be 1");

  valk_aio_system_stats_on_client_stop(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.clients_count) == 0, "clients_count should be 0");

  valk_aio_system_stats_on_handle_create(&stats);
  valk_aio_system_stats_on_handle_create(&stats);
  valk_aio_system_stats_on_handle_create(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.handles_count) == 3, "handles_count should be 3");

  valk_aio_system_stats_on_handle_close(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.handles_count) == 2, "handles_count should be 2");

  valk_aio_system_stats_on_arena_acquire(&stats);
  valk_aio_system_stats_on_arena_acquire(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.arenas_used) == 2, "arenas_used should be 2");

  valk_aio_system_stats_on_arena_release(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.arenas_used) == 1, "arenas_used should be 1");

  valk_aio_system_stats_update_queue(&stats, 10, 5);
  VALK_TEST_ASSERT(atomic_load(&stats.pending_requests) == 10, "pending_requests should be 10");
  VALK_TEST_ASSERT(atomic_load(&stats.pending_responses) == 5, "pending_responses should be 5");
  VALK_TEST_ASSERT(atomic_load(&stats.queue_depth) == 15, "queue_depth should be 15");

  VALK_PASS();
}

void test_pending_stream_backpressure_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_stats_t stats;
  valk_aio_system_stats_init(&stats, 64, 128, 256);

  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_current) == 0,
                   "pending_streams_current should start at 0");
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_total) == 0,
                   "pending_streams_total should start at 0");

  valk_aio_system_stats_on_pending_enqueue(&stats);
  valk_aio_system_stats_on_pending_enqueue(&stats);
  valk_aio_system_stats_on_pending_enqueue(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_current) == 3,
                   "pending_streams_current should be 3");
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_total) == 3,
                   "pending_streams_total should be 3");

  valk_aio_system_stats_on_pending_dequeue(&stats, 1000);
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_current) == 2,
                   "pending_streams_current should be 2");
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_processed) == 1,
                   "pending_streams_processed should be 1");
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_wait_us) == 1000,
                   "pending_streams_wait_us should be 1000");

  valk_aio_system_stats_on_pending_dequeue(&stats, 2000);
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_wait_us) == 3000,
                   "pending_streams_wait_us should be 3000");

  valk_aio_system_stats_on_pending_drop(&stats);
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_current) == 0,
                   "pending_streams_current should be 0");
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_dropped) == 1,
                   "pending_streams_dropped should be 1");

  valk_aio_system_stats_update_pending_current(&stats, 42);
  VALK_TEST_ASSERT(atomic_load(&stats.pending_streams_current) == 42,
                   "pending_streams_current should be 42");

  VALK_PASS();
}

void test_combined_json_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  valk_aio_system_stats_t stats;
  valk_aio_system_stats_init(&stats, 64, 128, 256);

  valk_aio_metrics_on_connection(&metrics, true);
  valk_aio_metrics_on_stream_start(&metrics);
  valk_aio_metrics_on_stream_end(&metrics, false, 5000, 1024, 512);

  valk_aio_system_stats_on_server_start(&stats);
  valk_aio_system_stats_on_handle_create(&stats);
  valk_aio_system_stats_on_arena_acquire(&stats);

  char* json = valk_aio_combined_to_json(&metrics, &stats, NULL);
  VALK_TEST_ASSERT(json != NULL, "Combined JSON should not be NULL");

  VALK_TEST_ASSERT(strstr(json, "\"uptime_seconds\"") != NULL,
                   "JSON should contain uptime_seconds");
  VALK_TEST_ASSERT(strstr(json, "\"system\"") != NULL,
                   "JSON should contain system section");
  VALK_TEST_ASSERT(strstr(json, "\"connections\"") != NULL,
                   "JSON should contain connections section");
  VALK_TEST_ASSERT(strstr(json, "\"streams\"") != NULL,
                   "JSON should contain streams section");
  VALK_TEST_ASSERT(strstr(json, "\"bytes\"") != NULL,
                   "JSON should contain bytes section");
  VALK_TEST_ASSERT(strstr(json, "\"servers\":1") != NULL,
                   "JSON should show 1 server");
  VALK_TEST_ASSERT(strstr(json, "\"arenas_used\":1") != NULL,
                   "JSON should show 1 arena used");

  free(json);
  VALK_PASS();
}

void test_combined_json_named_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_metrics_t metrics;
  valk_aio_metrics_init(&metrics);

  valk_aio_system_stats_t stats;
  valk_aio_system_stats_init(&stats, 64, 128, 256);

  valk_aio_metrics_on_connection(&metrics, true);
  valk_aio_system_stats_on_server_start(&stats);

  char* json = valk_aio_combined_to_json_named("test-system", &metrics, &stats, NULL);
  VALK_TEST_ASSERT(json != NULL, "Named JSON should not be NULL");

  VALK_TEST_ASSERT(strstr(json, "\"name\":\"test-system\"") != NULL,
                   "JSON should contain the system name");
  VALK_TEST_ASSERT(strstr(json, "\"uptime_seconds\"") != NULL,
                   "JSON should contain uptime_seconds");
  VALK_TEST_ASSERT(strstr(json, "\"loop\"") != NULL,
                   "JSON should contain loop section");
  VALK_TEST_ASSERT(strstr(json, "\"system\"") != NULL,
                   "JSON should contain system section");
  VALK_TEST_ASSERT(strstr(json, "\"connections\"") != NULL,
                   "JSON should contain connections section");

  free(json);

  char* json_null_name = valk_aio_combined_to_json_named(NULL, &metrics, &stats, NULL);
  VALK_TEST_ASSERT(json_null_name != NULL, "JSON with NULL name should not be NULL");
  VALK_TEST_ASSERT(strstr(json_null_name, "\"name\":\"main\"") != NULL,
                   "JSON should default to 'main' when name is NULL");
  free(json_null_name);

  VALK_PASS();
}

void test_http_client_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http_clients_registry_t reg = {0};
  atomic_store(&reg.count, 0);

  int idx = valk_http_client_register(&reg, "redis", "cache", 10);
  VALK_TEST_ASSERT(idx == 0, "First client should get index 0");
  VALK_TEST_ASSERT(atomic_load(&reg.count) == 1, "Registry count should be 1");

  valk_http_client_metrics_t* client = &reg.clients[idx];
  VALK_TEST_ASSERT(strcmp(client->name, "redis") == 0, "Client name should be 'redis'");
  VALK_TEST_ASSERT(strcmp(client->type, "cache") == 0, "Client type should be 'cache'");
  VALK_TEST_ASSERT(atomic_load(&client->pool_size) == 10, "Pool size should be 10");

  valk_http_client_on_operation(client, 5000, false, false);
  VALK_TEST_ASSERT(atomic_load(&client->operations_total) == 1, "operations_total should be 1");
  VALK_TEST_ASSERT(atomic_load(&client->latency_us_sum) == 5000, "latency_us_sum should be 5000");
  VALK_TEST_ASSERT(atomic_load(&client->latency_count) == 1, "latency_count should be 1");
  VALK_TEST_ASSERT(atomic_load(&client->errors_total) == 0, "errors_total should be 0");
  VALK_TEST_ASSERT(atomic_load(&client->retries_total) == 0, "retries_total should be 0");

  valk_http_client_on_operation(client, 3000, true, false);
  VALK_TEST_ASSERT(atomic_load(&client->operations_total) == 2, "operations_total should be 2");
  VALK_TEST_ASSERT(atomic_load(&client->errors_total) == 1, "errors_total should be 1");

  valk_http_client_on_operation(client, 2000, false, true);
  VALK_TEST_ASSERT(atomic_load(&client->operations_total) == 3, "operations_total should be 3");
  VALK_TEST_ASSERT(atomic_load(&client->retries_total) == 1, "retries_total should be 1");

  valk_http_client_on_cache(client, true);
  VALK_TEST_ASSERT(atomic_load(&client->cache_hits_total) == 1, "cache_hits_total should be 1");

  valk_http_client_on_cache(client, false);
  VALK_TEST_ASSERT(atomic_load(&client->cache_misses_total) == 1, "cache_misses_total should be 1");

  VALK_PASS();
}

void test_http_client_registry_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http_clients_registry_t reg = {0};
  atomic_store(&reg.count, VALK_MAX_HTTP_CLIENTS);

  int idx = valk_http_client_register(&reg, "overflow", "test", 1);
  VALK_TEST_ASSERT(idx == -1, "Should return -1 when registry is full");
  VALK_TEST_ASSERT(atomic_load(&reg.count) == VALK_MAX_HTTP_CLIENTS,
                   "Count should remain at max");

  VALK_PASS();
}

void test_http_clients_prometheus_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http_clients_registry_t reg = {0};
  atomic_store(&reg.count, 0);

  char* prom_empty = valk_http_clients_to_prometheus(&reg, NULL);
  VALK_TEST_ASSERT(prom_empty == NULL, "Empty registry should return NULL");

  int idx1 = valk_http_client_register(&reg, "redis", "cache", 10);
  int idx2 = valk_http_client_register(&reg, "postgres", "db", 5);
  VALK_TEST_ASSERT(idx1 >= 0, "Redis registration should succeed");
  VALK_TEST_ASSERT(idx2 >= 0, "Postgres registration should succeed");

  valk_http_client_on_operation(&reg.clients[idx1], 1000, false, false);
  valk_http_client_on_cache(&reg.clients[idx1], true);
  valk_http_client_on_cache(&reg.clients[idx1], false);

  char* prom = valk_http_clients_to_prometheus(&reg, NULL);
  VALK_TEST_ASSERT(prom != NULL, "Prometheus output should not be NULL");

  VALK_TEST_ASSERT(strstr(prom, "http_client_connections_active") != NULL,
                   "Should contain connections_active metric");
  VALK_TEST_ASSERT(strstr(prom, "http_client_pool_size") != NULL,
                   "Should contain pool_size metric");
  VALK_TEST_ASSERT(strstr(prom, "http_client_operations_total") != NULL,
                   "Should contain operations_total metric");
  VALK_TEST_ASSERT(strstr(prom, "http_client_errors_total") != NULL,
                   "Should contain errors_total metric");
  VALK_TEST_ASSERT(strstr(prom, "http_client_retries_total") != NULL,
                   "Should contain retries_total metric");
  VALK_TEST_ASSERT(strstr(prom, "http_client_cache_hits_total") != NULL,
                   "Should contain cache_hits_total metric");
  VALK_TEST_ASSERT(strstr(prom, "http_client_cache_misses_total") != NULL,
                   "Should contain cache_misses_total metric");
  VALK_TEST_ASSERT(strstr(prom, "http_client_latency_seconds_avg") != NULL,
                   "Should contain latency_seconds_avg metric");

  VALK_TEST_ASSERT(strstr(prom, "client=\"redis\"") != NULL,
                   "Should contain redis client label");
  VALK_TEST_ASSERT(strstr(prom, "client=\"postgres\"") != NULL,
                   "Should contain postgres client label");

  free(prom);
  VALK_PASS();
}

void test_vm_metrics_null_input(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_vm_metrics_collect(NULL, NULL, NULL);

  char* json = valk_vm_metrics_to_json(NULL, NULL);
  VALK_TEST_ASSERT(json == NULL, "JSON should be NULL for NULL input");

  char* prom = valk_vm_metrics_to_prometheus(NULL, NULL);
  VALK_TEST_ASSERT(prom == NULL, "Prometheus should be NULL for NULL input");

  VALK_PASS();
}

void test_system_stats_prometheus_null_input(VALK_TEST_ARGS()) {
  VALK_TEST();

  char* prom = valk_aio_system_stats_to_prometheus(NULL, NULL);
  VALK_TEST_ASSERT(prom == NULL, "Should return NULL for NULL stats");

  VALK_PASS();
}

void test_http_clients_prometheus_null_input(VALK_TEST_ARGS()) {
  VALK_TEST();

  char* prom = valk_http_clients_to_prometheus(NULL, NULL);
  VALK_TEST_ASSERT(prom == NULL, "Should return NULL for NULL registry");

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
  valk_testsuite_add_test(suite, "test_system_stats_prometheus_output",
                          test_system_stats_prometheus_output);
  valk_testsuite_add_test(suite, "test_stream_metrics_with_duration",
                          test_stream_metrics_with_duration);
  valk_testsuite_add_test(suite, "test_request_duration_histogram",
                          test_request_duration_histogram);
  valk_testsuite_add_test(suite, "test_metrics_duration_microsecond_sum",
                          test_metrics_duration_microsecond_sum);
  valk_testsuite_add_test(suite, "test_stream_metrics_bytes_tracking",
                          test_stream_metrics_bytes_tracking);
  valk_testsuite_add_test(suite, "test_vm_metrics_collect_with_gc_heap",
                          test_vm_metrics_collect_with_gc_heap);
  valk_testsuite_add_test(suite, "test_vm_metrics_collect_null_heap",
                          test_vm_metrics_collect_null_heap);
  valk_testsuite_add_test(suite, "test_vm_metrics_json_contains_heap_values",
                          test_vm_metrics_json_contains_heap_values);
  valk_testsuite_add_test(suite, "test_vm_metrics_prometheus_contains_heap_values",
                          test_vm_metrics_prometheus_contains_heap_values);
  valk_testsuite_add_test(suite, "test_connection_state_tracking",
                          test_connection_state_tracking);
  valk_testsuite_add_test(suite, "test_system_stats_full_lifecycle",
                          test_system_stats_full_lifecycle);
  valk_testsuite_add_test(suite, "test_pending_stream_backpressure_metrics",
                          test_pending_stream_backpressure_metrics);
  valk_testsuite_add_test(suite, "test_combined_json_output",
                          test_combined_json_output);
  valk_testsuite_add_test(suite, "test_combined_json_named_output",
                          test_combined_json_named_output);
  valk_testsuite_add_test(suite, "test_http_client_metrics",
                          test_http_client_metrics);
  valk_testsuite_add_test(suite, "test_http_client_registry_overflow",
                          test_http_client_registry_overflow);
  valk_testsuite_add_test(suite, "test_http_clients_prometheus_output",
                          test_http_clients_prometheus_output);
  valk_testsuite_add_test(suite, "test_vm_metrics_null_input",
                          test_vm_metrics_null_input);
  valk_testsuite_add_test(suite, "test_system_stats_prometheus_null_input",
                          test_system_stats_prometheus_null_input);
  valk_testsuite_add_test(suite, "test_http_clients_prometheus_null_input",
                          test_http_clients_prometheus_null_input);
#else
  valk_testsuite_add_test(suite, "test_metrics_disabled", test_metrics_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
