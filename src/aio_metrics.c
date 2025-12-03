// src/aio_metrics.c - AIO metrics collection implementation
#ifdef VALK_METRICS_ENABLED

#include "aio_metrics.h"
#include "memory.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

// Initialize metrics structure
void valk_aio_metrics_init(valk_aio_metrics_t* m) {
  // Zero out all atomic counters
  atomic_store(&m->requests_total, 0);
  atomic_store(&m->requests_active, 0);
  atomic_store(&m->requests_errors, 0);
  atomic_store(&m->request_bytes_sent, 0);
  atomic_store(&m->request_bytes_recv, 0);
  atomic_store(&m->request_duration_us_sum, 0);

  atomic_store(&m->connections_total, 0);
  atomic_store(&m->connections_active, 0);
  atomic_store(&m->connections_failed, 0);
  atomic_store(&m->streams_total, 0);
  atomic_store(&m->streams_active, 0);

  atomic_store(&m->bytes_sent_total, 0);
  atomic_store(&m->bytes_recv_total, 0);

  // Set start time using uv_hrtime (high-resolution time in nanoseconds)
  m->start_time_us = uv_hrtime() / 1000;  // Convert to microseconds
}

// Record a new connection attempt
void valk_aio_metrics_on_connection(valk_aio_metrics_t* m, bool success) {
  atomic_fetch_add(&m->connections_total, 1);
  if (success) {
    atomic_fetch_add(&m->connections_active, 1);
  } else {
    atomic_fetch_add(&m->connections_failed, 1);
  }
}

// Record a connection close
void valk_aio_metrics_on_close(valk_aio_metrics_t* m) {
  atomic_fetch_sub(&m->connections_active, 1);
}

// Record a new stream start
void valk_aio_metrics_on_stream_start(valk_aio_metrics_t* m) {
  atomic_fetch_add(&m->streams_total, 1);
  atomic_fetch_add(&m->streams_active, 1);
  atomic_fetch_add(&m->requests_active, 1);
}

// Record a stream end
void valk_aio_metrics_on_stream_end(valk_aio_metrics_t* m, bool error,
                                     uint64_t duration_us,
                                     uint64_t bytes_sent, uint64_t bytes_recv) {
  atomic_fetch_sub(&m->streams_active, 1);
  atomic_fetch_sub(&m->requests_active, 1);
  atomic_fetch_add(&m->requests_total, 1);

  if (error) {
    atomic_fetch_add(&m->requests_errors, 1);
  }

  atomic_fetch_add(&m->request_duration_us_sum, duration_us);
  atomic_fetch_add(&m->request_bytes_sent, bytes_sent);
  atomic_fetch_add(&m->request_bytes_recv, bytes_recv);
  atomic_fetch_add(&m->bytes_sent_total, bytes_sent);
  atomic_fetch_add(&m->bytes_recv_total, bytes_recv);
}

// Helper function to calculate uptime in seconds
static double valk_aio_metrics_uptime_seconds(const valk_aio_metrics_t* m) {
  uint64_t current_time_us = uv_hrtime() / 1000;
  uint64_t uptime_us = current_time_us - m->start_time_us;
  return (double)uptime_us / 1000000.0;
}

// Render metrics as JSON
char* valk_aio_metrics_to_json(const valk_aio_metrics_t* m, struct valk_mem_allocator_t* alloc) {
  // Load atomic values
  uint64_t requests_total = atomic_load(&m->requests_total);
  uint64_t requests_active = atomic_load(&m->requests_active);
  uint64_t requests_errors = atomic_load(&m->requests_errors);
  uint64_t request_duration_us_sum = atomic_load(&m->request_duration_us_sum);

  uint64_t connections_total = atomic_load(&m->connections_total);
  uint64_t connections_active = atomic_load(&m->connections_active);
  uint64_t connections_failed = atomic_load(&m->connections_failed);
  uint64_t streams_total = atomic_load(&m->streams_total);
  uint64_t streams_active = atomic_load(&m->streams_active);

  uint64_t bytes_sent_total = atomic_load(&m->bytes_sent_total);
  uint64_t bytes_recv_total = atomic_load(&m->bytes_recv_total);

  // Calculate derived metrics
  double uptime_seconds = valk_aio_metrics_uptime_seconds(m);
  double rate_per_sec = uptime_seconds > 0 ? (double)requests_total / uptime_seconds : 0.0;
  double avg_latency_ms = requests_total > 0 ?
    (double)request_duration_us_sum / (double)requests_total / 1000.0 : 0.0;
  double sent_rate_kbps = uptime_seconds > 0 ?
    (double)bytes_sent_total / uptime_seconds / 1024.0 : 0.0;
  double recv_rate_kbps = uptime_seconds > 0 ?
    (double)bytes_recv_total / uptime_seconds / 1024.0 : 0.0;

  // Build JSON string
  // Allocate buffer (estimate ~800 bytes should be enough)
  size_t buffer_size = 1024;
  char* buffer;

  if (alloc) {
    buffer = valk_mem_allocator_alloc((valk_mem_allocator_t*)alloc, buffer_size);
  } else {
    buffer = malloc(buffer_size);
  }

  if (!buffer) {
    return nullptr;
  }

  int written = snprintf(buffer, buffer_size,
    "{\n"
    "  \"uptime_seconds\": %.2f,\n"
    "  \"connections\": {\n"
    "    \"total\": %lu,\n"
    "    \"active\": %lu,\n"
    "    \"failed\": %lu\n"
    "  },\n"
    "  \"streams\": {\n"
    "    \"total\": %lu,\n"
    "    \"active\": %lu\n"
    "  },\n"
    "  \"requests\": {\n"
    "    \"total\": %lu,\n"
    "    \"active\": %lu,\n"
    "    \"errors\": %lu,\n"
    "    \"rate_per_sec\": %.2f,\n"
    "    \"avg_latency_ms\": %.2f\n"
    "  },\n"
    "  \"bytes\": {\n"
    "    \"sent_total\": %lu,\n"
    "    \"recv_total\": %lu,\n"
    "    \"sent_rate_kbps\": %.2f,\n"
    "    \"recv_rate_kbps\": %.2f\n"
    "  }\n"
    "}",
    uptime_seconds,
    connections_total, connections_active, connections_failed,
    streams_total, streams_active,
    requests_total, requests_active, requests_errors, rate_per_sec, avg_latency_ms,
    bytes_sent_total, bytes_recv_total, sent_rate_kbps, recv_rate_kbps
  );

  if (written < 0 || (size_t)written >= buffer_size) {
    // Buffer too small, shouldn't happen with our estimate
    if (!alloc) {
      free(buffer);
    }
    return nullptr;
  }

  return buffer;
}

// Render metrics as Prometheus text format
char* valk_aio_metrics_to_prometheus(const valk_aio_metrics_t* m, struct valk_mem_allocator_t* alloc) {
  // Load atomic values
  uint64_t requests_total = atomic_load(&m->requests_total);
  uint64_t requests_active = atomic_load(&m->requests_active);
  uint64_t requests_errors = atomic_load(&m->requests_errors);

  uint64_t connections_total = atomic_load(&m->connections_total);
  uint64_t connections_active = atomic_load(&m->connections_active);
  uint64_t connections_failed = atomic_load(&m->connections_failed);
  uint64_t streams_total = atomic_load(&m->streams_total);
  uint64_t streams_active = atomic_load(&m->streams_active);

  uint64_t bytes_sent_total = atomic_load(&m->bytes_sent_total);
  uint64_t bytes_recv_total = atomic_load(&m->bytes_recv_total);
  uint64_t request_duration_us_sum = atomic_load(&m->request_duration_us_sum);

  // Calculate uptime
  double uptime_seconds = valk_aio_metrics_uptime_seconds(m);

  // Allocate buffer (estimate ~2KB should be enough for Prometheus format)
  size_t buffer_size = 2048;
  char* buffer;

  if (alloc) {
    buffer = valk_mem_allocator_alloc((valk_mem_allocator_t*)alloc, buffer_size);
  } else {
    buffer = malloc(buffer_size);
  }

  if (!buffer) {
    return nullptr;
  }

  int written = snprintf(buffer, buffer_size,
    "# HELP valk_aio_uptime_seconds Time in seconds since metrics initialization\n"
    "# TYPE valk_aio_uptime_seconds gauge\n"
    "valk_aio_uptime_seconds %.2f\n"
    "\n"
    "# HELP valk_aio_connections_total Total number of connection attempts\n"
    "# TYPE valk_aio_connections_total counter\n"
    "valk_aio_connections_total %lu\n"
    "\n"
    "# HELP valk_aio_connections_active Current number of active connections\n"
    "# TYPE valk_aio_connections_active gauge\n"
    "valk_aio_connections_active %lu\n"
    "\n"
    "# HELP valk_aio_connections_failed Total number of failed connection attempts\n"
    "# TYPE valk_aio_connections_failed counter\n"
    "valk_aio_connections_failed %lu\n"
    "\n"
    "# HELP valk_aio_streams_total Total number of HTTP/2 streams created\n"
    "# TYPE valk_aio_streams_total counter\n"
    "valk_aio_streams_total %lu\n"
    "\n"
    "# HELP valk_aio_streams_active Current number of active HTTP/2 streams\n"
    "# TYPE valk_aio_streams_active gauge\n"
    "valk_aio_streams_active %lu\n"
    "\n"
    "# HELP valk_aio_requests_total Total number of HTTP/2 requests completed\n"
    "# TYPE valk_aio_requests_total counter\n"
    "valk_aio_requests_total %lu\n"
    "\n"
    "# HELP valk_aio_requests_active Current number of active requests\n"
    "# TYPE valk_aio_requests_active gauge\n"
    "valk_aio_requests_active %lu\n"
    "\n"
    "# HELP valk_aio_requests_errors Total number of request errors\n"
    "# TYPE valk_aio_requests_errors counter\n"
    "valk_aio_requests_errors %lu\n"
    "\n"
    "# HELP valk_aio_request_duration_microseconds_sum Sum of request durations in microseconds\n"
    "# TYPE valk_aio_request_duration_microseconds_sum counter\n"
    "valk_aio_request_duration_microseconds_sum %lu\n"
    "\n"
    "# HELP valk_aio_bytes_sent_total Total bytes sent\n"
    "# TYPE valk_aio_bytes_sent_total counter\n"
    "valk_aio_bytes_sent_total %lu\n"
    "\n"
    "# HELP valk_aio_bytes_recv_total Total bytes received\n"
    "# TYPE valk_aio_bytes_recv_total counter\n"
    "valk_aio_bytes_recv_total %lu\n",
    uptime_seconds,
    connections_total,
    connections_active,
    connections_failed,
    streams_total,
    streams_active,
    requests_total,
    requests_active,
    requests_errors,
    request_duration_us_sum,
    bytes_sent_total,
    bytes_recv_total
  );

  if (written < 0 || (size_t)written >= buffer_size) {
    // Buffer too small, shouldn't happen with our estimate
    if (!alloc) {
      free(buffer);
    }
    return nullptr;
  }

  return buffer;
}

#endif // VALK_METRICS_ENABLED
