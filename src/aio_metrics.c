// src/aio_metrics.c - AIO metrics collection implementation
#ifdef VALK_METRICS_ENABLED

#include "aio_metrics.h"
#include "memory.h"
#include "gc.h"
#include "parser.h"
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
  atomic_store(&m->connections_rejected, 0);
  atomic_store(&m->connections_rejected_load, 0);
  atomic_store(&m->connections_connecting, 0);
  atomic_store(&m->connections_idle, 0);
  atomic_store(&m->connections_closing, 0);
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

// Connection state tracking
void valk_aio_metrics_on_connecting(valk_aio_metrics_t* m) {
  atomic_fetch_add(&m->connections_connecting, 1);
}

void valk_aio_metrics_on_connected(valk_aio_metrics_t* m) {
  atomic_fetch_sub(&m->connections_connecting, 1);
  atomic_fetch_add(&m->connections_active, 1);
}

void valk_aio_metrics_on_idle(valk_aio_metrics_t* m) {
  atomic_fetch_sub(&m->connections_active, 1);
  atomic_fetch_add(&m->connections_idle, 1);
}

void valk_aio_metrics_on_reactivate(valk_aio_metrics_t* m) {
  atomic_fetch_sub(&m->connections_idle, 1);
  atomic_fetch_add(&m->connections_active, 1);
}

void valk_aio_metrics_on_closing(valk_aio_metrics_t* m) {
  // Called when connection enters closing state
  // The caller should have already decremented active/idle as appropriate
  atomic_fetch_add(&m->connections_closing, 1);
}

void valk_aio_metrics_on_closed(valk_aio_metrics_t* m) {
  atomic_fetch_sub(&m->connections_closing, 1);
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
  uint64_t connections_connecting = atomic_load(&m->connections_connecting);
  uint64_t connections_idle = atomic_load(&m->connections_idle);
  uint64_t connections_closing = atomic_load(&m->connections_closing);
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
    "    \"failed\": %lu,\n"
    "    \"connecting\": %lu,\n"
    "    \"idle\": %lu,\n"
    "    \"closing\": %lu\n"
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
    connections_connecting, connections_idle, connections_closing,
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
  uint64_t connections_connecting = atomic_load(&m->connections_connecting);
  uint64_t connections_idle = atomic_load(&m->connections_idle);
  uint64_t connections_closing = atomic_load(&m->connections_closing);
  uint64_t streams_total = atomic_load(&m->streams_total);
  uint64_t streams_active = atomic_load(&m->streams_active);

  uint64_t bytes_sent_total = atomic_load(&m->bytes_sent_total);
  uint64_t bytes_recv_total = atomic_load(&m->bytes_recv_total);
  uint64_t request_duration_us_sum = atomic_load(&m->request_duration_us_sum);

  // Calculate uptime
  double uptime_seconds = valk_aio_metrics_uptime_seconds(m);

  // Allocate buffer (increase to 2560 for new metrics)
  size_t buffer_size = 2560;
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
    "# HELP valk_aio_connections_connecting Connections being established\n"
    "# TYPE valk_aio_connections_connecting gauge\n"
    "valk_aio_connections_connecting %lu\n"
    "\n"
    "# HELP valk_aio_connections_idle Idle connections awaiting reuse\n"
    "# TYPE valk_aio_connections_idle gauge\n"
    "valk_aio_connections_idle %lu\n"
    "\n"
    "# HELP valk_aio_connections_closing Connections in graceful shutdown\n"
    "# TYPE valk_aio_connections_closing gauge\n"
    "valk_aio_connections_closing %lu\n"
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
    connections_connecting,
    connections_idle,
    connections_closing,
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

// Initialize system stats structure
void valk_aio_system_stats_init(valk_aio_system_stats_t* s,
                                 uint64_t arenas_total,
                                 uint64_t tcp_buffers_total,
                                 uint64_t queue_capacity) {
  atomic_store(&s->servers_count, 0);
  atomic_store(&s->clients_count, 0);
  atomic_store(&s->handles_count, 0);

  atomic_store(&s->arenas_used, 0);
  s->arenas_total = arenas_total;
  atomic_store(&s->tcp_buffers_used, 0);
  s->tcp_buffers_total = tcp_buffers_total;

  atomic_store(&s->queue_depth, 0);
  atomic_store(&s->pending_requests, 0);
  atomic_store(&s->pending_responses, 0);
  s->queue_capacity = queue_capacity;

  atomic_store(&s->arena_pool_overflow, 0);
  atomic_store(&s->tcp_buffer_overflow, 0);
  atomic_store(&s->connections_rejected_load, 0);

  // Pending stream backpressure metrics
  atomic_store(&s->pending_streams_current, 0);
  atomic_store(&s->pending_streams_total, 0);
  atomic_store(&s->pending_streams_processed, 0);
  atomic_store(&s->pending_streams_dropped, 0);
  atomic_store(&s->pending_streams_wait_us, 0);
  s->pending_streams_pool_size = 64;  // PENDING_STREAM_POOL_SIZE from aio_uv.c
}

// Server tracking
void valk_aio_system_stats_on_server_start(valk_aio_system_stats_t* s) {
  atomic_fetch_add(&s->servers_count, 1);
}

void valk_aio_system_stats_on_server_stop(valk_aio_system_stats_t* s) {
  atomic_fetch_sub(&s->servers_count, 1);
}

// Client tracking
void valk_aio_system_stats_on_client_start(valk_aio_system_stats_t* s) {
  atomic_fetch_add(&s->clients_count, 1);
}

void valk_aio_system_stats_on_client_stop(valk_aio_system_stats_t* s) {
  atomic_fetch_sub(&s->clients_count, 1);
}

// Handle tracking
void valk_aio_system_stats_on_handle_create(valk_aio_system_stats_t* s) {
  atomic_fetch_add(&s->handles_count, 1);
}

void valk_aio_system_stats_on_handle_close(valk_aio_system_stats_t* s) {
  atomic_fetch_sub(&s->handles_count, 1);
}

// Arena tracking
void valk_aio_system_stats_on_arena_acquire(valk_aio_system_stats_t* s) {
  atomic_fetch_add(&s->arenas_used, 1);
}

void valk_aio_system_stats_on_arena_release(valk_aio_system_stats_t* s) {
  atomic_fetch_sub(&s->arenas_used, 1);
}

// Queue depth updates
void valk_aio_system_stats_update_queue(valk_aio_system_stats_t* s,
                                         uint64_t pending_requests,
                                         uint64_t pending_responses) {
  atomic_store(&s->pending_requests, pending_requests);
  atomic_store(&s->pending_responses, pending_responses);
  atomic_store(&s->queue_depth, pending_requests + pending_responses);
}

// Pending stream backpressure instrumentation
void valk_aio_system_stats_on_pending_enqueue(valk_aio_system_stats_t* s) {
  atomic_fetch_add(&s->pending_streams_current, 1);
  atomic_fetch_add(&s->pending_streams_total, 1);
}

void valk_aio_system_stats_on_pending_dequeue(valk_aio_system_stats_t* s, uint64_t wait_us) {
  atomic_fetch_sub(&s->pending_streams_current, 1);
  atomic_fetch_add(&s->pending_streams_processed, 1);
  atomic_fetch_add(&s->pending_streams_wait_us, wait_us);
}

void valk_aio_system_stats_on_pending_drop(valk_aio_system_stats_t* s) {
  atomic_fetch_sub(&s->pending_streams_current, 1);
  atomic_fetch_add(&s->pending_streams_dropped, 1);
}

void valk_aio_system_stats_update_pending_current(valk_aio_system_stats_t* s, uint64_t count) {
  atomic_store(&s->pending_streams_current, count);
}

// Combined JSON rendering (HTTP metrics + AIO system stats)
char* valk_aio_combined_to_json(const valk_aio_metrics_t* m,
                                 const valk_aio_system_stats_t* s,
                                 struct valk_mem_allocator_t* alloc) {
  // Load HTTP metrics (atomic values)
  uint64_t requests_total = atomic_load(&m->requests_total);
  uint64_t requests_active = atomic_load(&m->requests_active);
  uint64_t requests_errors = atomic_load(&m->requests_errors);
  uint64_t request_duration_us_sum = atomic_load(&m->request_duration_us_sum);

  uint64_t connections_total = atomic_load(&m->connections_total);
  uint64_t connections_active = atomic_load(&m->connections_active);
  uint64_t connections_failed = atomic_load(&m->connections_failed);
  uint64_t connections_rejected = atomic_load(&m->connections_rejected);
  uint64_t connections_rejected_load = atomic_load(&m->connections_rejected_load);
  uint64_t connections_connecting = atomic_load(&m->connections_connecting);
  uint64_t connections_idle = atomic_load(&m->connections_idle);
  uint64_t connections_closing = atomic_load(&m->connections_closing);
  uint64_t streams_total = atomic_load(&m->streams_total);
  uint64_t streams_active = atomic_load(&m->streams_active);

  uint64_t bytes_sent_total = atomic_load(&m->bytes_sent_total);
  uint64_t bytes_recv_total = atomic_load(&m->bytes_recv_total);

  // Load system stats (atomic values)
  uint64_t servers = atomic_load(&s->servers_count);
  uint64_t clients = atomic_load(&s->clients_count);
  uint64_t handles = atomic_load(&s->handles_count);
  uint64_t arenas_used = atomic_load(&s->arenas_used);
  uint64_t tcp_buffers_used = atomic_load(&s->tcp_buffers_used);
  uint64_t queue_depth = atomic_load(&s->queue_depth);
  uint64_t pending_requests = atomic_load(&s->pending_requests);
  uint64_t pending_responses = atomic_load(&s->pending_responses);

  // Calculate derived metrics
  double uptime_seconds = valk_aio_metrics_uptime_seconds(m);
  double rate_per_sec = uptime_seconds > 0 ? (double)requests_total / uptime_seconds : 0.0;
  double avg_latency_ms = requests_total > 0 ?
    (double)request_duration_us_sum / (double)requests_total / 1000.0 : 0.0;
  double sent_rate_kbps = uptime_seconds > 0 ?
    (double)bytes_sent_total / uptime_seconds / 1024.0 : 0.0;
  double recv_rate_kbps = uptime_seconds > 0 ?
    (double)bytes_recv_total / uptime_seconds / 1024.0 : 0.0;

  // Allocate buffer (larger for combined output, including new connection states)
  size_t buffer_size = 2304;
  char* buffer;

  if (alloc) {
    buffer = valk_mem_allocator_alloc((valk_mem_allocator_t*)alloc, buffer_size);
  } else {
    buffer = malloc(buffer_size);
  }

  if (!buffer) {
    return nullptr;
  }

  // Note: The outer "aio_metrics" wrapper is added by the Lisp layer in debug.valk
  // This function returns just the inner object content
  int written = snprintf(buffer, buffer_size,
    "{\n"
    "  \"uptime_seconds\": %.2f,\n"
    "  \"system\": {\n"
    "    \"servers\": %lu,\n"
    "    \"clients\": %lu,\n"
    "    \"handles\": %lu,\n"
    "    \"arenas_used\": %lu,\n"
    "    \"arenas_total\": %lu,\n"
    "    \"tcp_buffers_used\": %lu,\n"
    "    \"tcp_buffers_total\": %lu,\n"
    "    \"queue_depth\": %lu,\n"
    "    \"pending_requests\": %lu,\n"
    "    \"pending_responses\": %lu\n"
    "  },\n"
    "  \"connections\": {\n"
    "    \"total\": %lu,\n"
    "    \"active\": %lu,\n"
    "    \"failed\": %lu,\n"
    "    \"rejected\": %lu,\n"
    "    \"rejected_load\": %lu,\n"
    "    \"connecting\": %lu,\n"
    "    \"idle\": %lu,\n"
    "    \"closing\": %lu\n"
    "  },\n"
    "  \"streams\": {\n"
    "    \"total\": %lu,\n"
    "    \"active\": %lu\n"
    "  },\n"
    "  \"bytes\": {\n"
    "    \"sent_total\": %lu,\n"
    "    \"recv_total\": %lu,\n"
    "    \"sent_rate_kbps\": %.2f,\n"
    "    \"recv_rate_kbps\": %.2f\n"
    "  }\n"
    "}",
    uptime_seconds,
    servers, clients, handles,
    arenas_used, s->arenas_total,
    tcp_buffers_used, s->tcp_buffers_total,
    queue_depth, pending_requests, pending_responses,
    connections_total, connections_active, connections_failed,
    connections_rejected, connections_rejected_load,
    connections_connecting, connections_idle, connections_closing,
    streams_total, streams_active,
    bytes_sent_total, bytes_recv_total, sent_rate_kbps, recv_rate_kbps
  );

  if (written < 0 || (size_t)written >= buffer_size) {
    if (!alloc) {
      free(buffer);
    }
    return nullptr;
  }

  return buffer;
}

// Combined JSON rendering with system name (for multi-system support)
char* valk_aio_combined_to_json_named(const char* name,
                                       const valk_aio_metrics_t* m,
                                       const valk_aio_system_stats_t* s,
                                       struct valk_mem_allocator_t* alloc) {
  // Load HTTP metrics (atomic values)
  uint64_t connections_active = atomic_load(&m->connections_active);
  uint64_t connections_idle = atomic_load(&m->connections_idle);
  uint64_t connections_closing = atomic_load(&m->connections_closing);

  // Load system stats (atomic values)
  uint64_t servers = atomic_load(&s->servers_count);
  uint64_t handles = atomic_load(&s->handles_count);
  uint64_t arenas_used = atomic_load(&s->arenas_used);
  uint64_t tcp_buffers_used = atomic_load(&s->tcp_buffers_used);
  uint64_t queue_depth = atomic_load(&s->queue_depth);
  uint64_t pending_requests = atomic_load(&s->pending_requests);
  uint64_t pending_responses = atomic_load(&s->pending_responses);

  // Calculate derived metrics
  double uptime_seconds = valk_aio_metrics_uptime_seconds(m);

  // Get connection slab info (need to access via sys, but we don't have it here)
  // For now, use arenas_total as a proxy for conn_slab_total
  uint64_t conn_slab_total = s->arenas_total > 0 ? s->arenas_total * 16 : 256;
  uint64_t conn_slab_available = conn_slab_total - (connections_active + connections_idle + connections_closing);

  // Allocate buffer
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
    "{"
    "\"name\":\"%s\","
    "\"uptime_seconds\":%.2f,"
    "\"loop\":{\"iterations\":0,\"events_processed\":0},"
    "\"system\":{"
      "\"servers\":%lu,"
      "\"handles\":%lu,"
      "\"arenas_used\":%lu,"
      "\"arenas_total\":%lu,"
      "\"tcp_buffers_used\":%lu,"
      "\"tcp_buffers_total\":%lu,"
      "\"queue_depth\":%lu,"
      "\"pending_requests\":%lu,"
      "\"pending_responses\":%lu,"
      "\"conn_slab_total\":%lu,"
      "\"conn_slab_available\":%lu"
    "},"
    "\"connections\":{"
      "\"active\":%lu,"
      "\"idle\":%lu,"
      "\"closing\":%lu"
    "}"
    "}",
    name ? name : "main",
    uptime_seconds,
    servers, handles,
    arenas_used, s->arenas_total,
    tcp_buffers_used, s->tcp_buffers_total,
    queue_depth, pending_requests, pending_responses,
    conn_slab_total, conn_slab_available,
    connections_active, connections_idle, connections_closing
  );

  if (written < 0 || (size_t)written >= buffer_size) {
    if (!alloc) {
      free(buffer);
    }
    return nullptr;
  }

  return buffer;
}

// Export AIO system stats in Prometheus format
char* valk_aio_system_stats_to_prometheus(const valk_aio_system_stats_t* s,
                                           struct valk_mem_allocator_t* alloc) {
  if (!s) return nullptr;

  // Load atomic values
  uint64_t servers = atomic_load(&s->servers_count);
  uint64_t clients = atomic_load(&s->clients_count);
  uint64_t handles = atomic_load(&s->handles_count);
  uint64_t arenas_used = atomic_load(&s->arenas_used);
  uint64_t tcp_buffers_used = atomic_load(&s->tcp_buffers_used);
  uint64_t queue_depth = atomic_load(&s->queue_depth);
  uint64_t pending_requests = atomic_load(&s->pending_requests);
  uint64_t pending_responses = atomic_load(&s->pending_responses);
  uint64_t arena_overflow = atomic_load(&s->arena_pool_overflow);
  uint64_t tcp_buffer_overflow = atomic_load(&s->tcp_buffer_overflow);
  uint64_t connections_rejected_load = atomic_load(&s->connections_rejected_load);

  // Allocate buffer
  size_t buffer_size = 3072;  // Estimate for all metrics
  char* buffer;
  if (alloc) {
    buffer = valk_mem_allocator_alloc((valk_mem_allocator_t*)alloc, buffer_size);
  } else {
    buffer = malloc(buffer_size);
  }
  if (!buffer) return nullptr;

  int written = snprintf(buffer, buffer_size,
    "# HELP valk_aio_servers_count Number of HTTP servers\n"
    "# TYPE valk_aio_servers_count gauge\n"
    "valk_aio_servers_count %lu\n"
    "\n"
    "# HELP valk_aio_clients_count Number of HTTP clients\n"
    "# TYPE valk_aio_clients_count gauge\n"
    "valk_aio_clients_count %lu\n"
    "\n"
    "# HELP valk_aio_handles_count Total active handles\n"
    "# TYPE valk_aio_handles_count gauge\n"
    "valk_aio_handles_count %lu\n"
    "\n"
    "# HELP valk_aio_arenas_used Stream arenas in use\n"
    "# TYPE valk_aio_arenas_used gauge\n"
    "valk_aio_arenas_used %lu\n"
    "\n"
    "# HELP valk_aio_arenas_total Total stream arenas available\n"
    "# TYPE valk_aio_arenas_total gauge\n"
    "valk_aio_arenas_total %lu\n"
    "\n"
    "# HELP valk_aio_tcp_buffers_used TCP buffers in use\n"
    "# TYPE valk_aio_tcp_buffers_used gauge\n"
    "valk_aio_tcp_buffers_used %lu\n"
    "\n"
    "# HELP valk_aio_tcp_buffers_total Total TCP buffers available\n"
    "# TYPE valk_aio_tcp_buffers_total gauge\n"
    "valk_aio_tcp_buffers_total %lu\n"
    "\n"
    "# HELP valk_aio_queue_depth HTTP queue depth\n"
    "# TYPE valk_aio_queue_depth gauge\n"
    "valk_aio_queue_depth %lu\n"
    "\n"
    "# HELP valk_aio_pending_requests Pending HTTP requests\n"
    "# TYPE valk_aio_pending_requests gauge\n"
    "valk_aio_pending_requests %lu\n"
    "\n"
    "# HELP valk_aio_pending_responses Pending HTTP responses\n"
    "# TYPE valk_aio_pending_responses gauge\n"
    "valk_aio_pending_responses %lu\n"
    "\n"
    "# HELP valk_aio_arena_pool_overflow_total Arena acquire failures\n"
    "# TYPE valk_aio_arena_pool_overflow_total counter\n"
    "valk_aio_arena_pool_overflow_total %lu\n"
    "\n"
    "# HELP valk_aio_tcp_buffer_overflow_total TCP buffer acquire failures\n"
    "# TYPE valk_aio_tcp_buffer_overflow_total counter\n"
    "valk_aio_tcp_buffer_overflow_total %lu\n"
    "\n"
    "# HELP valk_aio_connections_rejected_load_total Connections rejected due to load\n"
    "# TYPE valk_aio_connections_rejected_load_total counter\n"
    "valk_aio_connections_rejected_load_total %lu\n",
    servers,
    clients,
    handles,
    arenas_used,
    s->arenas_total,
    tcp_buffers_used,
    s->tcp_buffers_total,
    queue_depth,
    pending_requests,
    pending_responses,
    arena_overflow,
    tcp_buffer_overflow,
    connections_rejected_load
  );

  if (written < 0 || (size_t)written >= buffer_size) {
    if (!alloc) free(buffer);
    return nullptr;
  }

  return buffer;
}

// Get event loop metrics from libuv
void valk_event_loop_metrics_get(uv_loop_t* loop, valk_event_loop_metrics_t* out) {
  if (!loop || !out) return;

  // Zero out first
  memset(out, 0, sizeof(*out));

  // Get metrics from libuv (available since libuv 1.39.0)
  uv_metrics_t metrics;
  if (uv_metrics_info(loop, &metrics) == 0) {
    out->loop_count = metrics.loop_count;
    out->events = metrics.events;
    out->events_waiting = metrics.events_waiting;
  }

  // Get idle time (requires UV_METRICS_IDLE_TIME option)
  // Returns nanoseconds, convert to microseconds
  out->idle_time_us = uv_metrics_idle_time(loop) / 1000;
}

// ============================================================================
// Combined VM Metrics
// ============================================================================

// Collect all VM metrics
void valk_vm_metrics_collect(valk_vm_metrics_t* out,
                              struct valk_gc_malloc_heap_t* heap,
                              struct uv_loop_s* loop) {
  if (!out) return;
  memset(out, 0, sizeof(*out));

  // GC metrics
  if (heap) {
    valk_gc_get_runtime_metrics(heap,
      &out->gc_cycles, &out->gc_pause_us_total, &out->gc_pause_us_max,
      &out->gc_reclaimed_bytes, &out->gc_heap_used, &out->gc_heap_total);
  }

  // Interpreter metrics
  valk_eval_metrics_get(
    &out->eval_total, &out->function_calls, &out->builtin_calls,
    &out->stack_depth_max, &out->closures_created, &out->env_lookups);

  // Event loop metrics
  if (loop) {
    valk_event_loop_metrics_t loop_m;
    valk_event_loop_metrics_get(loop, &loop_m);
    out->loop_count = loop_m.loop_count;
    out->events_processed = loop_m.events;
    out->idle_time_us = loop_m.idle_time_us;
  }
}

// Export VM metrics as JSON
char* valk_vm_metrics_to_json(const valk_vm_metrics_t* m,
                               struct valk_mem_allocator_t* alloc) {
  if (!m) return nullptr;

  size_t buf_size = 2048;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return nullptr;

  double heap_util = m->gc_heap_total > 0
    ? 100.0 * (double)m->gc_heap_used / (double)m->gc_heap_total
    : 0.0;

  int written = snprintf(buf, buf_size,
    "{\n"
    "  \"gc\": {\n"
    "    \"cycles_total\": %lu,\n"
    "    \"pause_us_total\": %lu,\n"
    "    \"pause_us_max\": %lu,\n"
    "    \"pause_ms_avg\": %.3f,\n"
    "    \"reclaimed_bytes_total\": %lu,\n"
    "    \"heap_used_bytes\": %zu,\n"
    "    \"heap_total_bytes\": %zu,\n"
    "    \"heap_utilization_pct\": %.2f\n"
    "  },\n"
    "  \"interpreter\": {\n"
    "    \"evals_total\": %lu,\n"
    "    \"function_calls\": %lu,\n"
    "    \"builtin_calls\": %lu,\n"
    "    \"stack_depth_max\": %u,\n"
    "    \"closures_created\": %lu,\n"
    "    \"env_lookups\": %lu\n"
    "  },\n"
    "  \"event_loop\": {\n"
    "    \"iterations\": %lu,\n"
    "    \"events_processed\": %lu,\n"
    "    \"idle_time_us\": %lu,\n"
    "    \"idle_time_pct\": %.2f\n"
    "  }\n"
    "}",
    m->gc_cycles,
    m->gc_pause_us_total,
    m->gc_pause_us_max,
    m->gc_cycles > 0 ? (double)m->gc_pause_us_total / m->gc_cycles / 1000.0 : 0.0,
    m->gc_reclaimed_bytes,
    m->gc_heap_used,
    m->gc_heap_total,
    heap_util,
    m->eval_total,
    m->function_calls,
    m->builtin_calls,
    m->stack_depth_max,
    m->closures_created,
    m->env_lookups,
    m->loop_count,
    m->events_processed,
    m->idle_time_us,
    0.0  // TODO: Calculate idle percentage when we have total runtime
  );

  (void)written;
  return buf;
}

// Export VM metrics in Prometheus format
char* valk_vm_metrics_to_prometheus(const valk_vm_metrics_t* m,
                                     struct valk_mem_allocator_t* alloc) {
  if (!m) return nullptr;

  size_t buf_size = 4096;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return nullptr;

  double heap_util_ratio = m->gc_heap_total > 0
    ? (double)m->gc_heap_used / (double)m->gc_heap_total
    : 0.0;

  int written = snprintf(buf, buf_size,
    "# HELP valk_gc_cycles_total Total garbage collection cycles\n"
    "# TYPE valk_gc_cycles_total counter\n"
    "valk_gc_cycles_total %lu\n"
    "\n"
    "# HELP valk_gc_pause_seconds_total Total GC pause time in seconds\n"
    "# TYPE valk_gc_pause_seconds_total counter\n"
    "valk_gc_pause_seconds_total %.6f\n"
    "\n"
    "# HELP valk_gc_pause_seconds_max Maximum single GC pause in seconds\n"
    "# TYPE valk_gc_pause_seconds_max gauge\n"
    "valk_gc_pause_seconds_max %.6f\n"
    "\n"
    "# HELP valk_gc_reclaimed_bytes_total Total bytes reclaimed by GC\n"
    "# TYPE valk_gc_reclaimed_bytes_total counter\n"
    "valk_gc_reclaimed_bytes_total %lu\n"
    "\n"
    "# HELP valk_gc_heap_used_bytes Current heap memory in use\n"
    "# TYPE valk_gc_heap_used_bytes gauge\n"
    "valk_gc_heap_used_bytes %zu\n"
    "\n"
    "# HELP valk_gc_heap_total_bytes Total heap capacity\n"
    "# TYPE valk_gc_heap_total_bytes gauge\n"
    "valk_gc_heap_total_bytes %zu\n"
    "\n"
    "# HELP valk_gc_heap_utilization_ratio Heap utilization as ratio (0.0-1.0)\n"
    "# TYPE valk_gc_heap_utilization_ratio gauge\n"
    "valk_gc_heap_utilization_ratio %.6f\n"
    "\n"
    "# HELP valk_eval_total Total expression evaluations\n"
    "# TYPE valk_eval_total counter\n"
    "valk_eval_total %lu\n"
    "\n"
    "# HELP valk_function_calls_total User function invocations\n"
    "# TYPE valk_function_calls_total counter\n"
    "valk_function_calls_total %lu\n"
    "\n"
    "# HELP valk_builtin_calls_total Builtin function invocations\n"
    "# TYPE valk_builtin_calls_total counter\n"
    "valk_builtin_calls_total %lu\n"
    "\n"
    "# HELP valk_stack_depth_max Peak call stack depth\n"
    "# TYPE valk_stack_depth_max gauge\n"
    "valk_stack_depth_max %u\n"
    "\n"
    "# HELP valk_closures_created_total Lambda closures created\n"
    "# TYPE valk_closures_created_total counter\n"
    "valk_closures_created_total %lu\n"
    "\n"
    "# HELP valk_env_lookups_total Symbol resolution lookups\n"
    "# TYPE valk_env_lookups_total counter\n"
    "valk_env_lookups_total %lu\n"
    "\n"
    "# HELP valk_loop_iterations_total Event loop iterations\n"
    "# TYPE valk_loop_iterations_total counter\n"
    "valk_loop_iterations_total %lu\n"
    "\n"
    "# HELP valk_events_processed_total Events processed by event loop\n"
    "# TYPE valk_events_processed_total counter\n"
    "valk_events_processed_total %lu\n"
    "\n"
    "# HELP valk_loop_idle_seconds_total Time spent idle in event loop\n"
    "# TYPE valk_loop_idle_seconds_total counter\n"
    "valk_loop_idle_seconds_total %.6f\n",
    m->gc_cycles,
    (double)m->gc_pause_us_total / 1e6,
    (double)m->gc_pause_us_max / 1e6,
    m->gc_reclaimed_bytes,
    m->gc_heap_used,
    m->gc_heap_total,
    heap_util_ratio,
    m->eval_total,
    m->function_calls,
    m->builtin_calls,
    m->stack_depth_max,
    m->closures_created,
    m->env_lookups,
    m->loop_count,
    m->events_processed,
    (double)m->idle_time_us / 1e6
  );

  (void)written;
  return buf;
}

// ============================================================================
// HTTP Client Metrics (Phase 3)
// ============================================================================

// Initialize a single client metrics entry
void valk_http_client_metrics_init(valk_http_client_metrics_t* c,
                                    const char* name, const char* type,
                                    uint64_t pool_size) {
  strncpy(c->name, name, sizeof(c->name) - 1);
  c->name[sizeof(c->name) - 1] = '\0';
  strncpy(c->type, type, sizeof(c->type) - 1);
  c->type[sizeof(c->type) - 1] = '\0';

  atomic_store(&c->connections_active, 0);
  atomic_store(&c->pool_size, pool_size);
  atomic_store(&c->operations_total, 0);
  atomic_store(&c->errors_total, 0);
  atomic_store(&c->retries_total, 0);
  atomic_store(&c->cache_hits_total, 0);
  atomic_store(&c->cache_misses_total, 0);
  atomic_store(&c->latency_us_sum, 0);
  atomic_store(&c->latency_count, 0);
}

// Register a new HTTP client, returns index or -1 on failure
int valk_http_client_register(valk_http_clients_registry_t* reg,
                               const char* name, const char* type,
                               uint64_t pool_size) {
  uint32_t idx = atomic_fetch_add(&reg->count, 1);
  if (idx >= VALK_MAX_HTTP_CLIENTS) {
    atomic_fetch_sub(&reg->count, 1);
    return -1;
  }
  valk_http_client_metrics_init(&reg->clients[idx], name, type, pool_size);
  return (int)idx;
}

// Record an operation on a client
void valk_http_client_on_operation(valk_http_client_metrics_t* c,
                                    uint64_t duration_us, bool error, bool retry) {
  atomic_fetch_add(&c->operations_total, 1);
  atomic_fetch_add(&c->latency_us_sum, duration_us);
  atomic_fetch_add(&c->latency_count, 1);
  if (error) atomic_fetch_add(&c->errors_total, 1);
  if (retry) atomic_fetch_add(&c->retries_total, 1);
}

// Record cache hit/miss (for cache clients)
void valk_http_client_on_cache(valk_http_client_metrics_t* c, bool hit) {
  if (hit) {
    atomic_fetch_add(&c->cache_hits_total, 1);
  } else {
    atomic_fetch_add(&c->cache_misses_total, 1);
  }
}

// Export client metrics as Prometheus
char* valk_http_clients_to_prometheus(const valk_http_clients_registry_t* reg,
                                       struct valk_mem_allocator_t* alloc) {
  if (!reg) return nullptr;

  uint32_t count = atomic_load(&reg->count);
  if (count == 0) return nullptr;

  // Estimate 512 bytes per client for all metrics
  size_t buf_size = 512 + count * 512;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return nullptr;

  size_t pos = 0;

  // Write HELP/TYPE headers once
  pos += snprintf(buf + pos, buf_size - pos,
    "# HELP http_client_connections_active Active connections per client\n"
    "# TYPE http_client_connections_active gauge\n");

  // Write per-client values
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    pos += snprintf(buf + pos, buf_size - pos,
      "http_client_connections_active{client=\"%s\",type=\"%s\"} %lu\n",
      c->name, c->type, atomic_load(&c->connections_active));
  }

  // Continue for other metrics...
  pos += snprintf(buf + pos, buf_size - pos,
    "\n# HELP http_client_pool_size Connection pool size per client\n"
    "# TYPE http_client_pool_size gauge\n");
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    pos += snprintf(buf + pos, buf_size - pos,
      "http_client_pool_size{client=\"%s\",type=\"%s\"} %lu\n",
      c->name, c->type, atomic_load(&c->pool_size));
  }

  // operations_total
  pos += snprintf(buf + pos, buf_size - pos,
    "\n# HELP http_client_operations_total Total operations per client\n"
    "# TYPE http_client_operations_total counter\n");
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    pos += snprintf(buf + pos, buf_size - pos,
      "http_client_operations_total{client=\"%s\",type=\"%s\"} %lu\n",
      c->name, c->type, atomic_load(&c->operations_total));
  }

  // errors_total
  pos += snprintf(buf + pos, buf_size - pos,
    "\n# HELP http_client_errors_total Total errors per client\n"
    "# TYPE http_client_errors_total counter\n");
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    pos += snprintf(buf + pos, buf_size - pos,
      "http_client_errors_total{client=\"%s\",type=\"%s\"} %lu\n",
      c->name, c->type, atomic_load(&c->errors_total));
  }

  // retries_total
  pos += snprintf(buf + pos, buf_size - pos,
    "\n# HELP http_client_retries_total Total retries per client\n"
    "# TYPE http_client_retries_total counter\n");
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    pos += snprintf(buf + pos, buf_size - pos,
      "http_client_retries_total{client=\"%s\",type=\"%s\"} %lu\n",
      c->name, c->type, atomic_load(&c->retries_total));
  }

  // cache_hits_total
  pos += snprintf(buf + pos, buf_size - pos,
    "\n# HELP http_client_cache_hits_total Cache hits per client\n"
    "# TYPE http_client_cache_hits_total counter\n");
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    uint64_t hits = atomic_load(&c->cache_hits_total);
    if (hits > 0) {  // Only emit if cache is being used
      pos += snprintf(buf + pos, buf_size - pos,
        "http_client_cache_hits_total{client=\"%s\",type=\"%s\"} %lu\n",
        c->name, c->type, hits);
    }
  }

  // cache_misses_total
  pos += snprintf(buf + pos, buf_size - pos,
    "\n# HELP http_client_cache_misses_total Cache misses per client\n"
    "# TYPE http_client_cache_misses_total counter\n");
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    uint64_t misses = atomic_load(&c->cache_misses_total);
    if (misses > 0) {  // Only emit if cache is being used
      pos += snprintf(buf + pos, buf_size - pos,
        "http_client_cache_misses_total{client=\"%s\",type=\"%s\"} %lu\n",
        c->name, c->type, misses);
    }
  }

  // latency (as avg in seconds)
  pos += snprintf(buf + pos, buf_size - pos,
    "\n# HELP http_client_latency_seconds_avg Average latency per client\n"
    "# TYPE http_client_latency_seconds_avg gauge\n");
  for (uint32_t i = 0; i < count; i++) {
    const valk_http_client_metrics_t* c = &reg->clients[i];
    uint64_t sum = atomic_load(&c->latency_us_sum);
    uint64_t cnt = atomic_load(&c->latency_count);
    double avg = cnt > 0 ? (double)sum / (double)cnt / 1e6 : 0.0;
    pos += snprintf(buf + pos, buf_size - pos,
      "http_client_latency_seconds_avg{client=\"%s\",type=\"%s\"} %.6f\n",
      c->name, c->type, avg);
  }

  return buf;
}

#endif // VALK_METRICS_ENABLED
