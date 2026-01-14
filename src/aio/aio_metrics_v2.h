// src/aio/aio_metrics_v2.h - AIO metrics using metrics_v2 registry
// This replaces the direct atomic counter approach in aio_metrics.h
#ifndef VALK_AIO_METRICS_V2_H
#define VALK_AIO_METRICS_V2_H

#include "metrics_v2.h"
#include <stdbool.h>

// ============================================================================
// HTTP SERVER METRICS BUNDLE (mirrors valk_aio_metrics_t)
// ============================================================================

// HTTP Server metrics using V2 registry (RED/USE methodology)
// All metrics are marked as persistent (non-evictable)
typedef struct valk_aio_metrics_v2 {
  // RED Method (Rate, Errors, Duration)
  valk_counter_v2_t *requests_total;
  valk_gauge_v2_t *requests_active;
  valk_counter_v2_t *requests_errors;
  valk_counter_v2_t *request_bytes_sent;
  valk_counter_v2_t *request_bytes_recv;
  valk_counter_v2_t *request_duration_us_sum;
  valk_histogram_v2_t *request_duration;

  // USE Method (Utilization, Saturation, Errors)
  valk_counter_v2_t *connections_total;
  valk_gauge_v2_t *connections_active;
  valk_counter_v2_t *connections_failed;
  valk_counter_v2_t *connections_rejected;
  valk_counter_v2_t *connections_rejected_load;
  valk_gauge_v2_t *connections_connecting;
  valk_gauge_v2_t *connections_idle;
  valk_gauge_v2_t *connections_closing;
  valk_counter_v2_t *streams_total;
  valk_gauge_v2_t *streams_active;

  // Resource usage
  valk_counter_v2_t *bytes_sent_total;
  valk_counter_v2_t *bytes_recv_total;

  // Uptime gauge (updated periodically)
  valk_gauge_v2_t *uptime_seconds;

  // System name for labels
  const char *system_name;
} valk_aio_metrics_v2_t;

// ============================================================================
// AIO SYSTEM STATS BUNDLE (mirrors valk_aio_system_stats_t)
// ============================================================================

// AIO System-level statistics using V2 registry
typedef struct valk_aio_system_stats_v2 {
  // Resource counts
  valk_gauge_v2_t *servers_count;
  valk_gauge_v2_t *clients_count;
  valk_gauge_v2_t *handles_count;

  // Memory pool utilization
  valk_gauge_v2_t *arenas_used;
  valk_gauge_v2_t *arenas_total;
  valk_gauge_v2_t *tcp_buffers_used;
  valk_gauge_v2_t *tcp_buffers_total;

  // Event loop queue stats
  valk_gauge_v2_t *queue_depth;
  valk_gauge_v2_t *pending_requests;
  valk_gauge_v2_t *pending_responses;
  valk_gauge_v2_t *queue_capacity;

  // Overflow tracking (cumulative)
  valk_counter_v2_t *arena_pool_overflow;
  valk_counter_v2_t *tcp_buffer_overflow;
  valk_counter_v2_t *connections_rejected_load;

  // System name for labels
  const char *system_name;
} valk_aio_system_stats_v2_t;

// ============================================================================
// VM METRICS BUNDLE (mirrors valk_vm_metrics_t)
// ============================================================================

// GC pause histogram bucket bounds (milliseconds converted to seconds)
#define VALK_GC_PAUSE_BUCKET_COUNT 5
static const double VALK_GC_PAUSE_BUCKETS[VALK_GC_PAUSE_BUCKET_COUNT] = {
  0.001,   // 1ms
  0.005,   // 5ms
  0.010,   // 10ms
  0.016,   // 16ms (~60fps frame budget)
  0.100    // 100ms
};

// Request duration histogram bucket bounds (seconds)
#define VALK_REQUEST_DURATION_BUCKET_COUNT 8
static const double VALK_REQUEST_DURATION_BUCKETS[VALK_REQUEST_DURATION_BUCKET_COUNT] = {
  0.001,   // 1ms
  0.005,   // 5ms
  0.010,   // 10ms
  0.025,   // 25ms
  0.050,   // 50ms
  0.100,   // 100ms
  0.250,   // 250ms
  1.000    // 1s
};

// VM-level metrics using V2 registry
typedef struct valk_vm_metrics_v2 {
  // GC metrics
  valk_counter_v2_t *gc_cycles;
  valk_counter_v2_t *gc_pause_us_total;
  valk_gauge_v2_t *gc_pause_us_max;
  valk_counter_v2_t *gc_reclaimed_bytes;
  valk_counter_v2_t *gc_allocated_bytes;
  valk_gauge_v2_t *gc_efficiency_pct;
  valk_gauge_v2_t *gc_heap_used;
  valk_gauge_v2_t *gc_heap_total;
  valk_gauge_v2_t *gc_large_object_bytes;
  valk_histogram_v2_t *gc_pause_duration;

  // Interpreter metrics
  valk_counter_v2_t *eval_total;
  valk_counter_v2_t *function_calls;
  valk_counter_v2_t *builtin_calls;
  valk_gauge_v2_t *stack_depth_max;
  valk_counter_v2_t *closures_created;
  valk_counter_v2_t *env_lookups;

  // Event loop metrics (via event_loop_metrics.h)
  // These are created separately to allow multiple loops
} valk_vm_metrics_v2_t;

// ============================================================================
// FACTORY API
// ============================================================================

// Initialize HTTP server metrics for a named system
// All metrics are created with system={name} label and marked persistent
// Returns true on success, false if registry is full
bool valk_aio_metrics_v2_init(valk_aio_metrics_v2_t *m, const char *system_name);

// Initialize system stats metrics for a named system
bool valk_aio_system_stats_v2_init(valk_aio_system_stats_v2_t *s,
                                    const char *system_name,
                                    u64 arenas_total,
                                    u64 tcp_buffers_total,
                                    u64 queue_capacity);

// Initialize VM-level metrics (singleton, no labels needed)
bool valk_vm_metrics_v2_init(valk_vm_metrics_v2_t *m);

// ============================================================================
// INSTRUMENTATION API (replaces valk_aio_metrics_on_* functions)
// ============================================================================

// Connection instrumentation
static inline void valk_aio_metrics_v2_on_connection(valk_aio_metrics_v2_t *m, bool success) {
  if (!m) return;
  valk_counter_v2_inc(m->connections_total);
  if (success) {
    valk_gauge_v2_inc(m->connections_active);
  } else {
    valk_counter_v2_inc(m->connections_failed);
  }
}

static inline void valk_aio_metrics_v2_on_close(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_gauge_v2_dec(m->connections_active);
}

// Stream instrumentation
static inline void valk_aio_metrics_v2_on_stream_start(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_counter_v2_inc(m->streams_total);
  valk_gauge_v2_inc(m->streams_active);
  valk_gauge_v2_inc(m->requests_active);
}

static inline void valk_aio_metrics_v2_on_stream_end(valk_aio_metrics_v2_t *m,
                                                      bool error,
                                                      u64 duration_us,
                                                      u64 bytes_sent,
                                                      u64 bytes_recv) {
  if (!m) return;
  valk_gauge_v2_dec(m->streams_active);
  valk_gauge_v2_dec(m->requests_active);
  valk_counter_v2_inc(m->requests_total);

  if (error) {
    valk_counter_v2_inc(m->requests_errors);
  }

  valk_counter_v2_add(m->request_duration_us_sum, duration_us);
  valk_counter_v2_add(m->request_bytes_sent, bytes_sent);
  valk_counter_v2_add(m->request_bytes_recv, bytes_recv);
  valk_counter_v2_add(m->bytes_sent_total, bytes_sent);
  valk_counter_v2_add(m->bytes_recv_total, bytes_recv);
  valk_histogram_v2_observe_us(m->request_duration, duration_us);
}

// Connection state tracking
static inline void valk_aio_metrics_v2_on_connecting(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_gauge_v2_inc(m->connections_connecting);
}

static inline void valk_aio_metrics_v2_on_connected(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_gauge_v2_dec(m->connections_connecting);
  valk_gauge_v2_inc(m->connections_active);
}

static inline void valk_aio_metrics_v2_on_idle(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_gauge_v2_dec(m->connections_active);
  valk_gauge_v2_inc(m->connections_idle);
}

static inline void valk_aio_metrics_v2_on_reactivate(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_gauge_v2_dec(m->connections_idle);
  valk_gauge_v2_inc(m->connections_active);
}

static inline void valk_aio_metrics_v2_on_closing(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_gauge_v2_inc(m->connections_closing);
}

static inline void valk_aio_metrics_v2_on_closed(valk_aio_metrics_v2_t *m) {
  if (!m) return;
  valk_gauge_v2_dec(m->connections_closing);
}

// ============================================================================
// SYSTEM STATS INSTRUMENTATION
// ============================================================================

static inline void valk_aio_system_stats_v2_on_server_start(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_inc(s->servers_count);
}

static inline void valk_aio_system_stats_v2_on_server_stop(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_dec(s->servers_count);
}

static inline void valk_aio_system_stats_v2_on_client_start(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_inc(s->clients_count);
}

static inline void valk_aio_system_stats_v2_on_client_stop(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_dec(s->clients_count);
}

static inline void valk_aio_system_stats_v2_on_handle_create(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_inc(s->handles_count);
}

static inline void valk_aio_system_stats_v2_on_handle_close(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_dec(s->handles_count);
}

static inline void valk_aio_system_stats_v2_on_arena_acquire(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_inc(s->arenas_used);
}

static inline void valk_aio_system_stats_v2_on_arena_release(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_gauge_v2_dec(s->arenas_used);
}

static inline void valk_aio_system_stats_v2_on_arena_overflow(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_counter_v2_inc(s->arena_pool_overflow);
}

static inline void valk_aio_system_stats_v2_on_tcp_buffer_overflow(valk_aio_system_stats_v2_t *s) {
  if (!s) return;
  valk_counter_v2_inc(s->tcp_buffer_overflow);
}

static inline void valk_aio_system_stats_v2_update_queue(valk_aio_system_stats_v2_t *s,
                                                          u64 pending_requests,
                                                          u64 pending_responses) {
  if (!s) return;
  valk_gauge_v2_set(s->pending_requests, (i64)pending_requests);
  valk_gauge_v2_set(s->pending_responses, (i64)pending_responses);
  valk_gauge_v2_set(s->queue_depth, (i64)(pending_requests + pending_responses));
}

#endif // VALK_AIO_METRICS_V2_H
