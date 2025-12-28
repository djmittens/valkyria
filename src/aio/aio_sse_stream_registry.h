#ifndef VALK_AIO_SSE_STREAM_REGISTRY_H
#define VALK_AIO_SSE_STREAM_REGISTRY_H

#include <stdbool.h>
#include <stdatomic.h>
#include <nghttp2/nghttp2.h>

#include "aio_sse_diagnostics.h"
#include "metrics_delta.h"

// Forward declarations
typedef struct valk_aio_system valk_aio_system_t;
typedef struct valk_aio_handle_t valk_aio_handle_t;
typedef struct uv_timer_s uv_timer_t;
typedef struct valk_sse_stream_entry valk_sse_stream_entry_t;
typedef struct valk_sse_stream_registry valk_sse_stream_registry_t;

// Stream subscription types
typedef enum {
  VALK_SSE_SUB_DIAGNOSTICS,    // Memory + metrics combined
  VALK_SSE_SUB_METRICS_ONLY,   // Metrics only (modular)
  VALK_SSE_SUB_MEMORY_ONLY,    // Memory snapshots only
} valk_sse_subscription_type_e;

// Registry entry for a single SSE stream
struct valk_sse_stream_entry {
  valk_sse_stream_entry_t *next;
  valk_sse_stream_entry_t *prev;  // Doubly-linked for O(1) removal

  u64 stream_id;                 // Unique ID within registry
  valk_sse_subscription_type_e type;

  // HTTP/2 context
  valk_aio_handle_t *handle;
  valk_aio_system_t *aio_system;  // Direct reference (avoid dereferencing handle)
  nghttp2_session *session;
  i32 http2_stream_id;

  // Lifecycle state
  _Atomic bool active;
  _Atomic bool being_removed;

  // Activity tracking for idle timeout
  u64 created_at_ms;
  u64 last_activity_ms;
  u64 idle_timeout_ms;       // 0 = no timeout

  // Per-stream state
  bool first_event_sent;
  u64 last_event_id;
  valk_mem_snapshot_t prev_snapshot;
  valk_metrics_baseline_t *metrics_baseline;

  // Pending write buffer
  char *pending_data;
  u64 pending_len;
  u64 pending_offset;
  u64 pending_capacity;

  // AIO metrics baseline (must match valk_sse_diag_conn_t.prev_metrics)
  struct {
    u64 bytes_sent;
    u64 bytes_recv;
    u64 requests_total;
    u64 connections_total;
    u64 gc_cycles;
    // Pending streams backpressure metrics
    u64 pending_streams_current;
    u64 pending_streams_total;
    u64 pending_streams_processed;
    u64 pending_streams_dropped;
  } prev_aio_metrics;
};

// Global registry for all SSE streams
struct valk_sse_stream_registry {
  valk_sse_stream_entry_t *streams;
  u64 stream_count;

  // Global timer
  valk_aio_handle_t *timer_handle;
  bool timer_running;
  u64 timer_interval_ms;

  // Shutdown state
  bool shutting_down;
  u64 shutdown_deadline_ms;

  // Shared state
  valk_mem_snapshot_t current_snapshot;
  valk_delta_snapshot_t modular_delta;
  bool modular_delta_initialized;
  valk_metrics_baseline_t global_baseline;

  valk_aio_system_t *aio_system;

  // Statistics
  u64 events_pushed_total;
  u64 bytes_pushed_total;
  u64 streams_timed_out;
  u64 streams_cancelled;
};

// Registry Lifecycle
void valk_sse_registry_init(valk_sse_stream_registry_t *registry, valk_aio_system_t *aio);
void valk_sse_registry_shutdown(valk_sse_stream_registry_t *registry);

// Stream Management
valk_sse_stream_entry_t* valk_sse_registry_subscribe(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    nghttp2_session *session,
    i32 stream_id,
    valk_sse_subscription_type_e type,
    nghttp2_data_provider2 *data_prd_out);

void valk_sse_registry_unsubscribe(valk_sse_stream_registry_t *registry,
                                    valk_sse_stream_entry_t *entry);

// Returns the number of streams that were unsubscribed
u64 valk_sse_registry_unsubscribe_connection(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle);

// Find entry by handle and HTTP/2 stream ID (for cleanup when req is unavailable)
valk_sse_stream_entry_t* valk_sse_registry_find_by_stream(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    i32 http2_stream_id);

// Timer Control
void valk_sse_registry_timer_start(valk_sse_stream_registry_t *registry);
void valk_sse_registry_timer_stop(valk_sse_stream_registry_t *registry);

// Query API
u64 valk_sse_registry_stream_count(valk_sse_stream_registry_t *registry);
u64 valk_sse_registry_stats_json(valk_sse_stream_registry_t *registry, char *buf, u64 buf_size);

// Timeout Management
void valk_sse_registry_set_idle_timeout(valk_sse_stream_entry_t *entry, u64 timeout_ms);
u64 valk_sse_registry_check_timeouts(valk_sse_stream_registry_t *registry);

// Stream Cancellation
int valk_sse_registry_cancel_stream(valk_sse_stream_registry_t *registry, u64 stream_id);
valk_sse_stream_entry_t *valk_sse_registry_find_by_id(valk_sse_stream_registry_t *registry, u64 stream_id);

// Graceful Shutdown
int valk_sse_registry_graceful_shutdown(valk_sse_stream_registry_t *registry, u64 drain_timeout_ms);
u64 valk_sse_registry_force_close_all(valk_sse_stream_registry_t *registry);
bool valk_sse_registry_is_shutting_down(valk_sse_stream_registry_t *registry);

#endif // VALK_AIO_SSE_STREAM_REGISTRY_H
