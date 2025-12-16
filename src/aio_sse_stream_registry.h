#ifndef VALK_AIO_SSE_STREAM_REGISTRY_H
#define VALK_AIO_SSE_STREAM_REGISTRY_H

#include <stdint.h>
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

  uint64_t stream_id;                 // Unique ID within registry
  valk_sse_subscription_type_e type;

  // HTTP/2 context
  valk_aio_handle_t *handle;
  valk_aio_system_t *aio_system;  // Direct reference (avoid dereferencing handle)
  nghttp2_session *session;
  int32_t http2_stream_id;

  // Lifecycle state
  _Atomic bool active;
  _Atomic bool being_removed;

  // Per-stream state
  bool first_event_sent;
  uint64_t last_event_id;
  valk_mem_snapshot_t prev_snapshot;
  valk_metrics_baseline_t *metrics_baseline;

  // Pending write buffer
  char *pending_data;
  size_t pending_len;
  size_t pending_offset;
  size_t pending_capacity;

  // AIO metrics baseline (must match valk_sse_diag_conn_t.prev_metrics)
  struct {
    uint64_t bytes_sent;
    uint64_t bytes_recv;
    uint64_t requests_total;
    uint64_t connections_total;
    uint64_t gc_cycles;
    // Pending streams backpressure metrics
    uint64_t pending_streams_current;
    uint64_t pending_streams_total;
    uint64_t pending_streams_processed;
    uint64_t pending_streams_dropped;
  } prev_aio_metrics;
};

// Global registry for all SSE streams
struct valk_sse_stream_registry {
  valk_sse_stream_entry_t *streams;
  size_t stream_count;

  // Global timer
  valk_aio_handle_t *timer_handle;
  bool timer_running;
  uint64_t timer_interval_ms;

  // Shared state
  valk_mem_snapshot_t current_snapshot;
  valk_delta_snapshot_t modular_delta;
  bool modular_delta_initialized;
  valk_metrics_baseline_t global_baseline;

  valk_aio_system_t *aio_system;

  // Statistics
  uint64_t events_pushed_total;
  uint64_t bytes_pushed_total;
};

// Registry Lifecycle
void valk_sse_registry_init(valk_sse_stream_registry_t *registry, valk_aio_system_t *aio);
void valk_sse_registry_shutdown(valk_sse_stream_registry_t *registry);

// Stream Management
valk_sse_stream_entry_t* valk_sse_registry_subscribe(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    nghttp2_session *session,
    int32_t stream_id,
    valk_sse_subscription_type_e type,
    nghttp2_data_provider2 *data_prd_out);

void valk_sse_registry_unsubscribe(valk_sse_stream_registry_t *registry,
                                    valk_sse_stream_entry_t *entry);

// Returns the number of streams that were unsubscribed
size_t valk_sse_registry_unsubscribe_connection(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle);

// Find entry by handle and HTTP/2 stream ID (for cleanup when req is unavailable)
valk_sse_stream_entry_t* valk_sse_registry_find_by_stream(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    int32_t http2_stream_id);

// Timer Control
void valk_sse_registry_timer_start(valk_sse_stream_registry_t *registry);
void valk_sse_registry_timer_stop(valk_sse_stream_registry_t *registry);

// Query API
size_t valk_sse_registry_stream_count(valk_sse_stream_registry_t *registry);
size_t valk_sse_registry_stats_json(valk_sse_stream_registry_t *registry, char *buf, size_t buf_size);

#endif // VALK_AIO_SSE_STREAM_REGISTRY_H
