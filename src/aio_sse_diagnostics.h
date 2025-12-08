#ifndef VALK_AIO_SSE_DIAGNOSTICS_H
#define VALK_AIO_SSE_DIAGNOSTICS_H

#include "aio.h"
#include "memory.h"
#include "gc.h"
#include "metrics_delta.h"
#include <stdint.h>
#include <stdbool.h>

// Forward declarations
typedef struct uv_timer_s uv_timer_t;

// Include nghttp2 for HTTP/2 types
#include <nghttp2/nghttp2.h>

// Per-slot state for connection-aware slabs
typedef struct {
  char state;        // 'A'=active, 'I'=idle, 'C'=closing, 'F'=free
  uint16_t owner;    // Owner index (0xFFFF = none)
  uint32_t age_ms;   // Time since last state change
} valk_slot_diag_t;

// Enhanced slab snapshot with optional per-slot diagnostics
typedef struct {
  const char *name;
  size_t total_slots;
  size_t used_slots;
  size_t overflow_count;

  // Binary bitmap (for simple slabs like LVAL, TCP buffers)
  uint8_t *bitmap;
  size_t bitmap_bytes;

  // Per-slot diagnostics (for connection slabs like handles)
  valk_slot_diag_t *slots;  // NULL for simple bitmap slabs
  bool has_slot_diag;

  // Summary stats for HTTP connections (only for handle slabs)
  struct {
    size_t active;
    size_t idle;
    size_t closing;
  } by_state;

  // Handle type breakdown (only for handle slabs)
  struct {
    size_t tcp_listeners;   // VALK_DIAG_HNDL_TCP
    size_t tasks;           // VALK_DIAG_HNDL_TASK
    size_t timers;          // VALK_DIAG_HNDL_TIMER
    size_t http_conns;      // VALK_DIAG_HNDL_HTTP_CONN
  } by_type;

  // Per-owner connection counts with state breakdown (HTTP connections only)
  struct {
    uint16_t owner_idx;
    size_t active;
    size_t idle;
    size_t closing;
  } by_owner[16];
  size_t owner_count;
} valk_slab_snapshot_t;

// Memory snapshot for SSE transmission
typedef struct valk_mem_snapshot {
  // Slab snapshots
  valk_slab_snapshot_t slabs[8];
  size_t slab_count;

  // Owner map for server/client names
  const char *owner_map[16];
  size_t owner_count;

  // Arena gauges
  struct {
    const char *name;
    size_t used_bytes;
    size_t capacity_bytes;
    size_t high_water_mark;
    size_t overflow_fallbacks;
  } arenas[16];
  size_t arena_count;

  // GC heap stats
  struct {
    size_t allocated_bytes;
    size_t peak_usage;
    size_t gc_threshold;
    uint64_t gc_cycles;
    uint64_t emergency_collections;
  } gc_heap;
} valk_mem_snapshot_t;

// Forward declare state struct
typedef struct valk_sse_diag_state valk_sse_diag_state_t;

// SSE stream context for memory diagnostics (HTTP/2 streaming)
// Multiple streams can share one HTTP/2 connection and timer
typedef struct valk_sse_diag_conn {
  struct valk_sse_diag_conn *next;  // Linked list of streams on same connection
  valk_sse_diag_state_t *state;     // Back-pointer to shared state
  valk_aio_handle_t *handle;        // HTTP connection handle
  nghttp2_session *session;         // HTTP/2 session for data frames
  int32_t stream_id;                // HTTP/2 stream ID
  uint64_t last_event_id;           // For resumption
  valk_aio_system_t *aio_system;    // AIO system reference
  char *pending_data;               // Pending SSE data to send
  size_t pending_len;               // Length of pending data
  size_t pending_offset;            // Offset into pending data
  bool active;                      // Connection alive
  bool data_deferred;               // True if waiting for data

  // Delta tracking - send full state on first event, deltas thereafter
  bool first_event_sent;            // True after first full snapshot sent
  valk_mem_snapshot_t prev_snapshot; // Previous snapshot for delta calculation

  // Previous metrics for delta calculation
  struct {
    uint64_t bytes_sent;
    uint64_t bytes_recv;
    uint64_t requests_total;
    uint64_t connections_total;
    uint64_t gc_cycles;
  } prev_metrics;
} valk_sse_diag_conn_t;

// SSE diagnostics state for an HTTP connection (shared timer, multiple streams)
struct valk_sse_diag_state {
  valk_aio_handle_t *timer_handle;  // Shared timer handle
  valk_sse_diag_conn_t *streams;    // Linked list of active SSE streams
  valk_aio_system_t *aio_system;    // AIO system reference
  valk_aio_handle_t *http_handle;   // HTTP connection handle (for cleanup)

  // Modular metrics delta (collected once per tick, shared by all streams)
  valk_delta_snapshot_t modular_delta;
  bool modular_delta_initialized;

  // Per-connection baseline for stateless delta collection
  // This allows multiple HTTP connections to independently track metric changes
  valk_metrics_baseline_t *modular_baseline;
};

// Initialize SSE diagnostics for an HTTP connection (deprecated, use _http2)
void valk_sse_diag_init(valk_aio_handle_t *conn, valk_aio_system_t *aio);

// Initialize HTTP/2 SSE streaming - returns connection context and populates data provider
// The data provider should be passed to nghttp2_submit_response2
valk_sse_diag_conn_t* valk_sse_diag_init_http2(
    valk_aio_handle_t *handle,
    valk_aio_system_t *aio,
    nghttp2_session *session,
    int32_t stream_id,
    nghttp2_data_provider2 *data_prd_out);

// Stop SSE stream (removes from shared state, stops timer if last stream)
void valk_sse_diag_stop(valk_sse_diag_conn_t *sse_conn);

// Stop all SSE streams on a connection (for abrupt disconnect cleanup)
void valk_sse_diag_stop_all(valk_sse_diag_state_t *state);

// Collect memory snapshot (called by timer)
void valk_mem_snapshot_collect(valk_mem_snapshot_t *snapshot, valk_aio_system_t *aio);

// Flush pending HTTP/2 data on a connection (implemented in aio_uv.c)
void valk_http2_flush_pending(valk_aio_handle_t *conn);

// Check if a session pointer is still valid for a given handle
// Returns true if handle's session matches the provided session pointer
// Used by SSE timer callback to detect if session was freed during processing
bool valk_aio_http_session_valid(valk_aio_handle_t *handle, void *session);

// Encode snapshot to SSE event (memory only - legacy)
int valk_mem_snapshot_to_sse(valk_mem_snapshot_t *snapshot, char *buf, size_t buf_size, uint64_t event_id);

// Encode combined diagnostics to SSE event (memory + metrics)
// This unified event eliminates the need for separate polling from the dashboard
int valk_diag_snapshot_to_sse(valk_mem_snapshot_t *snapshot, valk_aio_system_t *aio,
                               char *buf, size_t buf_size, uint64_t event_id);

// Encode delta diagnostics to SSE event (only changed fields)
// Returns 0 if no changes detected (skip sending), >0 for bytes written, <0 for error
// modular_delta: collected once per tick by timer, NULL if no modular metrics
int valk_diag_delta_to_sse(valk_mem_snapshot_t *current, valk_mem_snapshot_t *prev,
                            valk_sse_diag_conn_t *conn, valk_aio_system_t *aio,
                            valk_delta_snapshot_t *modular_delta,
                            char *buf, size_t buf_size, uint64_t event_id);

// Get fresh diagnostics state as JSON (for /debug/metrics/state endpoint)
// Returns bytes written, or -1 on error
int valk_diag_fresh_state_json(valk_aio_system_t *aio, char *buf, size_t buf_size);

// Free snapshot allocations (bitmaps, slots)
void valk_mem_snapshot_free(valk_mem_snapshot_t *snapshot);

// Copy snapshot for delta tracking (deep copy of bitmaps/slots)
void valk_mem_snapshot_copy(valk_mem_snapshot_t *dst, const valk_mem_snapshot_t *src);

#endif // VALK_AIO_SSE_DIAGNOSTICS_H
