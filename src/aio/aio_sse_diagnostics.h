#ifndef VALK_AIO_SSE_DIAGNOSTICS_H
#define VALK_AIO_SSE_DIAGNOSTICS_H

#include "aio.h"
#include "memory.h"
#include "gc.h"
#include "metrics_delta.h"
#include <stdbool.h>

#define VALK_DIAG_RETAINED_SET_MAX 10

// Forward declarations
typedef struct uv_timer_s uv_timer_t;

// Include nghttp2 for HTTP/2 types
#include <nghttp2/nghttp2.h>

// Per-slot state for connection-aware slabs
typedef struct {
  char state;        // 'A'=active, 'I'=idle, 'C'=closing, 'F'=free
  u16 owner;    // Owner index (0xFFFF = none)
  u32 age_ms;   // Time since last state change
} valk_slot_diag_t;

// ============================================================================
// Generic Heap Tier System
// ============================================================================

// Generic heap tier snapshot - one entry per memory pool/slab
// All fields are present; unused fields are 0 (e.g., malloc has no objects)
typedef struct {
  const char *name;              // e.g., "lval", "lenv", "malloc"

  // Byte-level metrics
  u64 bytes_used;
  u64 bytes_total;
  u64 bytes_peak;             // High water mark (bytes)

  // Object-level metrics (0 for malloc-style allocators)
  u64 objects_used;
  u64 objects_total;
  u64 objects_peak;           // High water mark (objects)
} valk_heap_tier_snapshot_t;

// Enhanced slab snapshot with optional per-slot diagnostics
typedef struct {
  const char *name;
  u64 total_slots;
  u64 used_slots;
  u64 peak_used;  // High water mark
  u64 overflow_count;

  // Slab change detection - numFree from slab at snapshot time
  // Used to skip expensive bitmap regeneration when slab unchanged
  u64 cached_num_free;

  // Binary bitmap (for simple slabs like LVAL, TCP buffers)
  u8 *bitmap;
  u64 bitmap_bytes;

  // Per-slot diagnostics (for connection slabs like handles)
  valk_slot_diag_t *slots;  // NULL for simple bitmap slabs
  bool has_slot_diag;

  // Summary stats for HTTP connections (only for handle slabs)
  struct {
    u64 active;
    u64 idle;
    u64 closing;
  } by_state;

  // Handle type breakdown (only for handle slabs)
  struct {
    u64 tcp_listeners;   // VALK_DIAG_HNDL_TCP
    u64 tasks;           // VALK_DIAG_HNDL_TASK
    u64 timers;          // VALK_DIAG_HNDL_TIMER
    u64 http_conns;      // VALK_DIAG_HNDL_HTTP_CONN
  } by_type;

  // Per-owner connection counts with state breakdown (HTTP connections only)
  struct {
    u16 owner_idx;
    u64 active;
    u64 idle;
    u64 closing;
  } by_owner[16];
  u64 owner_count;
} valk_slab_snapshot_t;

// Memory snapshot for SSE transmission
typedef struct valk_mem_snapshot {
  // Slab snapshots
  valk_slab_snapshot_t slabs[8];
  u64 slab_count;

  // Owner map for server/client names
  const char *owner_map[16];
  u64 owner_count;

  // Arena gauges
  struct {
    const char *name;
    u64 used_bytes;
    u64 capacity_bytes;
    u64 high_water_mark;
    u64 overflow_fallbacks;
    u64 overflow_bytes;
  } arenas[16];
  u64 arena_count;

  // GC heap stats (generic tier array)
  struct {
    // Dynamic tier array (populated by collection)
    valk_heap_tier_snapshot_t tiers[8];
    u64 tier_count;

    // Common GC stats
    u8 gc_threshold_pct;   // GC triggers at this % of capacity
    u64 gc_cycles;
    u64 emergency_collections;
    u8 efficiency_pct;     // Last GC efficiency (reclaimed/before * 100)

    // Object survival histogram - tracks how long objects live before dying
    // Used to detect potential memory leaks (objects surviving many GC cycles)
    u64 survival_gen_0;      // Died in first GC (short-lived, expected)
    u64 survival_gen_1_5;    // Survived 1-5 cycles (normal)
    u64 survival_gen_6_20;   // Survived 6-20 cycles (medium-lived)
    u64 survival_gen_21_plus; // Survived 21+ cycles (potential leak)

    // Frame-time pause histogram - tracks GC pause impact on frame budgets
    // Used by game profile to show distribution of pauses relative to frame time
    u64 pause_0_1ms;         // No impact (0-1ms)
    u64 pause_1_5ms;         // Minor impact (1-5ms)
    u64 pause_5_10ms;        // Noticeable (5-10ms)
    u64 pause_10_16ms;       // Frame drop risk at 60fps (10-16ms)
    u64 pause_16ms_plus;     // Frame drop certain at 60fps (16ms+)

    // Fragmentation metrics - tracks slab utilization vs peak
    double lval_fragmentation;    // 1.0 - (used/peak), 0 = no fragmentation
    double lenv_fragmentation;    // Same for lenv slab
    u64 free_list_count;       // Objects on malloc free list
    u64 free_list_bytes;       // Estimated bytes on free list

    // Parallel GC metrics
    bool parallel_enabled;        // True if multiple threads registered
    u64 threads_registered;    // Number of threads participating in GC
    u64 parallel_cycles;       // Number of parallel GC cycles
    u64 parallel_pause_us_total; // Total pause time across parallel cycles

    // Size class statistics (heap2)
    struct {
      u16 slot_size;           // Slot size in bytes (16, 32, 64, ...)
      u64 used_slots;
      u64 total_slots;
    } size_classes[9];         // 9 size classes: 16B to 4KB
    u64 size_class_count;
    u64 large_object_bytes;    // Bytes in large objects (>4KB)
  } gc_heap;

  // Process-level memory (from OS)
  valk_process_memory_t process;

  // Detailed smaps breakdown (Linux only)
  valk_smaps_breakdown_t smaps;

  // Aggregated breakdown by subsystem (for overview widget)
  // Each subsystem has capacity (mapped) and used (resident) bytes
  struct {
    u64 scratch_arena_used;
    u64 scratch_arena_capacity;
    u64 gc_heap_used;
    u64 gc_heap_capacity;
    u64 gc_lval_slab_used;
    u64 gc_lval_slab_capacity;
    u64 gc_lenv_slab_used;
    u64 gc_lenv_slab_capacity;
    u64 gc_malloc_used;         // Malloc has no fixed capacity
    u64 aio_slabs_used;
    u64 aio_slabs_capacity;
    u64 metrics_used;           // Metrics registry active slots
    u64 metrics_capacity;       // Metrics registry total size
    u64 untracked_bytes;        // process.rss - tracked used (resident but untracked)
    u64 untracked_reserved;     // process.vms - tracked capacities (mapped but untracked)
  } breakdown;

  // REPL eval memory delta (only populated when running as REPL)
  struct {
    bool valid;                    // True if running as REPL with eval data
    i64 heap_delta;            // Heap change from last eval
    i64 scratch_delta;         // Scratch change from last eval
    i64 lval_delta;            // LVAL count change
    i64 lenv_delta;            // LENV count change
    u64 eval_count;           // Total evals since REPL start
  } repl_eval;
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
  i32 stream_id;                // HTTP/2 stream ID
  u64 last_event_id;           // For resumption
  valk_aio_system_t *aio_system;    // AIO system reference
  char *pending_data;               // Pending SSE data to send
  u64 pending_len;               // Length of pending data
  u64 pending_offset;            // Offset into pending data
  bool active;                      // Connection alive
  bool data_deferred;               // True if waiting for data

  // Delta tracking - send full state on first event, deltas thereafter
  bool first_event_sent;            // True after first full snapshot sent
  valk_mem_snapshot_t prev_snapshot; // Previous snapshot for delta calculation

  // Previous metrics for delta calculation
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

  // Cached snapshot for bitmap/slot caching optimization
  // Avoids O(n) free list walks when slabs haven't changed
  valk_mem_snapshot_t cached_snapshot;
  bool cached_snapshot_valid;
};

// Initialize HTTP/2 SSE streaming - returns connection context and populates data provider
// The data provider should be passed to nghttp2_submit_response2
valk_sse_diag_conn_t* valk_sse_diag_init_http2(
    valk_aio_handle_t *handle,
    valk_aio_system_t *aio,
    nghttp2_session *session,
    i32 stream_id,
    nghttp2_data_provider2 *data_prd_out);

// Stop SSE stream (removes from shared state, stops timer if last stream)
void valk_sse_diag_stop(valk_sse_diag_conn_t *sse_conn);

// Stop all SSE streams on a connection (for abrupt disconnect cleanup)
void valk_sse_diag_stop_all(valk_sse_diag_state_t *state);

// Collect memory snapshot (called by timer)
// If prev is non-NULL, slabs with unchanged numFree will reuse cached bitmaps
void valk_mem_snapshot_collect(valk_mem_snapshot_t *snapshot, valk_aio_system_t *aio);
void valk_mem_snapshot_collect_with_cache(valk_mem_snapshot_t *snapshot,
                                          valk_aio_system_t *aio,
                                          const valk_mem_snapshot_t *prev);

// Flush pending HTTP/2 data on a connection (implemented in aio_uv.c)
void valk_http2_flush_pending(valk_aio_handle_t *conn);

// Check if a session pointer is still valid for a given handle
// Returns true if handle's session matches the provided session pointer
// Used by SSE timer callback to detect if session was freed during processing
bool valk_aio_http_session_valid(valk_aio_handle_t *handle, void *session);

// Encode snapshot to SSE event (memory only - legacy)
int valk_mem_snapshot_to_sse(valk_mem_snapshot_t *snapshot, char *buf, u64 buf_size, u64 event_id);

// Encode memory delta to SSE event (memory only, no AIO/modular metrics)
// Returns 0 if no changes detected (skip sending), >0 for bytes written, <0 for error
int valk_mem_delta_to_sse(valk_mem_snapshot_t *current, valk_mem_snapshot_t *prev,
                           char *buf, u64 buf_size, u64 event_id);

// Encode combined diagnostics to SSE event (memory + metrics)
// This unified event eliminates the need for separate polling from the dashboard
int valk_diag_snapshot_to_sse(valk_mem_snapshot_t *snapshot, valk_aio_system_t *aio,
                               char *buf, u64 buf_size, u64 event_id);

// Encode delta diagnostics to SSE event (only changed fields)
// Returns 0 if no changes detected (skip sending), >0 for bytes written, <0 for error
// modular_delta: collected once per tick by timer, NULL if no modular metrics
int valk_diag_delta_to_sse(valk_mem_snapshot_t *current, valk_mem_snapshot_t *prev,
                            valk_sse_diag_conn_t *conn, valk_aio_system_t *aio,
                            valk_delta_snapshot_t *modular_delta,
                            char *buf, u64 buf_size, u64 event_id);

// Get fresh diagnostics state as JSON (for /debug/metrics/state endpoint)
// Returns bytes written, or -1 on error
int valk_diag_fresh_state_json(valk_aio_system_t *aio, char *buf, u64 buf_size);

// Free snapshot allocations (bitmaps, slots)
void valk_mem_snapshot_free(valk_mem_snapshot_t *snapshot);

// Copy snapshot for delta tracking (deep copy of bitmaps/slots)
void valk_mem_snapshot_copy(valk_mem_snapshot_t *dst, const valk_mem_snapshot_t *src);

#endif // VALK_AIO_SSE_DIAGNOSTICS_H
