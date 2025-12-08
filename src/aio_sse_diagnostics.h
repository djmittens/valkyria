#ifndef VALK_AIO_SSE_DIAGNOSTICS_H
#define VALK_AIO_SSE_DIAGNOSTICS_H

#include "aio.h"
#include "memory.h"
#include "gc.h"
#include <stdint.h>
#include <stdbool.h>

// Forward declarations
typedef struct uv_timer_s uv_timer_t;

// SSE connection context for memory diagnostics
typedef struct valk_sse_diag_conn {
  valk_aio_handle_t *handle;      // TCP connection handle
  uv_timer_t *timer;               // Push timer (100ms)
  uint64_t last_event_id;         // For resumption
  valk_aio_system_t *aio_system;  // AIO system reference
  char write_buffer[16384];       // Event buffer
  bool active;                    // Connection alive
} valk_sse_diag_conn_t;

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

  // Summary stats (for connection slabs)
  struct {
    size_t active;
    size_t idle;
    size_t closing;
  } by_state;

  // Per-owner connection counts (for owner breakdown visualization)
  struct {
    uint16_t owner_idx;
    size_t count;
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

// Initialize SSE diagnostics for an HTTP connection
void valk_sse_diag_init(valk_aio_handle_t *conn, valk_aio_system_t *aio);

// Stop SSE stream
void valk_sse_diag_stop(valk_sse_diag_conn_t *sse_conn);

// Collect memory snapshot (called by timer)
void valk_mem_snapshot_collect(valk_mem_snapshot_t *snapshot, valk_aio_system_t *aio);

// Encode snapshot to SSE event
int valk_mem_snapshot_to_sse(valk_mem_snapshot_t *snapshot, char *buf, size_t buf_size, uint64_t event_id);

#endif // VALK_AIO_SSE_DIAGNOSTICS_H
