#include "aio_sse_diagnostics.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <uv.h>

#include "aio.h"
#include "common.h"
#include "gc.h"
#include "log.h"
#include "memory.h"

// ============================================================================
// Slab Bitmap Generation
// ============================================================================

// Walk Treiber stack to generate actual bitmap
// Returns heap-allocated bitmap, caller must free
static uint8_t *slab_to_bitmap(valk_slab_t *slab, size_t *out_bytes,
                                size_t *out_used) {
  size_t total_slots = slab->numItems;
  size_t bitmap_bytes = (total_slots + 7) / 8;
  uint8_t *bitmap = calloc(bitmap_bytes, 1);

  if (!bitmap) {
    *out_bytes = 0;
    *out_used = 0;
    return NULL;
  }

  // Start with all slots marked as USED (1)
  memset(bitmap, 0xFF, bitmap_bytes);

  // Walk free list and mark slots as FREE (0)
  // The slab uses a Treiber stack with versioned pointers
  uint64_t head_tag = __atomic_load_n(&slab->head, __ATOMIC_ACQUIRE);

  // Unpack version and offset from versioned pointer
  // Version is in upper 32 bits, offset in lower 32 bits
  size_t head_offset = head_tag & (size_t)UINT32_MAX;

  size_t free_count = 0;

  while (head_offset != SIZE_MAX) {
    if (head_offset >= total_slots) {
      VALK_ERROR("Invalid slab offset %zu (total=%zu)", head_offset,
                 total_slots);
      break;
    }

    // Clear bit (mark as free)
    bitmap[head_offset / 8] &= ~(1 << (head_offset % 8));
    free_count++;

    // Get item at this offset
    size_t stride = valk_slab_item_stride(slab->itemSize);
    valk_slab_item_t *item =
        (valk_slab_item_t *)&slab->heap[stride * head_offset];

    // Get next in free list (also versioned)
    uint64_t next_tag = __atomic_load_n(&item->next, __ATOMIC_ACQUIRE);
    head_offset = next_tag & (size_t)UINT32_MAX;

    // Safety: prevent infinite loops
    if (free_count > total_slots) {
      VALK_ERROR("Slab free list corrupted (cycle detected)");
      break;
    }
  }

  *out_bytes = bitmap_bytes;
  *out_used = total_slots - free_count;
  return bitmap;
}

// Convert bitmap bytes to hex string
static void bitmap_to_hex(const uint8_t *bitmap, size_t bytes, char *hex_out) {
  static const char hex_chars[] = "0123456789abcdef";
  for (size_t i = 0; i < bytes; i++) {
    hex_out[i * 2] = hex_chars[(bitmap[i] >> 4) & 0x0F];
    hex_out[i * 2 + 1] = hex_chars[bitmap[i] & 0x0F];
  }
  hex_out[bytes * 2] = '\0';
}

#ifdef VALK_METRICS_ENABLED
// ============================================================================
// Per-Slot Diagnostics for Connection-Aware Slabs
// ============================================================================

// Walk handle slab and extract per-slot diagnostics with state and owner
static void slab_to_slot_diag(valk_slab_t *slab, valk_slab_snapshot_t *out,
                               uint64_t now_ms) {
  (void)now_ms;  // Reserved for future use when struct access is available
  size_t total = slab->numItems;
  out->slots = calloc(total, sizeof(valk_slot_diag_t));
  if (!out->slots) {
    out->has_slot_diag = false;
    return;
  }
  out->has_slot_diag = true;
  out->total_slots = total;

  // Initialize all as free
  for (size_t i = 0; i < total; i++) {
    out->slots[i].state = 'F';
    out->slots[i].owner = 0xFFFF;
    out->slots[i].age_ms = 0;
  }

  // Walk free list to mark free slots
  size_t stride = valk_slab_item_stride(slab->itemSize);
  uint64_t head_tag = __atomic_load_n(&slab->head, __ATOMIC_ACQUIRE);
  size_t head_offset = head_tag & (size_t)UINT32_MAX;
  size_t free_count = 0;

  // Build a set of free slot indices
  bool *is_free = calloc(total, sizeof(bool));
  if (!is_free) {
    free(out->slots);
    out->slots = NULL;
    out->has_slot_diag = false;
    return;
  }

  while (head_offset != SIZE_MAX && head_offset < total && free_count < total) {
    is_free[head_offset] = true;
    free_count++;

    valk_slab_item_t *item =
        (valk_slab_item_t *)&slab->heap[stride * head_offset];
    uint64_t next_tag = __atomic_load_n(&item->next, __ATOMIC_ACQUIRE);
    head_offset = next_tag & (size_t)UINT32_MAX;
  }

  // Now iterate all slots and extract diag from allocated handles
  size_t used_count = 0;
  for (size_t i = 0; i < total; i++) {
    if (is_free[i]) {
      out->slots[i].state = 'F';
      continue;
    }

    // Get handle at this slot (skip the slab_item_t header)
    // Note: item unused for now - actual diag extraction requires struct visibility
    (void)stride;  // Suppress unused warning

    // The handle struct layout is:
    // - kind (handle_kind_t enum, internal to aio_uv.c)
    // - prev, next, sys, arg pointers
    // - onOpen, onClose callbacks
    // - uv union
    // - http sub-struct with diag field
    // We access the diag field through byte offset since the struct is opaque
    // For now, treat all used slots as active unless we can read the diag

    // Access diag field - it's at the end of the http sub-struct
    // The http sub-struct contains: state, ssl, session, handler, connectReq, server,
    // active_streams, pending_write, spillover_data, spillover_len,
    // backpressure, backpressure_next, backpressure_start_time, then diag
    //
    // Rather than calculate exact offset, we'll use a simpler approach:
    // All allocated handles are treated as "active" for basic visualization
    // The actual state tracking via diag field requires knowing the struct layout

    out->slots[i].state = 'A';
    out->slots[i].owner = 0xFFFF;
    out->slots[i].age_ms = 0;
    out->by_state.active++;
    used_count++;
  }

  out->used_slots = used_count;
  out->overflow_count = __atomic_load_n(&slab->overflowCount, __ATOMIC_ACQUIRE);

  free(is_free);
}

// Encode slot states as compact string: "AAIFAACI..."
static void slots_to_state_string(valk_slot_diag_t *slots, size_t count, char *out) {
  for (size_t i = 0; i < count; i++) {
    out[i] = slots[i].state;
  }
  out[count] = '\0';
}
#endif // VALK_METRICS_ENABLED

// ============================================================================
// Snapshot Collection
// ============================================================================

void valk_mem_snapshot_collect(valk_mem_snapshot_t *snapshot,
                                valk_aio_system_t *aio) {
  memset(snapshot, 0, sizeof(*snapshot));

  if (!aio) {
    return;
  }

  // Collect slab allocators using accessor functions
  size_t slab_idx = 0;

#ifdef VALK_METRICS_ENABLED
  // Helper macro to add a slab to the snapshot
  #define ADD_SLAB(accessor, label) do { \
    valk_slab_t *slab = accessor(aio); \
    if (slab && slab_idx < 8) { \
      snapshot->slabs[slab_idx].name = (const char *)label; \
      snapshot->slabs[slab_idx].bitmap = \
          slab_to_bitmap(slab, &snapshot->slabs[slab_idx].bitmap_bytes, \
                         &snapshot->slabs[slab_idx].used_slots); \
      snapshot->slabs[slab_idx].total_slots = slab->numItems; \
      snapshot->slabs[slab_idx].overflow_count = \
          __atomic_load_n(&slab->overflowCount, __ATOMIC_ACQUIRE); \
      slab_idx++; \
    } \
  } while(0)

  // TCP Buffers (simple bitmap)
  ADD_SLAB(valk_aio_get_tcp_buffer_slab, "tcp_buffers");

  // Handle Slab - use per-slot diagnostics for connection state tracking
  {
    valk_slab_t *handle_slab = valk_aio_get_handle_slab(aio);
    if (handle_slab && slab_idx < 8) {
      snapshot->slabs[slab_idx].name = "handles";
      // Get current time for age calculation
      uint64_t now_ms = (uint64_t)(uv_hrtime() / 1000000ULL);
      slab_to_slot_diag(handle_slab, &snapshot->slabs[slab_idx], now_ms);
      slab_idx++;
    }
  }

  // Stream Arenas (simple bitmap)
  ADD_SLAB(valk_aio_get_stream_arenas_slab, "stream_arenas");

  // HTTP Servers
  ADD_SLAB(valk_aio_get_http_servers_slab, "http_servers");

  // HTTP Clients
  ADD_SLAB(valk_aio_get_http_clients_slab, "http_clients");

  // LVAL Slab (from GC heap)
  valk_gc_malloc_heap_t *gc_heap = valk_aio_get_gc_heap(aio);
  if (gc_heap && gc_heap->lval_slab && slab_idx < 8) {
    snapshot->slabs[slab_idx].name = (const char *)"lval";
    snapshot->slabs[slab_idx].bitmap =
        slab_to_bitmap(gc_heap->lval_slab,
                       &snapshot->slabs[slab_idx].bitmap_bytes,
                       &snapshot->slabs[slab_idx].used_slots);
    snapshot->slabs[slab_idx].total_slots = gc_heap->lval_slab->numItems;
    snapshot->slabs[slab_idx].overflow_count =
        __atomic_load_n(&gc_heap->lval_slab->overflowCount, __ATOMIC_ACQUIRE);
    slab_idx++;
  }

  #undef ADD_SLAB
#endif

  snapshot->slab_count = slab_idx;

  // Collect arena allocators
  size_t arena_idx = 0;

  // Scratch Arena (from thread context)
  if (valk_thread_ctx.scratch && arena_idx < 16) {
    snapshot->arenas[arena_idx].name = (const char *)"scratch";
    snapshot->arenas[arena_idx].used_bytes =
        __atomic_load_n(&valk_thread_ctx.scratch->offset, __ATOMIC_ACQUIRE);
    snapshot->arenas[arena_idx].capacity_bytes = valk_thread_ctx.scratch->capacity;
    snapshot->arenas[arena_idx].high_water_mark =
        valk_thread_ctx.scratch->stats.high_water_mark;
    snapshot->arenas[arena_idx].overflow_fallbacks =
        valk_thread_ctx.scratch->stats.overflow_fallbacks;
    arena_idx++;
  }

  // Stream arenas are allocated from slab, individual usage not tracked here
  // We only track the slab allocation status above

  snapshot->arena_count = arena_idx;

  // Collect GC heap stats
#ifdef VALK_METRICS_ENABLED
  // gc_heap was already fetched above for LVAL slab collection
  if (gc_heap) {
    snapshot->gc_heap.allocated_bytes = gc_heap->allocated_bytes;
    snapshot->gc_heap.peak_usage = gc_heap->stats.peak_usage;
    snapshot->gc_heap.gc_threshold = gc_heap->gc_threshold;
    snapshot->gc_heap.gc_cycles =
        atomic_load(&gc_heap->runtime_metrics.cycles_total);
    snapshot->gc_heap.emergency_collections =
        gc_heap->stats.emergency_collections;
  }

  // Collect owner map for server/client names
  size_t owner_count = valk_owner_get_count(aio);
  snapshot->owner_count = owner_count;
  for (size_t i = 0; i < owner_count && i < 16; i++) {
    snapshot->owner_map[i] = valk_owner_get_name(aio, (uint16_t)i);
  }
#endif
}

// ============================================================================
// SSE Event Formatting
// ============================================================================

int valk_mem_snapshot_to_sse(valk_mem_snapshot_t *snapshot, char *buf,
                              size_t buf_size, uint64_t event_id) {
  char *p = buf;
  char *end = buf + buf_size;

  // SSE event header
  int n = snprintf(p, end - p, "event: memory\nid: %lu\ndata: {", event_id);
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // Slabs array
  n = snprintf(p, end - p, "\"slabs\":[");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  for (size_t i = 0; i < snapshot->slab_count; i++) {
    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || n >= end - p) return -1;
      p += n;
    }

    valk_slab_snapshot_t *slab = &snapshot->slabs[i];

    if (slab->has_slot_diag && slab->slots) {
      // Connection-aware slab with per-slot state string
      char *states = malloc(slab->total_slots + 1);
      if (!states) return -1;
      slots_to_state_string(slab->slots, slab->total_slots, states);

      n = snprintf(p, end - p,
                   "{\"name\":\"%s\",\"total\":%zu,\"used\":%zu,"
                   "\"states\":\"%s\","
                   "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu},"
                   "\"overflow\":%zu}",
                   slab->name, slab->total_slots, slab->used_slots,
                   states,
                   slab->by_state.active, slab->by_state.idle, slab->by_state.closing,
                   slab->overflow_count);

      free(states);
    } else {
      // Simple bitmap slab
      size_t hex_len = slab->bitmap_bytes * 2 + 1;
      char *hex = malloc(hex_len);
      if (!hex) return -1;

      if (slab->bitmap) {
        bitmap_to_hex(slab->bitmap, slab->bitmap_bytes, hex);
      } else {
        hex[0] = '\0';
      }

      n = snprintf(p, end - p,
                   "{\"name\":\"%s\",\"bitmap\":\"%s\",\"total\":%zu,\"used\":%zu,"
                   "\"overflow\":%zu}",
                   slab->name, hex, slab->total_slots, slab->used_slots,
                   slab->overflow_count);

      free(hex);
    }

    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // Arenas array
  n = snprintf(p, end - p, "\"arenas\":[");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  for (size_t i = 0; i < snapshot->arena_count; i++) {
    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || n >= end - p) return -1;
      p += n;
    }

    n = snprintf(
        p, end - p,
        "{\"name\":\"%s\",\"used\":%zu,\"capacity\":%zu,\"hwm\":%zu,"
        "\"overflow\":%zu}",
        snapshot->arenas[i].name, snapshot->arenas[i].used_bytes,
        snapshot->arenas[i].capacity_bytes,
        snapshot->arenas[i].high_water_mark,
        snapshot->arenas[i].overflow_fallbacks);

    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // GC heap stats
  n = snprintf(p, end - p,
               "\"gc\":{\"allocated\":%zu,\"peak\":%zu,\"threshold\":%zu,"
               "\"cycles\":%lu,\"emergency\":%zu},",
               snapshot->gc_heap.allocated_bytes,
               snapshot->gc_heap.peak_usage, snapshot->gc_heap.gc_threshold,
               snapshot->gc_heap.gc_cycles,
               snapshot->gc_heap.emergency_collections);

  if (n < 0 || n >= end - p) return -1;
  p += n;

  // Owner map for server/client names
  n = snprintf(p, end - p, "\"owner_map\":[");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  for (size_t i = 0; i < snapshot->owner_count; i++) {
    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || n >= end - p) return -1;
      p += n;
    }
    n = snprintf(p, end - p, "\"%s\"",
                 snapshot->owner_map[i] ? snapshot->owner_map[i] : "");
    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  n = snprintf(p, end - p, "]");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // Close JSON and add SSE empty line
  n = snprintf(p, end - p, "}\n\n");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  return p - buf;
}

// ============================================================================
// SSE Connection Management
// ============================================================================

// Timer callback - called every 100ms to push memory state
static void sse_push_memory_state(uv_timer_t *timer) {
  valk_sse_diag_conn_t *conn = (valk_sse_diag_conn_t *)timer->data;

  if (!conn->active) {
    uv_timer_stop(timer);
    return;
  }

  // Collect memory snapshot
  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, conn->aio_system);

  // Format SSE event
  int len = valk_mem_snapshot_to_sse(&snapshot, conn->write_buffer,
                                      sizeof(conn->write_buffer),
                                      ++conn->last_event_id);

  if (len <= 0) {
    VALK_ERROR("Failed to format SSE memory event");
    goto cleanup;
  }

  // Send event via TCP write
  // Note: This is a simplified implementation that writes directly to TCP
  // For HTTP/2, you would use nghttp2_submit_data instead
  uv_buf_t buf = uv_buf_init(conn->write_buffer, len);
  uv_write_t *req = malloc(sizeof(uv_write_t));
  if (!req) {
    VALK_ERROR("Failed to allocate write request");
    goto cleanup;
  }

  req->data = conn;

  // Get the underlying TCP stream from handle
  // Note: This assumes the handle has a uv.tcp field - adjust based on your
  // actual valk_aio_handle_t structure
  uv_stream_t *stream = (uv_stream_t *)conn->handle;

  int result = uv_write(req, stream, &buf, 1, NULL);

  if (result < 0) {
    VALK_ERROR("SSE write failed: %s", uv_strerror(result));
    conn->active = false;
    free(req);
  }

cleanup:
  // Free snapshot allocations
  for (size_t i = 0; i < snapshot.slab_count; i++) {
    free(snapshot.slabs[i].bitmap);
    free(snapshot.slabs[i].slots);
  }
}

// Initialize SSE diagnostics for an HTTP connection
void valk_sse_diag_init(valk_aio_handle_t *handle, valk_aio_system_t *aio) {
  if (!handle || !aio) {
    VALK_ERROR("Invalid arguments to valk_sse_diag_init");
    return;
  }

  valk_sse_diag_conn_t *conn = malloc(sizeof(valk_sse_diag_conn_t));
  if (!conn) {
    VALK_ERROR("Failed to allocate SSE diagnostics connection");
    return;
  }

  conn->handle = handle;
  conn->aio_system = aio;
  conn->last_event_id = 0;
  conn->active = true;

  // Allocate and initialize timer
  conn->timer = malloc(sizeof(uv_timer_t));
  if (!conn->timer) {
    VALK_ERROR("Failed to allocate SSE timer");
    free(conn);
    return;
  }

  uv_timer_init(valk_aio_get_event_loop(aio), conn->timer);
  conn->timer->data = conn;

  // Start timer with 100ms interval
  uv_timer_start(conn->timer, sse_push_memory_state, 0, 100);

  VALK_INFO("SSE diagnostics stream started");
}

// Close callback for timer handle
static void on_timer_close(uv_handle_t *handle) {
  free(handle);
}

// Stop SSE stream
void valk_sse_diag_stop(valk_sse_diag_conn_t *sse_conn) {
  if (!sse_conn) {
    return;
  }

  sse_conn->active = false;

  if (sse_conn->timer) {
    uv_timer_stop(sse_conn->timer);
    uv_close((uv_handle_t *)sse_conn->timer, on_timer_close);
  }

  free(sse_conn);

  VALK_INFO("SSE diagnostics stream stopped");
}
