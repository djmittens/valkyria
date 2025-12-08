#include "aio_sse_diagnostics.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <uv.h>
#include <nghttp2/nghttp2.h>

#include "aio.h"
#include "aio_metrics.h"
#include "common.h"
#include "gc.h"
#include "log.h"
#include "memory.h"
#include "metrics.h"

// ============================================================================
// Slab Bitmap Generation
// ============================================================================

// Walk Treiber stack to generate actual bitmap
// Returns heap-allocated bitmap, caller must free
// Note: This is a best-effort snapshot - the slab may be modified concurrently
// during browser refresh or connection churn. Races are expected and handled.
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

  // Use a visited bitmap to detect actual cycles (not just count overflow)
  uint8_t *visited = calloc(bitmap_bytes, 1);
  if (!visited) {
    free(bitmap);
    *out_bytes = 0;
    *out_used = 0;
    return NULL;
  }

  // Sentinel value is stored as UINT32_MAX in the lower 32 bits
  while (head_offset != (size_t)UINT32_MAX) {
    if (head_offset >= total_slots) {
      VALK_WARN("Slab free list: invalid offset %zu >= total %zu", head_offset, total_slots);
      break;
    }

    // Check if we've already visited this slot (true cycle detection)
    size_t byte_idx = head_offset / 8;
    uint8_t bit_mask = 1 << (head_offset % 8);
    VALK_ASSERT((visited[byte_idx] & bit_mask) == 0, "Slab free list cycle detected at offset %zu", head_offset);
    visited[byte_idx] |= bit_mask;

    // Clear bit in output bitmap (mark as free)
    bitmap[head_offset / 8] &= ~(1 << (head_offset % 8));
    free_count++;

    // Get item at this offset
    size_t stride = valk_slab_item_stride(slab->itemSize);
    valk_slab_item_t *item =
        (valk_slab_item_t *)&slab->heap[stride * head_offset];

    // Get next in free list (also versioned)
    uint64_t next_tag = __atomic_load_n(&item->next, __ATOMIC_ACQUIRE);
    size_t prev_offset = head_offset;
    head_offset = next_tag & (size_t)UINT32_MAX;

    // Safety: hard limit to prevent infinite loops
    if (free_count > total_slots) {
      VALK_WARN("Slab free list: exceeded total slots (free=%zu, total=%zu, last=%zu->%zu)",
                free_count, total_slots, prev_offset, head_offset);
      free_count = total_slots;
      break;
    }
  }

  free(visited);

  *out_bytes = bitmap_bytes;
  *out_used = free_count <= total_slots ? total_slots - free_count : 0;
  return bitmap;
}

// Convert bitmap bytes to RLE hex string
// Format: "XX*N" where XX is hex byte, N is count (omitted if 1)
// Example: "ff*32" = 32 bytes of 0xff, "00*16,ff*8" = 16 zeros then 8 ones
// Returns length written (not including null terminator)
static size_t bitmap_to_rle_hex(const uint8_t *bitmap, size_t bytes, char *out, size_t out_size) {
  static const char hex_chars[] = "0123456789abcdef";

  if (bytes == 0 || out_size < 3) {
    out[0] = '\0';
    return 0;
  }

  char *p = out;
  char *end = out + out_size - 1;
  size_t i = 0;

  while (i < bytes) {
    uint8_t byte = bitmap[i];
    size_t run_len = 1;

    // Count consecutive identical bytes
    while (i + run_len < bytes && bitmap[i + run_len] == byte) {
      run_len++;
    }

    // Check if we have enough space: comma(1) + hex(2) + asterisk(1) + digits(up to 7)
    size_t needed = (p != out ? 1 : 0) + 2 + (run_len > 1 ? 8 : 0);
    if (p + needed >= end) break;

    // Add separator if not first
    if (p != out) {
      *p++ = ',';
    }

    // Write hex pair
    *p++ = hex_chars[(byte >> 4) & 0x0F];
    *p++ = hex_chars[byte & 0x0F];

    // Write run length if > 1
    if (run_len > 1) {
      int n = snprintf(p, end - p, "*%zu", run_len);
      if (n < 0 || p + n >= end) break;
      p += n;
    }

    i += run_len;
  }

  *p = '\0';
  return p - out;
}

#ifdef VALK_METRICS_ENABLED
// ============================================================================
// Per-Slot Diagnostics for Connection-Aware Slabs
// ============================================================================

// Convert valk_diag_conn_state_e to single character for wire format
static char state_to_char(valk_diag_conn_state_e state) {
  switch (state) {
    case VALK_DIAG_CONN_FREE:       return 'F';
    case VALK_DIAG_CONN_CONNECTING: return 'N';  // coNnecting
    case VALK_DIAG_CONN_ACTIVE:     return 'A';
    case VALK_DIAG_CONN_IDLE:       return 'I';
    case VALK_DIAG_CONN_CLOSING:    return 'C';
    default:                        return 'F';
  }
}

// Walk handle slab and extract per-slot diagnostics with state and owner
static void slab_to_slot_diag(valk_slab_t *slab, valk_slab_snapshot_t *out,
                               valk_aio_system_t *aio, uint64_t now_ms) {
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

  // Sentinel value is stored as UINT32_MAX in the lower 32 bits
  while (head_offset != (size_t)UINT32_MAX && head_offset < total && free_count < total) {
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

    // Use accessor to get handle diagnostics
    valk_handle_diag_t diag = {0};
    if (valk_aio_get_handle_diag(aio, i, &diag)) {
      char state_char = state_to_char(diag.state);
      out->slots[i].state = state_char;
      out->slots[i].owner = diag.owner_idx;

      // Calculate age since last state change
      if (diag.state_change_time > 0 && now_ms > diag.state_change_time) {
        out->slots[i].age_ms = (uint32_t)(now_ms - diag.state_change_time);
      }

      // Update state counters
      switch (diag.state) {
        case VALK_DIAG_CONN_ACTIVE:
        case VALK_DIAG_CONN_CONNECTING:
          out->by_state.active++;
          break;
        case VALK_DIAG_CONN_IDLE:
          out->by_state.idle++;
          break;
        case VALK_DIAG_CONN_CLOSING:
          out->by_state.closing++;
          break;
        default:
          break;
      }

      // Track HTTP connection in type breakdown
      out->by_type.http_conns++;

      // Update per-owner counts with state breakdown
      if (diag.owner_idx != 0xFFFF && diag.owner_idx < 16) {
        // Find or add owner entry
        size_t owner_slot = out->owner_count;
        for (size_t j = 0; j < out->owner_count; j++) {
          if (out->by_owner[j].owner_idx == diag.owner_idx) {
            owner_slot = j;
            break;
          }
        }
        // Add new owner if not found
        if (owner_slot == out->owner_count && out->owner_count < 16) {
          out->by_owner[owner_slot].owner_idx = diag.owner_idx;
          out->by_owner[owner_slot].active = 0;
          out->by_owner[owner_slot].idle = 0;
          out->by_owner[owner_slot].closing = 0;
          out->owner_count++;
        }
        // Increment the appropriate state counter for this owner
        if (owner_slot < 16) {
          switch (diag.state) {
            case VALK_DIAG_CONN_ACTIVE:
            case VALK_DIAG_CONN_CONNECTING:
              out->by_owner[owner_slot].active++;
              break;
            case VALK_DIAG_CONN_IDLE:
              out->by_owner[owner_slot].idle++;
              break;
            case VALK_DIAG_CONN_CLOSING:
              out->by_owner[owner_slot].closing++;
              break;
            default:
              break;
          }
        }
      }
    } else {
      // Not an HTTP connection handle - get the handle kind and track it
      valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(aio, i);
      switch (kind) {
        case VALK_DIAG_HNDL_TCP:
          out->slots[i].state = 'T';  // TCP listener
          out->by_type.tcp_listeners++;
          break;
        case VALK_DIAG_HNDL_TASK:
          out->slots[i].state = 'K';  // tasK
          out->by_type.tasks++;
          break;
        case VALK_DIAG_HNDL_TIMER:
          out->slots[i].state = 'M';  // tiMer
          out->by_type.timers++;
          break;
        default:
          out->slots[i].state = 'A';  // Unknown, treat as active
          break;
      }
    }
    used_count++;
  }

  out->used_slots = used_count;
  out->overflow_count = __atomic_load_n(&slab->overflowCount, __ATOMIC_ACQUIRE);

  free(is_free);
}

// Encode slot states as RLE string: "F16A3I2" means 16 Free, 3 Active, 2 Idle
// Returns the length written (not including null terminator)
static size_t slots_to_rle_string(valk_slot_diag_t *slots, size_t count, char *out, size_t out_size) {
  if (count == 0 || out_size < 3) {
    out[0] = '\0';
    return 0;
  }

  char *p = out;
  char *end = out + out_size - 1;  // Reserve space for null terminator
  size_t i = 0;

  while (i < count && p < end - 10) {  // Reserve space for worst case "X999999"
    char state = slots[i].state;
    size_t run_len = 1;

    // Count consecutive slots with same state
    while (i + run_len < count && slots[i + run_len].state == state) {
      run_len++;
    }

    // Write state char + count
    int n = snprintf(p, end - p, "%c%zu", state, run_len);
    if (n < 0 || p + n >= end) break;
    p += n;
    i += run_len;
  }

  *p = '\0';
  return p - out;
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
      slab_to_slot_diag(handle_slab, &snapshot->slabs[slab_idx], aio, now_ms);
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
      // Connection-aware slab with RLE-encoded state string
      // Worst case: every slot different = 2 chars per slot, but typically much smaller
      size_t rle_buf_size = slab->total_slots * 8 + 1;  // Generous buffer
      char *states = malloc(rle_buf_size);
      if (!states) return -1;
      slots_to_rle_string(slab->slots, slab->total_slots, states, rle_buf_size);

      // Build by_owner JSON object with per-owner state breakdown:
      // {"0": {"A": x, "I": y, "C": z}, "1": {...}, ...}
      char by_owner_buf[512] = {0};
      char *bp = by_owner_buf;
      char *bp_end = by_owner_buf + sizeof(by_owner_buf);
      int bn = snprintf(bp, bp_end - bp, "{");
      if (bn > 0) bp += bn;
      for (size_t j = 0; j < slab->owner_count && bp < bp_end - 64; j++) {
        if (j > 0) {
          bn = snprintf(bp, bp_end - bp, ",");
          if (bn > 0) bp += bn;
        }
        bn = snprintf(bp, bp_end - bp, "\"%u\":{\"A\":%zu,\"I\":%zu,\"C\":%zu}",
                      slab->by_owner[j].owner_idx,
                      slab->by_owner[j].active,
                      slab->by_owner[j].idle,
                      slab->by_owner[j].closing);
        if (bn > 0) bp += bn;
      }
      snprintf(bp, bp_end - bp, "}");

      n = snprintf(p, end - p,
                   "{\"name\":\"%s\",\"total\":%zu,\"used\":%zu,"
                   "\"states\":\"%s\","
                   "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu,\"by_owner\":%s},"
                   "\"by_type\":{\"tcp\":%zu,\"task\":%zu,\"timer\":%zu,\"http\":%zu},"
                   "\"overflow\":%zu}",
                   slab->name, slab->total_slots, slab->used_slots,
                   states,
                   slab->by_state.active, slab->by_state.idle, slab->by_state.closing,
                   by_owner_buf,
                   slab->by_type.tcp_listeners, slab->by_type.tasks,
                   slab->by_type.timers, slab->by_type.http_conns,
                   slab->overflow_count);

      free(states);
    } else {
      // Simple bitmap slab with RLE encoding
      // Worst case: alternating bytes = "XX,YY,XX,YY,..." = 3 chars per byte
      // Typical case: long runs = "XX*N" = much smaller
      size_t rle_buf_size = slab->bitmap_bytes * 4 + 1;
      char *hex = malloc(rle_buf_size);
      if (!hex) return -1;

      if (slab->bitmap) {
        bitmap_to_rle_hex(slab->bitmap, slab->bitmap_bytes, hex, rle_buf_size);
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
// Combined Diagnostics SSE Event (Memory + Metrics)
// ============================================================================

// Format combined diagnostics event with memory snapshot AND metrics
// This eliminates the need for separate polling from the dashboard
int valk_diag_snapshot_to_sse(valk_mem_snapshot_t *snapshot,
                               valk_aio_system_t *aio,
                               char *buf, size_t buf_size, uint64_t event_id) {
  char *p = buf;
  char *end = buf + buf_size;

  // SSE event header - use "diagnostics" event type for combined data
  int n = snprintf(p, end - p, "event: diagnostics\nid: %lu\ndata: {", event_id);
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // ===== Memory section (same as valk_mem_snapshot_to_sse) =====
  n = snprintf(p, end - p, "\"memory\":{");
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
      // RLE-encoded state string
      size_t rle_buf_size = slab->total_slots * 8 + 1;
      char *states = malloc(rle_buf_size);
      if (!states) return -1;
      slots_to_rle_string(slab->slots, slab->total_slots, states, rle_buf_size);

      char by_owner_buf[512] = {0};
      char *bp = by_owner_buf;
      char *bp_end = by_owner_buf + sizeof(by_owner_buf);
      int bn = snprintf(bp, bp_end - bp, "{");
      if (bn > 0) bp += bn;
      for (size_t j = 0; j < slab->owner_count && bp < bp_end - 64; j++) {
        if (j > 0) {
          bn = snprintf(bp, bp_end - bp, ",");
          if (bn > 0) bp += bn;
        }
        bn = snprintf(bp, bp_end - bp, "\"%u\":{\"A\":%zu,\"I\":%zu,\"C\":%zu}",
                      slab->by_owner[j].owner_idx,
                      slab->by_owner[j].active,
                      slab->by_owner[j].idle,
                      slab->by_owner[j].closing);
        if (bn > 0) bp += bn;
      }
      snprintf(bp, bp_end - bp, "}");

      n = snprintf(p, end - p,
                   "{\"name\":\"%s\",\"total\":%zu,\"used\":%zu,"
                   "\"states\":\"%s\","
                   "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu,\"by_owner\":%s},"
                   "\"by_type\":{\"tcp\":%zu,\"task\":%zu,\"timer\":%zu,\"http\":%zu},"
                   "\"overflow\":%zu}",
                   slab->name, slab->total_slots, slab->used_slots,
                   states,
                   slab->by_state.active, slab->by_state.idle, slab->by_state.closing,
                   by_owner_buf,
                   slab->by_type.tcp_listeners, slab->by_type.tasks,
                   slab->by_type.timers, slab->by_type.http_conns,
                   slab->overflow_count);

      free(states);
    } else {
      // Simple bitmap slab with RLE encoding
      size_t rle_buf_size = slab->bitmap_bytes * 4 + 1;
      char *hex = malloc(rle_buf_size);
      if (!hex) return -1;

      if (slab->bitmap) {
        bitmap_to_rle_hex(slab->bitmap, slab->bitmap_bytes, hex, rle_buf_size);
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

  // Owner map
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

  n = snprintf(p, end - p, "]},");  // Close memory section
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // ===== Metrics section =====
#ifdef VALK_METRICS_ENABLED
  // Collect VM metrics
  valk_vm_metrics_t vm_metrics = {0};
  valk_gc_malloc_heap_t *gc_heap = valk_aio_get_gc_heap(aio);
  uv_loop_t *loop = valk_aio_get_event_loop(aio);
  valk_vm_metrics_collect(&vm_metrics, gc_heap, loop);

  // Get AIO metrics
  const valk_aio_metrics_t *aio_metrics = valk_aio_get_metrics(aio);

  // Format metrics section
  n = snprintf(p, end - p, "\"metrics\":{");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // VM metrics subsection
  n = snprintf(p, end - p,
               "\"vm\":{\"gc\":{\"cycles_total\":%lu,\"pause_us_total\":%lu,"
               "\"pause_us_max\":%lu,\"reclaimed_bytes\":%lu,"
               "\"heap_used_bytes\":%zu,\"heap_total_bytes\":%zu},"
               "\"interpreter\":{\"evals_total\":%lu,\"function_calls\":%lu,"
               "\"builtin_calls\":%lu,\"stack_depth_max\":%u,"
               "\"closures_created\":%lu,\"env_lookups\":%lu},"
               "\"event_loop\":{\"iterations\":%lu,\"events_processed\":%lu,"
               "\"idle_time_us\":%lu}},",
               vm_metrics.gc_cycles, vm_metrics.gc_pause_us_total,
               vm_metrics.gc_pause_us_max, vm_metrics.gc_reclaimed_bytes,
               vm_metrics.gc_heap_used, vm_metrics.gc_heap_total,
               vm_metrics.eval_total, vm_metrics.function_calls,
               vm_metrics.builtin_calls, vm_metrics.stack_depth_max,
               vm_metrics.closures_created, vm_metrics.env_lookups,
               vm_metrics.loop_count, vm_metrics.events_processed,
               vm_metrics.idle_time_us);

  if (n < 0 || n >= end - p) return -1;
  p += n;

  // AIO metrics subsection
  if (aio_metrics) {
    // Calculate uptime
    uint64_t now_us = (uint64_t)(uv_hrtime() / 1000);
    double uptime_seconds = (double)(now_us - aio_metrics->start_time_us) / 1000000.0;

    n = snprintf(p, end - p,
                 "\"aio\":{\"uptime_seconds\":%.2f,"
                 "\"connections\":{\"total\":%lu,\"active\":%lu,\"failed\":%lu,"
                 "\"idle\":%lu,\"closing\":%lu,\"connecting\":%lu},"
                 "\"streams\":{\"total\":%lu,\"active\":%lu},"
                 "\"requests\":{\"total\":%lu,\"active\":%lu,\"errors\":%lu},"
                 "\"bytes\":{\"sent\":%lu,\"recv\":%lu}},",
                 uptime_seconds,
                 atomic_load(&aio_metrics->connections_total),
                 atomic_load(&aio_metrics->connections_active),
                 atomic_load(&aio_metrics->connections_failed),
                 atomic_load(&aio_metrics->connections_idle),
                 atomic_load(&aio_metrics->connections_closing),
                 atomic_load(&aio_metrics->connections_connecting),
                 atomic_load(&aio_metrics->streams_total),
                 atomic_load(&aio_metrics->streams_active),
                 atomic_load(&aio_metrics->requests_total),
                 atomic_load(&aio_metrics->requests_active),
                 atomic_load(&aio_metrics->requests_errors),
                 atomic_load(&aio_metrics->bytes_sent_total),
                 atomic_load(&aio_metrics->bytes_recv_total));

    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  // Modular metrics (HTTP server counters, gauges, histograms)
  // Use a heap-allocated buffer since metrics can be large during stress tests
  size_t modular_buf_size = 131072;  // 128KB for modular metrics
  char *modular_buf = malloc(modular_buf_size);
  if (modular_buf) {
    size_t modular_len = valk_metrics_json(modular_buf, modular_buf_size);
    // valk_metrics_json returns cap on overflow, or actual length on success
    if (modular_len > 0 && modular_len < modular_buf_size) {
      n = snprintf(p, end - p, "\"modular\":%s", modular_buf);
      if (n < 0 || n >= end - p) {
        free(modular_buf);
        return -1;
      }
      p += n;
    } else {
      // Buffer overflow or empty - use empty object
      // Log warning on overflow so we know to increase buffer
      if (modular_len >= modular_buf_size) {
        VALK_WARN("Modular metrics exceeded %zu byte buffer", modular_buf_size);
      }
      n = snprintf(p, end - p, "\"modular\":{}");
      if (n < 0 || n >= end - p) {
        free(modular_buf);
        return -1;
      }
      p += n;
    }
    free(modular_buf);
  } else {
    // Allocation failed - use empty object
    n = snprintf(p, end - p, "\"modular\":{}");
    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  n = snprintf(p, end - p, "}");  // Close metrics section
  if (n < 0 || n >= end - p) return -1;
  p += n;
#else
  // Metrics disabled - empty section
  n = snprintf(p, end - p, "\"metrics\":{}");
  if (n < 0 || n >= end - p) return -1;
  p += n;
#endif

  // Close JSON and add SSE empty line
  n = snprintf(p, end - p, "}\n\n");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  return p - buf;
}

// ============================================================================
// SSE Connection Management (HTTP/2 Streaming)
// ============================================================================

// SSE buffer size - large enough for full snapshot + metrics
#define SSE_BUFFER_SIZE 262144

// Forward declare the data provider callback
static nghttp2_ssize sse_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

// Timer callback - called every 100ms to push diagnostics (memory + metrics) via HTTP/2
// This unified approach eliminates the need for separate polling from the dashboard
static void sse_push_diagnostics(uv_timer_t *timer) {
  valk_sse_diag_conn_t *conn = (valk_sse_diag_conn_t *)timer->data;

  if (!conn || !conn->active) {
    return;
  }

  // If we still have pending data, skip this tick
  if (conn->pending_data && conn->pending_offset < conn->pending_len) {
    return;
  }

  // Collect memory snapshot
  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, conn->aio_system);

  // Allocate or reuse pending buffer
  if (!conn->pending_data) {
    conn->pending_data = malloc(SSE_BUFFER_SIZE);
    if (!conn->pending_data) {
      VALK_ERROR("Failed to allocate SSE buffer");
      goto cleanup;
    }
  }

  // Format combined SSE event (memory + metrics)
  int len = valk_diag_snapshot_to_sse(&snapshot, conn->aio_system,
                                       conn->pending_data, SSE_BUFFER_SIZE,
                                       ++conn->last_event_id);

  if (len <= 0) {
    VALK_ERROR("Failed to format SSE diagnostics event");
    goto cleanup;
  }

  conn->pending_len = (size_t)len;
  conn->pending_offset = 0;

  // If data was deferred, resume the stream and flush
  if (conn->data_deferred && conn->session) {
    // Check if the stream is still valid before trying to resume
    // nghttp2_session_get_stream_user_data returns NULL if stream doesn't exist
    if (nghttp2_session_get_stream_user_data(conn->session, conn->stream_id) == NULL) {
      // Stream was closed, mark connection as inactive
      VALK_INFO("SSE stream %d closed, stopping diagnostics", conn->stream_id);
      conn->active = false;
      goto cleanup;
    }

    conn->data_deferred = false;
    int rv = nghttp2_session_resume_data(conn->session, conn->stream_id);
    if (rv != 0) {
      // Stream may have been closed between check and resume - not a fatal error
      if (rv == NGHTTP2_ERR_INVALID_ARGUMENT) {
        VALK_INFO("SSE stream %d no longer valid, stopping diagnostics", conn->stream_id);
        conn->active = false;
      } else {
        VALK_ERROR("Failed to resume HTTP/2 stream: %s", nghttp2_strerror(rv));
      }
    } else {
      // Trigger HTTP/2 send to actually transmit the data
      valk_http2_flush_pending(conn->handle);
    }
  }

cleanup:
  // Free snapshot allocations
  for (size_t i = 0; i < snapshot.slab_count; i++) {
    free(snapshot.slabs[i].bitmap);
    free(snapshot.slabs[i].slots);
  }
}

// nghttp2 data provider callback - reads pending SSE data
static nghttp2_ssize sse_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data) {
  (void)session;
  (void)stream_id;
  (void)user_data;

  valk_sse_diag_conn_t *conn = (valk_sse_diag_conn_t *)source->ptr;

  if (!conn || !conn->active) {
    // Stream is closed, signal EOF
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  // Check if we have data to send
  if (!conn->pending_data || conn->pending_offset >= conn->pending_len) {
    // No data available, defer until timer fires
    conn->data_deferred = true;
    return NGHTTP2_ERR_DEFERRED;
  }

  // Calculate how much to send
  size_t remaining = conn->pending_len - conn->pending_offset;
  size_t to_send = remaining < length ? remaining : length;

  memcpy(buf, conn->pending_data + conn->pending_offset, to_send);
  conn->pending_offset += to_send;

  // Don't set EOF - this is a streaming response
  // Don't set NO_COPY - we copied data into the provided buffer

  return (nghttp2_ssize)to_send;
}

// Initialize SSE diagnostics for an HTTP/2 connection (streaming)
void valk_sse_diag_init(valk_aio_handle_t *handle, valk_aio_system_t *aio) {
  (void)handle;
  (void)aio;
  // Legacy function - use valk_sse_diag_init_http2 for HTTP/2 streaming
  VALK_ERROR("valk_sse_diag_init is deprecated, use valk_sse_diag_init_http2");
}

// Initialize HTTP/2 SSE streaming - returns data provider and connection context
valk_sse_diag_conn_t* valk_sse_diag_init_http2(
    valk_aio_handle_t *handle,
    valk_aio_system_t *aio,
    nghttp2_session *session,
    int32_t stream_id,
    nghttp2_data_provider2 *data_prd_out) {

  if (!handle || !aio || !session || !data_prd_out) {
    VALK_ERROR("Invalid arguments to valk_sse_diag_init_http2");
    return NULL;
  }

  valk_sse_diag_conn_t *conn = malloc(sizeof(valk_sse_diag_conn_t));
  if (!conn) {
    VALK_ERROR("Failed to allocate SSE diagnostics connection");
    return NULL;
  }

  memset(conn, 0, sizeof(*conn));
  conn->handle = handle;
  conn->aio_system = aio;
  conn->session = session;
  conn->stream_id = stream_id;
  conn->last_event_id = 0;
  conn->active = true;
  conn->data_deferred = true;  // Start deferred until first timer tick
  conn->pending_data = NULL;
  conn->pending_len = 0;
  conn->pending_offset = 0;

  // Allocate timer handle from slab (tracked in diagnostics)
  conn->timer_handle = valk_aio_timer_alloc(aio);
  if (!conn->timer_handle) {
    VALK_ERROR("Failed to allocate SSE timer from handle slab");
    free(conn);
    return NULL;
  }

  valk_aio_timer_init(conn->timer_handle);
  valk_aio_timer_set_data(conn->timer_handle, conn);

  // Set up data provider for nghttp2
  data_prd_out->source.ptr = conn;
  data_prd_out->read_callback = sse_data_read_callback;

  // Start timer with 100ms interval (first tick after 100ms)
  valk_aio_timer_start(conn->timer_handle, 100, 100, sse_push_diagnostics);

  VALK_INFO("SSE diagnostics HTTP/2 stream started (stream_id=%d)", stream_id);
  return conn;
}

// Close callback for timer handle - releases back to slab
static void on_timer_close(uv_handle_t *handle) {
  valk_aio_handle_t *timer_handle = (valk_aio_handle_t *)handle->data;
  if (timer_handle) {
    VALK_DEBUG("SSE timer close callback, releasing handle %p", (void*)timer_handle);
    valk_aio_timer_free(timer_handle);
  } else {
    VALK_WARN("SSE timer close callback with NULL handle data");
  }
}

// Stop SSE stream
void valk_sse_diag_stop(valk_sse_diag_conn_t *sse_conn) {
  if (!sse_conn) {
    return;
  }

  VALK_DEBUG("SSE diag stop called, timer_handle=%p", (void*)sse_conn->timer_handle);
  sse_conn->active = false;

  if (sse_conn->timer_handle) {
    VALK_DEBUG("Stopping and closing SSE timer");
    valk_aio_timer_stop(sse_conn->timer_handle);
    valk_aio_timer_close(sse_conn->timer_handle, on_timer_close);
    sse_conn->timer_handle = NULL;  // Prevent double-close
  }

  // Free pending buffer
  if (sse_conn->pending_data) {
    free(sse_conn->pending_data);
    sse_conn->pending_data = NULL;
  }

  free(sse_conn);

  VALK_INFO("SSE diagnostics stream stopped");
}
