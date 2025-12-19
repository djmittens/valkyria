#include "aio_sse_diagnostics.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <uv.h>
#include <nghttp2/nghttp2.h>

#include "aio.h"
#include "aio_alloc.h"
#include "aio_metrics.h"
#include "aio_sse_stream_registry.h"
#include "common.h"
#include "gc.h"
#include "log.h"
#include "memory.h"
#include "metrics_v2.h"
#include "metrics_delta.h"

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

    // Check if we've already visited this slot (cycle detection)
    size_t byte_idx = head_offset / 8;
    uint8_t bit_mask = 1 << (head_offset % 8);
    if (visited[byte_idx] & bit_mask) {
      // Cycle in free list - indicates slab corruption, just stop the walk
      break;
    }
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
// GC Tier JSON Helpers
// ============================================================================

// Emit GC tiers array to JSON buffer
// Returns bytes written, or -1 on error
static int gc_tiers_to_json(const valk_mem_snapshot_t *snapshot, char *buf, size_t buf_size) {
  char *p = buf;
  char *end = buf + buf_size;
  int n;

  n = snprintf(p, end - p, "\"tiers\":[");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  for (size_t i = 0; i < snapshot->gc_heap.tier_count; i++) {
    const valk_heap_tier_snapshot_t *tier = &snapshot->gc_heap.tiers[i];

    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || n >= end - p) return -1;
      p += n;
    }

    // Emit tier - all fields present, consumer decides what to use based on name
    // Object fields are 0 for non-slab allocators (e.g., malloc)
    n = snprintf(p, end - p,
                 "{\"name\":\"%s\","
                 "\"bytes_used\":%zu,\"bytes_total\":%zu,\"bytes_peak\":%zu,"
                 "\"objects_used\":%zu,\"objects_total\":%zu,\"objects_peak\":%zu}",
                 tier->name,
                 tier->bytes_used, tier->bytes_total, tier->bytes_peak,
                 tier->objects_used, tier->objects_total, tier->objects_peak);
    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  n = snprintf(p, end - p, "]");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  return (int)(p - buf);
}

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
      snapshot->slabs[slab_idx].peak_used = \
          __atomic_load_n(&slab->peakUsed, __ATOMIC_ACQUIRE); \
      snapshot->slabs[slab_idx].overflow_count = \
          __atomic_load_n(&slab->overflowCount, __ATOMIC_ACQUIRE); \
      slab_idx++; \
    } \
  } while(0)

  // TCP Buffers (simple bitmap)
  {
    valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(aio);
    if (tcp_slab) {
      size_t numFree = __atomic_load_n(&tcp_slab->numFree, __ATOMIC_ACQUIRE);
      VALK_DEBUG("TCP buffer slab: numItems=%zu, numFree=%zu, expected_used=%zu",
                 tcp_slab->numItems, numFree, tcp_slab->numItems - numFree);
    }
  }
  ADD_SLAB(valk_aio_get_tcp_buffer_slab, "tcp_buffers");

  // Handle Slab - use per-slot diagnostics for connection state tracking
  {
    valk_slab_t *handle_slab = valk_aio_get_handle_slab(aio);
    if (handle_slab && slab_idx < 8) {
      snapshot->slabs[slab_idx].name = "handles";
      // Always set total_slots from the slab, even if slot_diag fails
      snapshot->slabs[slab_idx].total_slots = handle_slab->numItems;
      snapshot->slabs[slab_idx].peak_used =
          __atomic_load_n(&handle_slab->peakUsed, __ATOMIC_ACQUIRE);
      // Get current time for age calculation
      uint64_t now_ms = (uint64_t)(uv_hrtime() / 1000000ULL);
      slab_to_slot_diag(handle_slab, &snapshot->slabs[slab_idx], aio, now_ms);
      // Note: if slot_diag fails (OOM), has_slot_diag will be false and
      // the SSE formatter will use an empty bitmap. This is acceptable
      // for transient OOM conditions - next snapshot will likely succeed.
      slab_idx++;
    }
  }

  // Stream Arenas (simple bitmap)
  {
    valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(aio);
    if (arena_slab) {
      size_t numFree = __atomic_load_n(&arena_slab->numFree, __ATOMIC_ACQUIRE);
      VALK_DEBUG("Stream arena slab: numItems=%zu, numFree=%zu, expected_used=%zu",
                 arena_slab->numItems, numFree, arena_slab->numItems - numFree);
    }
  }
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
    snapshot->slabs[slab_idx].peak_used =
        __atomic_load_n(&gc_heap->lval_slab->peakUsed, __ATOMIC_ACQUIRE);
    snapshot->slabs[slab_idx].overflow_count =
        __atomic_load_n(&gc_heap->lval_slab->overflowCount, __ATOMIC_ACQUIRE);
    slab_idx++;
  }

  // LENV Slab (from GC heap)
  if (gc_heap && gc_heap->lenv_slab && slab_idx < 8) {
    snapshot->slabs[slab_idx].name = (const char *)"lenv";
    snapshot->slabs[slab_idx].bitmap =
        slab_to_bitmap(gc_heap->lenv_slab,
                       &snapshot->slabs[slab_idx].bitmap_bytes,
                       &snapshot->slabs[slab_idx].used_slots);
    snapshot->slabs[slab_idx].total_slots = gc_heap->lenv_slab->numItems;
    snapshot->slabs[slab_idx].peak_used =
        __atomic_load_n(&gc_heap->lenv_slab->peakUsed, __ATOMIC_ACQUIRE);
    snapshot->slabs[slab_idx].overflow_count =
        __atomic_load_n(&gc_heap->lenv_slab->overflowCount, __ATOMIC_ACQUIRE);
    slab_idx++;
  }

  #undef ADD_SLAB
#endif

  snapshot->slab_count = slab_idx;

  // Collect arena allocators
  size_t arena_idx = 0;

  // Scratch Arena (from AIO system, which stores main thread's scratch arena)
  valk_mem_arena_t *scratch = valk_aio_get_scratch_arena(aio);
  if (scratch && arena_idx < 16) {
    snapshot->arenas[arena_idx].name = (const char *)"scratch";
    snapshot->arenas[arena_idx].used_bytes =
        __atomic_load_n(&scratch->offset, __ATOMIC_ACQUIRE);
    snapshot->arenas[arena_idx].capacity_bytes = scratch->capacity;
    snapshot->arenas[arena_idx].high_water_mark =
        scratch->stats.high_water_mark;
    snapshot->arenas[arena_idx].overflow_fallbacks =
        scratch->stats.overflow_fallbacks;
    snapshot->arenas[arena_idx].overflow_bytes =
        scratch->stats.overflow_bytes;
    arena_idx++;
  }

  // Stream arenas are allocated from slab, individual usage not tracked here
  // We only track the slab allocation status above

  snapshot->arena_count = arena_idx;

  // Collect GC heap stats (generic tier array)
#ifdef VALK_METRICS_ENABLED
  // gc_heap was already fetched above for LVAL slab collection
  if (gc_heap) {
    size_t tier_idx = 0;

    // Helper macro to add a slab to the tiers snapshot
    #define ADD_SLAB_TIER(slab_ptr, tier_name) do { \
      if ((slab_ptr) && tier_idx < 8) { \
        valk_heap_tier_snapshot_t *tier = &snapshot->gc_heap.tiers[tier_idx]; \
        size_t slab_used = (slab_ptr)->numItems - (slab_ptr)->numFree; \
        size_t slab_total = (slab_ptr)->numItems; \
        size_t item_size = (slab_ptr)->itemSize; \
        tier->name = tier_name; \
        tier->bytes_used = slab_used * item_size; \
        tier->bytes_total = slab_total * item_size; \
        tier->bytes_peak = __atomic_load_n(&(slab_ptr)->peakUsed, __ATOMIC_RELAXED) * item_size; \
        tier->objects_used = slab_used; \
        tier->objects_total = slab_total; \
        tier->objects_peak = __atomic_load_n(&(slab_ptr)->peakUsed, __ATOMIC_RELAXED); \
        tier_idx++; \
      } \
    } while(0)

    // Add slab tiers (just slabs with different names)
    ADD_SLAB_TIER(gc_heap->lval_slab, "lval");
    ADD_SLAB_TIER(gc_heap->lenv_slab, "lenv");

    #undef ADD_SLAB_TIER

    // Add malloc (no object tracking, just bytes)
    if (tier_idx < 8) {
      valk_heap_tier_snapshot_t *tier = &snapshot->gc_heap.tiers[tier_idx];
      tier->name = "malloc";
      tier->bytes_used = gc_heap->allocated_bytes;
      tier->bytes_total = gc_heap->hard_limit;
      tier->bytes_peak = gc_heap->stats.peak_usage;
      tier->objects_used = 0;
      tier->objects_total = 0;
      tier->objects_peak = 0;
      tier_idx++;
    }

    snapshot->gc_heap.tier_count = tier_idx;

    // Common GC stats
    snapshot->gc_heap.gc_threshold_pct = gc_heap->gc_threshold_pct;
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

  // Collect process-level memory from OS
  valk_process_memory_collect(&snapshot->process);

  // Collect detailed smaps breakdown (Linux only)
  valk_smaps_collect(&snapshot->smaps);

  // Compute breakdown aggregates (used and capacity for each subsystem)
  memset(&snapshot->breakdown, 0, sizeof(snapshot->breakdown));

  // Sum scratch arena usage and capacity
  for (size_t i = 0; i < snapshot->arena_count; i++) {
    snapshot->breakdown.scratch_arena_used += snapshot->arenas[i].used_bytes;
    snapshot->breakdown.scratch_arena_capacity += snapshot->arenas[i].capacity_bytes;
  }

  // Sum GC heap tiers (used and capacity)
  for (size_t i = 0; i < snapshot->gc_heap.tier_count; i++) {
    const char *name = snapshot->gc_heap.tiers[i].name;
    size_t used = snapshot->gc_heap.tiers[i].bytes_used;
    size_t capacity = snapshot->gc_heap.tiers[i].bytes_total;

    snapshot->breakdown.gc_heap_used += used;
    snapshot->breakdown.gc_heap_capacity += capacity;

    if (name && strcmp(name, "lval") == 0) {
      snapshot->breakdown.gc_lval_slab_used = used;
      snapshot->breakdown.gc_lval_slab_capacity = capacity;
    } else if (name && strcmp(name, "lenv") == 0) {
      snapshot->breakdown.gc_lenv_slab_used = used;
      snapshot->breakdown.gc_lenv_slab_capacity = capacity;
    } else if (name && strcmp(name, "malloc") == 0) {
      snapshot->breakdown.gc_malloc_used = used;
      // malloc has no fixed capacity
    }
  }

  // Sum AIO slabs (tcp_buffers, handles, stream_arenas, http_servers, http_clients)
  for (size_t i = 0; i < snapshot->slab_count; i++) {
    const char *name = snapshot->slabs[i].name;
    // Skip lval and lenv slabs - they're already counted in gc_heap
    if (name && (strcmp(name, "lval") == 0 || strcmp(name, "lenv") == 0)) {
      continue;
    }
    // Estimate bytes from slot count (rough estimate using 256 bytes per slot)
    snapshot->breakdown.aio_slabs_used += snapshot->slabs[i].used_slots * 256;
    snapshot->breakdown.aio_slabs_capacity += snapshot->slabs[i].total_slots * 256;
  }

  // Add SSL (OpenSSL), nghttp2, and libuv tracked allocations to AIO total
  // These libraries use malloc-based tracking allocators
  snapshot->breakdown.aio_slabs_used += valk_aio_lib_bytes_used();

  // Metrics registry (statically allocated in BSS)
  valk_registry_stats_t metrics_stats = {0};
  valk_registry_stats_collect(&metrics_stats);

  // Calculate used bytes based on active slots and approximate slot sizes
  snapshot->breakdown.metrics_used =
      metrics_stats.counters_active * sizeof(valk_counter_v2_t) +
      metrics_stats.gauges_active * sizeof(valk_gauge_v2_t) +
      metrics_stats.histograms_active * sizeof(valk_histogram_v2_t) +
      metrics_stats.summaries_active * sizeof(valk_summary_v2_t) +
      metrics_stats.string_pool_used * sizeof(char*);

  // Capacity is the full registry struct size
  snapshot->breakdown.metrics_capacity = sizeof(valk_metrics_registry_t);

  // Untracked = RSS - all tracked allocators (based on actual usage, not capacity)
  size_t tracked_used = snapshot->breakdown.scratch_arena_used
                      + snapshot->breakdown.gc_heap_used
                      + snapshot->breakdown.aio_slabs_used
                      + snapshot->breakdown.metrics_used;
  snapshot->breakdown.untracked_bytes = (snapshot->process.rss_bytes > tracked_used)
                                       ? (snapshot->process.rss_bytes - tracked_used)
                                       : 0;

  // Untracked reserved = VMS - all tracked capacities (mapped but not instrumented)
  size_t tracked_cap = snapshot->breakdown.scratch_arena_capacity
                     + snapshot->breakdown.gc_heap_capacity
                     + snapshot->breakdown.aio_slabs_capacity
                     + snapshot->breakdown.metrics_capacity;
  snapshot->breakdown.untracked_reserved = (snapshot->process.vms_bytes > tracked_cap)
                                          ? (snapshot->process.vms_bytes - tracked_cap)
                                          : 0;
}

// ============================================================================
// Snapshot Memory Management
// ============================================================================

void valk_mem_snapshot_free(valk_mem_snapshot_t *snapshot) {
  if (!snapshot) return;

  for (size_t i = 0; i < snapshot->slab_count; i++) {
    free(snapshot->slabs[i].bitmap);
    snapshot->slabs[i].bitmap = NULL;
    free(snapshot->slabs[i].slots);
    snapshot->slabs[i].slots = NULL;
  }
  snapshot->slab_count = 0;
  snapshot->arena_count = 0;
  snapshot->owner_count = 0;
}

void valk_mem_snapshot_copy(valk_mem_snapshot_t *dst, const valk_mem_snapshot_t *src) {
  if (!dst || !src) return;

  // Free any existing allocations in dst
  valk_mem_snapshot_free(dst);

  // Copy scalar fields
  dst->slab_count = src->slab_count;
  dst->arena_count = src->arena_count;
  dst->owner_count = src->owner_count;
  dst->gc_heap = src->gc_heap;

  // Copy arenas (no heap allocations)
  memcpy(dst->arenas, src->arenas, sizeof(dst->arenas));

  // Copy owner map (pointers to static strings, no deep copy needed)
  memcpy(dst->owner_map, src->owner_map, sizeof(dst->owner_map));

  // Deep copy slabs
  for (size_t i = 0; i < src->slab_count; i++) {
    dst->slabs[i].name = src->slabs[i].name;
    dst->slabs[i].total_slots = src->slabs[i].total_slots;
    dst->slabs[i].used_slots = src->slabs[i].used_slots;
    dst->slabs[i].peak_used = src->slabs[i].peak_used;
    dst->slabs[i].overflow_count = src->slabs[i].overflow_count;
    dst->slabs[i].has_slot_diag = src->slabs[i].has_slot_diag;
    dst->slabs[i].by_state = src->slabs[i].by_state;
    dst->slabs[i].by_type = src->slabs[i].by_type;
    dst->slabs[i].owner_count = src->slabs[i].owner_count;
    memcpy(dst->slabs[i].by_owner, src->slabs[i].by_owner, sizeof(dst->slabs[i].by_owner));

    // Deep copy bitmap
    if (src->slabs[i].bitmap && src->slabs[i].bitmap_bytes > 0) {
      dst->slabs[i].bitmap_bytes = src->slabs[i].bitmap_bytes;
      dst->slabs[i].bitmap = malloc(src->slabs[i].bitmap_bytes);
      if (dst->slabs[i].bitmap) {
        memcpy(dst->slabs[i].bitmap, src->slabs[i].bitmap, src->slabs[i].bitmap_bytes);
      }
    } else {
      dst->slabs[i].bitmap = NULL;
      dst->slabs[i].bitmap_bytes = 0;
    }

    // Deep copy slots
    if (src->slabs[i].slots && src->slabs[i].total_slots > 0) {
      dst->slabs[i].slots = malloc(src->slabs[i].total_slots * sizeof(valk_slot_diag_t));
      if (dst->slabs[i].slots) {
        memcpy(dst->slabs[i].slots, src->slabs[i].slots,
               src->slabs[i].total_slots * sizeof(valk_slot_diag_t));
      }
    } else {
      dst->slabs[i].slots = NULL;
    }
  }
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
                   "{\"name\":\"%s\",\"total\":%zu,\"used\":%zu,\"hwm\":%zu,"
                   "\"states\":\"%s\","
                   "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu,\"by_owner\":%s},"
                   "\"by_type\":{\"tcp\":%zu,\"task\":%zu,\"timer\":%zu,\"http\":%zu},"
                   "\"overflow\":%zu}",
                   slab->name, slab->total_slots, slab->used_slots, slab->peak_used,
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
                   "\"hwm\":%zu,\"overflow\":%zu}",
                   slab->name, hex, slab->total_slots, slab->used_slots,
                   slab->peak_used, slab->overflow_count);

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
        "\"overflow\":%zu,\"overflow_bytes\":%zu}",
        snapshot->arenas[i].name, snapshot->arenas[i].used_bytes,
        snapshot->arenas[i].capacity_bytes,
        snapshot->arenas[i].high_water_mark,
        snapshot->arenas[i].overflow_fallbacks,
        snapshot->arenas[i].overflow_bytes);

    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // GC heap stats (generic tiers array)
  n = snprintf(p, end - p, "\"gc\":{");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  n = gc_tiers_to_json(snapshot, p, end - p);
  if (n < 0) return -1;
  p += n;

  n = snprintf(p, end - p,
               ",\"threshold_pct\":%u,\"cycles\":%lu,\"emergency\":%zu},",
               (unsigned)snapshot->gc_heap.gc_threshold_pct,
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
                   "{\"name\":\"%s\",\"total\":%zu,\"used\":%zu,\"hwm\":%zu,"
                   "\"states\":\"%s\","
                   "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu,\"by_owner\":%s},"
                   "\"by_type\":{\"tcp\":%zu,\"task\":%zu,\"timer\":%zu,\"http\":%zu},"
                   "\"overflow\":%zu}",
                   slab->name, slab->total_slots, slab->used_slots, slab->peak_used,
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
                   "\"hwm\":%zu,\"overflow\":%zu}",
                   slab->name, hex, slab->total_slots, slab->used_slots,
                   slab->peak_used, slab->overflow_count);

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
        "\"overflow\":%zu,\"overflow_bytes\":%zu}",
        snapshot->arenas[i].name, snapshot->arenas[i].used_bytes,
        snapshot->arenas[i].capacity_bytes,
        snapshot->arenas[i].high_water_mark,
        snapshot->arenas[i].overflow_fallbacks,
        snapshot->arenas[i].overflow_bytes);

    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // GC heap stats (generic tiers array)
  n = snprintf(p, end - p, "\"gc\":{");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  n = gc_tiers_to_json(snapshot, p, end - p);
  if (n < 0) return -1;
  p += n;

  n = snprintf(p, end - p,
               ",\"threshold_pct\":%u,\"cycles\":%lu,\"emergency\":%zu},",
               (unsigned)snapshot->gc_heap.gc_threshold_pct,
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

  n = snprintf(p, end - p, "],");  // Close owner_map array
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // Process-level memory stats
  n = snprintf(p, end - p,
               "\"process\":{\"rss\":%zu,\"vms\":%zu,\"system_total\":%zu,"
               "\"shared\":%zu,\"data\":%zu,\"page_faults_minor\":%lu,"
               "\"page_faults_major\":%lu},",
               snapshot->process.rss_bytes, snapshot->process.vms_bytes,
               snapshot->process.system_total_bytes,
               snapshot->process.shared_bytes, snapshot->process.data_bytes,
               (unsigned long)snapshot->process.page_faults_minor,
               (unsigned long)snapshot->process.page_faults_major);
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // Smaps breakdown (detailed RSS by region type - Linux only)
  n = snprintf(p, end - p,
               "\"smaps\":{"
               "\"heap\":%zu,\"stack\":%zu,\"anon\":%zu,"
               "\"file\":%zu,\"shmem\":%zu,\"uring\":%zu,"
               "\"other\":%zu,\"total\":%zu,"
               "\"anon_regions\":%u,\"file_regions\":%u},",
               snapshot->smaps.heap_rss,
               snapshot->smaps.stack_rss,
               snapshot->smaps.anon_rss,
               snapshot->smaps.file_rss,
               snapshot->smaps.shmem_rss,
               snapshot->smaps.uring_rss,
               snapshot->smaps.other_rss,
               snapshot->smaps.total_rss,
               snapshot->smaps.anon_regions,
               snapshot->smaps.file_regions);
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // Breakdown by subsystem (used and capacity)
  n = snprintf(p, end - p,
               "\"breakdown\":{"
               "\"scratch_used\":%zu,\"scratch_cap\":%zu,"
               "\"gc_used\":%zu,\"gc_cap\":%zu,"
               "\"gc_lval_used\":%zu,\"gc_lval_cap\":%zu,"
               "\"gc_lenv_used\":%zu,\"gc_lenv_cap\":%zu,"
               "\"gc_malloc\":%zu,"
               "\"aio_used\":%zu,\"aio_cap\":%zu,"
               "\"ssl_used\":%zu,\"nghttp2_used\":%zu,\"libuv_used\":%zu,"
               "\"metrics_used\":%zu,\"metrics_cap\":%zu,"
               "\"untracked\":%zu,\"untracked_reserved\":%zu}},",
               snapshot->breakdown.scratch_arena_used,
               snapshot->breakdown.scratch_arena_capacity,
               snapshot->breakdown.gc_heap_used,
               snapshot->breakdown.gc_heap_capacity,
               snapshot->breakdown.gc_lval_slab_used,
               snapshot->breakdown.gc_lval_slab_capacity,
               snapshot->breakdown.gc_lenv_slab_used,
               snapshot->breakdown.gc_lenv_slab_capacity,
               snapshot->breakdown.gc_malloc_used,
               snapshot->breakdown.aio_slabs_used,
               snapshot->breakdown.aio_slabs_capacity,
               valk_aio_ssl_bytes_used(),
               valk_aio_nghttp2_bytes_used(),
               valk_aio_libuv_bytes_used(),
               snapshot->breakdown.metrics_used,
               snapshot->breakdown.metrics_capacity,
               snapshot->breakdown.untracked_bytes,
               snapshot->breakdown.untracked_reserved);
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

    // Get system stats for queue data
    valk_aio_system_stats_t *sys_stats = valk_aio_get_system_stats(aio);
    uint64_t pending_req = sys_stats ? atomic_load(&sys_stats->pending_requests) : 0;
    uint64_t pending_resp = sys_stats ? atomic_load(&sys_stats->pending_responses) : 0;
    uint64_t queue_cap = sys_stats ? sys_stats->queue_capacity : 0;

    // Pending stream backpressure stats
    uint64_t bp_current = sys_stats ? atomic_load(&sys_stats->pending_streams_current) : 0;
    uint64_t bp_total = sys_stats ? atomic_load(&sys_stats->pending_streams_total) : 0;
    uint64_t bp_processed = sys_stats ? atomic_load(&sys_stats->pending_streams_processed) : 0;
    uint64_t bp_dropped = sys_stats ? atomic_load(&sys_stats->pending_streams_dropped) : 0;
    uint64_t bp_wait_us = sys_stats ? atomic_load(&sys_stats->pending_streams_wait_us) : 0;
    uint64_t bp_pool_size = sys_stats ? sys_stats->pending_streams_pool_size : 0;
    // Calculate average wait time (avoid division by zero)
    double bp_avg_wait_ms = (bp_processed > 0) ? (double)bp_wait_us / (double)bp_processed / 1000.0 : 0.0;

    n = snprintf(p, end - p,
                 "\"aio\":{\"uptime_seconds\":%.2f,"
                 "\"connections\":{\"total\":%lu,\"active\":%lu,\"failed\":%lu,"
                 "\"idle\":%lu,\"closing\":%lu,\"connecting\":%lu},"
                 "\"streams\":{\"total\":%lu,\"active\":%lu},"
                 "\"requests\":{\"total\":%lu,\"active\":%lu,\"errors\":%lu},"
                 "\"bytes\":{\"sent\":%lu,\"recv\":%lu},"
                 "\"queue\":{\"pending_requests\":%lu,\"pending_responses\":%lu,\"capacity\":%lu},"
                 "\"pending_streams\":{\"current\":%lu,\"total\":%lu,"
                 "\"processed\":%lu,\"dropped\":%lu,\"avg_wait_ms\":%.2f,\"pool_size\":%lu}},",
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
                 atomic_load(&aio_metrics->bytes_recv_total),
                 pending_req, pending_resp, queue_cap,
                 bp_current, bp_total, bp_processed, bp_dropped, bp_avg_wait_ms, bp_pool_size);

    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  // SSE registry stats (long-lived diagnostic streams - separate from HTTP requests)
  valk_sse_stream_registry_t *sse_registry = valk_aio_get_sse_registry(aio);
  if (sse_registry) {
    n = snprintf(p, end - p,
                 "\"sse\":{\"streams_active\":%zu,"
                 "\"events_pushed_total\":%lu,\"bytes_pushed_total\":%lu},",
                 sse_registry->stream_count,
                 sse_registry->events_pushed_total,
                 sse_registry->bytes_pushed_total);
    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  // Modular metrics (HTTP server counters, gauges, histograms)
  // Use a heap-allocated buffer since metrics can be large during stress tests
  size_t modular_buf_size = 131072;  // 128KB for modular metrics
  char *modular_buf = malloc(modular_buf_size);
  if (modular_buf) {
    size_t modular_len = valk_metrics_v2_to_json(&g_metrics, modular_buf, modular_buf_size);
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

  // Registry stats (meta-metrics about the metrics system itself)
  {
    valk_registry_stats_t reg_stats;
    valk_registry_stats_collect(&reg_stats);
    char reg_buf[1024];
    size_t reg_len = valk_registry_stats_to_json(&reg_stats, reg_buf, sizeof(reg_buf));
    if (reg_len > 0) {
      n = snprintf(p, end - p, ",\"registry\":%s", reg_buf);
      if (n < 0 || n >= end - p) return -1;
      p += n;
    }
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
// Delta SSE Event Formatting
// ============================================================================

// Compare two bitmaps and return true if they differ
static bool bitmap_differs(const uint8_t *a, const uint8_t *b, size_t bytes) {
  if (!a && !b) return false;
  if (!a || !b) return true;
  return memcmp(a, b, bytes) != 0;
}

// Compare slot states and return true if they differ
static bool slots_differ(const valk_slot_diag_t *a, const valk_slot_diag_t *b, size_t count) {
  if (!a && !b) return false;
  if (!a || !b) return true;
  for (size_t i = 0; i < count; i++) {
    if (a[i].state != b[i].state) return true;
  }
  return false;
}

// Check if a slab changed between snapshots
static bool slab_changed(const valk_slab_snapshot_t *curr, const valk_slab_snapshot_t *prev) {
  if (curr->used_slots != prev->used_slots) return true;
  if (curr->overflow_count != prev->overflow_count) return true;
  if (curr->peak_used != prev->peak_used) return true;

  if (curr->has_slot_diag && prev->has_slot_diag) {
    if (slots_differ(curr->slots, prev->slots, curr->total_slots)) return true;
    // Check state summary changes
    if (curr->by_state.active != prev->by_state.active ||
        curr->by_state.idle != prev->by_state.idle ||
        curr->by_state.closing != prev->by_state.closing) return true;
  } else if (curr->bitmap && prev->bitmap) {
    // Bitmap sizes must match for comparison
    if (curr->bitmap_bytes != prev->bitmap_bytes) return true;
    if (bitmap_differs(curr->bitmap, prev->bitmap, curr->bitmap_bytes)) return true;
  }

  return false;
}

// Find slots that changed and encode as sparse delta
// Format: "offset:RLE,offset:RLE,..." e.g. "3:A2I1,10:F3"
static size_t slots_to_delta_string(const valk_slot_diag_t *curr, const valk_slot_diag_t *prev,
                                     size_t count, char *out, size_t out_size) {
  if (count == 0 || out_size < 8) {
    out[0] = '\0';
    return 0;
  }

  char *p = out;
  char *end = out + out_size - 1;
  bool first_region = true;

  size_t i = 0;
  while (i < count && p < end - 20) {
    // Find start of a changed region
    while (i < count && curr[i].state == prev[i].state) i++;
    if (i >= count) break;

    size_t region_start = i;

    // Build RLE for changed region
    char rle_buf[256];
    char *rp = rle_buf;
    char *rend = rle_buf + sizeof(rle_buf) - 10;

    while (i < count && p < end - 20 && rp < rend) {
      char state = curr[i].state;
      size_t run_len = 1;

      // Count consecutive slots with same NEW state (include unchanged if adjacent)
      while (i + run_len < count && curr[i + run_len].state == state) {
        run_len++;
      }

      // Stop if we hit a long unchanged region (>4 slots same as prev)
      size_t unchanged_run = 0;
      for (size_t j = 0; j < run_len && i + j < count; j++) {
        if (curr[i + j].state == prev[i + j].state) {
          unchanged_run++;
          if (unchanged_run > 4) {
            run_len = j - unchanged_run + 1;
            break;
          }
        } else {
          unchanged_run = 0;
        }
      }

      if (run_len == 0) break;

      int n = snprintf(rp, rend - rp, "%c%zu", state, run_len);
      if (n < 0 || rp + n >= rend) break;
      rp += n;
      i += run_len;

      // Check if next slot is unchanged and we should end this region
      if (i < count && curr[i].state == prev[i].state) {
        break;
      }
    }
    *rp = '\0';

    // Write "offset:RLE"
    if (rp > rle_buf) {
      int n;
      if (first_region) {
        n = snprintf(p, end - p, "%zu:%s", region_start, rle_buf);
        first_region = false;
      } else {
        n = snprintf(p, end - p, ",%zu:%s", region_start, rle_buf);
      }
      if (n < 0 || p + n >= end) break;
      p += n;
    }
  }

  *p = '\0';
  return p - out;
}

// Encode delta diagnostics to SSE event
// Returns 0 if no meaningful changes, >0 for bytes written, <0 for error
int valk_diag_delta_to_sse(valk_mem_snapshot_t *current, valk_mem_snapshot_t *prev,
                            valk_sse_diag_conn_t *conn, valk_aio_system_t *aio,
                            valk_delta_snapshot_t *modular_delta,
                            char *buf, size_t buf_size, uint64_t event_id) {
  char *p = buf;
  char *end = buf + buf_size;

  // Track if we have any changes worth sending
  bool has_memory_changes = false;
  bool has_aio_metric_changes = false;
  bool has_modular_metric_changes = modular_delta && modular_delta->delta_count > 0;

  // Check for slab changes
  bool slab_changes[8] = {false};
  for (size_t i = 0; i < current->slab_count && i < prev->slab_count; i++) {
    if (slab_changed(&current->slabs[i], &prev->slabs[i])) {
      slab_changes[i] = true;
      has_memory_changes = true;
    }
  }

  // Check for arena changes (>1% change threshold)
  bool arena_changes[16] = {false};
  for (size_t i = 0; i < current->arena_count && i < prev->arena_count; i++) {
    size_t diff = current->arenas[i].used_bytes > prev->arenas[i].used_bytes
                    ? current->arenas[i].used_bytes - prev->arenas[i].used_bytes
                    : prev->arenas[i].used_bytes - current->arenas[i].used_bytes;
    size_t threshold = prev->arenas[i].capacity_bytes / 100;  // 1%
    if (diff > threshold || current->arenas[i].overflow_fallbacks != prev->arenas[i].overflow_fallbacks) {
      arena_changes[i] = true;
      has_memory_changes = true;
    }
  }

  // Check GC changes
  bool gc_changed = (current->gc_heap.gc_cycles != prev->gc_heap.gc_cycles ||
                     current->gc_heap.emergency_collections != prev->gc_heap.emergency_collections);
  if (gc_changed) has_memory_changes = true;

  // Check AIO metrics changes
#ifdef VALK_METRICS_ENABLED
  const valk_aio_metrics_t *aio_metrics = valk_aio_get_metrics(aio);
  const valk_aio_system_stats_t *sys_stats = valk_aio_get_system_stats(aio);
  if (aio_metrics && conn) {
    uint64_t bytes_sent = atomic_load(&aio_metrics->bytes_sent_total);
    uint64_t bytes_recv = atomic_load(&aio_metrics->bytes_recv_total);
    uint64_t requests = atomic_load(&aio_metrics->requests_total);
    uint64_t connections = atomic_load(&aio_metrics->connections_total);

    if (bytes_sent != conn->prev_metrics.bytes_sent ||
        bytes_recv != conn->prev_metrics.bytes_recv ||
        requests != conn->prev_metrics.requests_total ||
        connections != conn->prev_metrics.connections_total) {
      has_aio_metric_changes = true;
    }

    // Check pending streams changes
    if (sys_stats) {
      uint64_t pending_current = atomic_load(&sys_stats->pending_streams_current);
      uint64_t pending_total = atomic_load(&sys_stats->pending_streams_total);
      uint64_t pending_processed = atomic_load(&sys_stats->pending_streams_processed);
      uint64_t pending_dropped = atomic_load(&sys_stats->pending_streams_dropped);

      if (pending_current != conn->prev_metrics.pending_streams_current ||
          pending_total != conn->prev_metrics.pending_streams_total ||
          pending_processed != conn->prev_metrics.pending_streams_processed ||
          pending_dropped != conn->prev_metrics.pending_streams_dropped) {
        has_aio_metric_changes = true;
      }
    }
  }
#else
  (void)conn;
  (void)aio;
#endif

  // If nothing changed, send a heartbeat event so dashboard maintains even time intervals
  if (!has_memory_changes && !has_aio_metric_changes && !has_modular_metric_changes) {
    int n = snprintf(p, end - p, "event: diagnostics-delta\nid: %lu\ndata: {\"heartbeat\":true}\n\n", event_id);
    if (n < 0 || n >= end - p) return -1;
    return n;
  }

  // SSE event header - use "diagnostics-delta" event type
  int n = snprintf(p, end - p, "event: diagnostics-delta\nid: %lu\ndata: {", event_id);
  if (n < 0 || n >= end - p) return -1;
  p += n;

  bool need_comma = false;

  // ===== Memory section (only changed items) =====
  if (has_memory_changes) {
    n = snprintf(p, end - p, "\"memory\":{");
    if (n < 0 || n >= end - p) return -1;
    p += n;

    bool mem_need_comma = false;

    // Changed slabs only
    bool any_slab_changed = false;
    for (size_t i = 0; i < current->slab_count; i++) {
      if (slab_changes[i]) { any_slab_changed = true; break; }
    }

    if (any_slab_changed) {
      n = snprintf(p, end - p, "\"slabs\":[");
      if (n < 0 || n >= end - p) return -1;
      p += n;

      bool first_slab = true;
      for (size_t i = 0; i < current->slab_count; i++) {
        if (!slab_changes[i]) continue;

        valk_slab_snapshot_t *slab = &current->slabs[i];
        valk_slab_snapshot_t *prev_slab = &prev->slabs[i];

        if (!first_slab) {
          n = snprintf(p, end - p, ",");
          if (n < 0 || n >= end - p) return -1;
          p += n;
        }
        first_slab = false;

        if (slab->has_slot_diag && slab->slots && prev_slab->slots) {
          // Encode sparse delta for slot states
          char delta_buf[4096];
          slots_to_delta_string(slab->slots, prev_slab->slots, slab->total_slots,
                                delta_buf, sizeof(delta_buf));

          // Build by_owner JSON for delta (same format as full snapshot)
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
                       "{\"name\":\"%s\",\"used\":%zu,\"hwm\":%zu,"
                       "\"delta_states\":\"%s\","
                       "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu,\"by_owner\":%s},"
                       "\"by_type\":{\"tcp\":%zu,\"task\":%zu,\"timer\":%zu,\"http\":%zu}}",
                       slab->name, slab->used_slots, slab->peak_used,
                       delta_buf,
                       slab->by_state.active, slab->by_state.idle, slab->by_state.closing,
                       by_owner_buf,
                       slab->by_type.tcp_listeners, slab->by_type.tasks,
                       slab->by_type.timers, slab->by_type.http_conns);
        } else {
          // For bitmap slabs, send full bitmap (already RLE compressed)
          size_t rle_buf_size = slab->bitmap_bytes * 4 + 1;
          char *hex = malloc(rle_buf_size);
          if (!hex) return -1;

          if (slab->bitmap) {
            bitmap_to_rle_hex(slab->bitmap, slab->bitmap_bytes, hex, rle_buf_size);
          } else {
            hex[0] = '\0';
          }

          n = snprintf(p, end - p,
                       "{\"name\":\"%s\",\"bitmap\":\"%s\",\"used\":%zu,\"hwm\":%zu}",
                       slab->name, hex, slab->used_slots, slab->peak_used);
          free(hex);
        }

        if (n < 0 || n >= end - p) return -1;
        p += n;
      }

      n = snprintf(p, end - p, "]");
      if (n < 0 || n >= end - p) return -1;
      p += n;
      mem_need_comma = true;
    }

    // Changed arenas only
    bool any_arena_changed = false;
    for (size_t i = 0; i < current->arena_count; i++) {
      if (arena_changes[i]) { any_arena_changed = true; break; }
    }

    if (any_arena_changed) {
      n = snprintf(p, end - p, "%s\"arenas\":[", mem_need_comma ? "," : "");
      if (n < 0 || n >= end - p) return -1;
      p += n;

      bool first_arena = true;
      for (size_t i = 0; i < current->arena_count; i++) {
        if (!arena_changes[i]) continue;

        if (!first_arena) {
          n = snprintf(p, end - p, ",");
          if (n < 0 || n >= end - p) return -1;
          p += n;
        }
        first_arena = false;

        n = snprintf(p, end - p, "{\"name\":\"%s\",\"used\":%zu}",
                     current->arenas[i].name, current->arenas[i].used_bytes);
        if (n < 0 || n >= end - p) return -1;
        p += n;
      }

      n = snprintf(p, end - p, "]");
      if (n < 0 || n >= end - p) return -1;
      p += n;
      mem_need_comma = true;
    }

    // GC changes (generic tiers array)
    if (gc_changed) {
      n = snprintf(p, end - p, "%s\"gc\":{", mem_need_comma ? "," : "");
      if (n < 0 || n >= end - p) return -1;
      p += n;

      n = gc_tiers_to_json(current, p, end - p);
      if (n < 0) return -1;
      p += n;

      n = snprintf(p, end - p,
                   ",\"cycles\":%lu,\"emergency\":%zu}",
                   current->gc_heap.gc_cycles,
                   current->gc_heap.emergency_collections);
      if (n < 0 || n >= end - p) return -1;
      p += n;
    }

    n = snprintf(p, end - p, "}");  // Close memory
    if (n < 0 || n >= end - p) return -1;
    p += n;
    need_comma = true;
  }

  // ===== Metrics section (delta values) =====
#ifdef VALK_METRICS_ENABLED
  // Include metrics section if GC changed (need VM metrics for UI) or other metrics changed
  // Always emit metrics section (at minimum for registry stats)
  // Registry stats are always included for real-time monitoring
  {
    n = snprintf(p, end - p, "%s\"metrics\":{", need_comma ? "," : "");
    if (n < 0 || n >= end - p) return -1;
    p += n;

    bool metrics_need_comma = false;

    // VM metrics - only emit GC when changed
    // Note: event_loop metrics are now part of modular metrics system
    // and will be included in the modular delta automatically
    if (gc_changed) {
      valk_vm_metrics_t vm_metrics = {0};
      valk_gc_malloc_heap_t *gc_heap = valk_aio_get_gc_heap(aio);
      valk_vm_metrics_collect(&vm_metrics, gc_heap, NULL);

      n = snprintf(p, end - p,
                   "\"vm\":{\"gc\":{\"cycles_total\":%lu,\"pause_us_total\":%lu,"
                   "\"pause_us_max\":%lu,\"reclaimed_bytes\":%lu,"
                   "\"heap_used_bytes\":%zu,\"heap_total_bytes\":%zu}}",
                   vm_metrics.gc_cycles, vm_metrics.gc_pause_us_total,
                   vm_metrics.gc_pause_us_max, vm_metrics.gc_reclaimed_bytes,
                   vm_metrics.gc_heap_used, vm_metrics.gc_heap_total);
      if (n < 0 || n >= end - p) return -1;
      p += n;
      metrics_need_comma = true;
    }

    // AIO metrics delta
    if (has_aio_metric_changes && conn) {
      const valk_aio_metrics_t *aio_metrics = valk_aio_get_metrics(aio);
      if (aio_metrics) {
        uint64_t bytes_sent = atomic_load(&aio_metrics->bytes_sent_total);
        uint64_t bytes_recv = atomic_load(&aio_metrics->bytes_recv_total);
        uint64_t requests = atomic_load(&aio_metrics->requests_total);

        // Send deltas for monotonic counters
        uint64_t d_sent = bytes_sent - conn->prev_metrics.bytes_sent;
        uint64_t d_recv = bytes_recv - conn->prev_metrics.bytes_recv;
        uint64_t d_req = requests - conn->prev_metrics.requests_total;

        // Get pending streams metrics for delta
        const valk_aio_system_stats_t *sys_stats_delta = valk_aio_get_system_stats(aio);
        uint64_t pending_current = 0, pending_total = 0, pending_processed = 0, pending_dropped = 0;
        uint64_t d_pending_total = 0, d_pending_processed = 0, d_pending_dropped = 0;
        if (sys_stats_delta) {
          pending_current = atomic_load(&sys_stats_delta->pending_streams_current);
          pending_total = atomic_load(&sys_stats_delta->pending_streams_total);
          pending_processed = atomic_load(&sys_stats_delta->pending_streams_processed);
          pending_dropped = atomic_load(&sys_stats_delta->pending_streams_dropped);
          d_pending_total = pending_total - conn->prev_metrics.pending_streams_total;
          d_pending_processed = pending_processed - conn->prev_metrics.pending_streams_processed;
          d_pending_dropped = pending_dropped - conn->prev_metrics.pending_streams_dropped;
        }

        n = snprintf(p, end - p,
                     "%s\"aio\":{\"bytes\":{\"d_sent\":%lu,\"d_recv\":%lu},"
                     "\"requests\":{\"d_total\":%lu},"
                     "\"connections\":{\"active\":%lu,\"idle\":%lu,\"closing\":%lu},"
                     "\"pending_streams\":{\"current\":%lu,\"d_total\":%lu,\"d_processed\":%lu,\"d_dropped\":%lu}}",
                     metrics_need_comma ? "," : "",
                     d_sent, d_recv, d_req,
                     atomic_load(&aio_metrics->connections_active),
                     atomic_load(&aio_metrics->connections_idle),
                     atomic_load(&aio_metrics->connections_closing),
                     pending_current, d_pending_total, d_pending_processed, d_pending_dropped);
        if (n < 0 || n >= end - p) return -1;
        p += n;
        metrics_need_comma = true;

        // Update previous metrics for next delta
        conn->prev_metrics.bytes_sent = bytes_sent;
        conn->prev_metrics.bytes_recv = bytes_recv;
        conn->prev_metrics.requests_total = requests;
        conn->prev_metrics.connections_total = atomic_load(&aio_metrics->connections_total);
        // Update pending streams previous values
        conn->prev_metrics.pending_streams_current = pending_current;
        conn->prev_metrics.pending_streams_total = pending_total;
        conn->prev_metrics.pending_streams_processed = pending_processed;
        conn->prev_metrics.pending_streams_dropped = pending_dropped;
      }
    }

    // SSE registry stats (always include for real-time dashboard stream count)
    valk_sse_stream_registry_t *sse_registry = valk_aio_get_sse_registry(aio);
    if (sse_registry) {
      n = snprintf(p, end - p,
                   "%s\"sse\":{\"streams_active\":%zu,"
                   "\"events_pushed_total\":%lu,\"bytes_pushed_total\":%lu}",
                   metrics_need_comma ? "," : "",
                   sse_registry->stream_count,
                   sse_registry->events_pushed_total,
                   sse_registry->bytes_pushed_total);
      if (n < 0 || n >= end - p) return -1;
      p += n;
      metrics_need_comma = true;
    }

    // Modular metrics delta (counters, gauges, histograms)
    if (has_modular_metric_changes && modular_delta) {
      // Use valk_delta_to_json to encode the modular metrics delta
      char modular_buf[32768];
      size_t modular_len = valk_delta_to_json(modular_delta, modular_buf, sizeof(modular_buf));
      if (modular_len > 0 && modular_len < sizeof(modular_buf)) {
        n = snprintf(p, end - p, "%s\"modular\":%s",
                     metrics_need_comma ? "," : "", modular_buf);
        if (n < 0 || n >= end - p) return -1;
        p += n;
        metrics_need_comma = true;
      }
    }

    // Registry stats (meta-metrics - always send for real-time tracking)
    {
      valk_registry_stats_t reg_stats;
      valk_registry_stats_collect(&reg_stats);
      char reg_buf[1024];
      size_t reg_len = valk_registry_stats_to_json(&reg_stats, reg_buf, sizeof(reg_buf));
      if (reg_len > 0) {
        n = snprintf(p, end - p, "%s\"registry\":%s",
                     metrics_need_comma ? "," : "", reg_buf);
        if (n < 0 || n >= end - p) return -1;
        p += n;
      }
    }

    n = snprintf(p, end - p, "}");  // Close metrics
    if (n < 0 || n >= end - p) return -1;
    p += n;
  }
#else
  (void)modular_delta;
#endif

  // Close JSON and add SSE empty line
  n = snprintf(p, end - p, "}\n\n");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  return p - buf;
}

// ============================================================================
// Fresh State JSON (for /debug/metrics/state endpoint)
// ============================================================================

// Get fresh diagnostics state as JSON (for /debug/metrics/state endpoint)
// Returns bytes written, or -1 on error
// This is similar to valk_diag_snapshot_to_sse but WITHOUT SSE framing
int valk_diag_fresh_state_json(valk_aio_system_t *aio, char *buf, size_t buf_size) {
  char *p = buf;
  char *end = buf + buf_size;
  int n;

  // Collect snapshot
  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, aio);

  // Start JSON object (NO SSE framing)
  n = snprintf(p, end - p, "{");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // ===== Memory section =====
  n = snprintf(p, end - p, "\"memory\":{");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // Slabs array
  n = snprintf(p, end - p, "\"slabs\":[");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  for (size_t i = 0; i < snapshot.slab_count; i++) {
    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || n >= end - p) goto cleanup;
      p += n;
    }

    valk_slab_snapshot_t *slab = &snapshot.slabs[i];

    if (slab->has_slot_diag && slab->slots) {
      // RLE-encoded state string
      size_t rle_buf_size = slab->total_slots * 8 + 1;
      char *states = malloc(rle_buf_size);
      if (!states) goto cleanup;
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
                   "{\"name\":\"%s\",\"total\":%zu,\"used\":%zu,\"hwm\":%zu,"
                   "\"states\":\"%s\","
                   "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu,\"by_owner\":%s},"
                   "\"by_type\":{\"tcp\":%zu,\"task\":%zu,\"timer\":%zu,\"http\":%zu},"
                   "\"overflow\":%zu}",
                   slab->name, slab->total_slots, slab->used_slots, slab->peak_used,
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
      if (!hex) goto cleanup;

      if (slab->bitmap) {
        bitmap_to_rle_hex(slab->bitmap, slab->bitmap_bytes, hex, rle_buf_size);
      } else {
        hex[0] = '\0';
      }

      n = snprintf(p, end - p,
                   "{\"name\":\"%s\",\"bitmap\":\"%s\",\"total\":%zu,\"used\":%zu,"
                   "\"hwm\":%zu,\"overflow\":%zu}",
                   slab->name, hex, slab->total_slots, slab->used_slots,
                   slab->peak_used, slab->overflow_count);

      free(hex);
    }

    if (n < 0 || n >= end - p) goto cleanup;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // Arenas array
  n = snprintf(p, end - p, "\"arenas\":[");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  for (size_t i = 0; i < snapshot.arena_count; i++) {
    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || n >= end - p) goto cleanup;
      p += n;
    }

    n = snprintf(
        p, end - p,
        "{\"name\":\"%s\",\"used\":%zu,\"capacity\":%zu,\"hwm\":%zu,"
        "\"overflow\":%zu,\"overflow_bytes\":%zu}",
        snapshot.arenas[i].name, snapshot.arenas[i].used_bytes,
        snapshot.arenas[i].capacity_bytes,
        snapshot.arenas[i].high_water_mark,
        snapshot.arenas[i].overflow_fallbacks,
        snapshot.arenas[i].overflow_bytes);

    if (n < 0 || n >= end - p) goto cleanup;
    p += n;
  }

  n = snprintf(p, end - p, "],");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // GC heap stats (generic tiers array)
  n = snprintf(p, end - p, "\"gc\":{");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  n = gc_tiers_to_json(&snapshot, p, end - p);
  if (n < 0) goto cleanup;
  p += n;

  n = snprintf(p, end - p,
               ",\"threshold_pct\":%u,\"cycles\":%lu,\"emergency\":%zu},",
               (unsigned)snapshot.gc_heap.gc_threshold_pct,
               snapshot.gc_heap.gc_cycles,
               snapshot.gc_heap.emergency_collections);
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // Owner map
  n = snprintf(p, end - p, "\"owner_map\":[");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  for (size_t i = 0; i < snapshot.owner_count; i++) {
    if (i > 0) {
      n = snprintf(p, end - p, ",");
      if (n < 0 || n >= end - p) goto cleanup;
      p += n;
    }
    n = snprintf(p, end - p, "\"%s\"",
                 snapshot.owner_map[i] ? snapshot.owner_map[i] : "");
    if (n < 0 || n >= end - p) goto cleanup;
    p += n;
  }

  n = snprintf(p, end - p, "],");  // Close owner_map array
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // Process-level memory stats
  n = snprintf(p, end - p,
               "\"process\":{\"rss\":%zu,\"vms\":%zu,\"system_total\":%zu,"
               "\"shared\":%zu,\"data\":%zu,\"page_faults_minor\":%lu,"
               "\"page_faults_major\":%lu},",
               snapshot.process.rss_bytes, snapshot.process.vms_bytes,
               snapshot.process.system_total_bytes,
               snapshot.process.shared_bytes, snapshot.process.data_bytes,
               (unsigned long)snapshot.process.page_faults_minor,
               (unsigned long)snapshot.process.page_faults_major);
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // Smaps breakdown (detailed RSS by region type - Linux only)
  n = snprintf(p, end - p,
               "\"smaps\":{"
               "\"heap\":%zu,\"stack\":%zu,\"anon\":%zu,"
               "\"file\":%zu,\"shmem\":%zu,\"uring\":%zu,"
               "\"other\":%zu,\"total\":%zu,"
               "\"anon_regions\":%u,\"file_regions\":%u},",
               snapshot.smaps.heap_rss,
               snapshot.smaps.stack_rss,
               snapshot.smaps.anon_rss,
               snapshot.smaps.file_rss,
               snapshot.smaps.shmem_rss,
               snapshot.smaps.uring_rss,
               snapshot.smaps.other_rss,
               snapshot.smaps.total_rss,
               snapshot.smaps.anon_regions,
               snapshot.smaps.file_regions);
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // Breakdown by subsystem (used and capacity)
  n = snprintf(p, end - p,
               "\"breakdown\":{"
               "\"scratch_used\":%zu,\"scratch_cap\":%zu,"
               "\"gc_used\":%zu,\"gc_cap\":%zu,"
               "\"gc_lval_used\":%zu,\"gc_lval_cap\":%zu,"
               "\"gc_lenv_used\":%zu,\"gc_lenv_cap\":%zu,"
               "\"gc_malloc\":%zu,"
               "\"aio_used\":%zu,\"aio_cap\":%zu,"
               "\"ssl_used\":%zu,\"nghttp2_used\":%zu,\"libuv_used\":%zu,"
               "\"metrics_used\":%zu,\"metrics_cap\":%zu,"
               "\"untracked\":%zu,\"untracked_reserved\":%zu}},",
               snapshot.breakdown.scratch_arena_used,
               snapshot.breakdown.scratch_arena_capacity,
               snapshot.breakdown.gc_heap_used,
               snapshot.breakdown.gc_heap_capacity,
               snapshot.breakdown.gc_lval_slab_used,
               snapshot.breakdown.gc_lval_slab_capacity,
               snapshot.breakdown.gc_lenv_slab_used,
               snapshot.breakdown.gc_lenv_slab_capacity,
               snapshot.breakdown.gc_malloc_used,
               snapshot.breakdown.aio_slabs_used,
               snapshot.breakdown.aio_slabs_capacity,
               valk_aio_ssl_bytes_used(),
               valk_aio_nghttp2_bytes_used(),
               valk_aio_libuv_bytes_used(),
               snapshot.breakdown.metrics_used,
               snapshot.breakdown.metrics_capacity,
               snapshot.breakdown.untracked_bytes,
               snapshot.breakdown.untracked_reserved);
  if (n < 0 || n >= end - p) goto cleanup;
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
  if (n < 0 || n >= end - p) goto cleanup;
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

  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // AIO metrics subsection
  if (aio_metrics) {
    // Calculate uptime
    uint64_t now_us = (uint64_t)(uv_hrtime() / 1000);
    double uptime_seconds = (double)(now_us - aio_metrics->start_time_us) / 1000000.0;

    // Get system stats for queue data
    valk_aio_system_stats_t *sys_stats = valk_aio_get_system_stats(aio);
    uint64_t pending_req = sys_stats ? atomic_load(&sys_stats->pending_requests) : 0;
    uint64_t pending_resp = sys_stats ? atomic_load(&sys_stats->pending_responses) : 0;
    uint64_t queue_cap = sys_stats ? sys_stats->queue_capacity : 0;

    // Pending stream backpressure stats
    uint64_t bp_current = sys_stats ? atomic_load(&sys_stats->pending_streams_current) : 0;
    uint64_t bp_total = sys_stats ? atomic_load(&sys_stats->pending_streams_total) : 0;
    uint64_t bp_processed = sys_stats ? atomic_load(&sys_stats->pending_streams_processed) : 0;
    uint64_t bp_dropped = sys_stats ? atomic_load(&sys_stats->pending_streams_dropped) : 0;
    uint64_t bp_wait_us = sys_stats ? atomic_load(&sys_stats->pending_streams_wait_us) : 0;
    uint64_t bp_pool_size = sys_stats ? sys_stats->pending_streams_pool_size : 0;
    // Calculate average wait time (avoid division by zero)
    double bp_avg_wait_ms = (bp_processed > 0) ? (double)bp_wait_us / (double)bp_processed / 1000.0 : 0.0;

    n = snprintf(p, end - p,
                 "\"aio\":{\"uptime_seconds\":%.2f,"
                 "\"connections\":{\"total\":%lu,\"active\":%lu,\"failed\":%lu,"
                 "\"idle\":%lu,\"closing\":%lu,\"connecting\":%lu},"
                 "\"streams\":{\"total\":%lu,\"active\":%lu},"
                 "\"requests\":{\"total\":%lu,\"active\":%lu,\"errors\":%lu},"
                 "\"bytes\":{\"sent\":%lu,\"recv\":%lu},"
                 "\"queue\":{\"pending_requests\":%lu,\"pending_responses\":%lu,\"capacity\":%lu},"
                 "\"pending_streams\":{\"current\":%lu,\"total\":%lu,"
                 "\"processed\":%lu,\"dropped\":%lu,\"avg_wait_ms\":%.2f,\"pool_size\":%lu}},",
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
                 atomic_load(&aio_metrics->bytes_recv_total),
                 pending_req, pending_resp, queue_cap,
                 bp_current, bp_total, bp_processed, bp_dropped, bp_avg_wait_ms, bp_pool_size);

    if (n < 0 || n >= end - p) goto cleanup;
    p += n;
  }

  // Modular metrics (HTTP server counters, gauges, histograms)
  // Use a heap-allocated buffer since metrics can be large during stress tests
  size_t modular_buf_size = 131072;  // 128KB for modular metrics
  char *modular_buf = malloc(modular_buf_size);
  if (modular_buf) {
    size_t modular_len = valk_metrics_v2_to_json(&g_metrics, modular_buf, modular_buf_size);
    // valk_metrics_json returns cap on overflow, or actual length on success
    if (modular_len > 0 && modular_len < modular_buf_size) {
      n = snprintf(p, end - p, "\"modular\":%s", modular_buf);
      if (n < 0 || n >= end - p) {
        free(modular_buf);
        goto cleanup;
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
        goto cleanup;
      }
      p += n;
    }
    free(modular_buf);
  } else {
    // Allocation failed - use empty object
    n = snprintf(p, end - p, "\"modular\":{}");
    if (n < 0 || n >= end - p) goto cleanup;
    p += n;
  }

  // Registry stats (meta-metrics about the metrics system itself)
  {
    valk_registry_stats_t reg_stats;
    valk_registry_stats_collect(&reg_stats);
    char reg_buf[1024];
    size_t reg_len = valk_registry_stats_to_json(&reg_stats, reg_buf, sizeof(reg_buf));
    if (reg_len > 0) {
      n = snprintf(p, end - p, ",\"registry\":%s", reg_buf);
      if (n < 0 || n >= end - p) goto cleanup;
      p += n;
    }
  }

  n = snprintf(p, end - p, "}");  // Close metrics section
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;
#else
  // Metrics disabled - empty section
  n = snprintf(p, end - p, "\"metrics\":{}");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;
#endif

  // ===== Timestamp =====
  uint64_t now_us = (uint64_t)(uv_hrtime() / 1000);
  n = snprintf(p, end - p, ",\"timestamp_us\":%lu}", now_us);
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

cleanup:
  valk_mem_snapshot_free(&snapshot);
  if (n < 0 || n >= end - p) return -1;
  return (p - buf);
}

// ============================================================================
// SSE Connection Management (HTTP/2 Streaming)
// ============================================================================

// SSE buffer size - large enough for full snapshot + metrics
#define SSE_BUFFER_SIZE 262144  // 256KB

// Forward declare the data provider callback
static nghttp2_ssize sse_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

// Push diagnostics to a single stream
// Returns true if data was successfully queued for sending
// modular_delta: collected once per tick, shared by all streams (NULL if none)
static bool sse_push_to_stream(valk_sse_diag_conn_t *stream,
                                valk_mem_snapshot_t *snapshot,
                                valk_delta_snapshot_t *modular_delta) {
  if (!stream || !stream->active || !stream->session) {
    return false;
  }

  // If we still have pending data, skip this tick for this stream
  if (stream->pending_data && stream->pending_offset < stream->pending_len) {
    return false;
  }

  // Allocate or reuse pending buffer
  if (!stream->pending_data) {
    stream->pending_data = malloc(SSE_BUFFER_SIZE);
    if (!stream->pending_data) {
      VALK_ERROR("Failed to allocate SSE buffer for stream %d", stream->stream_id);
      return false;
    }
  }

  int len;

  if (!stream->first_event_sent) {
    // First event: send full snapshot (event type: "diagnostics")
    len = valk_diag_snapshot_to_sse(snapshot, stream->aio_system,
                                     stream->pending_data, SSE_BUFFER_SIZE,
                                     ++stream->last_event_id);

    VALK_DEBUG("SSE[stream=%d]: valk_diag_snapshot_to_sse returned len=%d",
               stream->stream_id, len);

    if (len > 0) {
      stream->first_event_sent = true;

      // Initialize previous metrics for delta tracking
#ifdef VALK_METRICS_ENABLED
      const valk_aio_metrics_t *aio_metrics = valk_aio_get_metrics(stream->aio_system);
      if (aio_metrics) {
        stream->prev_metrics.bytes_sent = atomic_load(&aio_metrics->bytes_sent_total);
        stream->prev_metrics.bytes_recv = atomic_load(&aio_metrics->bytes_recv_total);
        stream->prev_metrics.requests_total = atomic_load(&aio_metrics->requests_total);
        stream->prev_metrics.connections_total = atomic_load(&aio_metrics->connections_total);
        stream->prev_metrics.gc_cycles = snapshot->gc_heap.gc_cycles;
      }
#endif

      // Store snapshot for next delta comparison
      valk_mem_snapshot_copy(&stream->prev_snapshot, snapshot);

      VALK_DEBUG("SSE[stream=%d]: sent full snapshot (%d bytes)", stream->stream_id, len);
    }
  } else {
    // Subsequent events: send delta only (event type: "diagnostics-delta")
    len = valk_diag_delta_to_sse(snapshot, &stream->prev_snapshot, stream,
                                  stream->aio_system, modular_delta,
                                  stream->pending_data, SSE_BUFFER_SIZE,
                                  ++stream->last_event_id);

    if (len > 0) {
      // Update stored snapshot for next comparison
      valk_mem_snapshot_copy(&stream->prev_snapshot, snapshot);
      VALK_DEBUG("SSE[stream=%d]: sent delta (%d bytes)", stream->stream_id, len);
    } else if (len == 0) {
      // No changes - don't send anything
      return false;
    }
  }

  if (len < 0) {
    VALK_ERROR("Failed to format SSE diagnostics event for stream %d", stream->stream_id);
    return false;
  }

  stream->pending_len = (size_t)len;
  stream->pending_offset = 0;

  // If data was deferred, resume the stream and flush
  if (stream->data_deferred && stream->session && stream->active) {
    // Verify session is still valid using the handle's authoritative session pointer
    if (!valk_aio_http_session_valid(stream->handle, stream->session)) {
      VALK_INFO("SSE session invalidated for stream %d", stream->stream_id);
      stream->active = false;
      return false;
    }

    // Check if the stream is still valid before trying to resume
    if (nghttp2_session_get_stream_user_data(stream->session, stream->stream_id) == NULL) {
      VALK_INFO("SSE stream %d closed, marking inactive", stream->stream_id);
      stream->active = false;
      return false;
    }

    stream->data_deferred = false;
    int rv = nghttp2_session_resume_data(stream->session, stream->stream_id);
    if (rv != 0) {
      if (rv == NGHTTP2_ERR_INVALID_ARGUMENT) {
        VALK_INFO("SSE stream %d no longer valid", stream->stream_id);
        stream->active = false;
      } else {
        VALK_ERROR("Failed to resume HTTP/2 stream %d: %s",
                   stream->stream_id, nghttp2_strerror(rv));
      }
      return false;
    }
  }

  return true;
}

// Timer callback - called every 100ms to push diagnostics to ALL streams
// Collects snapshot once, then pushes to each active stream
static void sse_push_diagnostics(uv_timer_t *timer) {
  valk_sse_diag_state_t *state = (valk_sse_diag_state_t *)timer->data;

  if (!state) {
    VALK_WARN("SSE timer: state is NULL");
    return;
  }

  if (!state->streams) {
    VALK_DEBUG("SSE timer: no streams attached");
    return;
  }

  // Collect memory snapshot once for all streams
  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, state->aio_system);

  // Collect modular metrics delta once for all streams on this connection
  // Uses per-connection baseline to avoid race conditions with other connections
#ifdef VALK_METRICS_ENABLED
  if (!state->modular_delta_initialized) {
    valk_delta_snapshot_init(&state->modular_delta);
    state->modular_delta_initialized = true;
  }
  if (!state->modular_baseline) {
    state->modular_baseline = malloc(sizeof(valk_metrics_baseline_t));
    if (state->modular_baseline) {
      valk_metrics_baseline_init(state->modular_baseline);
    }
  }
  size_t modular_changes = 0;
  if (state->modular_baseline) {
    modular_changes = valk_delta_snapshot_collect_stateless(
        &state->modular_delta, &g_metrics, state->modular_baseline);
  }
  valk_delta_snapshot_t *modular_delta_ptr = modular_changes > 0 ? &state->modular_delta : NULL;
#else
  valk_delta_snapshot_t *modular_delta_ptr = NULL;
#endif

  VALK_DEBUG("SSE timer: collected snapshot with %zu slabs, %zu arenas, %zu modular changes",
             snapshot.slab_count, snapshot.arena_count,
             modular_delta_ptr ? modular_delta_ptr->delta_count : 0);

  // Push to each active stream
  bool any_data_sent = false;
  for (valk_sse_diag_conn_t *stream = state->streams; stream; stream = stream->next) {
    if (sse_push_to_stream(stream, &snapshot, modular_delta_ptr)) {
      any_data_sent = true;
    }
  }

  // If any stream has data to send, flush the HTTP/2 session
  // All streams share the same connection, so one flush is sufficient
  if (any_data_sent && state->http_handle) {
    valk_http2_flush_pending(state->http_handle);
  }

  // Free snapshot allocations
  valk_mem_snapshot_free(&snapshot);
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

// Forward declaration for getting/setting sse_state on handle
// These are implemented in aio_uv.c via accessor functions
extern valk_sse_diag_state_t* valk_aio_get_sse_state(valk_aio_handle_t *handle);
extern void valk_aio_set_sse_state(valk_aio_handle_t *handle, valk_sse_diag_state_t *state);

// Close callback for timer handle - releases back to slab and frees state
static void on_timer_close(uv_handle_t *handle) {
  valk_sse_diag_state_t *state = (valk_sse_diag_state_t *)handle->data;

  if (!state) {
    VALK_WARN("SSE timer close callback: state is NULL");
    return;
  }

  if (!state->timer_handle) {
    VALK_WARN("SSE timer close callback: timer_handle is NULL (double close?)");
    // Still free modular delta if initialized
    if (state->modular_delta_initialized) {
      valk_delta_snapshot_free(&state->modular_delta);
    }
    free(state->modular_baseline);
    free(state);
    return;
  }

  VALK_DEBUG("SSE timer close callback, releasing timer handle %p", (void*)state->timer_handle);
  valk_aio_timer_free(state->timer_handle);
  state->timer_handle = NULL;

  // Note: sse_state was already cleared synchronously in valk_sse_diag_stop()
  // to prevent race conditions with new connections

  // Free modular delta snapshot if initialized
  if (state->modular_delta_initialized) {
    valk_delta_snapshot_free(&state->modular_delta);
  }

  // Free per-connection baseline
  free(state->modular_baseline);

  // Now safe to free the state struct itself
  free(state);
}

// Initialize HTTP/2 SSE streaming - returns stream context and populates data provider
// Multiple streams can share one timer via the handle's sse_state
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

  // Get or create shared state for this HTTP connection
  valk_sse_diag_state_t *state = valk_aio_get_sse_state(handle);
  bool new_state = false;

  if (!state) {
    // First SSE stream on this connection - create shared state with timer
    state = malloc(sizeof(valk_sse_diag_state_t));
    if (!state) {
      VALK_ERROR("Failed to allocate SSE diagnostics state");
      return NULL;
    }

    memset(state, 0, sizeof(*state));
    state->aio_system = aio;
    state->http_handle = handle;
    state->streams = NULL;

    // Allocate timer handle from slab
    state->timer_handle = valk_aio_timer_alloc(aio);
    if (!state->timer_handle) {
      VALK_ERROR("Failed to allocate SSE timer from handle slab");
      free(state);
      return NULL;
    }

    valk_aio_timer_init(state->timer_handle);
    valk_aio_timer_set_data(state->timer_handle, state);

    new_state = true;
    VALK_INFO("SSE: created new shared state for connection (timer=%p)",
              (void*)state->timer_handle);
  }

  // Create new stream context
  valk_sse_diag_conn_t *stream = malloc(sizeof(valk_sse_diag_conn_t));
  if (!stream) {
    VALK_ERROR("Failed to allocate SSE stream context");
    if (new_state) {
      // Clean up the state we just created
      valk_aio_timer_free(state->timer_handle);
      free(state);
    }
    return NULL;
  }

  memset(stream, 0, sizeof(*stream));
  stream->state = state;
  stream->handle = handle;
  stream->aio_system = aio;
  stream->session = session;
  stream->stream_id = stream_id;
  stream->last_event_id = 0;
  stream->active = true;
  stream->data_deferred = true;  // Start deferred until first timer tick
  stream->pending_data = NULL;
  stream->pending_len = 0;
  stream->pending_offset = 0;

  // Add stream to linked list (prepend for O(1) insertion)
  stream->next = state->streams;
  state->streams = stream;

  // Set up data provider for nghttp2
  data_prd_out->source.ptr = stream;
  data_prd_out->read_callback = sse_data_read_callback;

  // If this is a new state, start the timer and store in handle
  if (new_state) {
    valk_aio_set_sse_state(handle, state);
    // Start timer with 100ms interval, first tick after 10ms
    valk_aio_timer_start(state->timer_handle, 10, 100, sse_push_diagnostics);
  }

  VALK_INFO("SSE: stream %d started (stream=%p, state=%p, new_state=%s)",
            stream_id, (void*)stream, (void*)state, new_state ? "yes" : "no");
  return stream;
}

// Free a single stream's resources (does not remove from list)
static void sse_stream_free(valk_sse_diag_conn_t *stream) {
  if (!stream) return;

  stream->active = false;
  stream->session = NULL;

  // Free pending buffer
  if (stream->pending_data) {
    free(stream->pending_data);
    stream->pending_data = NULL;
  }

  // Free previous snapshot used for delta tracking
  valk_mem_snapshot_free(&stream->prev_snapshot);

  free(stream);
}

// Stop SSE stream (removes from shared state, stops timer if last stream)
void valk_sse_diag_stop(valk_sse_diag_conn_t *sse_conn) {
  if (!sse_conn) {
    return;
  }

  valk_sse_diag_state_t *state = sse_conn->state;
  if (!state) {
    VALK_WARN("SSE[stream=%d]: stop called but no state attached", sse_conn->stream_id);
    sse_stream_free(sse_conn);
    return;
  }

  VALK_INFO("SSE[stream=%d]: stopping (stream=%p, state=%p)",
            sse_conn->stream_id, (void*)sse_conn, (void*)state);

  // Remove stream from linked list
  valk_sse_diag_conn_t **pp = &state->streams;
  while (*pp) {
    if (*pp == sse_conn) {
      *pp = sse_conn->next;
      break;
    }
    pp = &(*pp)->next;
  }

  // Free stream resources
  sse_stream_free(sse_conn);

  // If no more streams, stop timer and free state
  if (!state->streams) {
    VALK_INFO("SSE: last stream closed, stopping timer");

    // Clear sse_state SYNCHRONOUSLY to prevent race with new connections
    // (new stream might connect before async on_timer_close fires)
    if (state->http_handle) {
      valk_aio_set_sse_state(state->http_handle, NULL);
    }

    if (state->timer_handle) {
      valk_aio_timer_stop(state->timer_handle);
      // The close callback will free state
      valk_aio_timer_close(state->timer_handle, on_timer_close);
    } else {
      // Timer already closed, just free state
      free(state);
    }
  }
}

// Stop all SSE streams on a connection (for abrupt disconnect cleanup)
void valk_sse_diag_stop_all(valk_sse_diag_state_t *state) {
  if (!state) {
    return;
  }

  VALK_INFO("SSE: stopping all streams on state %p", (void*)state);

  // Free all streams
  valk_sse_diag_conn_t *stream = state->streams;
  while (stream) {
    valk_sse_diag_conn_t *next = stream->next;
    sse_stream_free(stream);
    stream = next;
  }
  state->streams = NULL;

  // Stop timer and free state
  if (state->timer_handle) {
    valk_aio_timer_stop(state->timer_handle);
    // The close callback will free state and clear handle's sse_state
    valk_aio_timer_close(state->timer_handle, on_timer_close);
  } else {
    // Timer already closed, just free state
    if (state->http_handle) {
      valk_aio_set_sse_state(state->http_handle, NULL);
    }
    // Free modular delta if initialized
    if (state->modular_delta_initialized) {
      valk_delta_snapshot_free(&state->modular_delta);
    }
    // Free per-connection baseline
    free(state->modular_baseline);
    free(state);
  }
}
