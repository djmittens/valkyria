# Memory Diagnostics Dashboard - Implementation Plan

This document details the implementation of a new SSE-powered memory diagnostics endpoint, replacing the decorative connection pool "heatmap" with functional real-time memory visualizations.

## Executive Summary

Split the metrics system into two parts:
1. **Existing `/debug/metrics`**: Keep for RED/USE metrics, request rates, latencies (polling-based)
2. **New `/api/diagnostics/memory/stream`**: SSE-powered real-time memory state (push-based, 100ms interval)

The new endpoint will visualize:
- All slab allocators (TCP buffers, handles, stream arenas, servers, clients, LVAL)
- Arena allocators (scratch, per-stream arenas)
- Memory pressure indicators and leak detection (long-lived allocations)

---

## 1. Memory Systems Inventory

Based on codebase analysis, here are all managed memory systems to visualize:

### 1.1 Slab Allocators

| Slab | Location | Item Size | Capacity | Visualization |
|------|----------|-----------|----------|---------------|
| **TCP Buffers** | `aio_uv.c:97` (thread-local) | `SSL3_RT_MAX_PACKET_SIZE * 2` (~16KB) | `config.tcp_buffer_pool_size` (default ~400) | 20×10 grid |
| **Handle Slab** | `aio_uv.c:531` | `sizeof(valk_aio_handle_t)` | `AIO_MAX_HANDLES = 2056` | 32×64 grid (scaled) |
| **Stream Arenas** | `aio_uv.c:528` | `arena_size + header` (~64MB) | `config.arena_pool_size` (default 64) | 8×8 grid |
| **HTTP Servers** | `aio_uv.c:526` | `sizeof(valk_arc_box) + sizeof(server)` | `HTTP_MAX_SERVERS = 3` | 3×1 grid |
| **HTTP Clients** | `aio_uv.c:527` | `sizeof(valk_arc_box) + sizeof(client)` | `HTTP_MAX_CLIENTS = 3` | 3×1 grid |
| **LVAL Slab** | `gc.c:82-98` | `sizeof(gc_header) + sizeof(lval)` | `256 * 1024` (262K) | 32×32 aggregated |

### 1.2 Arena Allocators

| Arena | Location | Capacity | Tracking |
|-------|----------|----------|----------|
| **Scratch Arena** | `memory.c:385` (per-thread) | Configurable (typically 64MB) | offset, high_water_mark, overflow_count |
| **Stream Arenas** | `aio_uv.c:816` (per-request) | `config.arena_size` (64MB) | offset per active arena |

### 1.3 GC Heap

| Metric | Location | Description |
|--------|----------|-------------|
| **allocated_bytes** | `gc.c:47` | Current heap usage |
| **gc_threshold** | `gc.c:48` | Trigger GC threshold |
| **peak_usage** | `gc.c:201` | Maximum ever allocated |
| **emergency_collections** | `gc.c:128` | OOM near-misses |

---

## 2. SSE Endpoint Implementation

### 2.1 C Backend: New SSE Handler

**File:** `src/aio_sse_diagnostics.c` (new file)

```c
// src/aio_sse_diagnostics.h
#ifndef VALK_AIO_SSE_DIAGNOSTICS_H
#define VALK_AIO_SSE_DIAGNOSTICS_H

#include "aio.h"
#include "memory.h"
#include "gc.h"

// SSE connection context for memory diagnostics
typedef struct valk_sse_diag_conn {
  valk_aio_handle_t *handle;      // TCP connection handle
  uv_timer_t timer;               // Push timer (100ms)
  uint64_t last_event_id;         // For resumption
  valk_aio_system_t *aio_system;  // AIO system reference
  char write_buffer[16384];       // Event buffer
  bool active;                    // Connection alive
} valk_sse_diag_conn_t;

// Memory snapshot for SSE transmission
typedef struct valk_mem_snapshot {
  // Slab bitmaps (hex-encoded)
  struct {
    char *name;
    uint8_t *bitmap;      // Actual bitmap data
    size_t bitmap_bytes;  // Size of bitmap
    size_t total_slots;
    size_t used_slots;
    size_t overflow_count;
  } slabs[8];
  size_t slab_count;

  // Arena gauges
  struct {
    char *name;
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
```

### 2.2 Slab Bitmap Generation

**File:** `src/aio_sse_diagnostics.c:50-120`

```c
// Walk Treiber stack to generate actual bitmap
// Returns heap-allocated bitmap, caller must free
static uint8_t* slab_to_bitmap(valk_slab_t *slab, size_t *out_bytes) {
  size_t total_slots = slab->item_count;
  size_t bitmap_bytes = (total_slots + 7) / 8;
  uint8_t *bitmap = calloc(bitmap_bytes, 1);

  // Start with all slots marked as USED (1)
  memset(bitmap, 0xFF, bitmap_bytes);

  // Walk free list and mark slots as FREE (0)
  // The slab uses a Treiber stack with versioned pointers
  valk_slab_item_t *item = (valk_slab_item_t*)(slab->head & ~0xFFFFULL); // Mask version

  while (item != NULL) {
    // Calculate slot index from pointer
    size_t slot_idx = ((uintptr_t)item - (uintptr_t)slab->items) / slab->item_size;

    if (slot_idx < total_slots) {
      // Clear bit (mark as free)
      bitmap[slot_idx / 8] &= ~(1 << (slot_idx % 8));
    }

    // Get next in free list (also versioned)
    item = (valk_slab_item_t*)(item->next & ~0xFFFFULL);
  }

  *out_bytes = bitmap_bytes;
  return bitmap;
}

// Convert bitmap to hex string
static void bitmap_to_hex(const uint8_t *bitmap, size_t bytes, char *hex_out) {
  static const char hex_chars[] = "0123456789abcdef";
  for (size_t i = 0; i < bytes; i++) {
    hex_out[i * 2]     = hex_chars[(bitmap[i] >> 4) & 0x0F];
    hex_out[i * 2 + 1] = hex_chars[bitmap[i] & 0x0F];
  }
  hex_out[bytes * 2] = '\0';
}
```

### 2.3 SSE Timer Callback

**File:** `src/aio_sse_diagnostics.c:150-250`

```c
// Called every 100ms to push memory state
static void sse_push_memory_state(uv_timer_t *timer) {
  valk_sse_diag_conn_t *conn = (valk_sse_diag_conn_t*)timer->data;

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
    VALK_LOG_ERROR("Failed to format SSE memory event");
    return;
  }

  // Send event via HTTP/2 DATA frame
  // Note: For HTTP/1.1, use raw TCP write
  // For HTTP/2, use nghttp2_submit_data
  uv_buf_t buf = uv_buf_init(conn->write_buffer, len);
  uv_write_t *req = malloc(sizeof(uv_write_t));
  req->data = conn;

  int result = uv_write(req, (uv_stream_t*)&conn->handle->uv.tcp,
                        &buf, 1, on_sse_write_complete);

  if (result < 0) {
    VALK_LOG_ERROR("SSE write failed: %s", uv_strerror(result));
    conn->active = false;
    free(req);
  }

  // Free snapshot allocations
  for (size_t i = 0; i < snapshot.slab_count; i++) {
    free(snapshot.slabs[i].bitmap);
  }
}
```

### 2.4 SSE Event Format

**Wire format for memory updates:**

```
event: memory
id: 1733580000123
data: {"slabs":[
data:   {"name":"tcp_buffers","bitmap":"ff00ff00...","total":200,"used":174,"overflow":3},
data:   {"name":"handles","bitmap":"...","total":2056,"used":247,"overflow":0},
data:   {"name":"stream_arenas","bitmap":"...","total":64,"used":18,"overflow":0},
data:   {"name":"http_servers","bitmap":"07","total":3,"used":1,"overflow":0},
data:   {"name":"http_clients","bitmap":"00","total":3,"used":0,"overflow":0},
data:   {"name":"lval","bitmap":"...","total":262144,"used":117965,"overflow":0}
data: ],"arenas":[
data:   {"name":"scratch","used":940000,"capacity":4194304,"hwm":2854912,"overflow":0},
data:   {"name":"stream_1","used":52428800,"capacity":67108864,"hwm":61341696,"overflow":2}
data: ],"gc":{"allocated":5242880,"peak":8388608,"threshold":10485760,"cycles":42}}

```

**Key design decisions:**
- Use hex-encoded bitmaps (2x smaller than base64)
- Include overflow counts for leak/pressure detection
- Include high water mark (HWM) for arena gauges
- Single event type with full state (simplifies client)

---

## 3. Lisp Integration

### 3.1 Route Handler

**File:** `src/modules/aio/debug.valk` (modified)

```lisp
; Add new diagnostic endpoint
(fun {aio/diagnostics-memory-stream sys req}
  "Handle SSE stream for memory diagnostics"
  {
    ; Set SSE headers
    (= {headers} (plist/new
      {:content-type "text/event-stream; charset=utf-8"}
      {:cache-control "no-cache"}
      {:connection "keep-alive"}
      {:x-accel-buffering "no"}))

    ; Return special :sse-stream response type
    ; This signals the HTTP handler to:
    ; 1. Send headers immediately
    ; 2. Keep connection open
    ; 3. Start SSE timer
    `{:status "200"
      :headers ,headers
      :body-type :sse-stream
      :sse-handler :memory-diagnostics}
  })

; Route dispatch (modify existing)
(fun {aio/debug-handle-request sys req}
  {
    (= {path} (plist/get req (head {:path})))
    (select
      ; ... existing routes ...
      {(== path "/api/diagnostics/memory/stream")
       (aio/diagnostics-memory-stream sys req)}
      {otherwise nil})
  })
```

### 3.2 C Builtin for SSE Setup

**File:** `src/parser.c` (add new builtin)

```c
// Line ~3950: Add builtin for SSE stream initialization
VALK_DEF_BUILTIN(builtin_aio_sse_memory_start) {
  VALK_ASSERT_NUM_ARGS("aio/sse-memory-start", args, 1);
  VALK_ASSERT_ARG_TYPE("aio/sse-memory-start", args, 0, LVAL_HANDLE);

  valk_async_handle_t *async_handle = LVAL_HANDLE(args->children[0]);
  valk_aio_handle_t *conn = (valk_aio_handle_t*)async_handle->conn;

  if (!conn || conn->kind != VALK_HNDL_HTTP_CONN) {
    return valk_lval_err("Invalid HTTP connection for SSE");
  }

  // Initialize SSE diagnostics stream
  valk_sse_diag_init(conn, g_aio_system);

  return valk_lval_sym(":ok");
}

// Register in builtins
// Line ~4280
{"aio/sse-memory-start", builtin_aio_sse_memory_start},
```

---

## 4. Frontend Implementation

### 4.1 EventSource Connection

**File:** `src/modules/aio/debug/script.js` (add new section)

```javascript
// Memory Diagnostics SSE Connection
// ================================

class MemoryDiagnostics {
  constructor() {
    this.eventSource = null;
    this.reconnectAttempts = 0;
    this.maxReconnectAttempts = 10;
    this.lastEventId = null;

    // DOM references
    this.grids = {};
    this.arenaGauges = {};

    // State for delta detection
    this.previousState = {};
  }

  connect() {
    const url = '/api/diagnostics/memory/stream';
    this.eventSource = new EventSource(url);

    this.eventSource.addEventListener('memory', (e) => {
      this.lastEventId = e.lastEventId;
      this.handleMemoryUpdate(JSON.parse(e.data));
    });

    this.eventSource.onopen = () => {
      this.reconnectAttempts = 0;
      this.updateConnectionStatus(true);
      console.log('[MemDiag] SSE connected');
    };

    this.eventSource.onerror = (e) => {
      if (this.eventSource.readyState === EventSource.CLOSED) {
        this.updateConnectionStatus(false);
        this.scheduleReconnect();
      }
    };
  }

  scheduleReconnect() {
    if (this.reconnectAttempts >= this.maxReconnectAttempts) {
      console.error('[MemDiag] Max reconnection attempts reached');
      return;
    }

    this.reconnectAttempts++;
    const delay = Math.min(1000 * Math.pow(2, this.reconnectAttempts), 30000);
    console.log(`[MemDiag] Reconnecting in ${delay}ms...`);

    setTimeout(() => {
      if (this.eventSource) {
        this.eventSource.close();
      }
      this.connect();
    }, delay);
  }

  updateConnectionStatus(connected) {
    const dot = document.querySelector('.sse-dot');
    if (dot) {
      dot.style.background = connected ? 'var(--success)' : 'var(--error)';
    }
  }

  handleMemoryUpdate(data) {
    // Update slab grids
    if (data.slabs) {
      data.slabs.forEach(slab => this.updateSlabGrid(slab));
    }

    // Update arena gauges
    if (data.arenas) {
      data.arenas.forEach(arena => this.updateArenaGauge(arena));
    }

    // Update GC stats
    if (data.gc) {
      this.updateGCStats(data.gc);
    }
  }

  updateSlabGrid(slab) {
    const gridId = `${slab.name.replace(/_/g, '-')}-grid`;
    const grid = document.getElementById(gridId);
    if (!grid) return;

    // Convert hex bitmap to bit array
    const bitmap = this.hexToBitArray(slab.bitmap);
    const cells = grid.children;

    // Track previous state for flash animation
    const prevKey = `slab_${slab.name}`;
    const prevBitmap = this.previousState[prevKey] || [];

    requestAnimationFrame(() => {
      // For large slabs, use aggregation
      if (slab.total > 500) {
        this.renderAggregatedGrid(grid, bitmap, slab.total, prevBitmap);
      } else {
        this.renderDirectGrid(grid, bitmap, prevBitmap);
      }
    });

    this.previousState[prevKey] = bitmap;

    // Update stats
    const statsEl = grid.closest('.memory-slab-panel')?.querySelector('.slab-stats');
    if (statsEl) {
      const usedCount = statsEl.querySelector('.used-count');
      if (usedCount) usedCount.textContent = slab.used.toLocaleString();

      const overflowEl = statsEl.querySelector('.overflow-warning');
      if (overflowEl) {
        if (slab.overflow > 0) {
          overflowEl.textContent = `⚠ ${slab.overflow} overflows`;
          overflowEl.style.display = '';
        } else {
          overflowEl.style.display = 'none';
        }
      }
    }
  }

  renderDirectGrid(grid, bitmap, prevBitmap) {
    // Ensure grid has correct number of cells
    while (grid.children.length < bitmap.length) {
      const cell = document.createElement('div');
      cell.className = 'slab-cell free';
      grid.appendChild(cell);
    }
    while (grid.children.length > bitmap.length) {
      grid.removeChild(grid.lastChild);
    }

    // Update cells with flash on change
    for (let i = 0; i < bitmap.length; i++) {
      const cell = grid.children[i];
      const newState = bitmap[i] ? 'used' : 'free';
      const oldState = prevBitmap[i] ? 'used' : 'free';

      if (newState !== oldState) {
        // State changed - flash animation
        cell.className = 'slab-cell flash';
        setTimeout(() => {
          cell.className = `slab-cell ${newState}`;
        }, 300);
      } else if (!cell.classList.contains(newState)) {
        cell.className = `slab-cell ${newState}`;
      }
    }
  }

  renderAggregatedGrid(grid, bitmap, totalSlots, prevBitmap) {
    // For large slabs, aggregate to displayable size
    const gridCols = 32;
    const gridRows = 32;
    const cellsPerSlot = Math.ceil(totalSlots / (gridCols * gridRows));

    const aggregated = new Array(gridCols * gridRows).fill(0);
    const prevAggregated = new Array(gridCols * gridRows).fill(0);

    for (let i = 0; i < bitmap.length; i++) {
      const aggIdx = Math.floor(i / cellsPerSlot);
      if (aggIdx < aggregated.length) {
        aggregated[aggIdx] += bitmap[i] ? 1 : 0;
        prevAggregated[aggIdx] += (prevBitmap[i] || 0) ? 1 : 0;
      }
    }

    // Normalize to 0-1
    const threshold = cellsPerSlot / 2;
    for (let i = 0; i < aggregated.length; i++) {
      aggregated[i] = aggregated[i] > threshold ? 1 : 0;
      prevAggregated[i] = prevAggregated[i] > threshold ? 1 : 0;
    }

    this.renderDirectGrid(grid, aggregated, prevAggregated);
  }

  updateArenaGauge(arena) {
    const gauge = document.querySelector(`[data-arena="${arena.name}"]`);
    if (!gauge) return;

    const percentage = (arena.used / arena.capacity) * 100;
    const hwmPercentage = (arena.hwm / arena.capacity) * 100;

    // Update bar
    const bar = gauge.querySelector('.arena-bar');
    if (bar) {
      bar.style.width = `${percentage}%`;

      // Color based on usage
      bar.className = 'arena-bar';
      if (percentage >= 90) {
        bar.classList.add('critical');
      } else if (percentage >= 70) {
        bar.classList.add('warning');
      } else {
        bar.classList.add('healthy');
      }
    }

    // Update high water mark
    const hwm = gauge.querySelector('.arena-hwm');
    if (hwm) {
      hwm.style.left = `${hwmPercentage}%`;
    }

    // Update label
    const label = gauge.querySelector('.arena-label');
    if (label) {
      const usedStr = this.formatBytes(arena.used);
      const capacityStr = this.formatBytes(arena.capacity);
      label.innerHTML = `<span class="pct">${percentage.toFixed(0)}%</span> &mdash; ${usedStr} / ${capacityStr}`;
    }

    // Update overflow indicator
    if (arena.overflow > 0) {
      gauge.classList.add('has-overflow');
    } else {
      gauge.classList.remove('has-overflow');
    }
  }

  updateGCStats(gc) {
    // Update GC panel if it exists
    const gcPanel = document.querySelector('.gc-stats-panel');
    if (!gcPanel) return;

    const allocated = gcPanel.querySelector('[data-gc="allocated"]');
    const peak = gcPanel.querySelector('[data-gc="peak"]');
    const cycles = gcPanel.querySelector('[data-gc="cycles"]');

    if (allocated) allocated.textContent = this.formatBytes(gc.allocated);
    if (peak) peak.textContent = this.formatBytes(gc.peak);
    if (cycles) cycles.textContent = gc.cycles.toLocaleString();
  }

  // Utility functions
  hexToBitArray(hex) {
    const bits = [];
    for (let i = 0; i < hex.length; i += 2) {
      const byte = parseInt(hex.substr(i, 2), 16);
      for (let b = 7; b >= 0; b--) {
        bits.push((byte >> b) & 1);
      }
    }
    return bits;
  }

  formatBytes(bytes) {
    if (bytes < 1024) return bytes + 'B';
    if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + 'KB';
    if (bytes < 1024 * 1024 * 1024) return (bytes / (1024 * 1024)).toFixed(1) + 'MB';
    return (bytes / (1024 * 1024 * 1024)).toFixed(1) + 'GB';
  }

  disconnect() {
    if (this.eventSource) {
      this.eventSource.close();
      this.eventSource = null;
    }
  }
}

// Initialize on page load
var memoryDiagnostics = null;
document.addEventListener('DOMContentLoaded', () => {
  memoryDiagnostics = new MemoryDiagnostics();
  memoryDiagnostics.connect();
});
```

### 4.2 HTML Structure

**File:** `src/modules/aio/debug/body.html` (add new section)

```html
<!-- Memory Diagnostics Section (SSE-powered) -->
<section class="panel-section memory-diagnostics-section">
  <div class="section-header">
    <div class="section-icon">MEM</div>
    <h2 class="section-title">Memory Diagnostics</h2>
    <span class="section-subtitle">Slab Allocators and Arenas (SSE Live)</span>
    <div class="section-badges">
      <span class="section-badge">
        <span class="sse-dot"></span> Live Streaming
      </span>
      <span class="section-badge">100ms refresh</span>
    </div>
  </div>

  <!-- Slab Grid -->
  <div class="memory-slab-grid">
    <!-- TCP Buffers -->
    <div class="memory-slab-panel" id="tcp-buffers-panel">
      <div class="slab-header">
        <span class="slab-name">TCP Buffers</span>
        <span class="slab-badge">0% used</span>
      </div>
      <div class="slab-canvas">
        <div class="slab-grid" id="tcp-buffers-grid"
             style="grid-template-columns: repeat(20, 1fr);"></div>
      </div>
      <div class="slab-stats">
        <span><span class="used-count">0</span> / 200 slots</span>
        <span class="overflow-warning" style="display:none"></span>
      </div>
    </div>

    <!-- Handles -->
    <div class="memory-slab-panel" id="handles-panel">
      <div class="slab-header">
        <span class="slab-name">Handles</span>
        <span class="slab-badge">0% used</span>
      </div>
      <div class="slab-canvas">
        <div class="slab-grid" id="handles-grid"
             style="grid-template-columns: repeat(32, 1fr);"></div>
      </div>
      <div class="slab-stats">
        <span><span class="used-count">0</span> / 2056 slots</span>
        <span class="overflow-warning" style="display:none"></span>
      </div>
    </div>

    <!-- Stream Arenas -->
    <div class="memory-slab-panel" id="stream-arenas-panel">
      <div class="slab-header">
        <span class="slab-name">Stream Arenas</span>
        <span class="slab-badge">0% used</span>
      </div>
      <div class="slab-canvas">
        <div class="slab-grid" id="stream-arenas-grid"
             style="grid-template-columns: repeat(8, 1fr);"></div>
      </div>
      <div class="slab-stats">
        <span><span class="used-count">0</span> / 64 slots</span>
        <span class="overflow-warning" style="display:none"></span>
      </div>
    </div>

    <!-- HTTP Servers -->
    <div class="memory-slab-panel" id="http-servers-panel">
      <div class="slab-header">
        <span class="slab-name">HTTP Servers</span>
        <span class="slab-badge">0% used</span>
      </div>
      <div class="slab-canvas">
        <div class="slab-grid" id="http-servers-grid"
             style="grid-template-columns: repeat(3, 1fr); padding: 20px;"></div>
      </div>
      <div class="slab-stats">
        <span><span class="used-count">0</span> / 3 slots</span>
        <span class="overflow-warning" style="display:none"></span>
      </div>
    </div>

    <!-- HTTP Clients -->
    <div class="memory-slab-panel" id="http-clients-panel">
      <div class="slab-header">
        <span class="slab-name">HTTP Clients</span>
        <span class="slab-badge">0% used</span>
      </div>
      <div class="slab-canvas">
        <div class="slab-grid" id="http-clients-grid"
             style="grid-template-columns: repeat(3, 1fr); padding: 20px;"></div>
      </div>
      <div class="slab-stats">
        <span><span class="used-count">0</span> / 3 slots</span>
        <span class="overflow-warning" style="display:none"></span>
      </div>
    </div>

    <!-- LVAL Objects (GC Slab) -->
    <div class="memory-slab-panel" id="lval-panel">
      <div class="slab-header">
        <span class="slab-name">LVAL Objects</span>
        <span class="slab-badge">0% used</span>
      </div>
      <div class="slab-canvas">
        <div class="slab-grid" id="lval-grid"
             style="grid-template-columns: repeat(32, 1fr);"></div>
      </div>
      <div class="slab-stats">
        <span><span class="used-count">0</span> / 262,144 slots</span>
        <span class="overflow-warning" style="display:none"></span>
      </div>
    </div>
  </div>

  <!-- Arena Gauges -->
  <div class="memory-arena-section">
    <div class="arena-title">Arena Allocators</div>
    <div class="arena-list">
      <div class="arena-gauge" data-arena="scratch">
        <span class="arena-name">Scratch Arena</span>
        <div class="arena-track">
          <div class="arena-bar healthy" style="width: 0%;"></div>
          <div class="arena-hwm" style="left: 0%;"></div>
        </div>
        <span class="arena-label"><span class="pct">0%</span> &mdash; 0B / 0B</span>
      </div>
      <!-- Dynamic stream arenas added by JS -->
    </div>
  </div>

  <!-- Legend -->
  <div class="legend">
    <div class="legend-item">
      <div class="legend-dot free"></div>
      <span>Free slot</span>
    </div>
    <div class="legend-item">
      <div class="legend-dot used"></div>
      <span>Used slot</span>
    </div>
    <div class="legend-item">
      <div class="legend-dot flash"></div>
      <span>State change</span>
    </div>
    <div class="legend-item">
      <div class="legend-dot hwm"></div>
      <span>High water mark</span>
    </div>
  </div>
</section>
```

### 4.3 CSS Additions

**File:** `src/modules/aio/debug/style.css` (add new rules)

```css
/* Memory Diagnostics Section */
/* ========================= */

.memory-diagnostics-section {
  margin-top: var(--space-lg);
}

.memory-slab-grid {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: var(--space-md);
  margin-bottom: var(--space-lg);
}

.memory-slab-panel {
  background: var(--card-bg);
  border: 1px solid var(--border);
  border-radius: var(--radius-md);
  padding: var(--space-md);
  display: flex;
  flex-direction: column;
}

.memory-slab-panel.critical {
  border-color: var(--color-warning);
}

.slab-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: var(--space-sm);
}

.slab-name {
  font-size: 12px;
  font-weight: 600;
  color: var(--text-muted);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}

.slab-badge {
  font-size: 10px;
  padding: 2px 6px;
  border-radius: 4px;
  background: var(--bg-darker);
  color: var(--text-muted);
}

.slab-badge.warning {
  background: rgba(245, 158, 11, 0.2);
  color: var(--color-warning);
}

.slab-canvas {
  flex: 1;
  min-height: 100px;
  border-radius: var(--radius-sm);
  background: var(--bg-darker);
  position: relative;
  overflow: hidden;
}

.slab-grid {
  display: grid;
  gap: 1px;
  padding: 4px;
  height: 100%;
}

.slab-cell {
  border-radius: 2px;
  transition: background-color 100ms ease-out;
}

.slab-cell.free {
  background: var(--bg-darker);
}

.slab-cell.used {
  background: var(--color-ok);
}

.slab-cell.flash {
  background: var(--color-warning);
  animation: slab-flash 300ms ease-out;
}

@keyframes slab-flash {
  0% { background: var(--color-warning); }
  100% { background: var(--color-ok); }
}

.slab-stats {
  margin-top: var(--space-sm);
  display: flex;
  justify-content: space-between;
  align-items: center;
  font-size: 11px;
  color: var(--text-muted);
}

.slab-stats .used-count {
  color: var(--color-ok);
  font-weight: 600;
}

.slab-stats .overflow-warning {
  color: var(--color-error);
  font-size: 10px;
}

/* Arena Gauges */
.memory-arena-section {
  background: var(--card-bg);
  border: 1px solid var(--border);
  border-radius: var(--radius-md);
  padding: var(--space-md);
}

.arena-title {
  font-size: 12px;
  font-weight: 600;
  color: var(--text-muted);
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-bottom: var(--space-md);
}

.arena-list {
  display: flex;
  flex-direction: column;
  gap: var(--space-sm);
}

.arena-gauge {
  display: flex;
  align-items: center;
  gap: var(--space-md);
  padding: var(--space-sm);
  background: var(--bg-darker);
  border-radius: var(--radius-sm);
}

.arena-gauge.has-overflow {
  border: 1px solid var(--color-warning);
}

.arena-name {
  min-width: 120px;
  font-size: 12px;
  font-weight: 500;
}

.arena-track {
  flex: 1;
  height: 12px;
  background: var(--bg);
  border-radius: 6px;
  position: relative;
  overflow: hidden;
}

.arena-bar {
  height: 100%;
  border-radius: 6px;
  transition: width 100ms ease-out, background-color 100ms ease-out;
}

.arena-bar.healthy {
  background: linear-gradient(90deg, var(--color-ok), #16a34a);
}

.arena-bar.warning {
  background: linear-gradient(90deg, var(--color-warning), #d97706);
}

.arena-bar.critical {
  background: linear-gradient(90deg, var(--color-error), #dc2626);
}

.arena-hwm {
  position: absolute;
  top: 0;
  bottom: 0;
  width: 2px;
  background: var(--color-warning);
  opacity: 0.8;
}

.arena-hwm::after {
  content: 'HWM';
  position: absolute;
  top: -16px;
  left: 50%;
  transform: translateX(-50%);
  font-size: 8px;
  color: var(--color-warning);
  white-space: nowrap;
}

.arena-label {
  min-width: 140px;
  font-size: 11px;
  color: var(--text-muted);
  text-align: right;
}

.arena-label .pct {
  color: var(--text);
  font-weight: 600;
}

/* Legend */
.legend {
  display: flex;
  gap: var(--space-lg);
  margin-top: var(--space-lg);
  padding-top: var(--space-md);
  border-top: 1px solid var(--border);
}

.legend-item {
  display: flex;
  align-items: center;
  gap: var(--space-xs);
  font-size: 11px;
  color: var(--text-muted);
}

.legend-dot {
  width: 10px;
  height: 10px;
  border-radius: 2px;
}

.legend-dot.free {
  background: var(--bg-darker);
  border: 1px solid var(--border);
}
.legend-dot.used { background: var(--color-ok); }
.legend-dot.flash { background: var(--color-warning); }
.legend-dot.hwm {
  background: var(--color-warning);
  width: 2px;
  height: 12px;
}

/* Responsive */
@media (max-width: 900px) {
  .memory-slab-grid {
    grid-template-columns: repeat(2, 1fr);
  }
}

@media (max-width: 600px) {
  .memory-slab-grid {
    grid-template-columns: 1fr;
  }
}

/* SSE Connection Indicator */
.sse-dot {
  width: 6px;
  height: 6px;
  border-radius: 50%;
  background: var(--color-ok);
  animation: sse-pulse 2s infinite;
}

@keyframes sse-pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.5; }
}
```

---

## 5. Implementation Steps

### Phase 1: Core Infrastructure (Backend)

1. **Create `src/aio_sse_diagnostics.h`** - Header with structures
2. **Create `src/aio_sse_diagnostics.c`** - Implementation:
   - `valk_sse_diag_init()` - Initialize SSE connection
   - `slab_to_bitmap()` - Walk Treiber stack for actual bitmap
   - `sse_push_memory_state()` - Timer callback (100ms)
   - `valk_mem_snapshot_to_sse()` - Format JSON event
3. **Modify `src/aio_uv.c`**:
   - Add route handler for `/api/diagnostics/memory/stream`
   - Integrate SSE connection setup
4. **Modify `Makefile`**:
   - Add `aio_sse_diagnostics.o` to build

### Phase 2: Lisp Integration

5. **Modify `src/modules/aio/debug.valk`**:
   - Add route for new endpoint
   - Add `:sse-stream` response type handling
6. **Modify `src/parser.c`**:
   - Add `aio/sse-memory-start` builtin

### Phase 3: Frontend

7. **Modify `src/modules/aio/debug/body.html`**:
   - Add Memory Diagnostics section
   - Replace old connection pool grid
8. **Modify `src/modules/aio/debug/script.js`**:
   - Add `MemoryDiagnostics` class
   - EventSource connection handling
   - Grid rendering with flash animations
9. **Modify `src/modules/aio/debug/style.css`**:
   - Add slab grid styles
   - Add arena gauge styles
   - Add legend and responsive rules

### Phase 4: Testing & Polish

10. **Test with load**:
    - Start HTTP server
    - Generate load to see slab activity
    - Verify overflow counters work
    - Check high water mark tracking
11. **Performance validation**:
    - Verify 100ms push doesn't impact server performance
    - Check browser rendering stays under 16.7ms/frame

---

## 6. File Changes Summary

| File | Action | Description |
|------|--------|-------------|
| `src/aio_sse_diagnostics.h` | **NEW** | SSE diagnostics header |
| `src/aio_sse_diagnostics.c` | **NEW** | SSE diagnostics implementation |
| `src/aio_uv.c` | MODIFY | Add SSE route, include new header |
| `src/parser.c` | MODIFY | Add `aio/sse-memory-start` builtin |
| `src/modules/aio/debug.valk` | MODIFY | Add route handler |
| `src/modules/aio/debug/body.html` | MODIFY | Add memory diagnostics section |
| `src/modules/aio/debug/script.js` | MODIFY | Add `MemoryDiagnostics` class |
| `src/modules/aio/debug/style.css` | MODIFY | Add memory visualization styles |
| `Makefile` | MODIFY | Add new object file |

---

## 7. Visual Design Recommendations

Based on design expert consultation:

### Color Scheme (from existing dashboard)
- **Free slots**: `#020617` (dark, from `--bg-darker`)
- **Used slots**: `#22c55e` (green, from `--color-ok`)
- **Flash/change**: `#f59e0b` (orange, from `--color-warning`)
- **Overflow/error**: `#ef4444` (red, from `--color-error`)

### Grid Sizing
- Small slabs (<10 items): Large cells with padding
- Medium slabs (10-500): Standard 1px gap grid
- Large slabs (>500): Aggregated view or Canvas rendering

### Arena Gauge Colors
- 0-70%: Green gradient (healthy)
- 70-90%: Yellow gradient (warning)
- 90-100%: Red gradient (critical)

### Animation Timing
- Flash duration: 300ms
- Gauge transitions: 100ms
- SSE reconnection: Exponential backoff (1s → 30s max)

---

## 8. Testing and Validation Plan

### 8.1 Unit Tests (C Backend)

**File:** `test/test_sse_diagnostics.c` (new)

```c
// Test slab bitmap generation
void test_slab_to_bitmap_empty(void) {
  // Create slab with all slots free
  valk_slab_t *slab = valk_slab_new(64, 100);
  size_t bitmap_bytes;
  uint8_t *bitmap = slab_to_bitmap(slab, &bitmap_bytes);

  // All bits should be 0 (free)
  ASSERT_EQ(bitmap_bytes, 13); // ceil(100/8)
  for (size_t i = 0; i < bitmap_bytes; i++) {
    ASSERT_EQ(bitmap[i], 0x00);
  }
  free(bitmap);
  valk_slab_free(slab);
}

void test_slab_to_bitmap_full(void) {
  // Create slab and allocate all slots
  valk_slab_t *slab = valk_slab_new(64, 8);
  void *items[8];
  for (int i = 0; i < 8; i++) {
    items[i] = valk_slab_aquire(slab);
  }

  size_t bitmap_bytes;
  uint8_t *bitmap = slab_to_bitmap(slab, &bitmap_bytes);

  // All bits should be 1 (used)
  ASSERT_EQ(bitmap_bytes, 1);
  ASSERT_EQ(bitmap[0], 0xFF);

  free(bitmap);
  for (int i = 0; i < 8; i++) {
    valk_slab_release_ptr(slab, items[i]);
  }
  valk_slab_free(slab);
}

void test_slab_to_bitmap_partial(void) {
  // Create slab, allocate slots 0, 2, 4, 6
  valk_slab_t *slab = valk_slab_new(64, 8);
  void *items[4];
  for (int i = 0; i < 4; i++) {
    items[i] = valk_slab_aquire(slab);
  }
  // Release odd slots
  valk_slab_release_ptr(slab, items[1]);
  valk_slab_release_ptr(slab, items[3]);

  size_t bitmap_bytes;
  uint8_t *bitmap = slab_to_bitmap(slab, &bitmap_bytes);

  // Bits 0, 2 should be 1 (used), bits 1, 3 should be 0 (free)
  // Pattern: 0b10100000 = 0xA0 (assuming big-endian bit order)
  ASSERT_EQ(bitmap[0] & 0xF0, 0xA0);

  free(bitmap);
  valk_slab_release_ptr(slab, items[0]);
  valk_slab_release_ptr(slab, items[2]);
  valk_slab_free(slab);
}

void test_bitmap_to_hex(void) {
  uint8_t bitmap[] = {0xDE, 0xAD, 0xBE, 0xEF};
  char hex[9];
  bitmap_to_hex(bitmap, 4, hex);
  ASSERT_STREQ(hex, "deadbeef");
}

void test_mem_snapshot_collect(void) {
  // Initialize AIO system
  valk_aio_system_t *aio = valk_aio_start();

  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, aio);

  // Verify all expected slabs are present
  ASSERT_GE(snapshot.slab_count, 5); // At least 5 slabs
  ASSERT_GE(snapshot.arena_count, 1); // At least scratch arena

  // Verify TCP buffers slab
  bool found_tcp = false;
  for (size_t i = 0; i < snapshot.slab_count; i++) {
    if (strcmp(snapshot.slabs[i].name, "tcp_buffers") == 0) {
      found_tcp = true;
      ASSERT_GT(snapshot.slabs[i].total_slots, 0);
      ASSERT_LE(snapshot.slabs[i].used_slots, snapshot.slabs[i].total_slots);
    }
  }
  ASSERT_TRUE(found_tcp);

  // Cleanup
  for (size_t i = 0; i < snapshot.slab_count; i++) {
    free(snapshot.slabs[i].bitmap);
  }
  valk_aio_stop();
}

void test_sse_event_format(void) {
  valk_mem_snapshot_t snapshot = {0};
  // Setup minimal snapshot
  snapshot.slab_count = 1;
  snapshot.slabs[0].name = "test";
  snapshot.slabs[0].bitmap = (uint8_t*)"\xFF";
  snapshot.slabs[0].bitmap_bytes = 1;
  snapshot.slabs[0].total_slots = 8;
  snapshot.slabs[0].used_slots = 8;
  snapshot.slabs[0].overflow_count = 0;

  char buf[4096];
  int len = valk_mem_snapshot_to_sse(&snapshot, buf, sizeof(buf), 12345);

  ASSERT_GT(len, 0);
  ASSERT_CONTAINS(buf, "event: memory");
  ASSERT_CONTAINS(buf, "id: 12345");
  ASSERT_CONTAINS(buf, "\"name\":\"test\"");
  ASSERT_CONTAINS(buf, "\"bitmap\":\"ff\"");
}
```

**Run with:** `make test_sse_diagnostics && ./build/test_sse_diagnostics`

### 8.2 Integration Tests (SSE Endpoint)

**File:** `test/test_sse_integration.valk` (new)

```lisp
; Test SSE endpoint responds with correct headers
(test "SSE endpoint returns event-stream content type"
  (do
    (= {client} (http-client/connect "localhost" 8080))
    (= {res} (http-client/get client "/api/diagnostics/memory/stream"))
    (assert (== (plist/get res {:content-type}) "text/event-stream; charset=utf-8"))
    (http-client/close client)))

; Test SSE events are valid JSON
(test "SSE events contain valid JSON data"
  (do
    (= {client} (http-client/connect "localhost" 8080))
    (= {stream} (http-client/get-stream client "/api/diagnostics/memory/stream"))
    ; Read first event
    (= {event} (stream/read-until stream "\n\n"))
    ; Extract data line
    (= {data-line} (string/find event "data: "))
    (assert (not (nil? data-line)))
    ; Parse JSON
    (= {json} (json/parse (string/substr data-line 6)))
    (assert (plist? json))
    (assert (list? (plist/get json {:slabs})))
    (http-client/close client)))

; Test SSE connection stays open
(test "SSE connection remains open for continuous updates"
  (do
    (= {client} (http-client/connect "localhost" 8080))
    (= {stream} (http-client/get-stream client "/api/diagnostics/memory/stream"))
    ; Read multiple events
    (= {event1} (stream/read-until stream "\n\n"))
    (aio/sleep 150) ; Wait for next push
    (= {event2} (stream/read-until stream "\n\n"))
    (assert (not (== event1 event2))) ; Event IDs should differ
    (http-client/close client)))
```

**Run with:** `make repl` then `(load "test/test_sse_integration.valk")`

### 8.3 Frontend Tests (JavaScript)

**File:** `test/test_memory_diagnostics.js` (new, runs in browser console)

```javascript
// Test hex to bit array conversion
function testHexToBitArray() {
  const md = new MemoryDiagnostics();

  // Test simple case
  const bits1 = md.hexToBitArray('ff');
  console.assert(bits1.length === 8, 'ff should produce 8 bits');
  console.assert(bits1.every(b => b === 1), 'ff should be all 1s');

  // Test zero
  const bits2 = md.hexToBitArray('00');
  console.assert(bits2.every(b => b === 0), '00 should be all 0s');

  // Test pattern
  const bits3 = md.hexToBitArray('a5'); // 10100101
  console.assert(bits3.join('') === '10100101', 'a5 should be 10100101');

  console.log('✓ testHexToBitArray passed');
}

// Test bytes formatting
function testFormatBytes() {
  const md = new MemoryDiagnostics();

  console.assert(md.formatBytes(0) === '0B');
  console.assert(md.formatBytes(512) === '512B');
  console.assert(md.formatBytes(1024) === '1.0KB');
  console.assert(md.formatBytes(1536) === '1.5KB');
  console.assert(md.formatBytes(1048576) === '1.0MB');
  console.assert(md.formatBytes(67108864) === '64.0MB');

  console.log('✓ testFormatBytes passed');
}

// Test grid rendering performance
function testGridRenderingPerformance() {
  const md = new MemoryDiagnostics();
  const grid = document.createElement('div');
  grid.id = 'test-grid';
  document.body.appendChild(grid);

  // Generate large bitmap (262144 slots aggregated to 1024)
  const largeBitmap = new Array(262144).fill(0).map(() => Math.random() > 0.5 ? 1 : 0);

  const start = performance.now();
  md.renderAggregatedGrid(grid, largeBitmap, 262144, []);
  const elapsed = performance.now() - start;

  console.assert(elapsed < 16.7, `Render took ${elapsed}ms, should be <16.7ms for 60fps`);

  document.body.removeChild(grid);
  console.log(`✓ testGridRenderingPerformance passed (${elapsed.toFixed(2)}ms)`);
}

// Test flash animation triggers on state change
function testFlashAnimation() {
  const md = new MemoryDiagnostics();
  const grid = document.createElement('div');
  grid.id = 'flash-test-grid';
  document.body.appendChild(grid);

  // Initial state: all free
  const bitmap1 = [0, 0, 0, 0];
  md.renderDirectGrid(grid, bitmap1, []);

  // State change: slot 1 becomes used
  const bitmap2 = [0, 1, 0, 0];
  md.renderDirectGrid(grid, bitmap2, bitmap1);

  const cell = grid.children[1];
  console.assert(cell.classList.contains('flash'), 'Cell should have flash class');

  setTimeout(() => {
    console.assert(!cell.classList.contains('flash'), 'Flash should be removed after 300ms');
    console.assert(cell.classList.contains('used'), 'Cell should be marked used');
    document.body.removeChild(grid);
    console.log('✓ testFlashAnimation passed');
  }, 350);
}

// Run all tests
function runFrontendTests() {
  console.log('Running frontend tests...');
  testHexToBitArray();
  testFormatBytes();
  testGridRenderingPerformance();
  testFlashAnimation();
}

// Auto-run if in test mode
if (window.location.search.includes('test=1')) {
  document.addEventListener('DOMContentLoaded', runFrontendTests);
}
```

### 8.4 Load Testing

**Script:** `test/load_test_sse.sh`

```bash
#!/bin/bash
# Load test for SSE endpoint

SERVER="http://localhost:8080"
ENDPOINT="/api/diagnostics/memory/stream"
DURATION=60  # seconds
CONNECTIONS=10

echo "=== SSE Memory Diagnostics Load Test ==="
echo "Server: $SERVER"
echo "Duration: ${DURATION}s"
echo "Concurrent connections: $CONNECTIONS"
echo ""

# Start server if not running
if ! curl -s "$SERVER/health" > /dev/null 2>&1; then
  echo "Starting server..."
  make repl &
  sleep 3
fi

# Function to monitor SSE stream
monitor_sse() {
  local id=$1
  local count=0
  local start=$(date +%s)

  timeout $DURATION curl -sN "$SERVER$ENDPOINT" | while read -r line; do
    if [[ $line == "event: memory" ]]; then
      count=$((count + 1))
    fi
  done

  echo "Connection $id received $count events"
}

# Start concurrent connections
echo "Starting $CONNECTIONS SSE connections..."
for i in $(seq 1 $CONNECTIONS); do
  monitor_sse $i &
done

# Monitor server metrics during test
echo "Monitoring server performance..."
while true; do
  metrics=$(curl -s "$SERVER/debug/metrics")
  cpu=$(echo "$metrics" | jq -r '.vm_metrics.event_loop.events_processed // 0')
  mem=$(echo "$metrics" | jq -r '.vm_metrics.gc.heap_used // 0')
  echo "[$(date +%H:%M:%S)] Events: $cpu, Heap: $((mem / 1024 / 1024))MB"
  sleep 5
done &
MONITOR_PID=$!

# Wait for load test to complete
wait

# Stop monitor
kill $MONITOR_PID 2>/dev/null

echo ""
echo "=== Load Test Complete ==="
```

### 8.5 Visual Regression Testing

**Checklist for manual visual verification:**

| Component | Expected Behavior | Mockup Reference |
|-----------|-------------------|------------------|
| **Section Header** | Purple gradient icon "MEM", title "Memory Diagnostics", subtitle, badges | `mockup:479-489` |
| **SSE Dot** | Green pulsing dot when connected, red when disconnected | `mockup:107-118` |
| **TCP Buffers Grid** | 20×10 grid (200 cells), green=used, dark=free | `mockup:500` |
| **Handles Grid** | 25-column grid (scaled from 2056), 12% green | `mockup:515` |
| **Stream Arenas Grid** | 8×8 grid (64 cells) | `mockup:530` |
| **HTTP Servers Grid** | 3×1 grid with padding, large cells | `mockup:545` |
| **HTTP Clients Grid** | 3×1 grid with padding, large cells | `mockup:560` |
| **LVAL Grid** | 32×8 aggregated grid (from 262K) | `mockup:575` |
| **Flash Animation** | Orange→green 300ms on state change | `mockup:208-211` |
| **Critical Panel** | Warning border when >85% usage | `mockup:141-143` |
| **Overflow Warning** | Red text "⚠ N overflows" in stats | `mockup:227-230` |
| **Scratch Arena Gauge** | Green bar, HWM marker, percentage label | `mockup:588-595` |
| **Stream Arena Gauges** | Dynamic list, warning border if overflow | `mockup:596-611` |
| **Legend** | 4 items: Free, Used, Flash, HWM | `mockup:616-633` |
| **Responsive 900px** | 2-column grid | `mockup:457-460` |
| **Responsive 600px** | 1-column grid | `mockup:466-470` |

### 8.6 End-to-End Test Scenarios

**Scenario 1: Normal Operation**
1. Start server with `make repl`
2. Load `(aio/http-server 8080 handler)`
3. Open dashboard at `http://localhost:8080/debug/`
4. Verify SSE dot is green and pulsing
5. Verify all 6 slab grids are rendering
6. Verify scratch arena gauge shows current usage
7. Make HTTP requests to trigger activity
8. Verify flash animations occur on slab changes

**Scenario 2: High Memory Pressure**
1. Start server with small buffer pool: `(aio/start {:tcp_buffer_pool_size 20})`
2. Generate concurrent HTTP load: `ab -n 1000 -c 50 http://localhost:8080/`
3. Verify TCP Buffers panel shows warning badge
4. Verify TCP Buffers panel border turns orange
5. Verify overflow counter increases
6. Verify flash animations are frequent

**Scenario 3: Connection Resilience**
1. Open dashboard in browser
2. Verify SSE connected (green dot)
3. Stop server: `(aio/stop)`
4. Verify SSE dot turns red
5. Verify console shows "Reconnecting in Xms..."
6. Restart server
7. Verify automatic reconnection (green dot)
8. Verify data resumes updating

**Scenario 4: Large Slab Visualization (LVAL)**
1. Allocate many lval objects: `(map (fn {x} (list x x x)) (range 100000))`
2. Verify LVAL grid shows increased usage
3. Trigger GC: `(gc/collect)`
4. Verify LVAL grid shows decreased usage with flash
5. Verify aggregation maintains visual coherence

**Scenario 5: Arena High Water Mark**
1. Open dashboard
2. Note initial HWM position
3. Perform large evaluation: `(map identity (range 1000000))`
4. Verify HWM marker moves right (higher)
5. Verify HWM persists after scratch reset
6. HWM should represent peak usage since startup

### 8.7 Performance Benchmarks

| Metric | Target | Measurement Method |
|--------|--------|-------------------|
| SSE event size | <4KB | `curl -sN /api/.../stream \| head -100 \| wc -c` |
| Event generation time | <5ms | Server-side timing in `sse_push_memory_state()` |
| Client render time | <16.7ms | `performance.now()` in `handleMemoryUpdate()` |
| Memory overhead | <1MB | `/debug/metrics` heap delta with SSE active |
| Max concurrent SSE | 100 | Load test with 100 connections |
| Reconnection time | <5s | Measure with network throttling |

### 8.8 Browser Compatibility Matrix

| Browser | Version | Status | Notes |
|---------|---------|--------|-------|
| Chrome | 120+ | Required | Primary target |
| Firefox | 120+ | Required | EventSource API |
| Safari | 17+ | Required | SSE support |
| Edge | 120+ | Required | Chromium-based |
| Mobile Chrome | Android 10+ | Optional | Touch events |
| Mobile Safari | iOS 15+ | Optional | Limited testing |

---

## 9. Alignment with Mockup

### 9.1 CSS Variable Mapping

The mockup and plan now use the same CSS variables as the production dashboard (`src/modules/aio/debug/style.css`):

| Variable | Hex Value | Usage |
|----------|-----------|-------|
| `--color-ok` | `#3fb950` | Used slots, healthy arena bars |
| `--color-ok-muted` | `#238636` | Arena bar gradient end |
| `--color-warning` | `#d29922` | Flash animation, HWM marker |
| `--color-warning-muted` | `#9e6a03` | Warning arena bar gradient end |
| `--color-error` | `#f85149` | Overflow warnings |
| `--color-error-muted` | `#da3633` | Critical arena bar gradient end |
| `--color-info` | `#58a6ff` | Idle connection state (old grid) |
| `--color-purple` | `#a371f7` | Section icon gradient |
| `--bg-primary` | `#0d1117` | Body background, arena track |
| `--bg-secondary` | `#161b22` | Card/panel backgrounds |
| `--bg-tertiary` | `#1c2128` | Slab canvas, free slot background |
| `--border-default` | `#30363d` | Panel borders |
| `--text-primary` | `#f0f6fc` | Titles, percentage labels |
| `--text-secondary` | `#c9d1d9` | Body text |
| `--text-muted` | `#8b949e` | Labels, subtitles |

### 9.2 Grid Column Configurations

Match mockup exactly:

| Slab | Mockup Columns | Mockup Line | Implementation |
|------|----------------|-------------|----------------|
| TCP Buffers | `repeat(20, 1fr)` | 500 | 20×10 = 200 cells |
| Handles | `repeat(25, 1fr)` | 515 | 25×10 = 250 cells (scaled) |
| Stream Arenas | `repeat(8, 1fr)` | 530 | 8×8 = 64 cells |
| HTTP Servers | `repeat(3, 1fr); padding: 20px` | 545 | 3×1 with padding |
| HTTP Clients | `repeat(3, 1fr); padding: 20px` | 560 | 3×1 with padding |
| LVAL Objects | `repeat(32, 1fr)` | 575 | 32×8 = 256 cells (aggregated) |

### 9.3 Animation Specifications

From mockup (`static/mockup-memory-diagnostics.html`):

```css
/* Flash animation - line 208-211 */
@keyframes flash {
  0% { background: var(--warning); }   /* #f59e0b */
  100% { background: var(--success); } /* #22c55e */
}
.slab-cell.flash {
  animation: flash 300ms ease-out;
}

/* SSE pulse - line 115-118 */
@keyframes pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.5; }
}
.sse-dot {
  animation: pulse 2s infinite;
}

/* Arena bar transition - line 286 */
.arena-bar {
  transition: width 100ms ease-out, background-color 100ms ease-out;
}

/* Cell transition - line 192 */
.slab-cell {
  transition: background-color 100ms ease-out;
}
```

### 9.4 Feature Parity Checklist

From mockup comparison section (lines 656-664):

- [x] Real bitmap from Treiber stack walk
- [x] Each cell = actual slab slot state
- [x] Flash animation on state changes
- [x] Overflow counters and warnings
- [x] SSE push every 100ms (no polling)
- [x] Arena high water mark tracking
- [x] Per-arena usage visualization

---

## 10. Implementation Notes (2024-12-07)

### What Was Implemented

The memory diagnostics system was implemented with the following components:

**Backend (C):**
- `src/aio_sse_diagnostics.h` - Header with `valk_sse_diag_conn_t` and `valk_mem_snapshot_t` structures
- `src/aio_sse_diagnostics.c` - Implementation with:
  - `slab_to_bitmap()` - Walks Treiber stack free lists using atomic loads
  - `bitmap_to_hex()` - Converts bitmap bytes to hex strings
  - `valk_mem_snapshot_collect()` - Collects all slab/arena/GC heap stats
  - `valk_mem_snapshot_to_sse()` - Formats snapshot as SSE JSON event
- `src/aio.h` - Added 5 slab accessor functions (required because `valk_aio_system_t` is opaque):
  - `valk_aio_get_tcp_buffer_slab()`
  - `valk_aio_get_handle_slab()`
  - `valk_aio_get_stream_arenas_slab()`
  - `valk_aio_get_http_servers_slab()`
  - `valk_aio_get_http_clients_slab()`
- `src/aio_uv.c` - Implemented accessor functions and SSE response handling in `__http_send_response()`
- `CMakeLists.txt` - Added `src/aio_sse_diagnostics.c` under `VALK_METRICS` conditional

**Lisp:**
- `src/modules/aio/debug.valk` - Added route `/debug/diagnostics/memory` with `:body-type :sse-stream`

**Frontend:**
- `src/modules/aio/debug/body.html` - Memory Diagnostics section with 6 slab grids, arena gauges, legend
- `src/modules/aio/debug/script.js` - `MemoryDiagnostics` class with EventSource, reconnection, grid rendering
- `src/modules/aio/debug/style.css` - Comprehensive CSS for grids, gauges, animations, responsive layout

### Deviations from Plan

1. **Route path changed**: `/api/diagnostics/memory/stream` → `/debug/diagnostics/memory` (to match debug handler namespace)

2. **No persistent SSE streaming yet**: The current implementation sends a single snapshot per request rather than keeping the HTTP/2 stream open with periodic DATA frames. This is because:
   - HTTP/2 SSE requires complex nghttp2 state management to keep streams open
   - The `nghttp2_submit_response2` API closes the stream after sending
   - True SSE would require using `NGHTTP2_DATA_FLAG_NO_END_STREAM` and periodic `nghttp2_submit_data` calls

3. **Lisp builtin not added**: `aio/sse-memory-start` was not needed because the SSE handling is done entirely in C within `__http_send_response()` when it detects `:body-type :sse-stream`.

4. **Parser-side SSE setup not required**: The C code handles the SSE response directly without needing a Lisp builtin to set up the connection.

### Current Behavior

The frontend uses EventSource which will:
1. Connect to `/debug/diagnostics/memory`
2. Receive a single snapshot
3. Connection closes (HTTP/2 stream ends)
4. EventSource triggers `onerror` and reconnects
5. Exponential backoff prevents hammering the server

This provides near-real-time updates (every ~1-2 seconds with reconnection overhead) without true push-based streaming.

### Future Work (TODO)

To implement true SSE streaming over HTTP/2:

1. **Keep stream open**: Use `NGHTTP2_DATA_FLAG_NO_END_STREAM` in the initial response
2. **Timer-based pushes**: Set up a `uv_timer_t` that calls `nghttp2_submit_data()` every 100ms
3. **Track SSE connections**: Maintain a list of active SSE streams per connection
4. **Handle disconnects**: Clean up timers when streams are reset or connection closes
5. **Backpressure**: Check `nghttp2_session_get_stream_remote_window_size()` before pushing

This would require significant changes to the HTTP/2 data flow in `aio_uv.c`.

---

## 11. Sources

- [Memory Heat Map: Anomaly detection in real-time embedded systems](https://ieeexplore.ieee.org/document/7167219)
- [Arena allocator tips and tricks](https://nullprogram.com/blog/2023/09/27/)
- [Untangling Lifetimes: The Arena Allocator](https://www.rfleury.com/p/untangling-lifetimes-the-arena-allocator)
- [Using server-sent events - MDN](https://developer.mozilla.org/en-US/docs/Web/API/Server-sent_events/Using_server-sent_events)
- [Server-Sent Events: A Practical Guide](https://tigerabrodi.blog/server-sent-events-a-practical-guide-for-the-real-world)
- [Optimizing Canvas Rendering - AG Grid](https://blog.ag-grid.com/optimising-html5-canvas-rendering-best-practices-and-techniques/)
- [heatmap.js - Dynamic Heatmaps for the Web](https://www.patrick-wied.at/static/heatmapjs/)
- [Wwise AkMemoryArena Profiler](https://www.audiokinetic.com/en/blog/ak-memory-arenas/)
