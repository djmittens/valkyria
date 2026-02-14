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
- **Connection-level diagnostics with per-slot state and server attribution**

---

## 0. Connection Pool Architecture (Option A)

### The Problem

Connections are allocated from a **shared slab** at the AIO system level, but each connection is **logically owned** by a specific server or client. The current visualization shows only used/free, missing:

1. **Connection state**: active, idle, closing
2. **Server attribution**: which server owns each connection
3. **Capacity vs utilization**: system-wide limit vs per-server usage

### Solution: Dual Visualization with Per-Slot Metadata

Instead of binary bitmaps (used/free), send **per-slot metadata** for connection-related slabs:

```
┌─────────────────────────────────────────────────────────────────┐
│ HANDLE SLAB (Connections)                            47 / 500   │
│                                                                 │
│ [Each cell colored by STATE, tooltip shows SERVER]             │
│ ┌──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┐  │
│ │▓▓│▓▓│▓▓│░░│▓▓│▓▓│  │  │▓▓│░░│░░│▓▓│▓▓│  │  │  │▓▓│▓▓│▓▓│░░│  │
│ └──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┘  │
│                                                                 │
│ Legend:  ▓▓ Active  ░░ Idle  ▒▒ Closing  __ Free                │
│                                                                 │
│ Breakdown by Server:          │ Breakdown by State:             │
│ ├── :8080  ████████ 32 (68%)  │ ● Active:  38                   │
│ ├── :9090  ███ 12 (26%)       │ ● Idle:     7                   │
│ └── :3000  █ 3 (6%)           │ ● Closing:  2                   │
└─────────────────────────────────────────────────────────────────┘
```

### Dashboard Layout Change

**Current**:
```
AIO System
├── Event loop stats
├── Connection Pool (aggregate)  ← WRONG: connections belong to servers
└── Memory Slabs

HTTP Servers (separate section)
└── Per-server cards
```

**Proposed**:
```
AIO System
├── Event Loop
│   └── iterations, events, handles, idle time
│
├── Shared Resource Pools (system-level capacity)
│   ├── Handle Slab: [per-cell grid with state colors]
│   │   └── Breakdown: by-server bar chart, by-state legend
│   ├── TCP Buffers: [grid]
│   ├── Stream Arenas: [grid]
│   └── Queue: pending requests/responses
│
├── HTTP Servers (nested, owned by this AIO)
│   └── Per-server cards showing:
│       ├── "This server: 32 connections (68% of pool)"
│       ├── Request rate, error rate
│       └── Latency, throughput
│
└── HTTP Clients (nested, owned by this AIO)
    └── Per-client cards
```

This shows:
1. **System capacity** at the slab level (are we approaching limits?)
2. **Per-server attribution** in the grid (who's using what?)
3. **Per-server details** in nested cards (what's the health of each?)

---

## 4. Frontend Implementation

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

## 11. Phase 2: Connection-Aware Diagnostics (Option A Implementation)

This section details the implementation of per-connection state tracking and server attribution, enabling the dual visualization described in Section 0.

### 11.1 Backend Changes

#### 11.1.1 Handle State Tracking

**File:** `src/aio.h` - Add connection state enum and tracking

```c
// Connection states (matches dashboard visualization)
typedef enum {
  VALK_CONN_FREE = 0,      // Slot not allocated
  VALK_CONN_CONNECTING,    // TCP handshake in progress
  VALK_CONN_ACTIVE,        // Processing request/response
  VALK_CONN_IDLE,          // Pooled, awaiting reuse
  VALK_CONN_CLOSING,       // Graceful shutdown
} valk_conn_state_e;

// Per-handle metadata for diagnostics
typedef struct {
  valk_conn_state_e state;
  uint16_t owner_idx;          // Index into owner_map (server/client ID)
  uint64_t state_change_time;  // Timestamp of last state change (for age_ms)
} valk_handle_diag_t;
```

**File:** `src/aio_uv.c` - Add state tracking to handle lifecycle

```c
// In valk_aio_handle_t struct, add:
valk_handle_diag_t diag;

// Update state on lifecycle events:
static void handle_on_connect(valk_aio_handle_t *h) {
  h->diag.state = VALK_CONN_ACTIVE;
  h->diag.state_change_time = uv_hrtime() / 1000000; // ms
}

static void handle_on_idle(valk_aio_handle_t *h) {
  h->diag.state = VALK_CONN_IDLE;
  h->diag.state_change_time = uv_hrtime() / 1000000;
}

static void handle_on_close_start(valk_aio_handle_t *h) {
  h->diag.state = VALK_CONN_CLOSING;
  h->diag.state_change_time = uv_hrtime() / 1000000;
}
```

#### 11.1.2 Owner Registration

**File:** `src/aio.h` - Owner registry

```c
#define VALK_MAX_OWNERS 16  // Max servers + clients

typedef struct {
  char name[32];           // e.g., ":8080", "postgres-primary"
  uint8_t type;            // 0=server, 1=client
  void *ptr;               // Pointer to server/client struct
} valk_owner_entry_t;

// Add to valk_aio_system_t:
typedef struct {
  valk_owner_entry_t entries[VALK_MAX_OWNERS];
  uint16_t count;
} valk_owner_registry_t;

// API
uint16_t valk_owner_register(valk_aio_system_t *aio, const char *name, uint8_t type, void *ptr);
const char* valk_owner_get_name(valk_aio_system_t *aio, uint16_t idx);
```

**File:** `src/aio_uv.c` - Registration on server/client creation

```c
// In http_server_create():
uint16_t owner_idx = valk_owner_register(aio, port_str, 0, server);
// Store owner_idx in server struct for assignment to new connections

// When accepting connection:
handle->diag.owner_idx = server->owner_idx;
handle->diag.state = VALK_CONN_CONNECTING;
```

#### 11.1.3 Enhanced Snapshot Collection

**File:** `src/aio_sse_diagnostics.h` - New snapshot format

```c
// Per-slot state for connection-aware slabs
typedef struct {
  char state;        // 'A'=active, 'I'=idle, 'C'=closing, 'F'=free
  uint16_t owner;    // Owner index (0xFFFF = none)
  uint32_t age_ms;   // Time since last state change
} valk_slot_diag_t;

// Enhanced slab snapshot
typedef struct {
  const char *name;
  size_t total_slots;
  size_t used_slots;
  size_t overflow_count;

  // Binary bitmap (existing, for simple slabs like LVAL)
  uint8_t *bitmap;
  size_t bitmap_bytes;

  // Per-slot diagnostics (for connection slabs)
  valk_slot_diag_t *slots;  // NULL for simple bitmap slabs
  bool has_slot_diag;

  // Summary stats
  struct {
    size_t active;
    size_t idle;
    size_t closing;
  } by_state;

  struct {
    uint16_t owner_idx;
    size_t count;
  } by_owner[VALK_MAX_OWNERS];
  size_t owner_count;
} valk_slab_snapshot_t;
```

**File:** `src/aio_sse_diagnostics.c` - Collect per-slot state

```c
// New function: walk slab and extract per-slot diagnostics
static void slab_to_slot_diag(valk_slab_t *slab, valk_slab_snapshot_t *out,
                               uint64_t now_ms) {
  size_t total = slab->numItems;
  out->slots = calloc(total, sizeof(valk_slot_diag_t));
  out->has_slot_diag = true;

  // Initialize all as free
  for (size_t i = 0; i < total; i++) {
    out->slots[i].state = 'F';
    out->slots[i].owner = 0xFFFF;
    out->slots[i].age_ms = 0;
  }

  // Walk allocated slots (inverse of free list walk)
  // This requires iterating all slots and checking if in free list
  // OR maintaining a separate "allocated" tracking structure

  // Alternative: walk free list to mark free, then iterate
  // all slots to get state from handle->diag

  size_t stride = valk_slab_item_stride(slab->itemSize);

  // Mark free slots first (same as existing bitmap code)
  uint64_t head_tag = __atomic_load_n(&slab->head, __ATOMIC_ACQUIRE);
  size_t head_offset = head_tag & (size_t)UINT32_MAX;

  while (head_offset != SIZE_MAX && head_offset < total) {
    out->slots[head_offset].state = 'F';
    valk_slab_item_t *item = (valk_slab_item_t *)&slab->heap[stride * head_offset];
    uint64_t next_tag = __atomic_load_n(&item->next, __ATOMIC_ACQUIRE);
    head_offset = next_tag & (size_t)UINT32_MAX;
  }

  // Now iterate all slots and extract diag from allocated handles
  for (size_t i = 0; i < total; i++) {
    if (out->slots[i].state == 'F') continue;

    // Get handle at this slot
    valk_aio_handle_t *h = (valk_aio_handle_t *)&slab->heap[stride * i];

    // Extract diagnostics
    switch (h->diag.state) {
      case VALK_CONN_ACTIVE:     out->slots[i].state = 'A'; out->by_state.active++; break;
      case VALK_CONN_IDLE:       out->slots[i].state = 'I'; out->by_state.idle++; break;
      case VALK_CONN_CLOSING:    out->slots[i].state = 'C'; out->by_state.closing++; break;
      case VALK_CONN_CONNECTING: out->slots[i].state = 'A'; out->by_state.active++; break;
      default:                   out->slots[i].state = 'A'; out->by_state.active++; break;
    }

    out->slots[i].owner = h->diag.owner_idx;
    out->slots[i].age_ms = (uint32_t)(now_ms - h->diag.state_change_time);
    out->used_slots++;

    // Update by_owner summary
    // (simplified - would need proper owner tracking)
  }
}
```

#### 11.1.4 Compact Wire Format

**File:** `src/aio_sse_diagnostics.c` - Encode slot diagnostics

```c
// Encode slot states as compact string: "AAIFAACI..."
static void slots_to_state_string(valk_slot_diag_t *slots, size_t count, char *out) {
  for (size_t i = 0; i < count; i++) {
    out[i] = slots[i].state;
  }
  out[count] = '\0';
}

// Encode owners as array of indices (only for used slots)
static int slots_to_owner_array(valk_slot_diag_t *slots, size_t count,
                                 char *buf, size_t buf_size) {
  char *p = buf;
  char *end = buf + buf_size;

  *p++ = '[';
  bool first = true;

  for (size_t i = 0; i < count; i++) {
    if (slots[i].state == 'F') continue;

    if (!first) *p++ = ',';
    first = false;

    int n = snprintf(p, end - p, "%u", slots[i].owner);
    if (n < 0 || n >= end - p) return -1;
    p += n;
  }

  *p++ = ']';
  *p = '\0';

  return p - buf;
}

// Updated SSE format for connection slabs
static int slab_snapshot_to_json(valk_slab_snapshot_t *slab, char *buf, size_t buf_size) {
  if (slab->has_slot_diag) {
    // Compact format with states string
    char *states = malloc(slab->total_slots + 1);
    slots_to_state_string(slab->slots, slab->total_slots, states);

    int n = snprintf(buf, buf_size,
      "{\"name\":\"%s\",\"total\":%zu,\"used\":%zu,"
      "\"states\":\"%s\","
      "\"summary\":{\"A\":%zu,\"I\":%zu,\"C\":%zu},"
      "\"overflow\":%zu}",
      slab->name, slab->total_slots, slab->used_slots,
      states,
      slab->by_state.active, slab->by_state.idle, slab->by_state.closing,
      slab->overflow_count);

    free(states);
    return n;
  } else {
    // Existing bitmap format for simple slabs
    // ... (existing code)
  }
}
```

### 11.2 Frontend Changes

#### 11.2.1 Dashboard Restructure

**File:** `src/modules/aio/debug/body.html` - New layout

```html
<!-- ==================== AIO SYSTEMS ==================== -->
<section class="section-group aio-section" aria-labelledby="aio-section-title">
  <div class="section-header">
    <div class="section-icon aio" aria-hidden="true">AIO</div>
    <h2 class="section-title" id="aio-section-title">Async I/O System</h2>
    <span class="section-subtitle">Event Loop, Resources, Servers & Clients</span>
  </div>

  <!-- Per-AIO system panels (dynamically generated) -->
  <div id="aio-systems-container">
    <!-- Template for each AIO system: -->
    <article class="panel aio-system-panel">

      <!-- Event Loop Stats -->
      <div class="aio-section-block">
        <div class="block-header">
          <span class="block-title">Event Loop</span>
        </div>
        <div class="mini-stats">
          <div class="mini-stat">
            <div class="mini-stat-value aio-sys-iterations">--</div>
            <div class="mini-stat-label">Loop Iters</div>
          </div>
          <div class="mini-stat">
            <div class="mini-stat-value aio-sys-events">--</div>
            <div class="mini-stat-label">Events</div>
          </div>
          <div class="mini-stat">
            <div class="mini-stat-value aio-sys-handles">--</div>
            <div class="mini-stat-label">Handles</div>
          </div>
          <div class="mini-stat">
            <div class="mini-stat-value aio-sys-queue">--</div>
            <div class="mini-stat-label">Queue</div>
          </div>
        </div>
      </div>

      <!-- Shared Resource Pools -->
      <div class="aio-section-block">
        <div class="block-header">
          <span class="block-title">Shared Resource Pools</span>
          <span class="section-badge"><span class="sse-dot"></span> Live</span>
        </div>

        <!-- Handle Slab (Connections) - WITH STATE COLORS -->
        <div class="resource-pool-panel" id="aio-handles-pool">
          <div class="pool-header">
            <span class="pool-name">Connections (Handle Slab)</span>
            <span class="pool-usage">-- / -- (--%) </span>
          </div>
          <div class="pool-grid-container">
            <!-- Each cell colored by state: active=green, idle=blue, closing=yellow, free=dark -->
            <div class="pool-grid connection-grid" id="aio-handles-grid"></div>
          </div>
          <div class="pool-breakdown">
            <div class="breakdown-by-state">
              <div class="legend-item"><span class="legend-dot active"></span> Active: <span class="count-active">--</span></div>
              <div class="legend-item"><span class="legend-dot idle"></span> Idle: <span class="count-idle">--</span></div>
              <div class="legend-item"><span class="legend-dot closing"></span> Closing: <span class="count-closing">--</span></div>
            </div>
            <div class="breakdown-by-owner" id="aio-handles-by-owner">
              <!-- Dynamically: :8080 ████ 32, :9090 ██ 12 -->
            </div>
          </div>
          <div class="pool-warnings">
            <span class="capacity-warning" style="display:none">⚠ Approaching capacity</span>
            <span class="overflow-warning" style="display:none">⚠ -- overflows</span>
          </div>
        </div>

        <!-- TCP Buffers (simple binary) -->
        <div class="resource-pool-panel compact" id="aio-tcp-pool">
          <div class="pool-header">
            <span class="pool-name">TCP Buffers</span>
            <span class="pool-usage">-- / --</span>
          </div>
          <div class="pool-grid-container">
            <div class="pool-grid" id="aio-tcp-grid"></div>
          </div>
        </div>

        <!-- Stream Arenas (simple binary) -->
        <div class="resource-pool-panel compact" id="aio-arenas-pool">
          <div class="pool-header">
            <span class="pool-name">Stream Arenas</span>
            <span class="pool-usage">-- / --</span>
          </div>
          <div class="pool-grid-container">
            <div class="pool-grid" id="aio-arenas-grid"></div>
          </div>
        </div>
      </div>

      <!-- HTTP Servers (nested under AIO) -->
      <div class="aio-section-block">
        <div class="block-header">
          <span class="block-title">HTTP Servers</span>
          <span class="block-badge" id="aio-servers-count">-- servers</span>
          <span class="block-badge" id="aio-servers-rate">-- req/s</span>
        </div>
        <div class="nested-cards-grid" id="aio-servers-container">
          <!-- Server cards injected here -->
        </div>
      </div>

      <!-- HTTP Clients (nested under AIO) -->
      <div class="aio-section-block">
        <div class="block-header">
          <span class="block-title">HTTP Clients</span>
          <span class="block-badge" id="aio-clients-count">-- clients</span>
        </div>
        <div class="nested-cards-grid" id="aio-clients-container">
          <!-- Client cards injected here -->
        </div>
      </div>

    </article>
  </div>
</section>
```

#### 11.2.2 Connection Grid Rendering

**File:** `src/modules/aio/debug/script.js` - State-aware grid

```javascript
// Color mapping for connection states
const CONN_STATE_COLORS = {
  'A': 'var(--color-ok)',       // Active - green
  'I': 'var(--color-info)',     // Idle - blue
  'C': 'var(--color-warning)',  // Closing - yellow
  'F': 'var(--bg-tertiary)'     // Free - dark
};

const CONN_STATE_LABELS = {
  'A': 'Active',
  'I': 'Idle',
  'C': 'Closing',
  'F': 'Free'
};

// Render connection grid with per-slot state colors
function renderConnectionGrid(grid, slab, ownerMap, prevStates) {
  const states = slab.states || '';
  const total = slab.total || 0;

  // Ensure grid has correct number of cells
  while (grid.children.length < total) {
    const cell = document.createElement('div');
    cell.className = 'pool-cell';
    grid.appendChild(cell);
  }
  while (grid.children.length > total) {
    grid.removeChild(grid.lastChild);
  }

  // Update cells with state colors
  for (let i = 0; i < total; i++) {
    const cell = grid.children[i];
    const state = states[i] || 'F';
    const prevState = prevStates ? prevStates[i] : state;

    // Set color based on state
    cell.style.backgroundColor = CONN_STATE_COLORS[state];

    // Flash animation on state change
    if (state !== prevState) {
      cell.classList.add('flash');
      setTimeout(() => cell.classList.remove('flash'), 300);
    }

    // Tooltip with owner info (if available)
    if (state !== 'F' && slab.owners && ownerMap) {
      const ownerIdx = slab.owners[i];
      const ownerName = ownerMap[ownerIdx] || 'unknown';
      cell.title = `${CONN_STATE_LABELS[state]} - ${ownerName}`;
    } else {
      cell.title = CONN_STATE_LABELS[state];
    }
  }

  return states; // Return for next comparison
}

// Render owner breakdown bar chart
function renderOwnerBreakdown(container, byOwner, ownerMap, total) {
  container.innerHTML = '';

  // Sort by count descending
  const entries = Object.entries(byOwner)
    .map(([idx, count]) => ({ name: ownerMap[idx] || `:${idx}`, count }))
    .sort((a, b) => b.count - a.count);

  for (const { name, count } of entries) {
    const pct = (count / total) * 100;

    const row = document.createElement('div');
    row.className = 'owner-row';
    row.innerHTML = `
      <span class="owner-name">${name}</span>
      <div class="owner-bar-track">
        <div class="owner-bar" style="width: ${pct}%"></div>
      </div>
      <span class="owner-count">${count} (${pct.toFixed(0)}%)</span>
    `;
    container.appendChild(row);
  }
}

// Update handleMemoryUpdate to use new format
handleMemoryUpdate(data) {
  if (data.slabs) {
    data.slabs.forEach(slab => {
      if (slab.states) {
        // Connection-aware slab (handles)
        this.updateConnectionSlab(slab, data.owner_map);
      } else if (slab.bitmap) {
        // Simple binary slab
        this.updateSlabGrid(slab);
      }
    });
  }
  // ... rest of existing code
}

updateConnectionSlab(slab, ownerMap) {
  const gridId = `aio-${slab.name.replace(/_/g, '-')}-grid`;
  const grid = document.getElementById(gridId);
  if (!grid) return;

  const prevKey = `conn_${slab.name}`;
  const prevStates = this.previousState[prevKey];

  this.previousState[prevKey] = renderConnectionGrid(grid, slab, ownerMap, prevStates);

  // Update summary counts
  if (slab.summary) {
    const panel = grid.closest('.resource-pool-panel');
    if (panel) {
      panel.querySelector('.count-active').textContent = slab.summary.A || 0;
      panel.querySelector('.count-idle').textContent = slab.summary.I || 0;
      panel.querySelector('.count-closing').textContent = slab.summary.C || 0;
    }
  }

  // Update owner breakdown
  if (slab.by_owner && ownerMap) {
    const breakdownEl = document.getElementById(`aio-${slab.name}-by-owner`);
    if (breakdownEl) {
      renderOwnerBreakdown(breakdownEl, slab.by_owner, ownerMap, slab.used);
    }
  }

  // Capacity warnings
  const usedPct = slab.total > 0 ? (slab.used / slab.total) * 100 : 0;
  const panel = grid.closest('.resource-pool-panel');
  if (panel) {
    const capacityWarn = panel.querySelector('.capacity-warning');
    if (capacityWarn) {
      capacityWarn.style.display = usedPct >= 70 ? '' : 'none';
    }
  }
}
```

#### 11.2.3 CSS for Connection Grid

**File:** `src/modules/aio/debug/style.css` - Connection-specific styles

```css
/* Connection Grid - State Colors */
.connection-grid .pool-cell {
  border-radius: 2px;
  transition: background-color 100ms ease-out;
  cursor: help;
}

.connection-grid .pool-cell[data-state="A"] { background: var(--color-ok); }
.connection-grid .pool-cell[data-state="I"] { background: var(--color-info); }
.connection-grid .pool-cell[data-state="C"] { background: var(--color-warning); }
.connection-grid .pool-cell[data-state="F"] { background: var(--bg-tertiary); }

/* Pool Breakdown Section */
.pool-breakdown {
  display: flex;
  gap: var(--space-lg);
  margin-top: var(--space-md);
  padding-top: var(--space-md);
  border-top: 1px dashed var(--border-muted);
}

.breakdown-by-state {
  display: flex;
  gap: var(--space-md);
  font-size: 11px;
}

.breakdown-by-state .legend-item {
  display: flex;
  align-items: center;
  gap: var(--space-xs);
  color: var(--text-muted);
}

.breakdown-by-state .legend-dot {
  width: 8px;
  height: 8px;
  border-radius: 2px;
}

.breakdown-by-state .legend-dot.active { background: var(--color-ok); }
.breakdown-by-state .legend-dot.idle { background: var(--color-info); }
.breakdown-by-state .legend-dot.closing { background: var(--color-warning); }

/* Owner Breakdown Bar Chart */
.breakdown-by-owner {
  flex: 1;
}

.owner-row {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  font-size: 11px;
  margin-bottom: 4px;
}

.owner-name {
  min-width: 60px;
  font-family: var(--font-mono);
  color: var(--text-secondary);
}

.owner-bar-track {
  flex: 1;
  height: 8px;
  background: var(--bg-tertiary);
  border-radius: 4px;
  overflow: hidden;
}

.owner-bar {
  height: 100%;
  background: var(--color-ok-muted);
  border-radius: 4px;
  transition: width 100ms ease-out;
}

.owner-count {
  min-width: 70px;
  text-align: right;
  color: var(--text-muted);
  font-family: var(--font-mono);
}

/* Nested Cards Grid */
.nested-cards-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
  gap: var(--space-md);
  margin-top: var(--space-md);
}

/* AIO Section Blocks */
.aio-section-block {
  margin-bottom: var(--space-lg);
  padding-bottom: var(--space-lg);
  border-bottom: 1px solid var(--border-muted);
}

.aio-section-block:last-child {
  border-bottom: none;
  margin-bottom: 0;
  padding-bottom: 0;
}

.block-header {
  display: flex;
  align-items: center;
  gap: var(--space-md);
  margin-bottom: var(--space-md);
}

.block-title {
  font-size: 12px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  color: var(--text-muted);
}

.block-badge {
  font-size: 10px;
  padding: 2px 6px;
  border-radius: 4px;
  background: var(--bg-tertiary);
  color: var(--text-muted);
}
```


### 11.4 Testing Scenarios

**Scenario: Multi-Server Connection Distribution**
1. Start two HTTP servers on different ports
2. Generate load to each server independently
3. Verify connection grid shows different colors for each server's connections
4. Verify owner breakdown shows accurate distribution
5. Stop one server and verify its connections move to "closing" state

**Scenario: Pool Exhaustion Warning**
1. Configure small handle slab (e.g., 50 slots)
2. Generate load until approaching 70% capacity
3. Verify warning appears in dashboard
4. Generate more load until 90%
5. Verify critical warning and overflow counter

### 11.5 Implementation Status

| Component | Status | Files Modified |
|-----------|--------|----------------|
| Frontend Layout Restructure | ✅ DONE | `body.html` - Nested servers/clients under AIO |
| JavaScript Rendering | ✅ DONE | `script.js` - `createAioSystemPanel()`, `renderHttpServers()` |
| CSS Styling | ✅ DONE | `style.css` - Section blocks, nested cards, pool breakdown |
| Backend State Tracking | 🔲 TODO | `src/aio.h`, `src/aio_uv.c` |
| SSE Enhanced Format | 🔲 TODO | `src/aio_sse_diagnostics.c` |

**Frontend Changes Implemented:**
- Removed separate HTTP Servers section
- HTTP Servers now render as nested cards within AIO system panel
- Added section blocks: Event Loop → Shared Resource Pools → HTTP Servers → HTTP Clients
- Connection pool panel with state-based coloring (active/idle/closing)
- Owner breakdown bar chart for connection attribution
- Responsive grid layout for nested server/client cards
- Pool warnings for capacity and overflow alerts

---

## 12. Sources

- [Memory Heat Map: Anomaly detection in real-time embedded systems](https://ieeexplore.ieee.org/document/7167219)
- [Arena allocator tips and tricks](https://nullprogram.com/blog/2023/09/27/)
- [Untangling Lifetimes: The Arena Allocator](https://www.rfleury.com/p/untangling-lifetimes-the-arena-allocator)
- [Using server-sent events - MDN](https://developer.mozilla.org/en-US/docs/Web/API/Server-sent_events/Using_server-sent_events)
- [Server-Sent Events: A Practical Guide](https://tigerabrodi.blog/server-sent-events-a-practical-guide-for-the-real-world)
- [Optimizing Canvas Rendering - AG Grid](https://blog.ag-grid.com/optimising-html5-canvas-rendering-best-practices-and-techniques/)
- [heatmap.js - Dynamic Heatmaps for the Web](https://www.patrick-wied.at/static/heatmapjs/)
- [Wwise AkMemoryArena Profiler](https://www.audiokinetic.com/en/blog/ak-memory-arenas/)
