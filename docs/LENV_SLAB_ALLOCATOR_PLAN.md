# Implementation Plan: Slab Allocator for lenvs

## Overview

Add a dedicated slab allocator for `valk_lenv_t` objects similar to the existing `lval_slab` for `valk_lval_t`. This will improve allocation performance for environments and provide better memory visibility in the debug dashboard.

## Current State Analysis

### lval Slab (Reference Implementation)
- **Location**: `gc.c:82-98` - initialization in `valk_gc_malloc_heap_init()`
- **Structure**: `valk_slab_t* lval_slab` field in `valk_gc_malloc_heap_t` (gc.h:58)
- **Item size**: `sizeof(valk_gc_header_t) + sizeof(valk_lval_t)` ≈ 256 bytes
- **Capacity**: 256K objects (fixed)
- **Allocation path**: `gc.c:222-246` - fast path checks `bytes == heap->lval_size`
- **Deallocation**: `gc.c:672-694` - address range check determines slab vs malloc

### lenv Current Allocation
- **Structure**: `valk_lenv_t` in `parser.h:60-81` ≈ 80 bytes (6 pointers + flags)
- **Allocation**: `valk_lenv_empty()` in `parser.c:1697-1709` - uses `valk_gc_malloc_heap_alloc()`
- **Deallocation**: `valk_lenv_free()` in `parser.c:1726-1752` - direct `free()` only for malloc allocator
- **GC marking**: `valk_gc_mark_env()` in `gc.c:542-564` - iterative worklist marking

---

## Implementation Tasks

### Phase 1: Core Slab Infrastructure

#### Task 1.1: Add lenv_slab field to GC heap
**File**: `src/gc.h` (line 58, after `lval_slab`)

```c
// In valk_gc_malloc_heap_t struct:
valk_slab_t* lval_slab;     // Fast slab allocator for valk_lval_t objects
size_t lval_size;           // Size of valk_lval_t for slab allocation
valk_slab_t* lenv_slab;     // Fast slab allocator for valk_lenv_t objects  // ADD
size_t lenv_size;           // Size of valk_lenv_t for slab allocation     // ADD
```

#### Task 1.2: Initialize lenv slab in heap init
**File**: `src/gc.c` (after line 98, following lval_slab init)

```c
// Create fast slab allocator for valk_lenv_t objects
// Environments are smaller and less numerous than lvals
heap->lenv_size = sizeof(valk_lenv_t);

// Smaller capacity than lval slab: 64K environments should be plenty
// Each lenv is ~80 bytes + header = ~96 bytes per slot
size_t lenv_slab_item_size = sizeof(valk_gc_header_t) + heap->lenv_size;
size_t num_lenvs = 64 * 1024;  // 64K environments

size_t lenv_slab_size = valk_slab_size(lenv_slab_item_size, num_lenvs);
heap->lenv_slab = malloc(lenv_slab_size);
if (heap->lenv_slab == NULL) {
  VALK_WARN("Failed to allocate lenv slab, will fall back to malloc");
} else {
  valk_slab_init(heap->lenv_slab, lenv_slab_item_size, num_lenvs);
}
```

#### Task 1.3: Add lenv slab fast path to allocation
**File**: `src/gc.c` - in `valk_gc_malloc_heap_alloc()` (around line 222-246)

After the lval slab fast path, add lenv slab fast path:

```c
// Fastest path: Slab allocator for valk_lval_t objects (most common case)
if (bytes == heap->lval_size && heap->lval_slab != NULL) {
  header = valk_mem_allocator_alloc((void*)heap->lval_slab, total_size);
  if (header != NULL) {
    from_slab = true;
  }
}

// Second fast path: Slab allocator for valk_lenv_t objects
if (header == NULL && bytes == heap->lenv_size && heap->lenv_slab != NULL) {
  header = valk_mem_allocator_alloc((void*)heap->lenv_slab, total_size);
  if (header != NULL) {
    from_slab = true;
  }
}

// Slow path: malloc if not found in slab
if (header == NULL) {
  // ... existing malloc code
}
```

#### Task 1.4: Update sweep to handle lenv slab deallocation
**File**: `src/gc.c` - in sweep function (around line 672-694)

The existing address range check needs to cover both slabs:

```c
// Check if object is from lval slab
bool from_lval_slab = false;
if (heap->lval_slab != NULL) {
  uintptr_t slab_start = (uintptr_t)heap->lval_slab;
  size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
  size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
  uintptr_t slab_end = slab_start + slab_total_size;
  from_lval_slab = (obj_addr >= slab_start && obj_addr < slab_end);
}

// Check if object is from lenv slab
bool from_lenv_slab = false;
if (!from_lval_slab && heap->lenv_slab != NULL) {
  uintptr_t slab_start = (uintptr_t)heap->lenv_slab;
  size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lenv_size;
  size_t slab_total_size = valk_slab_size(slab_item_size, 64 * 1024);
  uintptr_t slab_end = slab_start + slab_total_size;
  from_lenv_slab = (obj_addr >= slab_start && obj_addr < slab_end);
}

if (from_lval_slab) {
  valk_mem_allocator_free((void*)heap->lval_slab, header);
  VALK_TRACE("GC sweep: returned lval %p to slab", user_data);
} else if (from_lenv_slab) {
  valk_mem_allocator_free((void*)heap->lenv_slab, header);
  VALK_TRACE("GC sweep: returned lenv %p to slab", user_data);
} else {
  reclaimed += total_size;
  free(header);
  VALK_TRACE("GC sweep: freed %p (malloc)", user_data);
}
```

#### Task 1.5: Update heap usage percentage calculation
**File**: `src/gc.c` - in `valk_gc_heap_usage_pct()` (around line 124-145)

```c
uint8_t valk_gc_heap_usage_pct(valk_gc_malloc_heap_t* heap) {
  // Calculate lval slab usage percentage
  uint8_t lval_slab_pct = 0;
  if (heap->lval_slab != NULL && heap->lval_slab->numItems > 0) {
    size_t slab_used = heap->lval_slab->numItems - heap->lval_slab->numFree;
    lval_slab_pct = (uint8_t)((slab_used * 100) / heap->lval_slab->numItems);
  }

  // Calculate lenv slab usage percentage
  uint8_t lenv_slab_pct = 0;
  if (heap->lenv_slab != NULL && heap->lenv_slab->numItems > 0) {
    size_t slab_used = heap->lenv_slab->numItems - heap->lenv_slab->numFree;
    lenv_slab_pct = (uint8_t)((slab_used * 100) / heap->lenv_slab->numItems);
  }

  // Calculate malloc usage percentage
  uint8_t malloc_pct = (uint8_t)((heap->allocated_bytes * 100) / heap->hard_limit);

  // Return the highest - GC triggers if ANY tier is full
  uint8_t max_pct = lval_slab_pct > lenv_slab_pct ? lval_slab_pct : lenv_slab_pct;
  return max_pct > malloc_pct ? max_pct : malloc_pct;
}
```

---

### Phase 2: Dashboard Integration

#### Task 2.1: Update memory snapshot structure
**File**: `src/aio_sse_diagnostics.h` (in `valk_mem_snapshot.gc_heap` struct, around line 84-98)

```c
// GC heap stats (tiered: lval slab + lenv slab + malloc for overflow/large)
struct {
  // LVAL slab tier
  size_t lval_slab_bytes_used;
  size_t lval_slab_bytes_total;
  size_t lval_slab_objects_used;
  size_t lval_slab_objects_total;
  size_t lval_slab_peak_objects;

  // LENV slab tier (NEW)
  size_t lenv_slab_bytes_used;
  size_t lenv_slab_bytes_total;
  size_t lenv_slab_objects_used;
  size_t lenv_slab_objects_total;
  size_t lenv_slab_peak_objects;

  // Malloc tier
  size_t malloc_bytes_used;
  size_t malloc_bytes_limit;
  size_t malloc_peak_bytes;

  // Common
  size_t peak_usage;
  uint8_t gc_threshold_pct;
  uint64_t gc_cycles;
  uint64_t emergency_collections;
} gc_heap;
```

#### Task 2.2: Update snapshot collection
**File**: `src/aio_sse_diagnostics.c` - in the function that populates gc_heap (search for `slab_bytes_used`)

Add collection of lenv slab metrics alongside lval slab metrics:

```c
// LVAL slab metrics
if (heap->lval_slab) {
  size_t lval_used = heap->lval_slab->numItems - heap->lval_slab->numFree;
  snap->gc_heap.lval_slab_objects_used = lval_used;
  snap->gc_heap.lval_slab_objects_total = heap->lval_slab->numItems;
  snap->gc_heap.lval_slab_bytes_used = lval_used * heap->lval_slab->itemSize;
  snap->gc_heap.lval_slab_bytes_total = heap->lval_slab->numItems * heap->lval_slab->itemSize;
  snap->gc_heap.lval_slab_peak_objects = heap->lval_slab->peakUsed;
}

// LENV slab metrics (NEW)
if (heap->lenv_slab) {
  size_t lenv_used = heap->lenv_slab->numItems - heap->lenv_slab->numFree;
  snap->gc_heap.lenv_slab_objects_used = lenv_used;
  snap->gc_heap.lenv_slab_objects_total = heap->lenv_slab->numItems;
  snap->gc_heap.lenv_slab_bytes_used = lenv_used * heap->lenv_slab->itemSize;
  snap->gc_heap.lenv_slab_bytes_total = heap->lenv_slab->numItems * heap->lenv_slab->itemSize;
  snap->gc_heap.lenv_slab_peak_objects = heap->lenv_slab->peakUsed;
}
```

#### Task 2.3: Update JSON output format
**File**: `src/aio_sse_diagnostics.c` - in JSON generation (search for `"gc":`)

Rename existing `slab` to `lval_slab` and add `lenv_slab`:

```c
// GC section with tiered slabs
n += snprintf(buf + n, sz - n,
  "\"gc\":{"
    "\"lval_slab\":{\"bytes_used\":%zu,\"bytes_total\":%zu,\"objects_used\":%zu,\"objects_total\":%zu,\"peak_objects\":%zu},"
    "\"lenv_slab\":{\"bytes_used\":%zu,\"bytes_total\":%zu,\"objects_used\":%zu,\"objects_total\":%zu,\"peak_objects\":%zu},"
    "\"malloc\":{\"bytes_used\":%zu,\"bytes_limit\":%zu,\"peak_bytes\":%zu},"
    "\"threshold_pct\":%u,\"cycles\":%" PRIu64 ",\"emergency\":%" PRIu64
  "}",
  snap->gc_heap.lval_slab_bytes_used, snap->gc_heap.lval_slab_bytes_total,
  snap->gc_heap.lval_slab_objects_used, snap->gc_heap.lval_slab_objects_total,
  snap->gc_heap.lval_slab_peak_objects,
  snap->gc_heap.lenv_slab_bytes_used, snap->gc_heap.lenv_slab_bytes_total,
  snap->gc_heap.lenv_slab_objects_used, snap->gc_heap.lenv_slab_objects_total,
  snap->gc_heap.lenv_slab_peak_objects,
  snap->gc_heap.malloc_bytes_used, snap->gc_heap.malloc_bytes_limit,
  snap->gc_heap.malloc_peak_bytes,
  snap->gc_heap.gc_threshold_pct, snap->gc_heap.gc_cycles, snap->gc_heap.emergency_collections
);
```

#### Task 2.4: Update dashboard HTML to show lenv slab
**File**: `src/modules/aio/debug/body.html` (after line 268, after slab-tier div)

Add new tier for lenv slab:

```html
<!-- Tier 1b: LENV Slab (NEW) -->
<div class="heap-tier" id="lenv-slab-tier">
  <div class="tier-header">
    <span class="tier-icon">E</span>
    <span class="tier-name">Env Slab</span>
    <span class="tier-desc">Fixed-size environment objects</span>
    <span class="tier-usage">
      <span id="lenv-slab-used">--</span> / <span id="lenv-slab-total">--</span>
      (<span id="lenv-slab-pct">--</span>%)
    </span>
  </div>
  <div class="tier-bar-container">
    <div class="tier-bar lenv-slab-bar">
      <div class="tier-bar-fill" id="lenv-slab-bar-fill" style="width: 0%"></div>
      <div class="tier-bar-hwm" id="lenv-slab-bar-hwm" style="left: 0%"></div>
      <div class="tier-bar-threshold" id="lenv-slab-bar-threshold" style="left: 75%"></div>
    </div>
  </div>
  <!-- LENV Slab Grid Visualization -->
  <div class="slab-canvas">
    <div class="slab-grid" id="lenv-grid" role="img" aria-label="LENV slab allocation grid"></div>
  </div>
  <div class="tier-stats">
    <span class="tier-stat">
      <span class="stat-label">envs:</span>
      <span class="stat-value" id="lenv-objects-used">--</span>/<span id="lenv-objects-total">--</span>
    </span>
    <span class="tier-stat">
      <span class="stat-label">hwm:</span>
      <span class="stat-value" id="lenv-hwm-pct">--</span>%
    </span>
  </div>
</div>
```

#### Task 2.5: Update dashboard JavaScript to handle lenv slab
**File**: `src/modules/aio/debug/script.js`

Add handling for the new lenv slab data in the memory diagnostics update function:

```javascript
// In updateGcHeap() or similar function:

// LVAL slab (existing, rename from 'slab' to 'lval_slab')
if (gc.lval_slab) {
  const lvalSlab = gc.lval_slab;
  const lvalPct = lvalSlab.objects_total > 0
    ? Math.round((lvalSlab.objects_used / lvalSlab.objects_total) * 100)
    : 0;
  document.getElementById('slab-used').textContent = formatBytes(lvalSlab.bytes_used);
  document.getElementById('slab-total').textContent = formatBytes(lvalSlab.bytes_total);
  document.getElementById('slab-pct').textContent = lvalPct;
  document.getElementById('slab-objects-used').textContent = lvalSlab.objects_used;
  document.getElementById('slab-objects-total').textContent = lvalSlab.objects_total;
  document.getElementById('slab-bar-fill').style.width = lvalPct + '%';
  // ... hwm handling
}

// LENV slab (NEW)
if (gc.lenv_slab) {
  const lenvSlab = gc.lenv_slab;
  const lenvPct = lenvSlab.objects_total > 0
    ? Math.round((lenvSlab.objects_used / lenvSlab.objects_total) * 100)
    : 0;
  document.getElementById('lenv-slab-used').textContent = formatBytes(lenvSlab.bytes_used);
  document.getElementById('lenv-slab-total').textContent = formatBytes(lenvSlab.bytes_total);
  document.getElementById('lenv-slab-pct').textContent = lenvPct;
  document.getElementById('lenv-objects-used').textContent = lenvSlab.objects_used;
  document.getElementById('lenv-objects-total').textContent = lenvSlab.objects_total;
  document.getElementById('lenv-slab-bar-fill').style.width = lenvPct + '%';

  const lenvHwmPct = lenvSlab.objects_total > 0
    ? Math.round((lenvSlab.peak_objects / lenvSlab.objects_total) * 100)
    : 0;
  document.getElementById('lenv-hwm-pct').textContent = lenvHwmPct;
  document.getElementById('lenv-slab-bar-hwm').style.left = lenvHwmPct + '%';
}
```

#### Task 2.6: Add lenv slab to SSE bitmap generation
**File**: `src/aio_sse_diagnostics.c` - in the slab collection loop (around line 363-451)

Add the lenv slab to the list of slabs collected for visualization:

```c
// Add LENV slab from GC heap
if (heap->lenv_slab) {
  if (snap->slab_count < 8) {
    valk_slab_snapshot_t *ss = &snap->slabs[snap->slab_count++];
    ss->name = "lenv";
    ss->total_slots = heap->lenv_slab->numItems;
    ss->used_slots = ss->total_slots - heap->lenv_slab->numFree;
    ss->overflow_count = heap->lenv_slab->overflowCount;
    ss->has_slot_diag = false;

    // Generate bitmap for visualization
    size_t bitmap_bytes = (ss->total_slots + 7) / 8;
    ss->bitmap = scratch_alloc(bitmap_bytes);  // Use scratch arena
    ss->bitmap_bytes = bitmap_bytes;
    slab_to_bitmap(heap->lenv_slab, ss->bitmap, bitmap_bytes);
  }
}
```

---

### Phase 3: CSS Styling

#### Task 3.1: Add CSS for lenv slab tier
**File**: `src/modules/aio/debug/style.css`

```css
/* LENV slab tier styling (similar to existing slab tier) */
.lenv-slab-bar {
  background: var(--tier-bg, #2a2a3a);
}

.lenv-slab-bar .tier-bar-fill {
  background: linear-gradient(90deg, #6366f1, #818cf8);  /* Indigo gradient */
}

#lenv-slab-tier .tier-icon {
  background: #6366f1;
  color: white;
}

#lenv-grid {
  /* Same styling as lval-grid */
}
```

---

## Test Plan

### Unit Tests

#### Test 1: Slab initialization
**File**: `test/test_memory.c`

```c
void test_lenv_slab_init(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 4 * 1024 * 1024);

  TEST_ASSERT_NOT_NULL(heap->lenv_slab);
  TEST_ASSERT_EQUAL(sizeof(valk_lenv_t), heap->lenv_size);
  TEST_ASSERT_EQUAL(64 * 1024, heap->lenv_slab->numItems);
  TEST_ASSERT_EQUAL(64 * 1024, heap->lenv_slab->numFree);
  TEST_ASSERT_EQUAL(0, heap->lenv_slab->peakUsed);

  // Cleanup
  valk_gc_malloc_heap_destroy(heap);
}
```

#### Test 2: lenv allocation uses slab
**File**: `test/test_memory.c`

```c
void test_lenv_alloc_uses_slab(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 4 * 1024 * 1024);
  valk_thread_ctx.heap = heap;

  size_t initial_free = heap->lenv_slab->numFree;

  // Allocate an environment
  valk_lenv_t* env = valk_lenv_empty();
  TEST_ASSERT_NOT_NULL(env);

  // Verify slab was used
  TEST_ASSERT_EQUAL(initial_free - 1, heap->lenv_slab->numFree);

  // Verify address is within slab range
  uintptr_t addr = (uintptr_t)env;
  uintptr_t slab_start = (uintptr_t)heap->lenv_slab;
  size_t item_size = sizeof(valk_gc_header_t) + sizeof(valk_lenv_t);
  size_t slab_size = valk_slab_size(item_size, 64 * 1024);
  uintptr_t slab_end = slab_start + slab_size;

  // Account for GC header
  uintptr_t header_addr = addr - sizeof(valk_gc_header_t);
  TEST_ASSERT(header_addr >= slab_start && header_addr < slab_end);

  // Cleanup
  valk_thread_ctx.heap = NULL;
}
```

#### Test 3: lenv slab deallocation during GC sweep
**File**: `test/test_gc.c`

```c
void test_lenv_slab_gc_sweep(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 4 * 1024 * 1024);
  valk_lenv_t* root = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, root);
  valk_thread_ctx.heap = heap;

  size_t initial_free = heap->lenv_slab->numFree;

  // Allocate some orphan environments (no references)
  for (int i = 0; i < 10; i++) {
    valk_lenv_empty();  // Orphaned, will be collected
  }

  TEST_ASSERT_EQUAL(initial_free - 11, heap->lenv_slab->numFree);  // -1 for root, -10 for orphans

  // Run GC
  valk_gc_malloc_collect(heap, NULL);

  // Orphans should be returned to slab (only root survives)
  TEST_ASSERT_EQUAL(initial_free - 1, heap->lenv_slab->numFree);

  // Cleanup
  valk_thread_ctx.heap = NULL;
}
```

#### Test 4: Peak usage tracking
**File**: `test/test_memory.c`

```c
void test_lenv_slab_peak_tracking(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 4 * 1024 * 1024);
  valk_thread_ctx.heap = heap;

  TEST_ASSERT_EQUAL(0, heap->lenv_slab->peakUsed);

  // Allocate 5 envs
  valk_lenv_t* envs[5];
  for (int i = 0; i < 5; i++) {
    envs[i] = valk_lenv_empty();
  }
  TEST_ASSERT_EQUAL(5, heap->lenv_slab->peakUsed);

  // Peak should not decrease when freeing (it's a high water mark)
  // (would need GC sweep to actually free, which requires proper marking setup)

  // Cleanup
  valk_thread_ctx.heap = NULL;
}
```

#### Test 5: Heap usage percentage includes lenv slab
**File**: `test/test_gc.c`

```c
void test_heap_usage_includes_lenv_slab(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 4 * 1024 * 1024);
  valk_thread_ctx.heap = heap;

  // Initially empty
  uint8_t pct = valk_gc_heap_usage_pct(heap);
  TEST_ASSERT_EQUAL(0, pct);

  // Allocate 50% of lenv slab (32K envs)
  size_t half = heap->lenv_slab->numItems / 2;
  for (size_t i = 0; i < half; i++) {
    valk_lenv_empty();
  }

  // Usage should be ~50%
  pct = valk_gc_heap_usage_pct(heap);
  TEST_ASSERT(pct >= 48 && pct <= 52);  // Allow some tolerance

  // Cleanup
  valk_thread_ctx.heap = NULL;
}
```

### Integration Tests

#### Test 6: Dashboard metrics endpoint
**File**: Manual test or automated with curl

```bash
# Start webserver
build/valk examples/webserver_demo.valk &
VALK_PID=$!
sleep 3

# Fetch metrics and verify lenv_slab section exists
curl -k -s "https://localhost:6969/debug/metrics" | python3 -c "
import sys, json
d = json.load(sys.stdin)
gc = d.get('aio_metrics', {}).get('gc', {})
assert 'lenv_slab' in gc, 'lenv_slab missing from gc metrics'
lenv = gc['lenv_slab']
assert 'bytes_used' in lenv, 'bytes_used missing'
assert 'objects_total' in lenv, 'objects_total missing'
print('lenv_slab metrics: OK')
print(json.dumps(lenv, indent=2))
"

kill $VALK_PID
```

#### Test 7: SSE delta updates
**File**: Manual test

```bash
# Start webserver and verify lenv slab appears in SSE stream
build/valk examples/webserver_demo.valk &
sleep 3
timeout 5 curl -k -N "https://localhost:6969/debug/diagnostics/memory" 2>/dev/null | grep -o '"lenv_slab"'
pkill valk
```

### Stress Tests

#### Test 8: Slab exhaustion fallback
**File**: `test/test_memory.c`

```c
void test_lenv_slab_exhaustion_fallback(void) {
  // Create tiny lenv slab for testing
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 4 * 1024 * 1024);
  valk_thread_ctx.heap = heap;

  size_t slab_capacity = heap->lenv_slab->numItems;

  // Exhaust the slab
  for (size_t i = 0; i < slab_capacity; i++) {
    valk_lenv_empty();
  }

  // Next allocation should fall back to malloc
  size_t malloc_before = heap->allocated_bytes;
  valk_lenv_t* overflow_env = valk_lenv_empty();
  TEST_ASSERT_NOT_NULL(overflow_env);

  // Should have used malloc
  TEST_ASSERT(heap->allocated_bytes > malloc_before);
  TEST_ASSERT(heap->lenv_slab->overflowCount > 0);

  // Cleanup
  valk_thread_ctx.heap = NULL;
}
```

---

## File Change Summary

| File | Changes |
|------|---------|
| `src/gc.h` | Add `lenv_slab` and `lenv_size` fields to `valk_gc_malloc_heap_t` |
| `src/gc.c` | Initialize lenv slab, add allocation fast path, update sweep, update usage calc |
| `src/aio_sse_diagnostics.h` | Add lenv slab fields to `gc_heap` struct in `valk_mem_snapshot` |
| `src/aio_sse_diagnostics.c` | Collect lenv slab metrics, generate JSON, generate bitmap |
| `src/modules/aio/debug/body.html` | Add lenv slab tier visualization |
| `src/modules/aio/debug/script.js` | Handle lenv slab data updates |
| `src/modules/aio/debug/style.css` | Add lenv slab styling |
| `test/test_memory.c` | Add unit tests for lenv slab |
| `test/test_gc.c` | Add GC sweep tests for lenv slab |

---

## Rollout Considerations

1. **Backward Compatibility**: The JSON API changes from `slab` to `lval_slab` for the existing slab. Any external consumers need to update.

2. **Memory Usage**: The lenv slab adds ~6MB fixed overhead (64K slots × 96 bytes each). This is acceptable for server workloads.

3. **Graceful Degradation**: If slab allocation fails during init, malloc fallback works correctly.

4. **Metrics**: The dashboard will show empty/zero values for lenv slab until the feature is deployed and exercised.
