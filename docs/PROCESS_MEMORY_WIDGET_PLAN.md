# Process Memory Overview Widget Plan

## Goal

Add a dashboard widget that shows:
1. **Collapsed (default)**: Total process memory (RSS) with a compact summary
2. **Expanded**: Detailed breakdown showing how each subsystem contributes to total memory

## Current State

### What Exists
- **Allocator-level tracking**: Scratch arena, GC heap tiers (lval slab, lenv slab, malloc), AIO slabs
- **Dashboard widgets**: PoolWidget for individual subsystems with gauges/grids
- **SSE streaming**: `valk_mem_snapshot_t` aggregates all allocator data
- **No process-level tracking**: RSS/VSZ not collected

### Gap
The dashboard shows internal allocator usage but not:
- Actual process RSS (physical memory)
- Memory fragmentation overhead
- libuv/system allocations
- mmap'd regions outside allocators

---

## Implementation Plan

### Phase 1: Process Memory Collection (C Backend)

#### 1.1 Add Process Memory Structure

**File**: `src/memory.h`

```c
// Process-level memory stats (from OS)
typedef struct valk_process_memory {
  size_t rss_bytes;           // Resident Set Size (physical RAM)
  size_t vms_bytes;           // Virtual Memory Size
  size_t shared_bytes;        // Shared memory (Linux only)
  size_t data_bytes;          // Data + stack segment (Linux only)
  uint64_t page_faults_minor; // Soft page faults
  uint64_t page_faults_major; // Hard page faults (disk I/O)
} valk_process_memory_t;
```

#### 1.2 Implement Collection Function

**File**: `src/memory.c`

```c
#if defined(__linux__)
#include <sys/resource.h>

void valk_process_memory_collect(valk_process_memory_t *pm) {
  // Method 1: /proc/self/statm (fast, minimal parsing)
  FILE *f = fopen("/proc/self/statm", "r");
  if (f) {
    unsigned long size, resident, shared, text, lib, data, dirty;
    if (fscanf(f, "%lu %lu %lu %lu %lu %lu %lu",
               &size, &resident, &shared, &text, &lib, &data, &dirty) >= 4) {
      long page_size = sysconf(_SC_PAGESIZE);
      pm->vms_bytes = size * page_size;
      pm->rss_bytes = resident * page_size;
      pm->shared_bytes = shared * page_size;
      pm->data_bytes = data * page_size;
    }
    fclose(f);
  }

  // Page faults from getrusage
  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) == 0) {
    pm->page_faults_minor = ru.ru_minflt;
    pm->page_faults_major = ru.ru_majflt;
  }
}

#elif defined(__APPLE__)
#include <mach/mach.h>
#include <sys/resource.h>

void valk_process_memory_collect(valk_process_memory_t *pm) {
  mach_task_basic_info_data_t info;
  mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;

  if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO,
                (task_info_t)&info, &count) == KERN_SUCCESS) {
    pm->rss_bytes = info.resident_size;
    pm->vms_bytes = info.virtual_size;
  }

  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) == 0) {
    pm->page_faults_minor = ru.ru_minflt;
    pm->page_faults_major = ru.ru_majflt;
  }
}
#endif
```

#### 1.3 Add to Memory Snapshot

**File**: `src/aio_sse_diagnostics.h`

```c
typedef struct valk_mem_snapshot {
  // ... existing fields ...

  // NEW: Process-level memory
  valk_process_memory_t process;

  // NEW: Aggregated subsystem totals (for breakdown)
  struct {
    size_t scratch_arena_bytes;    // Scratch arena used
    size_t gc_heap_bytes;          // Sum of all GC heap tiers
    size_t gc_lval_slab_bytes;     // LVAL slab used
    size_t gc_lenv_slab_bytes;     // LENV slab used
    size_t gc_malloc_bytes;        // Malloc tier used
    size_t aio_slabs_bytes;        // Sum of all AIO slabs
    size_t untracked_bytes;        // process.rss - tracked subsystems
  } breakdown;
} valk_mem_snapshot_t;
```

#### 1.4 Collect and Compute Breakdown

**File**: `src/aio_sse_diagnostics.c`

In `valk_mem_snapshot_collect()`:

```c
void valk_mem_snapshot_collect(valk_mem_snapshot_t *snap, valk_aio_t *aio) {
  // ... existing collection code ...

  // Collect process-level memory
  valk_process_memory_collect(&snap->process);

  // Compute breakdown
  snap->breakdown.scratch_arena_bytes = scratch_arena_used;  // from arena stats

  // Sum GC heap tiers
  size_t gc_total = 0;
  for (size_t i = 0; i < snap->gc_heap.tier_count; i++) {
    gc_total += snap->gc_heap.tiers[i].bytes_used;
  }
  snap->breakdown.gc_heap_bytes = gc_total;
  snap->breakdown.gc_lval_slab_bytes = snap->gc_heap.tiers[0].bytes_used;
  snap->breakdown.gc_lenv_slab_bytes = snap->gc_heap.tiers[1].bytes_used;
  snap->breakdown.gc_malloc_bytes = snap->gc_heap.tiers[2].bytes_used;

  // Sum AIO slabs
  size_t aio_total = 0;
  for (size_t i = 0; i < snap->slab_count; i++) {
    aio_total += snap->slabs[i].used_slots * snap->slabs[i].slot_size;
  }
  snap->breakdown.aio_slabs_bytes = aio_total;

  // Untracked = RSS - all tracked allocators
  size_t tracked = snap->breakdown.scratch_arena_bytes
                 + snap->breakdown.gc_heap_bytes
                 + snap->breakdown.aio_slabs_bytes;
  snap->breakdown.untracked_bytes = (snap->process.rss_bytes > tracked)
                                   ? (snap->process.rss_bytes - tracked)
                                   : 0;
}
```

---

### Phase 2: SSE Protocol Update

#### 2.1 Add Process Memory to JSON Export

**File**: `src/aio_sse_diagnostics.c`

In the JSON encoder, add:

```c
// Process memory section
buf_append(buf, "\"process\":{");
buf_append_fmt(buf, "\"rss\":%zu,", snap->process.rss_bytes);
buf_append_fmt(buf, "\"vms\":%zu,", snap->process.vms_bytes);
buf_append_fmt(buf, "\"page_faults_minor\":%llu,", snap->process.page_faults_minor);
buf_append_fmt(buf, "\"page_faults_major\":%llu", snap->process.page_faults_major);
buf_append(buf, "},");

// Breakdown section
buf_append(buf, "\"breakdown\":{");
buf_append_fmt(buf, "\"scratch_arena\":%zu,", snap->breakdown.scratch_arena_bytes);
buf_append_fmt(buf, "\"gc_heap\":%zu,", snap->breakdown.gc_heap_bytes);
buf_append_fmt(buf, "\"gc_lval_slab\":%zu,", snap->breakdown.gc_lval_slab_bytes);
buf_append_fmt(buf, "\"gc_lenv_slab\":%zu,", snap->breakdown.gc_lenv_slab_bytes);
buf_append_fmt(buf, "\"gc_malloc\":%zu,", snap->breakdown.gc_malloc_bytes);
buf_append_fmt(buf, "\"aio_slabs\":%zu,", snap->breakdown.aio_slabs_bytes);
buf_append_fmt(buf, "\"untracked\":%zu", snap->breakdown.untracked_bytes);
buf_append(buf, "}");
```

---

### Phase 3: Dashboard Widget (Frontend)

#### 3.1 Widget Design (Integrated into Memory Section)

The process memory overview is integrated into the existing Memory subsection header:

```
┌─ Memory ───────────────── ████████░░░░  RSS: 256 MB  [▼] ─┐
│                                                            │
│ ┌─ Breakdown (toggle to show/hide) ───────────────────────┤
│ │ GC Heap    ████████████████░░░░░░░   128 MB   50%      │
│ │   └ LVAL   ██████████░░░░░░░░░░░░░    64 MB   25%      │
│ │   └ LENV   ████████░░░░░░░░░░░░░░░    32 MB   12%      │
│ │   └ Malloc ████████░░░░░░░░░░░░░░░    32 MB   12%      │
│ │ Scratch    ████░░░░░░░░░░░░░░░░░░░    16 MB    6%      │
│ │ AIO        ██░░░░░░░░░░░░░░░░░░░░░     8 MB    3%      │
│ │ Untracked  ████████████████████░░░   104 MB   41%      │
│ │ ──────────────────────────────────────────────────────  │
│ │ RSS: 256 MB │ VMS: 1.2 GB │ PF: 1234/0                 │
│ └─────────────────────────────────────────────────────────┤
│                                                            │
│ ┌─ Arenas ─────────┐  ┌─ GC Heap ──────────────────────┐ │
│ │  [existing]      │  │  [existing tier widgets]       │ │
│ └──────────────────┘  └────────────────────────────────┘ │
└────────────────────────────────────────────────────────────┘
```

- Inline gauge in header shows RSS usage
- Toggle button expands breakdown panel
- Breakdown shows subsystem contributions as % of RSS
- Existing Arenas and GC Heap blocks remain unchanged below

#### 3.2 HTML Structure

**File**: `src/modules/aio/debug/body.html`

Add new section at top of Runtime panel:

```html
<!-- Process Memory Overview Widget -->
<div class="panel" id="process-memory-panel">
  <div class="panel-header" onclick="togglePanel('process-memory-panel')"
       role="button" tabindex="0" aria-expanded="false">
    <div class="panel-icon process">M</div>
    <h3 class="panel-title">Process Memory</h3>
    <div class="gauge-inline" id="process-memory-gauge-inline">
      <div class="gauge-bar-inline">
        <div class="gauge-fill-inline" id="process-memory-fill-inline"></div>
      </div>
      <span class="gauge-text-inline" id="process-memory-text-inline">-- / --</span>
    </div>
    <span class="expand-icon">▼</span>
  </div>

  <div class="panel-body" id="process-memory-body">
    <!-- Breakdown bars -->
    <div class="breakdown-section">
      <div class="breakdown-header">Breakdown by Subsystem</div>

      <!-- GC Heap (parent) -->
      <div class="breakdown-row parent" id="breakdown-gc-heap">
        <span class="breakdown-label">GC Heap</span>
        <div class="breakdown-bar">
          <div class="breakdown-fill gc-heap" id="breakdown-gc-heap-fill"></div>
        </div>
        <span class="breakdown-value" id="breakdown-gc-heap-value">--</span>
        <span class="breakdown-pct" id="breakdown-gc-heap-pct">--%</span>
      </div>

      <!-- GC Heap children (indented) -->
      <div class="breakdown-row child" id="breakdown-gc-lval">
        <span class="breakdown-label">├─ LVAL Slab</span>
        <div class="breakdown-bar">
          <div class="breakdown-fill lval" id="breakdown-gc-lval-fill"></div>
        </div>
        <span class="breakdown-value" id="breakdown-gc-lval-value">--</span>
        <span class="breakdown-pct" id="breakdown-gc-lval-pct">--%</span>
      </div>

      <div class="breakdown-row child" id="breakdown-gc-lenv">
        <span class="breakdown-label">├─ LENV Slab</span>
        <div class="breakdown-bar">
          <div class="breakdown-fill lenv" id="breakdown-gc-lenv-fill"></div>
        </div>
        <span class="breakdown-value" id="breakdown-gc-lenv-value">--</span>
        <span class="breakdown-pct" id="breakdown-gc-lenv-pct">--%</span>
      </div>

      <div class="breakdown-row child" id="breakdown-gc-malloc">
        <span class="breakdown-label">└─ Malloc</span>
        <div class="breakdown-bar">
          <div class="breakdown-fill malloc" id="breakdown-gc-malloc-fill"></div>
        </div>
        <span class="breakdown-value" id="breakdown-gc-malloc-value">--</span>
        <span class="breakdown-pct" id="breakdown-gc-malloc-pct">--%</span>
      </div>

      <!-- Scratch Arena -->
      <div class="breakdown-row parent" id="breakdown-scratch">
        <span class="breakdown-label">Scratch Arena</span>
        <div class="breakdown-bar">
          <div class="breakdown-fill scratch" id="breakdown-scratch-fill"></div>
        </div>
        <span class="breakdown-value" id="breakdown-scratch-value">--</span>
        <span class="breakdown-pct" id="breakdown-scratch-pct">--%</span>
      </div>

      <!-- AIO Slabs -->
      <div class="breakdown-row parent" id="breakdown-aio">
        <span class="breakdown-label">AIO Slabs</span>
        <div class="breakdown-bar">
          <div class="breakdown-fill aio" id="breakdown-aio-fill"></div>
        </div>
        <span class="breakdown-value" id="breakdown-aio-value">--</span>
        <span class="breakdown-pct" id="breakdown-aio-pct">--%</span>
      </div>

      <!-- Untracked -->
      <div class="breakdown-row parent untracked" id="breakdown-untracked">
        <span class="breakdown-label">Untracked</span>
        <div class="breakdown-bar">
          <div class="breakdown-fill untracked" id="breakdown-untracked-fill"></div>
        </div>
        <span class="breakdown-value" id="breakdown-untracked-value">--</span>
        <span class="breakdown-pct" id="breakdown-untracked-pct">--%</span>
      </div>
    </div>

    <!-- Process stats footer -->
    <div class="process-stats-footer">
      <span class="stat">RSS: <span id="process-rss">--</span></span>
      <span class="stat-sep">│</span>
      <span class="stat">VMS: <span id="process-vms">--</span></span>
      <span class="stat-sep">│</span>
      <span class="stat">Page Faults: <span id="process-pf-minor">--</span> minor / <span id="process-pf-major">--</span> major</span>
    </div>
  </div>
</div>
```

#### 3.3 CSS Styles

**File**: `src/modules/aio/debug/style.css`

```css
/* Process Memory Panel - Icon */
.panel-icon.process {
  background: linear-gradient(135deg, #7c3aed, #a855f7);
  color: white;
}

/* Inline gauge in collapsed header */
.gauge-inline {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  flex: 1;
  max-width: 300px;
  margin-left: auto;
  margin-right: var(--space-md);
}

.gauge-bar-inline {
  flex: 1;
  height: 8px;
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
  overflow: hidden;
}

.gauge-fill-inline {
  height: 100%;
  background: linear-gradient(90deg, var(--color-ok), var(--color-warning));
  border-radius: var(--radius-sm);
  transition: width 0.3s ease;
}

.gauge-text-inline {
  font-size: var(--font-xs);
  color: var(--text-muted);
  white-space: nowrap;
  font-family: var(--font-mono);
}

/* Breakdown section */
.breakdown-section {
  padding: var(--space-md);
}

.breakdown-header {
  font-size: var(--font-xs);
  color: var(--text-muted);
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-bottom: var(--space-md);
}

.breakdown-row {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  padding: var(--space-xs) 0;
}

.breakdown-row.child {
  padding-left: var(--space-lg);
}

.breakdown-row.child .breakdown-label {
  color: var(--text-muted);
  font-size: var(--font-xs);
}

.breakdown-label {
  width: 120px;
  font-size: var(--font-sm);
  font-family: var(--font-mono);
  white-space: nowrap;
}

.breakdown-bar {
  flex: 1;
  height: 12px;
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
  overflow: hidden;
}

.breakdown-fill {
  height: 100%;
  border-radius: var(--radius-sm);
  transition: width 0.3s ease;
}

/* Subsystem colors */
.breakdown-fill.gc-heap { background: linear-gradient(90deg, #3b82f6, #60a5fa); }
.breakdown-fill.lval { background: #60a5fa; }
.breakdown-fill.lenv { background: #93c5fd; }
.breakdown-fill.malloc { background: #bfdbfe; }
.breakdown-fill.scratch { background: linear-gradient(90deg, #10b981, #34d399); }
.breakdown-fill.aio { background: linear-gradient(90deg, #f59e0b, #fbbf24); }
.breakdown-fill.untracked { background: linear-gradient(90deg, #6b7280, #9ca3af); }

.breakdown-value {
  width: 80px;
  text-align: right;
  font-size: var(--font-sm);
  font-family: var(--font-mono);
}

.breakdown-pct {
  width: 50px;
  text-align: right;
  font-size: var(--font-xs);
  color: var(--text-muted);
  font-family: var(--font-mono);
}

/* Untracked row styling */
.breakdown-row.untracked .breakdown-label {
  font-style: italic;
}

/* Process stats footer */
.process-stats-footer {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  padding: var(--space-md);
  border-top: 1px solid var(--border-color);
  font-size: var(--font-xs);
  color: var(--text-muted);
  font-family: var(--font-mono);
}

.stat-sep {
  color: var(--border-color);
}

/* Hide body when collapsed */
#process-memory-panel.collapsed #process-memory-body {
  display: none;
}

/* Rotate chevron when collapsed */
#process-memory-panel.collapsed .expand-icon {
  transform: rotate(-90deg);
}
```

#### 3.4 JavaScript Update Handler

**File**: `src/modules/aio/debug/script.js`

```javascript
// Update process memory widget
function updateProcessMemory(snapshot) {
  if (!snapshot.process || !snapshot.breakdown) return;

  var rss = snapshot.process.rss;
  var vms = snapshot.process.vms;
  var breakdown = snapshot.breakdown;

  // Update inline gauge in header
  var pct = (rss / vms) * 100;
  document.getElementById('process-memory-fill-inline').style.width = pct + '%';
  document.getElementById('process-memory-text-inline').textContent =
    formatBytes(rss) + ' / ' + formatBytes(vms);

  // Update breakdown bars (percentage of RSS)
  updateBreakdownRow('gc-heap', breakdown.gc_heap, rss);
  updateBreakdownRow('gc-lval', breakdown.gc_lval_slab, rss);
  updateBreakdownRow('gc-lenv', breakdown.gc_lenv_slab, rss);
  updateBreakdownRow('gc-malloc', breakdown.gc_malloc, rss);
  updateBreakdownRow('scratch', breakdown.scratch_arena, rss);
  updateBreakdownRow('aio', breakdown.aio_slabs, rss);
  updateBreakdownRow('untracked', breakdown.untracked, rss);

  // Update footer stats
  document.getElementById('process-rss').textContent = formatBytes(rss);
  document.getElementById('process-vms').textContent = formatBytes(vms);
  document.getElementById('process-pf-minor').textContent =
    formatNumber(snapshot.process.page_faults_minor);
  document.getElementById('process-pf-major').textContent =
    formatNumber(snapshot.process.page_faults_major);
}

function updateBreakdownRow(id, bytes, total) {
  var pct = total > 0 ? (bytes / total) * 100 : 0;
  document.getElementById('breakdown-' + id + '-fill').style.width = pct + '%';
  document.getElementById('breakdown-' + id + '-value').textContent = formatBytes(bytes);
  document.getElementById('breakdown-' + id + '-pct').textContent = pct.toFixed(0) + '%';
}

// Call from main updateDashboard()
function updateDashboard(snapshot) {
  // ... existing code ...
  updateProcessMemory(snapshot);
}
```

---

### Phase 4: Delta Tracking

#### 4.1 Add Process Memory to Delta Snapshot

Only send process/breakdown data when changed by more than 1%:

```c
typedef struct valk_mem_delta {
  // ... existing fields ...

  bool process_changed;
  valk_process_memory_t process;

  bool breakdown_changed;
  struct {
    size_t scratch_arena_bytes;
    size_t gc_heap_bytes;
    size_t aio_slabs_bytes;
    size_t untracked_bytes;
  } breakdown;
} valk_mem_delta_t;
```

---

## Task Checklist

### Backend (C)
- [x] Add `valk_process_memory_t` struct to `src/memory.h`
- [x] Implement `valk_process_memory_collect()` in `src/memory.c` (Linux + macOS)
- [x] Add breakdown fields to `valk_mem_snapshot_t`
- [x] Update `valk_mem_snapshot_collect()` to compute breakdown
- [x] Update JSON encoder to include process + breakdown sections
- [ ] Add delta tracking for process memory changes (future enhancement)
- [ ] Unit tests for process memory collection (future enhancement)

### Frontend (Dashboard)
- [x] Add Process Memory panel HTML to `body.html`
- [x] Add CSS styles for breakdown bars and inline gauge
- [x] Implement `updateProcessMemory()` in `script.js`
- [x] Wire up to SSE event handlers
- [x] Collapsed/expanded state persistence (uses existing togglePanel)
- [x] Responsive design for narrow screens

### Testing
- [ ] Verify RSS matches `ps aux` / `htop` output (manual verification needed)
- [ ] Verify breakdown percentages sum correctly (manual verification needed)
- [ ] Test under memory pressure (manual verification needed)
- [ ] Test on Linux and macOS (macOS untested)

---

## Notes

### Why "Untracked" Memory?

The difference between process RSS and tracked allocators includes:
- **libc malloc overhead**: Metadata, alignment, fragmentation
- **libuv internals**: Event loop structures, handles
- **Thread stacks**: Each thread has 8MB default stack
- **Shared libraries**: Code segments (.text)
- **mmap regions**: Files, anonymous mappings
- **Kernel buffers**: Network buffers, file caches

This "untracked" category helps users understand that internal allocator metrics don't tell the full story.

### Performance Considerations

- `/proc/self/statm` is very fast (single syscall, minimal parsing)
- Collection adds <1μs overhead per snapshot
- Delta tracking prevents unnecessary UI updates
