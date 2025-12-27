# Dashboard Memory Diagnostics Improvement Plan

## Executive Summary

The current Valkyria dashboard is heavily optimized for **web server workloads** with HTTP-centric metrics and Linux-specific memory introspection. This plan proposes improvements to make memory diagnostics useful across:

1. **Multiple platforms** (macOS, Linux, Windows, embedded)
2. **Multiple application types** (web servers, games, desktop apps, REPLs, LSPs, IDEs)
3. **Different debugging scenarios** (leaks, fragmentation, GC tuning, capacity planning)

---

## 1. Current State Analysis

### 1.1 What the Dashboard Currently Shows

| Subsystem | Metrics | Platform Support |
|-----------|---------|------------------|
| **Process Memory** | RSS, VMS, page faults | Cross-platform (RSS reliable, VMS unreliable on macOS) |
| **GC Heap** | LVAL slab, LENV slab, malloc overflow, pause times | Cross-platform |
| **Scratch Arena** | Used/capacity, high water mark, overflow count | Cross-platform |
| **AIO Slabs** | Handles, TCP buffers, stream arenas, HTTP servers/clients | Cross-platform |
| **smaps Breakdown** | Heap/anon/file/stack/uring regions | Linux only |
| **Metrics Registry** | Counters/gauges/histograms, string pool | Cross-platform |

### 1.2 Current Design Assumptions

The dashboard assumes:
- **Long-running server process** - Metrics accumulate over time
- **HTTP workload** - Request rates, latency histograms, status codes dominate
- **Linux deployment** - smaps, `/proc` access, predictable VMS
- **Network I/O focus** - AIO slabs, connection pools, throughput

### 1.3 Problems Identified

| Problem | Impact | Affected Users |
|---------|--------|----------------|
| VMS shows 392GB on macOS | Stacked bar visualization useless | macOS developers |
| smaps section empty on macOS | No OS-level memory breakdown | macOS developers |
| No RSS trend over time | Can't detect slow memory leaks | All users |
| No allocation rate metric | Can't assess GC pressure | Game/realtime developers |
| HTTP-centric layout | Irrelevant panels for non-web apps | REPL, LSP, game developers |
| No frame budget context | GC pauses not related to frame time | Game developers |
| No object lifetime analysis | Hard to find retained objects | All users debugging leaks |

---

## 2. Use Case Analysis

### 2.1 Web Server (Current Primary Focus)

**User**: SRE monitoring production, developer debugging performance

**Key Questions**:
- Is memory growing unbounded? (leak detection)
- Are GC pauses affecting P99 latency?
- Which connection pool is exhausted?
- What's the memory cost per request?

**Current Support**: Good - this is what the dashboard was designed for.

### 2.2 Video Game / Real-time Application

**User**: Game developer profiling frame-time budget

**Key Questions**:
- Will GC pause cause a frame hitch? (16.6ms budget at 60fps)
- What's allocation rate per frame?
- Are arenas being reset properly between frames?
- Is scratch arena sized correctly for peak usage?

**Current Support**: Poor
- No frame budget visualization
- No per-frame allocation tracking
- GC timeline doesn't show frame boundaries
- No arena reset event markers

### 2.3 Desktop UI Application

**User**: Developer building native app with Valkyria

**Key Questions**:
- Is memory stable during idle? (no background leaks)
- Does memory spike during operations? (undo buffer, file load)
- Are event handlers leaking closures?
- What's baseline vs. working set?

**Current Support**: Moderate
- RSS trend would help (not implemented)
- Closure count tracked but not trended
- No idle vs. active distinction

### 2.4 REPL / Interactive Development

**User**: Developer exploring language, running experiments

**Key Questions**:
- How much memory did that expression use?
- Did GC reclaim everything after evaluation?
- What's still retained in the environment?
- Arena high water mark after large eval?

**Current Support**: Moderate
- Heap usage shown but not delta-per-eval
- No "before/after" comparison mode
- No environment size breakdown

### 2.5 LSP / IDE Plugin

**User**: Developer integrating Valkyria as language server

**Key Questions**:
- Memory stable over long IDE session? (hours/days)
- Per-file memory overhead?
- Cache hit rates vs. memory cost?
- Response latency vs. GC correlation?

**Current Support**: Poor
- No long-term memory trending
- No per-operation memory attribution
- No cache metrics (not LSP-specific)

### 2.6 Embedded / Resource-Constrained

**User**: Developer targeting limited-memory device

**Key Questions**:
- Will this fit in 64MB? 16MB? 4MB?
- What's the absolute peak usage?
- Can I tune pool sizes to fit?
- What's the minimum viable configuration?

**Current Support**: Moderate
- Pool capacities visible
- High water marks tracked
- No "what-if" capacity modeling

---

## 3. Proposed Improvements

### 3.1 Cross-Platform Foundation (P0 - Critical)

#### 3.1.1 RSS Trend Sparkline

**What**: Add RSS history tracking and sparkline visualization

**Why**: RSS is the universal "is memory growing?" signal across all platforms

**Implementation**:
```javascript
// In history tracking
var history = {
  rss: [],  // Add RSS history
  // ... existing
};

// Push on each SSE update
pushHistory(history.rss, data.process.rss);

// Render sparkline in memory header
renderMiniSparkline('spark-rss', padSparklineData(history.rss, 60), 'var(--color-info)');
```

**Dashboard Location**: Memory subsection header, next to RSS value

**Validation Criteria**:
- [x] Sparkline visible on both macOS and Linux
- [x] Shows upward trend when allocating without GC
- [x] Shows sawtooth pattern during normal GC operation
- [x] Flattens during idle periods

#### 3.1.2 Remove/Fix macOS VMS Dependency

**What**: Already fixed - use RSS as bar baseline instead of VMS

**Validation Criteria**:
- [x] Stacked bar shows meaningful proportions on macOS
- [x] smaps section hidden when data unavailable

#### 3.1.3 Platform Detection and Adaptive UI

**What**: Server sends platform identifier, dashboard adapts

**Backend Change**:
```c
// In valk_diag_snapshot_to_sse()
"\"platform\":\"%s\","
#ifdef __APPLE__
  "darwin"
#elif defined(__linux__)
  "linux"
#elif defined(_WIN32)
  "windows"
#else
  "unknown"
#endif
```

**Frontend Change**:
```javascript
// Hide/show platform-specific sections
if (data.platform === 'linux') {
  document.querySelector('.smaps-breakdown').style.display = '';
} else {
  document.querySelector('.smaps-breakdown').style.display = 'none';
}
```

**Validation Criteria**:
- [x] Platform detected correctly on macOS, Linux
- [x] smaps section only shown on Linux
- [x] VMS de-emphasized on macOS (shown in footer only)

### 3.2 Allocation Pressure Metrics (P1 - High)

#### 3.2.1 Allocation Rate Gauge

**What**: Show bytes allocated per second vs. bytes reclaimed

**Why**: High allocation rate relative to reclaim indicates GC pressure

**Backend Change**:
```c
// Track allocation events
typedef struct {
  uint64_t bytes_allocated;    // Cumulative allocations
  uint64_t bytes_reclaimed;    // Cumulative GC reclaims
  uint64_t last_sample_time;
  double alloc_rate_bps;       // Bytes per second
  double reclaim_rate_bps;
} valk_alloc_rate_t;
```

**Dashboard Visualization**:
```
Allocation Pressure
[████████████░░░░░░░░] 
  ↑ 2.4 MB/s alloc    ↓ 1.8 MB/s reclaim
  Pressure: 33% (healthy)
```

**Validation Criteria**:
- [x] Rate updates in real-time (100ms intervals)
- [x] Shows warning when alloc >> reclaim sustained
- [x] Correlates with heap growth trend

#### 3.2.2 GC Efficiency Metric

**What**: Percentage of heap reclaimed per GC cycle

**Formula**: `efficiency = bytes_reclaimed / bytes_before_gc * 100`

**Why**: Low efficiency suggests long-lived objects accumulating (leak indicator)

**Validation Criteria**:
- [x] Shows >90% efficiency for normal workloads
- [x] Drops when simulating leak (retained list growing)
- [x] Displayed in GC panel stats (efficiency_pct in SSE data)

### 3.3 Application-Type Profiles (P1 - High)

#### 3.3.1 Profile Selector

**What**: Dashboard mode switch for different application types

**Profiles**:
| Profile | Focus | Hidden Panels | Added Panels |
|---------|-------|---------------|--------------|
| `server` (default) | HTTP, connections, throughput | - | - |
| `game` | Frame budget, allocation per frame | HTTP section | Frame timeline |
| `desktop` | Idle baseline, operation deltas | HTTP, AIO details | Event correlation |
| `repl` | Per-eval memory, environment size | HTTP, AIO | Eval history |
| `lsp` | Long-term stability, per-file | HTTP details | File cache stats |
| `embedded` | Absolute limits, capacity | Trends | Capacity planner |

**Implementation**: URL parameter or header toggle
```
/debug?profile=game
```

**Validation Criteria**:
- [x] Profile persists in localStorage
- [x] Irrelevant sections hidden smoothly
- [x] Profile-specific panels render correctly

#### 3.3.2 Game Profile: Frame Budget Overlay

**What**: Overlay showing GC pause impact on frame time

**Visualization**:
```
Frame Budget (16.6ms @ 60fps)
├─ Render: 8.2ms ████████
├─ Logic:  4.1ms ████
├─ GC:     2.4ms ██ ⚠
└─ Slack:  1.9ms █░
           ─────────────────
           0    5   10   15  16.6ms
```

**Backend**: Send GC pause histogram with frame-time buckets
```c
struct {
  size_t pauses_0_1ms;     // No impact
  size_t pauses_1_5ms;     // Minor impact
  size_t pauses_5_10ms;    // Warning
  size_t pauses_10_16ms;   // Frame drop risk
  size_t pauses_16ms_plus; // Frame drop certain
} frame_budget_histogram;
```

**Validation Criteria**:
- [x] Shows real GC pause distribution
- [x] Warns when >10% of pauses exceed 10ms
- [ ] Correlates with allocation rate

#### 3.3.3 REPL Profile: Eval Memory Delta

**What**: Show memory change after each evaluation

**Visualization**:
```
Last Eval: (map f (range 1000000))
├─ Allocated: 48.2 MB
├─ After GC:  12.4 MB retained
├─ Net Delta: +0.2 MB (expected: 0)
└─ Duration:  342ms (GC: 24ms)
```

**Backend**: Track pre/post eval memory state
```c
typedef struct {
  size_t heap_before;
  size_t heap_after_gc;
  size_t arena_hwm;
  uint64_t duration_us;
  uint64_t gc_pause_us;
} valk_eval_memory_t;
```

**Validation Criteria**:
- [x] Delta updates after each REPL eval
- [x] Shows warning if net delta > 0 repeatedly
- [x] Arena HWM visible for large evals

### 3.4 Leak Detection Assistance (P1 - High)

#### 3.4.1 Object Survival Analysis

**What**: Track how many GC cycles objects survive

**Why**: Objects surviving many cycles are likely leaks

**Backend Change**:
```c
// Add generation counter to GC header
typedef struct {
  uint8_t gc_mark : 1;
  uint8_t gc_gen : 7;  // Generations survived (0-127)
  // ...
} valk_lval_t;

// Collect histogram
struct {
  size_t gen_0;    // Died in first GC
  size_t gen_1_5;  // Short-lived
  size_t gen_6_20; // Medium-lived
  size_t gen_21_plus; // Long-lived (potential leaks)
} survival_histogram;
```

**Dashboard Visualization**:
```
Object Lifetimes
[Gen 0 ████████████████ 68%]
[1-5   ████████ 24%        ]
[6-20  ██ 6%               ]
[21+   █ 2%     ⚠ 1.2K old ]
```

**Validation Criteria**:
- [x] Histogram updates after each GC
- [x] Warning when gen_21_plus grows
- [ ] Drill-down shows object types (future)

#### 3.4.2 Retained Size Estimation

**What**: Show memory retained by long-lived root references

**Why**: Helps identify which bindings hold large object graphs

**Implementation**: Sample top N largest retained sets during GC
```c
typedef struct {
  const char *name;     // Symbol name
  size_t retained_bytes; // Transitive size
  size_t object_count;
} valk_retained_set_t;
```

**Dashboard**:
```
Top Retained Sets
1. *global-cache*    24.5 MB (12,847 objects)
2. *connection-pool* 8.2 MB (503 objects)  
3. user-data         2.1 MB (1,024 objects)
```

**Validation Criteria**:
- [x] Top 10 retained sets displayed
- [x] Updates after each GC
- [ ] Clickable to show object type breakdown (future)

### 3.5 Capacity Planning Tools (P2 - Medium)

#### 3.5.1 Pool Sizing Calculator

**What**: Interactive tool to model memory configuration

**Use Case**: Embedded/resource-constrained deployments

**UI**:
```
Capacity Planner
────────────────────────────
Target Memory Limit: [64 MB  ▼]

Recommended Configuration:
├─ LVAL Slab:      32K objects (16 MB)
├─ LENV Slab:      8K objects (4 MB)
├─ TCP Buffers:    64 slots (4 MB)
├─ Stream Arenas:  32 slots (8 MB)
├─ Scratch Arena:  16 MB
├─ Overhead:       ~16 MB
└─ Total:          64 MB ✓

Current Peak Usage: 48 MB (75% of limit)
```

**Validation Criteria**:
- [x] Slider adjusts total memory target
- [x] Proportions adjust based on observed usage patterns
- [x] Exportable as configuration snippet

#### 3.5.2 Fragmentation Metrics

**What**: Show slab fragmentation and arena waste

**Backend**:
```c
typedef struct {
  size_t allocated_bytes;   // Actually used
  size_t reserved_bytes;    // Committed capacity
  size_t fragmented_bytes;  // Dead space between allocations
  float fragmentation_pct;  // fragmented / reserved
} valk_frag_metrics_t;
```

**Dashboard**:
```
Fragmentation Analysis
LVAL Slab: 12% fragmented [████████████░░░]
LENV Slab: 3% fragmented  [███░░░░░░░░░░░░]
Scratch:   0% (bump allocator)
```

**Validation Criteria**:
- [x] Fragmentation calculated per slab
- [x] Warning threshold at 25%
- [ ] Suggestion to compact/resize

### 3.6 Historical Analysis (P2 - Medium)

#### 3.6.1 Extended History Buffer

**What**: Configurable history depth (1 min, 5 min, 1 hour)

**Current**: 3 minutes at 100ms intervals (1800 samples)

**Proposed**: 
```javascript
const HISTORY_PROFILES = {
  realtime: { samples: 600, interval: 100 },    // 1 min
  short:    { samples: 1800, interval: 100 },   // 3 min (current)
  medium:   { samples: 3000, interval: 1000 },  // 50 min
  long:     { samples: 3600, interval: 10000 }, // 10 hours
};
```

**UI**: Time range selector in header
```
[1m] [5m] [1h] [10h]
```

**Validation Criteria**:
- [x] Selector changes sparkline time range
- [x] Data downsampled appropriately for long ranges
- [x] Memory usage bounded (circular buffer)

#### 3.6.2 Snapshot Export/Import

**What**: Export current state as JSON for offline analysis

**Use Case**: 
- Share diagnostics with team
- Compare before/after optimization
- Attach to bug reports

**Implementation**:
```javascript
function exportSnapshot() {
  const snapshot = {
    timestamp: Date.now(),
    platform: currentPlatform,
    history: history,
    current: lastSnapshot,
  };
  downloadJSON('valkyria-snapshot.json', snapshot);
}
```

**Validation Criteria**:
- [x] Export button in header
- [x] JSON includes all relevant metrics
- [x] Import restores historical view

---

## 4. Implementation Phases

### Phase 1: Cross-Platform Foundation (Week 1-2)
1. [x] Fix VMS-based stacked bar (use RSS) 
2. [x] Hide smaps on non-Linux
3. [x] Add platform detection to SSE
4. [x] Implement RSS trend sparkline
5. [x] Add allocation rate tracking

### Phase 2: Leak Detection (Week 3-4)
1. [x] Add GC efficiency metric
2. [x] Implement object survival histogram
3. [x] Add retained size sampling
4. [x] Create leak warning indicators

### Phase 3: Application Profiles (Week 5-6)
1. [x] Implement profile selector
2. [x] Create game profile with frame budget
3. [x] Create REPL profile with eval delta
4. [x] Adapt panel visibility per profile

### Phase 4: Capacity Planning (Week 7-8)
1. [x] Add fragmentation metrics
2. [x] Build capacity planner UI
3. [x] Add configuration export
4. [x] Extended history buffer

---

## 5. Validation Criteria Summary

### 5.1 Cross-Platform
- [x] Dashboard fully functional on macOS (no broken visualizations)
- [x] Dashboard fully functional on Linux (smaps visible)
- [x] VMS display appropriate per platform
- [x] All core metrics available on both platforms

### 5.2 Leak Detection
- [x] Can detect simulated leak (retained list) within 5 GC cycles
- [x] Warning appears when retention grows
- [x] Object survival histogram shows distribution

### 5.3 Performance
- [x] Dashboard renders at 60fps with all panels open
- [x] SSE events processed within 16ms
- [x] Memory overhead < 10MB for dashboard state

### 5.4 Usability
- [x] Key metrics visible without scrolling (glanceable)
- [x] Profile switch hides irrelevant panels
- [x] Tooltips explain all metrics
- [x] Keyboard navigation works (j/k/space)

---

## 6. Success Metrics

| Metric | Current | Target |
|--------|---------|--------|
| macOS usability score | 40% (broken VMS, no smaps) | 95% |
| Time to detect leak | Manual inspection | < 1 minute with warnings |
| Game profile relevance | 0% (no frame metrics) | 80% (frame budget visible) |
| REPL profile relevance | 50% (basic heap) | 90% (per-eval delta) |
| Cross-platform parity | 60% | 95% |

---

## 7. Non-Goals (Out of Scope)

1. **Distributed tracing** - Focus on single-process diagnostics
2. **Historical persistence** - No database, in-memory only
3. **Alerting/notifications** - Visual warnings only
4. **Custom metric definitions** - Use built-in metrics
5. **Windows support** - macOS/Linux priority, Windows later
6. **Mobile dashboard** - Desktop browser focus

---

## 8. References

- Current dashboard: `src/modules/aio/debug/`
- Memory diagnostics plan: `docs/MEMORY_DIAGNOSTICS_PLAN.md`
- Dashboard design: `docs/DASHBOARD_DESIGN.md`
- HTTP memory architecture: `docs/HTTP_MEMORY_ARCHITECTURE_V2.md`
