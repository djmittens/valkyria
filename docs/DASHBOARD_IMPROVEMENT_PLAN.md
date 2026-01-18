# Debug Dashboard Improvement Plan

This document synthesizes expert research on observability dashboards, modern visual design trends, and a detailed UX analysis of the current Valkyria debug dashboard to provide a prioritized improvement plan.

---

## Executive Summary

The Valkyria debug dashboard has a **strong foundation** with modern dark theme, responsive grid layout, real-time SSE updates, and comprehensive memory visualization. However, expert analysis identified opportunities to improve:

1. **Information Architecture** - Fix fragmented memory sections, orphaned resources
2. **Visual Hierarchy** - Clearer section differentiation, inline legends
3. **Accessibility** - WCAG AA compliance, keyboard navigation, screen reader support
4. **Information Density** - Progressive disclosure, collapsible sections, reduced redundancy
5. **Animation/Transitions** - Loading states, smoother updates, reduced visual fatigue
6. **Help System** - Context-sensitive tooltips, onboarding, severity indicators

---

## Current Strengths (Keep These)

The dashboard already follows 2024-2025 best practices in many areas:

| Area | Implementation | Status |
|------|----------------|--------|
| Dark Mode Palette | GitHub-style with deep grays (#0d1117-#1c2128) | Excellent |
| Semantic Colors | Green/Yellow/Red with muted variants | Excellent |
| Spacing System | 8px grid (4, 8, 12, 16, 24, 32) | Excellent |
| Typography | System font stack, tabular-nums for metrics | Excellent |
| Responsive Grid | CSS Grid with 1400px/900px breakpoints | Good |
| Real-time Updates | SSE for memory diagnostics, 1s polling for metrics | Good |
| Micro-animations | 300ms flash, 2s pulse, transition easing | Good |
| Accessibility Base | Skip link, focus-visible, ARIA roles | Good foundation |
| Memory Visualization | Grid-based slab view with flash animation | Unique/Excellent |

---

## Phase 0: Information Architecture Fixes (HIGHEST PRIORITY)

These are fundamental structural problems that affect user understanding of the dashboard.

### 0.1 Fragmented VM Memory Visualization

**Current Problem:**
```
VM Metrics Section
├── GC Panel (garbage collector stats)
├── Heap Memory (gauge)           ← Shows heap % usage
├── Interpreter (stats)
└── Memory Resources subsection
    ├── LVAL Objects (slab grid)  ← Shows same heap allocation!
    └── Scratch Arena (gauge)
```

The "Heap Memory" gauge and "LVAL Objects" slab grid both visualize GC-managed memory but are displayed separately with no visual connection. Users see:
- A percentage gauge showing "72% used"
- A grid showing individual slot allocation

These are the SAME data from different perspectives, but this relationship is invisible.

**Proposed Restructure:**
```
VM Metrics Section
├── GC Panel (garbage collector stats + reclaim info)
├── Interpreter (stats)
└── VM Memory subsection (consolidated)
    ├── GC Heap
    │   ├── LVAL Slab Grid (visual)
    │   ├── Usage gauge (72% of 256K slots)
    │   └── Inline legend (free/used/flash)
    └── Scratch Arena
        ├── Usage bar with HWM
        └── Overflow count
```

**Implementation:**

**File:** `src/modules/aio/debug/body.html`

Remove standalone Heap Memory panel (lines 119-158) and integrate into Memory Resources:

```html
<!-- Replace lines 199-241 with consolidated VM Memory section -->
<div class="subsection-header">
  <h3 class="subsection-title">VM Memory</h3>
  <div class="section-badges">
    <span class="section-badge">
      <span class="sse-dot"></span> Live
    </span>
  </div>
</div>

<div class="vm-memory-consolidated">
  <!-- GC Heap (LVAL Slab) -->
  <div class="memory-block gc-heap-block">
    <div class="memory-block-header">
      <div class="memory-block-title">
        <span class="memory-icon gc">GC</span>
        GC Heap (LVAL Objects)
      </div>
      <div class="memory-block-summary">
        <span class="usage-pct" id="heap-gauge-value">--</span>% used
        <span class="usage-detail">(<span id="heap-used">--</span> / <span id="heap-total">--</span>)</span>
      </div>
    </div>
    <div class="memory-block-body">
      <div class="slab-with-legend">
        <div class="memory-slab-panel wide" id="lval-panel">
          <div class="slab-canvas">
            <div class="slab-grid" id="lval-grid"
                 style="grid-template-columns: repeat(32, 1fr);"></div>
          </div>
          <div class="slab-stats">
            <span><span class="used-count">0</span> / 262,144 slots</span>
            <span class="overflow-warning" style="display:none"></span>
          </div>
        </div>
        <!-- Inline legend for this visualization -->
        <div class="memory-legend-inline">
          <div class="legend-item"><div class="legend-dot free"></div><span>Free</span></div>
          <div class="legend-item"><div class="legend-dot used"></div><span>Used</span></div>
          <div class="legend-item"><div class="legend-dot flash"></div><span>Changed</span></div>
        </div>
      </div>
    </div>
  </div>

  <!-- Scratch Arena -->
  <div class="memory-block scratch-block">
    <div class="memory-block-header">
      <div class="memory-block-title">
        <span class="memory-icon scratch">S</span>
        Scratch Arena
      </div>
      <div class="memory-block-summary">
        <span class="pct" id="scratch-pct">0%</span>
        <span class="usage-detail" id="scratch-usage">0B / 0B</span>
      </div>
    </div>
    <div class="memory-block-body">
      <div class="arena-gauge" data-arena="scratch">
        <div class="arena-track">
          <div class="arena-bar healthy" style="width: 0%;"></div>
          <div class="arena-hwm" style="left: 0%;"></div>
        </div>
      </div>
      <div class="memory-legend-inline">
        <div class="legend-item"><div class="legend-dot hwm"></div><span>High Water Mark</span></div>
      </div>
    </div>
  </div>
</div>
```

### 0.2 Memory Legend Location

**Current Problem:**
```
Page Layout:
├── Health Overview
├── VM Section (memory grids here)
├── AIO Section (memory grids here)
├── HTTP Servers
└── Memory Legend ← User must scroll past everything to understand colors!
```

**Solution:** Remove footer legend entirely. Add inline legends within each memory visualization block (as shown in 0.1 above).

**File:** `src/modules/aio/debug/body.html`

Delete the footer legend (lines 379-397):
```html
<!-- DELETE THIS SECTION -->
<div class="memory-legend-footer">
  ...
</div>
```

**File:** `src/modules/aio/debug/style.css`

Add inline legend styles:
```css
/* Inline Memory Legend */
.memory-legend-inline {
  display: flex;
  gap: var(--space-md);
  margin-top: var(--space-sm);
  padding-top: var(--space-sm);
  border-top: 1px dashed var(--border-muted);
  font-size: 10px;
}

.memory-legend-inline .legend-item {
  display: flex;
  align-items: center;
  gap: var(--space-xs);
  color: var(--text-muted);
}

.memory-legend-inline .legend-dot {
  width: 8px;
  height: 8px;
  border-radius: 2px;
}
```

### 0.3 AIO Memory Resources Are Orphaned/Global

**Current Problem:**
```
AIO Systems Section
├── System 1 Panel (its own connections, handles, arenas)
├── System 2 Panel (its own connections, handles, arenas)
└── Memory Resources subsection ← GLOBAL slabs, not per-system!
    ├── TCP Buffers (from which system?)
    ├── Handles (from which system?)
    └── Stream Arenas (from which system?)
```

The memory slab grids show **global** allocator state, but they're visually nested under "AIO Systems" as if they belong to a specific system. With multiple AIO systems, each system allocates from these shared pools, but users can't see which slots belong to which system.

**Two Options:**

#### Option A: Move Global Resources to Dedicated Section (Simpler)

Create a new top-level "System Resources" section that clearly shows these are global:

```
New Page Layout:
├── Health Overview
├── VM Metrics (with integrated memory)
├── System Resources ← NEW: Global allocator pools
│   ├── LVAL Slab (moved from VM)
│   ├── TCP Buffers
│   ├── Handles
│   ├── Stream Arenas
│   ├── HTTP Servers
│   └── HTTP Clients
├── AIO Systems (per-system stats only)
└── HTTP Servers
```

#### Option B: Per-System Memory Breakdown (More Accurate, Complex)

Show memory usage per AIO system with the SSE endpoint providing per-system attribution:

```
AIO Systems Section
├── System 1 Panel
│   ├── Stats (iterations, events, handles)
│   ├── Connection Pool
│   └── Memory Usage ← NEW: System 1's allocations
│       ├── Handles: 47 / 2056 (this system)
│       ├── TCP Buffers: 12 / 200 (this system)
│       └── Stream Arenas: 3 / 64 (this system)
├── System 2 Panel
│   └── Memory Usage ← NEW: System 2's allocations
└── Global Pools (overflow tracking)
    └── Total usage across all systems
```

**Recommendation:** Start with **Option A** (simpler, clearer mental model). Option B requires backend changes to track per-system allocations.

**Implementation for Option A:**

**File:** `src/modules/aio/debug/body.html`

Move the AIO Memory Resources section OUT of the AIO section and create a new global section:

```html
<!-- NEW: Global System Resources Section (insert after VM section, before AIO) -->
<section class="section-group" aria-labelledby="resources-section-title">
  <div class="section-header">
    <div class="section-icon resources" aria-hidden="true">R</div>
    <h2 class="section-title" id="resources-section-title">System Resources</h2>
    <span class="section-subtitle">Global Allocator Pools</span>
    <div class="section-badges">
      <span class="section-badge">
        <span class="sse-dot"></span> Live
      </span>
    </div>
  </div>

  <p class="section-description">
    These pools are shared across all AIO systems. High usage indicates memory pressure.
  </p>

  <div class="memory-slab-grid">
    <!-- TCP Buffers -->
    <div class="memory-slab-panel" id="tcp-buffers-panel">
      <!-- ... existing content ... -->
    </div>
    <!-- Handles, Stream Arenas, HTTP Servers, HTTP Clients -->
    <!-- ... move from AIO section ... -->
  </div>

  <!-- Inline legend -->
  <div class="memory-legend-inline">
    <div class="legend-item"><div class="legend-dot free"></div><span>Free slot</span></div>
    <div class="legend-item"><div class="legend-dot used"></div><span>Used slot</span></div>
    <div class="legend-item"><div class="legend-dot flash"></div><span>State change</span></div>
  </div>
</section>

<!-- AIO Systems Section (now ONLY contains per-system panels) -->
<section class="section-group" aria-labelledby="aio-section-title">
  <div class="section-header">
    <div class="section-icon aio" aria-hidden="true">AIO</div>
    <h2 class="section-title" id="aio-section-title">AIO Systems</h2>
    <span class="section-subtitle">Event Loops and Connections</span>
    <!-- ... badges ... -->
  </div>

  <div class="grid-2" id="aio-systems-container">
    <!-- Dynamic system panels only - no memory grids here -->
  </div>
</section>
```

**File:** `src/modules/aio/debug/style.css`

Add resources section styling:
```css
.section-icon.resources {
  background: var(--color-warning-bg);
  color: var(--color-warning);
}

.section-description {
  font-size: 12px;
  color: var(--text-muted);
  margin-bottom: var(--space-md);
  max-width: 600px;
}
```

### 0.4 Label Slab Allocators Explicitly

**Current Problem:**
```
Panel Headers:
├── "TCP Buffers"      ← What kind of data structure?
├── "Handles"          ← Why is it a grid?
├── "LVAL Objects"     ← What do the cells mean?
```

Users see grids of colored cells but have no context that these are **slab allocators** - pre-allocated fixed-size memory pools. The grid visualization makes sense for slabs (each cell = one slot), but this isn't explained.

**Solution:** Add "Slab" label and brief explanation to each panel.

**File:** `src/modules/aio/debug/body.html`

Update slab panel headers:

```html
<!-- Example: TCP Buffers panel -->
<div class="memory-slab-panel" id="tcp-buffers-panel">
  <div class="slab-header">
    <span class="slab-name">TCP Buffers</span>
    <span class="slab-type-badge">Slab</span>
    <span class="slab-badge">0% used</span>
  </div>
  <!-- ... -->
</div>
```

**File:** `src/modules/aio/debug/style.css`

Add slab type badge styling:

```css
.slab-type-badge {
  font-size: 9px;
  padding: 1px 4px;
  border-radius: 3px;
  background: var(--color-purple-bg);
  color: var(--color-purple);
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin-left: var(--space-xs);
}
```

**Alternative: Section-Level Explanation**

Instead of per-panel badges, add an explanation to the section header:

```html
<div class="section-header">
  <div class="section-icon resources" aria-hidden="true">R</div>
  <h2 class="section-title">System Resources</h2>
  <span class="section-subtitle">Slab Allocator Pools</span>
</div>

<p class="section-description">
  Pre-allocated fixed-size memory pools. Each cell represents one slot.
  <span class="legend-inline">
    <span class="dot used"></span> = allocated,
    <span class="dot free"></span> = available
  </span>
</p>
```

**Recommended Approach:** Use **both**:
1. Section subtitle says "Slab Allocator Pools"
2. Each panel has small "Slab" badge for reinforcement
3. Inline legend explains cell meaning

This teaches users the pattern once at the section level, then reinforces with visual badges.

---

### 0.5 Proposed New Page Structure

After all Phase 0 changes, the dashboard structure becomes:

```
Header
├── Logo, Status Badge, Uptime, Last Update

Health Overview
├── Request Rate | Error Rate | Avg Latency | Heap Usage

VM Metrics
├── GC Panel (cycles, pauses, timeline)
├── Interpreter (evals, calls, stack depth)
└── VM Memory (consolidated)
    ├── GC Heap with LVAL grid + usage gauge + inline legend
    └── Scratch Arena with bar + HWM + inline legend

System Resources (NEW - Global Pools)
├── Description: "Shared across all AIO systems"
├── Slab grids: TCP Buffers, Handles, Stream Arenas, HTTP Servers/Clients
└── Inline legend

AIO Systems (Simplified - Per-System Only)
├── System panels with:
│   ├── Loop stats (iterations, events)
│   ├── Handle count
│   └── Connection pool visualization
└── No memory grids (moved to System Resources)

HTTP Servers
├── Per-server cards with status, latency, throughput
```

This structure:
1. **Consolidates VM memory** - Heap gauge + LVAL grid together with clear relationship
2. **Puts legends inline** - Users see explanation next to visualization
3. **Clarifies global vs per-system** - System Resources are explicitly global
4. **Simplifies AIO section** - Only per-system runtime stats

---

## Phase 1: Critical Fixes (Week 1)

### 1.1 Accessibility Compliance (WCAG AA)

#### Fix Color Contrast Failures
**File:** `src/modules/aio/debug/style.css`

```css
/* Line ~12: Change --text-faint for WCAG AA compliance */
--text-faint: #7d8590;  /* Was #6e7681 (3.2:1), now 4.5:1 */
```

**Issue:** `--text-faint` on `--bg-tertiary` fails WCAG AA for small text (3.2:1 < 4.5:1 required).

#### Add ARIA Labels to Memory Grids
**File:** `src/modules/aio/debug/body.html`

Replace static grid containers with accessible versions:

```html
<!-- Line ~217: LVAL Objects grid -->
<div class="slab-grid" id="lval-grid"
     role="img"
     aria-label="LVAL Object Slab: loading..."
     aria-live="polite"
     aria-atomic="false"
     style="grid-template-columns: repeat(32, 1fr);"></div>
```

**File:** `src/modules/aio/debug/script.js`

Update `updateSlabGrid()` to set dynamic aria-label:

```javascript
// After line ~1315
const panelEl = grid.closest('.memory-slab-panel');
const ariaLabel = `${slab.name.replace(/_/g, ' ')}: ${slab.used} of ${slab.total} slots used (${Math.round(slab.used/slab.total*100)}%)${slab.overflow > 0 ? `, ${slab.overflow} overflows detected` : ''}`;
grid.setAttribute('aria-label', ariaLabel);
```

#### Add Arena Gauge ARIA Attributes
**File:** `src/modules/aio/debug/body.html`

```html
<!-- Line ~230: Scratch Arena gauge -->
<div class="arena-gauge" data-arena="scratch"
     role="progressbar"
     aria-valuenow="0"
     aria-valuemin="0"
     aria-valuemax="100"
     aria-label="Scratch Arena: 0% used">
```

**File:** `src/modules/aio/debug/script.js`

Update `updateArenaGauge()`:

```javascript
// Line ~1379 area
gauge.setAttribute('aria-valuenow', Math.round(percentage));
gauge.setAttribute('aria-label', `${arena.name}: ${percentage.toFixed(0)}% used, ${usedStr} of ${capacityStr}`);
```

### 1.2 Keyboard Navigation Improvements

#### Add Visible Focus Styles to Histogram Bars
**File:** `src/modules/aio/debug/style.css`

```css
/* Line ~717-720: Enhance histogram bar focus */
.histogram-bar:focus-visible {
  outline: 2px solid var(--color-info);
  outline-offset: 2px;
  filter: brightness(1.3);
}

/* Show tooltip on focus (requires JS changes) */
.histogram-bar:focus-visible::after {
  content: attr(title);
  position: absolute;
  bottom: 100%;
  left: 50%;
  transform: translateX(-50%);
  background: var(--bg-elevated);
  border: 1px solid var(--border-default);
  border-radius: var(--radius-sm);
  padding: var(--space-xs) var(--space-sm);
  font-size: 11px;
  white-space: nowrap;
  z-index: 100;
}
```

#### Add Keyboard Shortcuts
**File:** `src/modules/aio/debug/script.js`

Add to end of file:

```javascript
// Keyboard shortcuts for section navigation
document.addEventListener('keydown', function(e) {
  if (!e.altKey) return;

  var shortcuts = {
    'h': '#health-title',      // Alt+H: Health Overview
    'v': '#vm-section-title',  // Alt+V: VM Metrics
    'a': '#aio-section-title', // Alt+A: AIO Systems
    's': '#http-section-title' // Alt+S: HTTP Servers
  };

  var target = shortcuts[e.key.toLowerCase()];
  if (target) {
    e.preventDefault();
    var el = document.querySelector(target);
    if (el) {
      el.scrollIntoView({ behavior: 'smooth', block: 'start' });
      el.focus();
    }
  }
});
```

### 1.3 Degraded Mode UI for Connection Failures

#### Add Stale Data Warning
**File:** `src/modules/aio/debug/style.css`

```css
/* Add after line ~1138 */
.panel.stale {
  opacity: 0.7;
  position: relative;
}

.panel.stale::before {
  content: 'Data may be stale';
  position: absolute;
  top: var(--space-sm);
  right: var(--space-sm);
  font-size: 10px;
  color: var(--color-warning);
  background: var(--color-warning-bg);
  padding: 2px 6px;
  border-radius: var(--radius-sm);
  z-index: 10;
}

.sse-status-warning {
  display: none;
  background: var(--color-warning-bg);
  border: 1px solid var(--color-warning-muted);
  color: var(--color-warning);
  padding: var(--space-sm) var(--space-md);
  border-radius: var(--radius-md);
  margin-bottom: var(--space-md);
  font-size: 12px;
}

.sse-status-warning.visible {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
}
```

**File:** `src/modules/aio/debug/body.html`

Add after error-banner (line ~37):

```html
<div class="sse-status-warning" id="sse-warning">
  <span>Memory diagnostics stream disconnected. Last update: <span id="sse-last-update">--</span></span>
</div>
```

**File:** `src/modules/aio/debug/script.js`

Enhance `MemoryDiagnostics` class:

```javascript
// Add to handleMemoryUpdate (after line ~1249)
var sseWarning = document.getElementById('sse-warning');
var sseLastUpdate = document.getElementById('sse-last-update');
if (sseWarning) sseWarning.classList.remove('visible');
if (sseLastUpdate) sseLastUpdate.textContent = new Date().toLocaleTimeString();

// Add to updateConnectionStatus(false) (line ~1242-1246)
var sseWarning = document.getElementById('sse-warning');
if (sseWarning) sseWarning.classList.add('visible');
document.querySelectorAll('.memory-slab-panel, .memory-arena-section').forEach(function(el) {
  el.classList.add('stale');
});
```

---

## Phase 2: Visual Hierarchy Improvements (Week 2)

### 2.1 Enhance Section Differentiation

#### Add Subtle Background Tints to Sections
**File:** `src/modules/aio/debug/style.css`

```css
/* After line ~274 - Section Groups */
.section-group.vm-section {
  background: linear-gradient(135deg, rgba(163, 113, 247, 0.02) 0%, transparent 50%);
  border-radius: var(--radius-lg);
  padding: var(--space-lg);
  margin: 0 calc(-1 * var(--space-lg)) var(--space-2xl);
}

.section-group.aio-section {
  background: linear-gradient(135deg, rgba(57, 212, 212, 0.02) 0%, transparent 50%);
  border-radius: var(--radius-lg);
  padding: var(--space-lg);
  margin: 0 calc(-1 * var(--space-lg)) var(--space-2xl);
}

.section-group.http-section {
  background: linear-gradient(135deg, rgba(88, 166, 255, 0.02) 0%, transparent 50%);
  border-radius: var(--radius-lg);
  padding: var(--space-lg);
  margin: 0 calc(-1 * var(--space-lg)) var(--space-2xl);
}
```

**File:** `src/modules/aio/debug/body.html`

Add class to sections:

```html
<!-- Line ~66 -->
<section class="section-group vm-section" aria-labelledby="vm-section-title">

<!-- Line ~244 -->
<section class="section-group aio-section" aria-labelledby="aio-section-title">

<!-- Line ~358 -->
<section class="section-group http-section" aria-labelledby="http-section-title">
```

### 2.2 Health Overview Visual Enhancement

#### Add State-Based Card Borders
**File:** `src/modules/aio/debug/style.css`

```css
/* After line ~266 - Health Card Status Styles */
.health-card {
  transition: border-color 0.3s ease, box-shadow 0.3s ease;
  border: 2px solid transparent;
}

.health-card.status-ok {
  border-color: var(--color-ok-muted);
  box-shadow: 0 0 0 1px var(--color-ok-bg);
}

.health-card.status-warning {
  border-color: var(--color-warning-muted);
  box-shadow: 0 0 8px var(--color-warning-bg);
}

.health-card.status-critical {
  border-color: var(--color-error-muted);
  box-shadow: 0 0 8px var(--color-error-bg);
  animation: pulse-critical 2s infinite;
}

@keyframes pulse-critical {
  0%, 100% { box-shadow: 0 0 8px var(--color-error-bg); }
  50% { box-shadow: 0 0 16px var(--color-error-bg); }
}
```

**File:** `src/modules/aio/debug/script.js`

Add health card status updates (in `updateDashboard` function after line ~1036):

```javascript
// Update health card statuses
function updateHealthCardStatus(cardId, value, warningThreshold, criticalThreshold, inverse) {
  var card = document.querySelector('.health-card:has(#' + cardId + ')') ||
             document.getElementById(cardId).closest('.health-card');
  if (!card) return;

  card.classList.remove('status-ok', 'status-warning', 'status-critical');

  var isWarning = inverse ? value < warningThreshold : value > warningThreshold;
  var isCritical = inverse ? value < criticalThreshold : value > criticalThreshold;

  if (isCritical) card.classList.add('status-critical');
  else if (isWarning) card.classList.add('status-warning');
  else card.classList.add('status-ok');
}

updateHealthCardStatus('health-error-rate', errorRate, 1, 5, false);
updateHealthCardStatus('health-heap-pct', heapPct, 70, 90, false);
updateHealthCardStatus('health-avg-latency', avgLatency, 100, 500, false);
```

### 2.3 Improve Subsection Headers

**File:** `src/modules/aio/debug/style.css`

```css
/* Replace lines 1179-1200 */
.subsection-header {
  display: flex;
  align-items: center;
  gap: var(--space-md);
  margin-top: var(--space-xl);
  margin-bottom: var(--space-md);
  padding: var(--space-sm) var(--space-md);
  background: var(--bg-tertiary);
  border-left: 3px solid var(--color-purple);
  border-radius: 0 var(--radius-sm) var(--radius-sm) 0;
}

.subsection-title {
  font-size: 12px;
  font-weight: 600;
  color: var(--text-secondary);
  text-transform: uppercase;
  letter-spacing: 0.75px;
}
```

---

## Phase 3: Information Density Optimization (Week 3)

### 3.1 Collapsible Server Cards

#### Add Expand/Collapse to HTTP Server Cards
**File:** `src/modules/aio/debug/style.css`

```css
/* Add after entity-card styles (~line 400) */
.entity-card.collapsed .entity-body {
  display: none;
}

.entity-card .expand-toggle {
  background: none;
  border: none;
  color: var(--text-muted);
  cursor: pointer;
  padding: var(--space-xs);
  margin-left: auto;
  transition: transform 0.2s;
}

.entity-card.collapsed .expand-toggle {
  transform: rotate(-90deg);
}
```

**File:** `src/modules/aio/debug/script.js`

Modify `createServerCard()` to add toggle:

```javascript
// Add to entity-header (line ~524-527)
<button class="expand-toggle"
        onclick="this.closest('.entity-card').classList.toggle('collapsed')"
        aria-label="Toggle details">
  <span aria-hidden="true">▼</span>
</button>
```

### 3.2 Remove Redundant Connection Pool Bar

**File:** `src/modules/aio/debug/script.js`

Remove or simplify the duplicate bar chart in `createAioSystemPanel()` (lines 311-315). Keep only the mini-grid visualization.

```javascript
// Replace lines 306-316 with simplified version:
'<div style="margin-bottom: var(--space-md);">' +
  '<div class="pool-header">' +
    '<span class="pool-name">Connection Pool</span>' +
    '<span class="pool-usage aio-sys-conn-usage">-- / --</span>' +
  '</div>' +
  '<div class="conn-pool-mini aio-sys-conn-grid" role="img" aria-label="Connection pool state"></div>' +
  '<div class="conn-pool-mini-legend">' +
    '<div class="legend-item"><div class="legend-dot active"></div><span>Active</span></div>' +
    '<div class="legend-item"><div class="legend-dot idle"></div><span>Idle</span></div>' +
    '<div class="legend-item"><div class="legend-dot closing"></div><span>Closing</span></div>' +
  '</div>' +
'</div>' +
```

### 3.3 Custom Tooltip Component

Replace native title tooltips with accessible custom tooltips.

**File:** `src/modules/aio/debug/style.css`

```css
/* Add at end of file */
/* Custom Tooltip Component */
.has-tooltip {
  position: relative;
}

.tooltip {
  visibility: hidden;
  opacity: 0;
  position: absolute;
  bottom: calc(100% + 8px);
  left: 50%;
  transform: translateX(-50%);
  background: var(--bg-elevated);
  border: 1px solid var(--border-default);
  border-radius: var(--radius-md);
  padding: var(--space-sm) var(--space-md);
  font-size: 12px;
  line-height: 1.5;
  color: var(--text-secondary);
  max-width: 300px;
  white-space: normal;
  z-index: 1000;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4);
  transition: opacity 0.15s, visibility 0.15s;
  pointer-events: none;
}

.tooltip::after {
  content: '';
  position: absolute;
  top: 100%;
  left: 50%;
  transform: translateX(-50%);
  border: 6px solid transparent;
  border-top-color: var(--border-default);
}

.has-tooltip:hover .tooltip,
.has-tooltip:focus-within .tooltip {
  visibility: visible;
  opacity: 1;
}

.tooltip-title {
  font-weight: 600;
  color: var(--text-primary);
  margin-bottom: var(--space-xs);
}

.tooltip-body {
  color: var(--text-muted);
}
```

**File:** `src/modules/aio/debug/script.js`

Add tooltip initialization function:

```javascript
// Add helper to convert title attributes to accessible tooltips
function initializeTooltips() {
  document.querySelectorAll('[data-tooltip]').forEach(function(el) {
    var tooltipText = el.getAttribute('data-tooltip');
    var tooltipTitle = el.getAttribute('data-tooltip-title') || '';

    el.classList.add('has-tooltip');
    el.removeAttribute('title'); // Remove native tooltip

    var tooltip = document.createElement('div');
    tooltip.className = 'tooltip';
    tooltip.setAttribute('role', 'tooltip');
    tooltip.innerHTML = (tooltipTitle ? '<div class="tooltip-title">' + tooltipTitle + '</div>' : '') +
                        '<div class="tooltip-body">' + tooltipText + '</div>';

    el.appendChild(tooltip);
    el.setAttribute('aria-describedby', 'tooltip-' + Math.random().toString(36).substr(2, 9));
    tooltip.id = el.getAttribute('aria-describedby');
  });
}

// Call after DOM ready
document.addEventListener('DOMContentLoaded', initializeTooltips);
```

---

## Phase 4: Animation & Transition Polish (Week 4)

### 4.1 Add Loading States

**File:** `src/modules/aio/debug/style.css`

```css
/* Skeleton loading animation */
@keyframes skeleton-pulse {
  0%, 100% { opacity: 0.4; }
  50% { opacity: 0.7; }
}

.skeleton {
  background: linear-gradient(90deg, var(--bg-tertiary) 0%, var(--bg-elevated) 50%, var(--bg-tertiary) 100%);
  background-size: 200% 100%;
  animation: skeleton-pulse 1.5s ease-in-out infinite;
  border-radius: var(--radius-sm);
}

.health-card-value.loading {
  color: transparent;
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
  animation: skeleton-pulse 1.5s ease-in-out infinite;
}
```

**File:** `src/modules/aio/debug/script.js`

Add loading state management:

```javascript
// Show loading state on initial load
function showLoadingState() {
  document.querySelectorAll('.health-card-value').forEach(function(el) {
    el.classList.add('loading');
  });
}

function hideLoadingState() {
  document.querySelectorAll('.health-card-value').forEach(function(el) {
    el.classList.remove('loading');
  });
}

// Call in poll() success handler
hideLoadingState();
```

### 4.2 Smooth Entity Status Transitions

**File:** `src/modules/aio/debug/style.css`

```css
/* Modify entity-status (around line 414) */
.entity-status {
  /* ... existing styles ... */
  transition: background-color 0.3s ease, box-shadow 0.3s ease;
}

.entity-status.ok {
  box-shadow: 0 0 8px var(--color-ok-bg);
}

.entity-status.warning {
  box-shadow: 0 0 8px var(--color-warning-bg);
}

.entity-status.error {
  box-shadow: 0 0 8px var(--color-error-bg);
}
```

### 4.3 Adaptive Refresh Rate

Reduce visual fatigue by adapting update frequency to change rate.

**File:** `src/modules/aio/debug/script.js`

```javascript
// Replace fixed POLL_INTERVAL with adaptive system
var adaptiveInterval = {
  min: 500,
  normal: 1000,
  slow: 5000,
  current: 1000,
  changeThreshold: 0.05, // 5% change triggers faster updates
  lastValues: {}
};

function calculateChangeRate(metrics) {
  var changes = 0;
  var total = 0;

  ['requestRate', 'errorRate', 'heapPct'].forEach(function(key) {
    var current = metrics[key] || 0;
    var last = adaptiveInterval.lastValues[key] || current;
    var change = Math.abs(current - last) / Math.max(last, 1);
    changes += change;
    total++;
    adaptiveInterval.lastValues[key] = current;
  });

  return changes / total;
}

function getAdaptiveInterval(changeRate) {
  if (changeRate > 0.10) return adaptiveInterval.min;
  if (changeRate > 0.02) return adaptiveInterval.normal;
  return adaptiveInterval.slow;
}

// Use in poll() function:
// var nextInterval = getAdaptiveInterval(calculateChangeRate({...}));
// setTimeout(poll, nextInterval);
```

### 4.4 Staggered Card Animations

**File:** `src/modules/aio/debug/style.css`

```css
/* Add staggered entrance animation for cards */
@keyframes card-enter {
  from {
    opacity: 0;
    transform: translateY(8px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.entity-card {
  animation: card-enter 0.3s ease-out backwards;
}

.entity-card:nth-child(1) { animation-delay: 0ms; }
.entity-card:nth-child(2) { animation-delay: 50ms; }
.entity-card:nth-child(3) { animation-delay: 100ms; }
.entity-card:nth-child(4) { animation-delay: 150ms; }
.entity-card:nth-child(5) { animation-delay: 200ms; }
.entity-card:nth-child(6) { animation-delay: 250ms; }
```

---

## Phase 5: Help System Enhancement (Week 5+)

### 5.1 Context-Sensitive Severity Indicators

Enhance tooltips to show whether current values are good/bad.

**File:** `src/modules/aio/debug/script.js`

```javascript
// Add severity context to metric updates
function getSeverityContext(value, thresholds, metricName) {
  var severity = 'ok';
  var message = '';

  if (value >= thresholds.critical) {
    severity = 'critical';
    message = thresholds.criticalMessage || 'Critical - immediate attention needed';
  } else if (value >= thresholds.warning) {
    severity = 'warning';
    message = thresholds.warningMessage || 'Warning - monitor closely';
  } else {
    message = thresholds.okMessage || 'Healthy';
  }

  return { severity: severity, message: message };
}

// Example usage for GC max pause:
var gcContext = getSeverityContext(gcMaxPauseMs, {
  warning: 10,
  critical: 50,
  warningMessage: 'Above 10ms - may affect P99 latency',
  criticalMessage: 'Above 50ms - may cause connection timeouts',
  okMessage: 'Within acceptable range'
});

// Update tooltip dynamically
document.getElementById('gc-max-pause').closest('[data-tooltip]')
  .setAttribute('data-tooltip', 'Current: ' + gcMaxPauseMs + 'ms - ' + gcContext.message);
```

### 5.2 Onboarding Tour

Add first-time user guidance.

**File:** `src/modules/aio/debug/body.html`

Add at end of body:

```html
<!-- Onboarding Tour Modal -->
<div class="onboarding-modal" id="onboarding" role="dialog" aria-modal="true" aria-labelledby="onboarding-title">
  <div class="onboarding-content">
    <h2 id="onboarding-title">Welcome to Valkyria Dashboard</h2>
    <div class="onboarding-steps">
      <div class="onboarding-step active" data-step="1">
        <h3>Health Overview</h3>
        <p>Key metrics at a glance. Green borders = healthy, yellow = warning, red = critical.</p>
      </div>
      <div class="onboarding-step" data-step="2">
        <h3>Real-time Memory</h3>
        <p>Memory grids update via SSE every 100ms. Watch for flash animations indicating state changes.</p>
      </div>
      <div class="onboarding-step" data-step="3">
        <h3>HTTP Servers</h3>
        <p>Per-server metrics including latency histograms and throughput. Click cards to expand details.</p>
      </div>
    </div>
    <div class="onboarding-nav">
      <button onclick="prevOnboardingStep()">Previous</button>
      <span class="onboarding-dots"></span>
      <button onclick="nextOnboardingStep()">Next</button>
      <button onclick="closeOnboarding()">Skip Tour</button>
    </div>
  </div>
</div>
```

---

## Implementation Priority Matrix

| Priority | Issue | Impact | Effort | Phase |
|----------|-------|--------|--------|-------|
| **P0** | **Consolidate VM memory (heap + LVAL)** | **Architecture** | **Medium** | **0** |
| **P0** | **Move legends inline** | **Usability** | **Low** | **0** |
| **P0** | **Separate global resources from AIO** | **Architecture** | **Medium** | **0** |
| **P0** | **Label slab allocators explicitly** | **Clarity** | **Low** | **0** |
| **P0** | WCAG AA contrast fix | Accessibility | Low | 1 |
| **P0** | ARIA labels on memory grids | Screen reader | Low | 1 |
| **P0** | SSE disconnection warning | Data trust | Medium | 1 |
| **P1** | Keyboard shortcuts | Accessibility | Low | 1 |
| **P1** | Health card status borders | Visual clarity | Low | 2 |
| **P1** | Section background tints | Hierarchy | Low | 2 |
| **P2** | Collapsible server cards | Density | Medium | 3 |
| **P2** | Remove duplicate conn bar | Consistency | Low | 3 |
| **P2** | Custom tooltip component | Accessibility | Medium | 3 |
| **P3** | Loading states | Polish | Low | 4 |
| **P3** | Adaptive refresh rate | Performance | Medium | 4 |
| **P3** | Staggered animations | Polish | Low | 4 |
| **P4** | Severity context in tooltips | Usability | Medium | 5 |
| **P4** | Onboarding tour | Discoverability | High | 5 |

---

## Mobile-Specific Improvements

### Critical Mobile Fixes

1. **Touch Targets**: Increase error banner dismiss button to 44x44px minimum
2. **Slab Grids on Mobile**: Switch to summary-only view below 600px
3. **Add Breakpoint at 1200px**: 3-column to 2-column transition for small laptops

**File:** `src/modules/aio/debug/style.css`

```css
/* Add at 1200px breakpoint */
@media (max-width: 1200px) {
  .grid-3 { grid-template-columns: repeat(2, 1fr); }
  .memory-slab-grid { grid-template-columns: repeat(2, 1fr); }
}

/* Mobile slab summary mode */
@media (max-width: 600px) {
  .slab-canvas {
    display: none;
  }

  .memory-slab-panel::after {
    content: 'Expand on desktop to view grid';
    display: block;
    text-align: center;
    color: var(--text-muted);
    font-size: 11px;
    padding: var(--space-md);
  }

  .error-banner-dismiss {
    min-width: 44px;
    min-height: 44px;
    padding: var(--space-md);
  }
}
```

---

## Performance Considerations

### Reduce Update Overhead

1. **Debounce rapid SSE updates**: If multiple events arrive within 50ms, batch them
2. **Use DocumentFragment for grid updates**: Reduce DOM reflows
3. **Throttle histogram recalculations**: Only recalculate bucket ranges every 5 seconds

### Memory Efficiency

1. **Limit history arrays**: Already capped at 60 entries (HISTORY_SIZE)
2. **Reuse DOM elements**: Your grid rendering already does this
3. **Clean up event listeners**: Add cleanup when cards are removed

---

## Testing Checklist

### Accessibility Testing
- [ ] Run axe-core or WAVE on dashboard
- [ ] Test with screen reader (VoiceOver, NVDA)
- [ ] Verify keyboard navigation (Tab, Enter, Arrow keys)
- [ ] Test with `prefers-reduced-motion: reduce`
- [ ] Verify color contrast with WebAIM checker

### Responsive Testing
- [ ] Test at 1440px (desktop)
- [ ] Test at 1200px (small laptop)
- [ ] Test at 900px (tablet)
- [ ] Test at 600px (large phone)
- [ ] Test at 375px (small phone)

### Real-time Testing
- [ ] Verify SSE reconnection after disconnect
- [ ] Test with high load (>50 requests/second)
- [ ] Verify animations don't cause jank (60fps)
- [ ] Test with network throttling (slow 3G)

---

## Sources & References

### Observability Best Practices
- Grafana Dashboard Best Practices Guide
- Datadog Effective Dashboards Repository
- New Relic APM Design Patterns

### Visual Design
- Vercel Dashboard Redesign Blog
- Linear Design System
- GitHub Actions UI Patterns
- Railway Observability Dashboard

### Accessibility Standards
- WCAG 2.1 Guidelines
- WAI-ARIA Authoring Practices
- Tableau Accessibility for Dashboards

### Memory Visualization
- AMD Radeon Memory Visualizer
- Firefox about:memory Architecture
- Chrome DevTools Memory Panel

---

*Document generated: 2024-12-07*
*Based on expert research from observability, visual design, and UX analysis agents*
