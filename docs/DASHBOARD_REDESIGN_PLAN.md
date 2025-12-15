# Dashboard Redesign Plan: Compact Information-Dense Layout

## Overview

This plan redesigns the Valkyria debug dashboard to maximize information density while reducing visual clutter. The current design suffers from excessive padding, redundant labels, and underutilized screen space, particularly in the System Health Overview section.

## Design Principles

Based on research from Tracy Profiler, Chrome DevTools, Datadog, and Dear ImGui:

1. **Data-ink ratio**: Remove decorative elements; every pixel should convey data
2. **Progressive disclosure**: Show summary first, expand for details
3. **Sparklines over gauges**: Small inline charts convey trends in minimal space
4. **Horizontal metrics**: `Label: Value │ Label: Value` saves 50%+ vertical space
5. **Collapsible sections**: Let users control information density

---

## Task Breakdown

### Phase 1: CSS Variable and Spacing Reduction

**Goal**: Reduce global padding/spacing by ~40% without breaking layouts.

#### Task 1.1: Update CSS Variables
**File**: `src/modules/aio/debug/style.css:36-41`

```css
/* BEFORE */
--space-xs: 4px;
--space-sm: 8px;
--space-md: 12px;
--space-lg: 16px;
--space-xl: 24px;
--space-2xl: 32px;

/* AFTER */
--space-xs: 2px;
--space-sm: 4px;
--space-md: 6px;
--space-lg: 10px;
--space-xl: 16px;
--space-2xl: 24px;
```

#### Task 1.2: Reduce Panel Padding
**File**: `src/modules/aio/debug/style.css:453-455`

```css
/* BEFORE */
.panel-body {
  padding: var(--space-lg);
}

/* AFTER */
.panel-body {
  padding: var(--space-md) var(--space-lg);
}
```

#### Task 1.3: Compact Section Headers
**File**: `src/modules/aio/debug/style.css:330-337`

```css
/* BEFORE */
.section-header {
  display: flex;
  align-items: center;
  gap: var(--space-md);
  margin-bottom: var(--space-lg);
  padding-bottom: var(--space-sm);
  border-bottom: 1px solid var(--border-muted);
}

/* AFTER */
.section-header {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  margin-bottom: var(--space-md);
  padding-bottom: var(--space-xs);
  border-bottom: 1px solid var(--border-muted);
}
```

**Test Plan**:
- [ ] Run dashboard locally: `make repl` then navigate to debug endpoint
- [ ] Verify all sections remain readable
- [ ] Check responsive breakpoints still work (resize browser to 600px, 900px, 1200px)
- [ ] Verify no overlapping elements

---

### Phase 2: Compact Health Overview with Inline Sparklines

**Goal**: Replace verbose health cards with single-line sparkline bar.

#### Task 2.1: Add Sparkline Health Bar CSS
**File**: `src/modules/aio/debug/style.css` (add after line 300)

```css
/* ===== COMPACT HEALTH BAR ===== */
.health-bar-compact {
  display: flex;
  align-items: center;
  gap: var(--space-lg);
  padding: var(--space-sm) var(--space-lg);
  background: var(--bg-secondary);
  border: 1px solid var(--border-default);
  border-radius: var(--radius-lg);
  margin-bottom: var(--space-lg);
}

.health-metric {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  flex: 1;
  min-width: 120px;
}

.health-metric-spark {
  width: 48px;
  height: 20px;
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
  overflow: hidden;
}

.health-metric-spark svg {
  width: 100%;
  height: 100%;
}

.health-metric-label {
  font-size: 11px;
  color: var(--text-muted);
  white-space: nowrap;
}

.health-metric-value {
  font-size: 14px;
  font-weight: 600;
  color: var(--text-primary);
  font-variant-numeric: tabular-nums;
}

.health-metric-value.ok { color: var(--color-ok); }
.health-metric-value.warning { color: var(--color-warning); }
.health-metric-value.critical { color: var(--color-error); }

.health-metric-unit {
  font-size: 11px;
  font-weight: 400;
  color: var(--text-muted);
}

.health-divider {
  width: 1px;
  height: 24px;
  background: var(--border-default);
}
```

#### Task 2.2: Update Health Overview HTML
**File**: `src/modules/aio/debug/body.html:49-74`

Replace the verbose health-overview section:

```html
<!-- BEFORE: Large cards with subtitles -->
<section class="health-overview" aria-labelledby="health-title">
  <h2 id="health-title">System Health Overview</h2>
  <div class="health-grid" role="list">
    <div class="health-card" ...>
      <div class="health-card-label">Request Rate</div>
      <div class="health-card-value" id="health-request-rate">--<span style="font-size: 14px; font-weight: 400;">/s</span></div>
      <div class="health-card-subtitle">Total across all servers</div>
    </div>
    <!-- ... 3 more cards ... -->
  </div>
</section>

<!-- AFTER: Compact inline sparkline bar -->
<section class="health-bar-compact" aria-label="System health metrics">
  <div class="health-metric" title="Requests per second across all HTTP servers">
    <div class="health-metric-spark" id="spark-request-rate"></div>
    <span class="health-metric-label">Req/s</span>
    <span class="health-metric-value" id="health-request-rate">--</span>
  </div>
  <div class="health-divider"></div>
  <div class="health-metric" title="Error rate (4xx + 5xx responses)">
    <div class="health-metric-spark" id="spark-error-rate"></div>
    <span class="health-metric-label">Err</span>
    <span class="health-metric-value" id="health-error-rate">--</span>
    <span class="health-metric-unit">%</span>
  </div>
  <div class="health-divider"></div>
  <div class="health-metric" title="Average response latency">
    <div class="health-metric-spark" id="spark-latency"></div>
    <span class="health-metric-label">Lat</span>
    <span class="health-metric-value" id="health-avg-latency">--</span>
    <span class="health-metric-unit">ms</span>
  </div>
  <div class="health-divider"></div>
  <div class="health-metric" title="GC heap memory utilization">
    <div class="health-metric-spark" id="spark-heap"></div>
    <span class="health-metric-label">Heap</span>
    <span class="health-metric-value" id="health-heap-pct">--</span>
    <span class="health-metric-unit">%</span>
  </div>
</section>
```

#### Task 2.3: Add Mini Sparkline Renderer
**File**: `src/modules/aio/debug/script.js` (add after line 324)

```javascript
// ==================== Rendering: Mini Sparklines (Health Bar) ====================
function renderMiniSparkline(containerId, data, color) {
  var container = $(containerId);
  if (!container || !data || data.length < 2) return;

  var width = 48;
  var height = 20;
  var max = Math.max.apply(null, data);
  var min = Math.min.apply(null, data);
  var range = max - min || 1;

  var points = data.map(function(v, i) {
    var x = (i / (data.length - 1)) * width;
    var y = height - 2 - ((v - min) / range) * (height - 4);
    return x + ',' + y;
  }).join(' ');

  // Area fill points (close the polygon at bottom)
  var areaPoints = points + ' ' + width + ',' + height + ' 0,' + height;

  container.innerHTML =
    '<svg viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none">' +
    '<polygon points="' + areaPoints + '" fill="' + color + '" opacity="0.2"/>' +
    '<polyline points="' + points + '" fill="none" stroke="' + color + '" stroke-width="1.5"/>' +
    '</svg>';
}
```

#### Task 2.4: Update Health Metrics Rendering
**File**: `src/modules/aio/debug/script.js` (find updateHealthOverview function and modify)

Add sparkline updates in the main render loop:

```javascript
// Add to the main update function after calculating rates
renderMiniSparkline('spark-request-rate', history.requestRate.slice(-20), 'var(--color-info)');
renderMiniSparkline('spark-error-rate', history.errorRate.slice(-20), 'var(--color-warning)');
renderMiniSparkline('spark-latency', history.latency.slice(-20), 'var(--color-cyan)');
renderMiniSparkline('spark-heap', history.heapUsage.slice(-20), 'var(--color-ok)');
```

**Test Plan**:
- [ ] Verify sparklines render correctly with sample data
- [ ] Verify sparklines update in real-time with SSE data
- [ ] Check that color changes based on threshold (ok/warning/critical)
- [ ] Test with empty data (should show blank, not error)
- [ ] Verify tooltips still work on hover

---

### Phase 3: Collapsible Panel Headers

**Goal**: Allow users to collapse panels to summary view.

#### Task 3.1: Add Collapsible Panel CSS
**File**: `src/modules/aio/debug/style.css:2014-2036` (enhance existing)

```css
/* ===== COLLAPSIBLE PANELS (enhanced) ===== */
.panel-header {
  cursor: pointer;
  user-select: none;
}

.panel-header:hover {
  background: var(--bg-elevated);
}

.panel-header .expand-icon {
  margin-left: auto;
  font-size: 10px;
  color: var(--text-muted);
  transition: transform 0.2s ease;
}

.panel.collapsed .panel-header .expand-icon {
  transform: rotate(-90deg);
}

.panel.collapsed .panel-body {
  display: none;
}

.panel-summary {
  display: none;
  font-size: 11px;
  color: var(--text-muted);
  margin-left: var(--space-sm);
}

.panel.collapsed .panel-summary {
  display: inline;
}
```

#### Task 3.2: Update GC Panel HTML for Collapse
**File**: `src/modules/aio/debug/body.html:90-128`

```html
<!-- GC Panel with collapse support -->
<article class="panel" aria-labelledby="gc-panel-title" id="gc-panel">
  <div class="panel-header" onclick="togglePanel('gc-panel')" role="button" tabindex="0" aria-expanded="true">
    <div class="panel-icon gc" aria-hidden="true">G</div>
    <h3 class="panel-title" id="gc-panel-title">Garbage Collector</h3>
    <span class="panel-summary" id="gc-summary">3 cycles, 4.2ms max, 12MB reclaimed</span>
    <div class="panel-badge" id="gc-cycles-badge" title="Total GC cycles">-- cycles</div>
    <span class="expand-icon" aria-hidden="true">▼</span>
  </div>
  <div class="panel-body">
    <!-- existing content -->
  </div>
</article>
```

#### Task 3.3: Add Panel Toggle JavaScript
**File**: `src/modules/aio/debug/script.js` (add helper function)

```javascript
// ==================== Panel Collapse/Expand ====================
function togglePanel(panelId) {
  var panel = $(panelId);
  if (!panel) return;

  var isCollapsed = panel.classList.contains('collapsed');
  var header = panel.querySelector('.panel-header');

  if (isCollapsed) {
    panel.classList.remove('collapsed');
    header.setAttribute('aria-expanded', 'true');
  } else {
    panel.classList.add('collapsed');
    header.setAttribute('aria-expanded', 'false');
  }

  // Save preference to localStorage
  try {
    var prefs = JSON.parse(localStorage.getItem('dashboard-panels') || '{}');
    prefs[panelId] = !isCollapsed;
    localStorage.setItem('dashboard-panels', JSON.stringify(prefs));
  } catch(e) {}
}

// Restore panel states on load
function restorePanelStates() {
  try {
    var prefs = JSON.parse(localStorage.getItem('dashboard-panels') || '{}');
    for (var panelId in prefs) {
      if (prefs[panelId]) {
        var panel = $(panelId);
        if (panel) {
          panel.classList.add('collapsed');
          var header = panel.querySelector('.panel-header');
          if (header) header.setAttribute('aria-expanded', 'false');
        }
      }
    }
  } catch(e) {}
}

// Call on page load
document.addEventListener('DOMContentLoaded', restorePanelStates);
```

#### Task 3.4: Update Panel Summary on Data Update
**File**: `src/modules/aio/debug/script.js`

Add summary update in the GC update code:

```javascript
// Update GC panel summary
var gcSummary = $('gc-summary');
if (gcSummary) {
  gcSummary.textContent = gcCycles + ' cycles, ' + fmtMs(gcMaxPause * 1000) + ' max, ' + fmtBytes(gcReclaimed) + ' reclaimed';
}
```

**Test Plan**:
- [ ] Click panel header to collapse/expand
- [ ] Verify summary text appears when collapsed
- [ ] Verify expand icon rotates on collapse
- [ ] Verify state persists across page refresh (localStorage)
- [ ] Test keyboard accessibility (Enter/Space to toggle)
- [ ] Verify ARIA attributes update correctly

---

### Phase 4: Inline Metrics Layout

**Goal**: Convert vertical metric lists to horizontal inline format.

#### Task 4.1: Add Inline Metrics CSS
**File**: `src/modules/aio/debug/style.css` (add new section)

```css
/* ===== INLINE METRICS ROW ===== */
.metrics-inline {
  display: flex;
  flex-wrap: wrap;
  gap: var(--space-xs) var(--space-lg);
  font-size: 12px;
  padding: var(--space-sm) 0;
}

.metric-inline {
  display: inline-flex;
  align-items: center;
  gap: var(--space-xs);
  white-space: nowrap;
}

.metric-inline-label {
  color: var(--text-muted);
}

.metric-inline-value {
  color: var(--text-primary);
  font-weight: 600;
  font-variant-numeric: tabular-nums;
}

.metric-inline-sep {
  color: var(--border-default);
  margin: 0 var(--space-xs);
}
```

#### Task 4.2: Update Interpreter Panel to Inline Format
**File**: `src/modules/aio/debug/body.html:131-166`

```html
<!-- BEFORE: Vertical layout -->
<div class="panel-body">
  <div class="mini-stats" role="list">
    <div class="mini-stat"><div class="mini-stat-value" id="interp-evals">--</div><div class="mini-stat-label">Evals</div></div>
    <!-- ... more ... -->
  </div>
  <div style="margin-top: var(--space-md);">
    <div class="metric-row"><span class="metric-label">Max Stack Depth</span><span class="metric-value" id="interp-stack-depth">--</span></div>
    <!-- ... more ... -->
  </div>
</div>

<!-- AFTER: Horizontal inline -->
<div class="panel-body">
  <div class="metrics-inline">
    <span class="metric-inline" title="Total expression evaluations">
      <span class="metric-inline-label">Evals:</span>
      <span class="metric-inline-value" id="interp-evals">--</span>
    </span>
    <span class="metric-inline-sep">│</span>
    <span class="metric-inline" title="User-defined function calls">
      <span class="metric-inline-label">Fn:</span>
      <span class="metric-inline-value" id="interp-fn-calls">--</span>
    </span>
    <span class="metric-inline-sep">│</span>
    <span class="metric-inline" title="Built-in function calls">
      <span class="metric-inline-label">Builtin:</span>
      <span class="metric-inline-value" id="interp-builtins">--</span>
    </span>
    <span class="metric-inline-sep">│</span>
    <span class="metric-inline" title="Max call stack depth">
      <span class="metric-inline-label">Stack:</span>
      <span class="metric-inline-value" id="interp-stack-depth">--</span>
    </span>
    <span class="metric-inline-sep">│</span>
    <span class="metric-inline" title="Closures created">
      <span class="metric-inline-label">Closures:</span>
      <span class="metric-inline-value" id="interp-closures">--</span>
    </span>
    <span class="metric-inline-sep">│</span>
    <span class="metric-inline" title="Environment lookups">
      <span class="metric-inline-label">Lookups:</span>
      <span class="metric-inline-value" id="interp-env-lookups">--</span>
    </span>
  </div>
</div>
```

**Test Plan**:
- [ ] Verify metrics display inline with separators
- [ ] Verify wrapping works correctly on narrow screens
- [ ] Check that values update correctly
- [ ] Verify tooltips work on each metric

---

### Phase 5: Compact GC Timeline

**Goal**: Reduce GC timeline vertical height while preserving functionality.

#### Task 5.1: Update GC Timeline CSS
**File**: `src/modules/aio/debug/style.css:836-858`

```css
/* BEFORE */
.gc-timeline {
  height: 60px;
  /* ... */
}

.gc-timeline-axis {
  /* ... */
  height: 14px;
  /* ... */
}

/* AFTER */
.gc-timeline {
  height: 36px;
  position: relative;
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
  overflow: hidden;
}

.gc-timeline-axis {
  position: absolute;
  bottom: 0;
  left: 0;
  right: 0;
  height: 10px;
  background: rgba(0,0,0,0.2);
  display: flex;
  justify-content: space-between;
  padding: 0 var(--space-xs);
  font-size: 8px;
  color: var(--text-faint);
  align-items: center;
}
```

#### Task 5.2: Reduce GC Stats Grid
**File**: `src/modules/aio/debug/style.css:903-908`

```css
/* BEFORE */
.gc-stats {
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  gap: var(--space-sm);
  margin-top: var(--space-md);
}

/* AFTER - inline format */
.gc-stats {
  display: flex;
  flex-wrap: wrap;
  gap: var(--space-sm) var(--space-lg);
  margin-top: var(--space-sm);
  padding: var(--space-sm);
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
}

.gc-stat {
  display: inline-flex;
  align-items: baseline;
  gap: var(--space-xs);
  padding: 0;
  background: transparent;
}

.gc-stat-value {
  font-size: 14px;
  font-weight: 600;
  color: var(--text-primary);
}

.gc-stat-label {
  font-size: 10px;
  color: var(--text-muted);
  margin-top: 0;
}
```

**Test Plan**:
- [ ] Verify GC timeline is shorter but bars still visible
- [ ] Verify axis labels are readable at smaller size
- [ ] Verify threshold line still appears
- [ ] Check that hover tooltips work on bars

---

### Phase 6: Memory Block Consolidation

**Goal**: Combine LVAL slab and scratch arena into a more compact layout.

#### Task 6.1: Update VM Memory Consolidated CSS
**File**: `src/modules/aio/debug/style.css:1880-1886`

```css
/* BEFORE */
.vm-memory-consolidated {
  display: grid;
  grid-template-columns: 2fr 1fr;
  gap: var(--space-lg);
}

/* AFTER */
.vm-memory-consolidated {
  display: grid;
  grid-template-columns: 1fr 180px;
  gap: var(--space-md);
}

.memory-block {
  background: var(--bg-secondary);
  border: 1px solid var(--border-default);
  border-radius: var(--radius-md);
  overflow: hidden;
}

.memory-block-header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: var(--space-sm) var(--space-md);
  background: var(--bg-tertiary);
  border-bottom: 1px solid var(--border-default);
}

.memory-block-body {
  padding: var(--space-sm) var(--space-md);
}
```

#### Task 6.2: Simplify Memory Block Headers
**File**: `src/modules/aio/debug/body.html:179-240`

Remove redundant nested panels and inline the slab visualization:

```html
<!-- AFTER: Compact memory layout -->
<div class="vm-memory-consolidated">
  <!-- GC Heap -->
  <div class="memory-block gc-heap-block">
    <div class="memory-block-header">
      <span class="memory-block-title">
        <span class="memory-icon gc">GC</span>
        Heap
      </span>
      <span class="memory-block-summary">
        <span id="heap-gauge-value">--</span>%
        (<span id="heap-used">--</span>/<span id="heap-total">--</span>)
      </span>
    </div>
    <div class="memory-block-body">
      <div class="slab-grid" id="lval-grid" role="img" aria-label="LVAL heap visualization"></div>
      <div class="slab-stats">
        <span><span class="used-count">0</span> / 262,144</span>
        <span>Reclaimed: <span id="heap-reclaimed">--</span></span>
      </div>
    </div>
  </div>

  <!-- Scratch Arena -->
  <div class="memory-block scratch-block">
    <div class="memory-block-header">
      <span class="memory-block-title">
        <span class="memory-icon scratch">S</span>
        Scratch
      </span>
      <span id="scratch-pct">0%</span>
    </div>
    <div class="memory-block-body">
      <div class="arena-gauge" data-arena="scratch">
        <div class="arena-track">
          <div class="arena-bar healthy" style="width: 0%;"></div>
          <div class="arena-hwm" style="left: 0%;"></div>
        </div>
      </div>
      <div class="arena-stats" id="scratch-usage">0B / 0B</div>
    </div>
  </div>
</div>
```

**Test Plan**:
- [ ] Verify memory blocks render side-by-side
- [ ] Verify LVAL grid cells display correctly
- [ ] Verify scratch arena gauge updates
- [ ] Verify high water mark indicator works
- [ ] Test responsive layout at narrow widths

---

### Phase 7: AIO Section Compaction

**Goal**: Reduce visual overhead in AIO system panels.

#### Task 7.1: Compact AIO Section Block Headers
**File**: `src/modules/aio/debug/style.css:2179-2218`

```css
/* BEFORE */
.block-header {
  display: flex;
  align-items: center;
  gap: var(--space-md);
  margin-bottom: var(--space-md);
  padding-bottom: var(--space-sm);
  border-bottom: 1px dashed var(--border-muted);
}

/* AFTER */
.block-header {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  margin-bottom: var(--space-sm);
  padding-bottom: var(--space-xs);
  border-bottom: 1px dashed var(--border-muted);
}

.block-title {
  font-size: 11px;
  font-weight: 600;
  color: var(--text-muted);
  text-transform: uppercase;
  letter-spacing: 0.5px;
}
```

#### Task 7.2: Reduce Mini Stats Padding
**File**: `src/modules/aio/debug/style.css:564-593`

```css
/* BEFORE */
.mini-stat {
  flex: 1;
  padding: var(--space-sm);
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
  text-align: center;
}

.mini-stat-value {
  font-size: 16px;
  /* ... */
}

/* AFTER */
.mini-stat {
  flex: 1;
  padding: var(--space-xs) var(--space-sm);
  background: var(--bg-tertiary);
  border-radius: var(--radius-sm);
  text-align: center;
  min-width: 0;
}

.mini-stat-value {
  font-size: 14px;
  font-weight: 600;
  color: var(--text-primary);
  font-variant-numeric: tabular-nums;
}

.mini-stat-label {
  font-size: 9px;
  color: var(--text-muted);
  margin-top: 0;
}
```

**Test Plan**:
- [ ] Verify AIO panels are more compact
- [ ] Verify mini-stats still readable
- [ ] Check that all badges display correctly
- [ ] Verify nested server/client cards work

---

## Implementation Order

1. **Phase 1** (CSS spacing) - Foundation changes, test thoroughly
2. **Phase 2** (Health bar) - High visual impact, user-facing
3. **Phase 3** (Collapsible panels) - User control for density
4. **Phase 4** (Inline metrics) - Moderate impact, interpreter panel
5. **Phase 5** (GC timeline) - Vertical space recovery
6. **Phase 6** (Memory blocks) - VM section cleanup
7. **Phase 7** (AIO compaction) - Final polish

## Rollback Plan

If issues arise, revert CSS variables in Phase 1 first, as all other phases depend on spacing changes.

## Metrics for Success

- **Vertical space reduction**: Target 30-40% reduction in full-page height
- **Information density**: Same data points in less screen area
- **No functionality loss**: All metrics and interactions preserved
- **Accessibility**: ARIA attributes and keyboard navigation maintained
- **Performance**: No additional render overhead from CSS changes

---

## File Summary

| File | Changes |
|------|---------|
| `src/modules/aio/debug/style.css` | Spacing vars, health bar, collapsible panels, inline metrics, compact sections |
| `src/modules/aio/debug/body.html` | Health bar HTML, collapsible panel attrs, inline metrics layout |
| `src/modules/aio/debug/script.js` | Mini sparkline renderer, panel toggle, summary updates |

## Testing Checklist

### Visual Tests
- [ ] Full page screenshot before/after comparison
- [ ] Responsive layouts at 600px, 900px, 1200px, 1800px widths
- [ ] Dark mode appearance (already dark, verify contrast)

### Functional Tests
- [ ] All metrics update via SSE
- [ ] Panel collapse/expand with localStorage persistence
- [ ] Sparklines animate on data updates
- [ ] Tooltips display on hover
- [ ] Keyboard navigation (Tab, Enter, Space)

### Accessibility Tests
- [ ] Screen reader announces panel states
- [ ] Focus indicators visible
- [ ] Color contrast ratios meet WCAG AA
- [ ] Skip link works

### Performance Tests
- [ ] No jank during SSE updates
- [ ] Memory stable over 5 minutes
- [ ] CPU usage comparable to current
