# AIO Dashboard Redesign Plan

## Overview

This plan redesigns the Async I/O (AIO) section of the Valkyria debug dashboard to:
1. Cover **all I/O subsystems** (not just HTTP)
2. Maximize **information density** with sparklines and compact layouts
3. Improve **usability** with collapsible sections and keyboard navigation
4. Add **trend visualization** for response codes and latency

**Target:** A unified view of all async I/O operations with glanceable health indicators and drill-down capability.

---

## 1. Architecture

### 1.1 Current Structure

```
AIO Systems Section
├── AIO System Panel (per event loop)
│   ├── Event Loop Stats (iterations, handles)
│   ├── Connection Pool (mini grid)
│   ├── Resource Pools (arenas, buffers)
│   ├── HTTP Servers (nested cards)
│   └── HTTP Clients (nested cards)
```

### 1.2 Proposed Structure

```
AIO Section (Async I/O)
├── Aggregate Health Bar
│   └── System-wide status, total ops/s, error rate, P99
│
├── Core Resources (shared)
│   ├── Event Loop (backend, iterations, handles, pending ops)
│   └── Resource Pools (connections, buffers, arenas, file descriptors)
│
├── Network I/O
│   ├── TCP Servers (listeners, accept rate, connections)
│   ├── TCP Clients (outbound connections, latency)
│   ├── UDP Sockets (send/recv rate, packet loss)
│   ├── HTTP Servers (requests, status codes, latency histogram)
│   └── HTTP Clients (requests, status codes, latency)
│
├── File I/O
│   └── Async Ops (reads, writes, fsync, throughput, latency)
│
└── IPC (Inter-Process Communication)
    ├── Unix Sockets (stream + datagram)
    └── Named Pipes (FIFOs)
```

### 1.3 Data Model Extensions

New metrics structures needed:

```c
// TCP metrics (raw, not HTTP)
typedef struct {
  uint64_t accepts_total;
  uint64_t bytes_recv_total;
  uint64_t bytes_sent_total;
  uint32_t connections_active;
  uint32_t connections_idle;
} valk_tcp_server_metrics_t;

typedef struct {
  uint64_t connects_total;
  uint64_t connect_errors;
  uint64_t bytes_recv_total;
  uint64_t bytes_sent_total;
  uint32_t connections_active;
  double   latency_p50_ms;
  double   latency_p99_ms;
} valk_tcp_client_metrics_t;

// UDP metrics
typedef struct {
  uint64_t packets_recv_total;
  uint64_t packets_sent_total;
  uint64_t bytes_recv_total;
  uint64_t bytes_sent_total;
  uint64_t packets_dropped;
} valk_udp_socket_metrics_t;

// File I/O metrics
typedef struct {
  uint64_t reads_total;
  uint64_t writes_total;
  uint64_t fsyncs_total;
  uint64_t bytes_read_total;
  uint64_t bytes_written_total;
  uint32_t pending_reads;
  uint32_t pending_writes;
  double   read_latency_p99_ms;
  double   write_latency_p99_ms;
} valk_file_io_metrics_t;

// IPC metrics
typedef struct {
  const char* path;           // Socket path or "@abstract" for abstract
  bool        is_stream;      // true=SOCK_STREAM, false=SOCK_DGRAM
  uint64_t    ops_total;
  uint64_t    bytes_total;
  uint32_t    connections;    // For stream sockets
  double      latency_p99_ms;
} valk_unix_socket_metrics_t;

typedef struct {
  const char* path;
  bool        is_writer;      // Direction
  uint64_t    bytes_total;
  uint32_t    buffer_pct;     // Buffer fullness
} valk_named_pipe_metrics_t;
```

---

## 2. Visual Design

### 2.1 Aggregate Health Bar

Always visible at top of AIO section. Shows system-wide health at a glance.

```
┌─────────────────────────────────────────────────────────────────────────┐
│ ●●● 8 OK  ●●○ 1 Warn  ●○○ 0 Down │ 3.1K ops/s │ 0.08% err │ P99: 45ms │
└─────────────────────────────────────────────────────────────────────────┘
```

**Elements:**
- Status counts with shape+color indicators (accessibility)
- Aggregate throughput (all I/O operations combined)
- Aggregate error rate
- Aggregate P99 latency

### 2.2 Sparkline Specifications

**Mini Sparkline (inline with metrics):**
- Dimensions: 48×16 px
- Data points: 20 samples (last 60 seconds at 3s intervals)
- Stroke: 1.5px, color varies by metric type
- Fill: 20% opacity gradient below line

**Trend Sparkline (in expanded cards):**
- Dimensions: 120×32 px
- Data points: 60 samples (last 60 seconds at 1s intervals)
- Multi-line support for percentiles (P50/P95/P99)

**Status Code Sparkline (stacked bar over time):**
- Dimensions: 60×20 px
- Shows 2xx/4xx/5xx proportions over 20 time buckets
- Color: green/yellow/red segments

### 2.3 Collapsible Card States

**Collapsed (1-line summary):**
```
│● api:8443  156/s  P99:45ms  ✓99.9%  ▁▂▃▅▄▃▂  [▼]│
```
Fields: status, name, rate, P99, success%, sparkline, expand button

**Expanded (full detail):**
```
│● api:8443  156/s  P99:45ms  ✓99.9%  ▁▂▃▅▄▃▂  [▲]│
│┌─────────────────────────────────────────────────┐│
││ Response Codes       │ Latency Trend            ││
││ ✓45.2K !127 ✕3      │ [multi-line sparkline]   ││
││ [stacked bar]       │ P50:12ms P95:45ms P99:120││
││─────────────────────────────────────────────────││
││ Throughput          │ Connections              ││
││ [in/out sparkline]  │ ●47 active ○12 idle      ││
│└─────────────────────────────────────────────────┘│
```

### 2.4 Status Indicators (Accessible)

Shape + color combinations for color-blind accessibility:

| Status | Shape | Color | Unicode |
|--------|-------|-------|---------|
| Healthy | Circle | Blue (#0066CC) | ● |
| Warning | Triangle | Yellow (#FFD700) | ▲ |
| Error | Square | Red (#DC2626) | ■ |
| Offline | X | Gray (#6B7280) | ✕ |
| Starting | Diamond | Purple (#8B5CF6) | ◆ |

### 2.5 I/O Type Section Headers

Each I/O type gets a collapsible section with aggregate stats:

```
┌─ NETWORK ─────────────────────────────────────── 2.1K ops/s ── [−] ─┐
│ ...                                                                  │
└──────────────────────────────────────────────────────────────────────┘

┌─ FILES ───────────────────────────────────────── 279 ops/s ── [−] ─┐
│ ...                                                                  │
└──────────────────────────────────────────────────────────────────────┘

┌─ IPC ─────────────────────────────────────────── 1.7K ops/s ── [−] ─┐
│ ...                                                                  │
└──────────────────────────────────────────────────────────────────────┘
```

---

## 3. Implementation Tasks

### Phase 1: Core Infrastructure (Foundation)

#### Task 1.1: Add History Tracking for Sparklines
**File:** `src/modules/aio/debug/script.js`
**Description:** Create a generic history buffer for tracking time-series data.

```javascript
// Generic circular buffer for sparkline history
function createHistoryBuffer(maxSize) {
  return {
    data: [],
    maxSize: maxSize || 60,
    push: function(value) {
      this.data.push(value);
      if (this.data.length > this.maxSize) {
        this.data.shift();
      }
    },
    toArray: function() {
      return this.data.slice();
    },
    last: function() {
      return this.data[this.data.length - 1];
    }
  };
}

// Per-entity history storage
var entityHistory = {
  // 'http-server:api:8443': { requestRate: buffer, errorRate: buffer, p50: buffer, ... }
};

function getEntityHistory(type, key) {
  var id = type + ':' + key;
  if (!entityHistory[id]) {
    entityHistory[id] = {
      requestRate: createHistoryBuffer(60),
      errorRate: createHistoryBuffer(60),
      p50: createHistoryBuffer(60),
      p95: createHistoryBuffer(60),
      p99: createHistoryBuffer(60),
      bytesIn: createHistoryBuffer(60),
      bytesOut: createHistoryBuffer(60),
      statusCodes: createHistoryBuffer(20) // { s2xx, s4xx, s5xx }
    };
  }
  return entityHistory[id];
}
```

**Test Plan:**
- [ ] Create buffer with maxSize=10, push 15 items, verify length is 10
- [ ] Verify oldest items are removed first (FIFO)
- [ ] Verify `toArray()` returns copy, not reference
- [ ] Test with empty buffer (edge case)

---

#### Task 1.2: Implement Mini Sparkline Renderer
**File:** `src/modules/aio/debug/script.js`
**Description:** SVG-based sparkline renderer for inline metrics.

```javascript
function renderMiniSparkline(container, data, options) {
  if (!container || !data || data.length < 2) {
    container.innerHTML = '';
    return;
  }

  var opts = options || {};
  var width = opts.width || 48;
  var height = opts.height || 16;
  var color = opts.color || 'var(--color-info)';
  var fillOpacity = opts.fillOpacity || 0.2;
  var strokeWidth = opts.strokeWidth || 1.5;

  var max = Math.max.apply(null, data);
  var min = opts.minValue !== undefined ? opts.minValue : Math.min.apply(null, data);
  var range = max - min || 1;

  var points = data.map(function(v, i) {
    var x = (i / (data.length - 1)) * width;
    var y = height - 2 - ((v - min) / range) * (height - 4);
    return x.toFixed(1) + ',' + y.toFixed(1);
  }).join(' ');

  var areaPoints = points + ' ' + width + ',' + height + ' 0,' + height;

  container.innerHTML =
    '<svg viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none">' +
    '<polygon points="' + areaPoints + '" fill="' + color + '" opacity="' + fillOpacity + '"/>' +
    '<polyline points="' + points + '" fill="none" stroke="' + color + '" stroke-width="' + strokeWidth + '" stroke-linecap="round" stroke-linejoin="round"/>' +
    '</svg>';
}
```

**Test Plan:**
- [ ] Render with valid data array, verify SVG created
- [ ] Render with empty array, verify container cleared
- [ ] Render with single data point, verify no crash
- [ ] Render with all same values, verify flat line
- [ ] Verify custom colors applied correctly
- [ ] Verify sparkline scales to container width

---

#### Task 1.3: Implement Multi-Line Percentile Sparkline
**File:** `src/modules/aio/debug/script.js`
**Description:** Overlay sparkline showing P50/P95/P99 trends.

```javascript
function renderPercentileSparkline(container, history, options) {
  if (!container || !history.p50 || history.p50.length < 2) {
    container.innerHTML = '';
    return;
  }

  var opts = options || {};
  var width = opts.width || 120;
  var height = opts.height || 32;

  var allData = history.p50.concat(history.p95).concat(history.p99);
  var max = Math.max.apply(null, allData) || 1;
  var min = 0;

  function pathFor(data, color, strokeWidth) {
    if (data.length < 2) return '';
    var points = data.map(function(v, i) {
      var x = (i / (data.length - 1)) * width;
      var y = height - ((v - min) / (max - min)) * (height - 4) - 2;
      return (i === 0 ? 'M' : 'L') + x.toFixed(1) + ',' + y.toFixed(1);
    }).join(' ');
    return '<path d="' + points + '" fill="none" stroke="' + color + '" stroke-width="' + strokeWidth + '" opacity="0.9"/>';
  }

  container.innerHTML =
    '<svg viewBox="0 0 ' + width + ' ' + height + '" preserveAspectRatio="none">' +
    pathFor(history.p99, 'var(--color-error)', 1) +
    pathFor(history.p95, 'var(--color-warning)', 1.2) +
    pathFor(history.p50, 'var(--color-ok)', 1.5) +
    '</svg>';
}
```

**Test Plan:**
- [ ] Render with all three percentile arrays populated
- [ ] Verify P50 line is thickest (foreground)
- [ ] Verify P99 line is thinnest (background)
- [ ] Test with divergent percentiles (P99 >> P50)
- [ ] Test with converged percentiles (all similar)

---

#### Task 1.4: Implement Status Code Stacked Sparkline
**File:** `src/modules/aio/debug/script.js`
**Description:** Stacked bar sparkline showing 2xx/4xx/5xx over time.

```javascript
function renderStatusCodeSparkline(container, history, options) {
  if (!container || !history || history.length < 2) {
    container.innerHTML = '';
    return;
  }

  var opts = options || {};
  var width = opts.width || 60;
  var height = opts.height || 20;
  var barWidth = width / history.length;

  var bars = history.map(function(d, i) {
    var total = d.s2xx + d.s4xx + d.s5xx;
    if (total === 0) return '';

    var x = i * barWidth;
    var h2xx = (d.s2xx / total) * height;
    var h4xx = (d.s4xx / total) * height;
    var h5xx = (d.s5xx / total) * height;

    var y2xx = 0;
    var y4xx = h2xx;
    var y5xx = h2xx + h4xx;

    return '<g>' +
      '<rect x="' + x + '" y="' + y2xx + '" width="' + (barWidth - 0.5) + '" height="' + h2xx + '" fill="var(--color-ok)"/>' +
      '<rect x="' + x + '" y="' + y4xx + '" width="' + (barWidth - 0.5) + '" height="' + h4xx + '" fill="var(--color-warning)"/>' +
      '<rect x="' + x + '" y="' + y5xx + '" width="' + (barWidth - 0.5) + '" height="' + h5xx + '" fill="var(--color-error)"/>' +
      '</g>';
  }).join('');

  container.innerHTML = '<svg viewBox="0 0 ' + width + ' ' + height + '">' + bars + '</svg>';
}
```

**Test Plan:**
- [ ] Render with all 2xx responses, verify solid green bar
- [ ] Render with mixed responses, verify stacked segments
- [ ] Render with all 5xx, verify solid red bar
- [ ] Test with zero total in some buckets
- [ ] Verify bar spacing prevents overlap

---

### Phase 2: Aggregate Health Bar

#### Task 2.1: Add Aggregate Health Bar HTML
**File:** `src/modules/aio/debug/body.html`
**Description:** Add health summary bar at top of AIO section.

```html
<!-- Add after AIO section header, before aio-systems-container -->
<div class="aio-aggregate-health" id="aio-health-bar">
  <div class="aio-health-status">
    <span class="health-group ok" title="Healthy endpoints">
      <span class="health-icon">●</span>
      <span class="health-count" id="aio-ok-count">0</span> OK
    </span>
    <span class="health-group warning" title="Endpoints with warnings">
      <span class="health-icon">▲</span>
      <span class="health-count" id="aio-warn-count">0</span> Warn
    </span>
    <span class="health-group error" title="Endpoints with errors or offline">
      <span class="health-icon">■</span>
      <span class="health-count" id="aio-error-count">0</span> Down
    </span>
  </div>
  <div class="aio-health-divider"></div>
  <div class="aio-health-metrics">
    <span class="aio-health-metric" title="Total operations per second across all I/O">
      <span class="aio-health-value" id="aio-total-ops">--</span>
      <span class="aio-health-label">ops/s</span>
    </span>
    <span class="aio-health-metric" title="Aggregate error rate">
      <span class="aio-health-value" id="aio-error-rate">--</span>
      <span class="aio-health-label">% err</span>
    </span>
    <span class="aio-health-metric" title="Aggregate P99 latency">
      <span class="aio-health-value" id="aio-p99">--</span>
      <span class="aio-health-label">ms P99</span>
    </span>
  </div>
</div>
```

**Test Plan:**
- [ ] Verify health bar renders below section header
- [ ] Verify all placeholder values display "--"
- [ ] Verify tooltips appear on hover
- [ ] Check responsive layout at narrow widths

---

#### Task 2.2: Add Aggregate Health Bar CSS
**File:** `src/modules/aio/debug/style.css`
**Description:** Styles for the health summary bar.

```css
/* ===== AGGREGATE HEALTH BAR ===== */
.aio-aggregate-health {
  display: flex;
  align-items: center;
  gap: var(--space-lg);
  padding: var(--space-sm) var(--space-lg);
  background: var(--bg-secondary);
  border: 1px solid var(--border-default);
  border-radius: var(--radius-md);
  margin-bottom: var(--space-lg);
}

.aio-health-status {
  display: flex;
  gap: var(--space-lg);
}

.health-group {
  display: flex;
  align-items: center;
  gap: var(--space-xs);
  font-size: 12px;
  font-weight: 500;
}

.health-group.ok .health-icon { color: var(--color-ok); }
.health-group.warning .health-icon { color: var(--color-warning); }
.health-group.error .health-icon { color: var(--color-error); }

.health-count {
  font-weight: 600;
  font-variant-numeric: tabular-nums;
}

.aio-health-divider {
  width: 1px;
  height: 24px;
  background: var(--border-default);
}

.aio-health-metrics {
  display: flex;
  gap: var(--space-lg);
}

.aio-health-metric {
  display: flex;
  align-items: baseline;
  gap: var(--space-xs);
}

.aio-health-value {
  font-size: 14px;
  font-weight: 600;
  color: var(--text-primary);
  font-variant-numeric: tabular-nums;
}

.aio-health-label {
  font-size: 11px;
  color: var(--text-muted);
}

/* Responsive: stack on narrow screens */
@media (max-width: 768px) {
  .aio-aggregate-health {
    flex-direction: column;
    align-items: flex-start;
    gap: var(--space-sm);
  }

  .aio-health-divider {
    width: 100%;
    height: 1px;
  }
}
```

**Test Plan:**
- [ ] Verify layout at 1200px width (horizontal)
- [ ] Verify layout at 600px width (stacked)
- [ ] Verify color coding matches status
- [ ] Check contrast ratios for accessibility

---

#### Task 2.3: Implement Health Aggregation Logic
**File:** `src/modules/aio/debug/script.js`
**Description:** Calculate aggregate health from all I/O subsystems.

```javascript
function updateAggregateHealth(data) {
  var okCount = 0, warnCount = 0, errorCount = 0;
  var totalOps = 0, totalErrors = 0, maxP99 = 0;

  // Count HTTP servers
  if (data.servers) {
    Object.keys(data.servers).forEach(function(key) {
      var s = data.servers[key];
      var errorRate = calculateErrorRate(s);
      if (errorRate > 5) errorCount++;
      else if (errorRate > 1) warnCount++;
      else okCount++;

      totalOps += s.requestRate || 0;
      totalErrors += (s.errors4xx || 0) + (s.errors5xx || 0);
      maxP99 = Math.max(maxP99, s.latencyP99 || 0);
    });
  }

  // Count HTTP clients
  if (data.clients) {
    Object.keys(data.clients).forEach(function(key) {
      var c = data.clients[key];
      var errorRate = calculateErrorRate(c);
      if (errorRate > 5) errorCount++;
      else if (errorRate > 1) warnCount++;
      else okCount++;

      totalOps += c.requestRate || 0;
      totalErrors += c.errors || 0;
      maxP99 = Math.max(maxP99, c.latencyP99 || 0);
    });
  }

  // TODO: Add TCP, UDP, Files, IPC when implemented

  // Update DOM
  $('aio-ok-count').textContent = okCount;
  $('aio-warn-count').textContent = warnCount;
  $('aio-error-count').textContent = errorCount;
  $('aio-total-ops').textContent = fmtCompact(totalOps);
  $('aio-error-rate').textContent = totalOps > 0
    ? ((totalErrors / totalOps) * 100).toFixed(2)
    : '0.00';
  $('aio-p99').textContent = fmtMs(maxP99);
}
```

**Test Plan:**
- [ ] Test with 0 servers/clients (all zeros)
- [ ] Test with mixed healthy/warning/error servers
- [ ] Test error rate calculation accuracy
- [ ] Verify P99 takes maximum across all endpoints

---

### Phase 3: Collapsible Entity Cards

#### Task 3.1: Update Entity Card HTML Structure
**File:** `src/modules/aio/debug/script.js` (createServerCard function)
**Description:** Add collapsed summary row and toggle functionality.

```javascript
function createServerCard(serverInfo) {
  var card = document.createElement('article');
  card.className = 'entity-card collapsed'; // Start collapsed
  card.id = 'server-' + serverInfo.key.replace(/[:.]/g, '-');
  card.setAttribute('tabindex', '0');
  card.setAttribute('role', 'article');
  card.setAttribute('aria-expanded', 'false');

  card.innerHTML = `
    <div class="entity-header" onclick="toggleEntityCard(this.parentElement)">
      <div class="entity-status ok" role="img" aria-label="Status: Healthy">
        <span class="status-shape">●</span>
      </div>
      <h3 class="entity-name">${serverInfo.server}:${serverInfo.port}</h3>

      <!-- Summary metrics (visible when collapsed) -->
      <div class="entity-summary">
        <span class="summary-metric req-rate">--/s</span>
        <span class="summary-metric p99-value">P99:--</span>
        <span class="summary-metric success-rate">---%</span>
        <div class="summary-spark" id="${card.id}-summary-spark"></div>
      </div>

      <button class="expand-toggle" aria-label="Toggle details">
        <span class="expand-icon">▼</span>
      </button>
    </div>

    <div class="entity-body">
      <!-- Full details (hidden when collapsed) -->
      <!-- ... existing body content ... -->
    </div>
  `;

  return card;
}

function toggleEntityCard(card) {
  var isCollapsed = card.classList.contains('collapsed');
  card.classList.toggle('collapsed');
  card.setAttribute('aria-expanded', isCollapsed ? 'true' : 'false');

  var icon = card.querySelector('.expand-icon');
  if (icon) {
    icon.textContent = isCollapsed ? '▲' : '▼';
  }
}
```

**Test Plan:**
- [ ] Cards start collapsed by default
- [ ] Click header expands card
- [ ] Click again collapses card
- [ ] aria-expanded updates correctly
- [ ] Icon rotates on expand/collapse
- [ ] Summary metrics visible when collapsed

---

#### Task 3.2: Add Collapsed Card CSS
**File:** `src/modules/aio/debug/style.css`
**Description:** Styles for collapsed card state.

```css
/* ===== COLLAPSIBLE ENTITY CARDS ===== */
.entity-card {
  transition: all 0.2s ease;
}

.entity-card.collapsed {
  border-radius: var(--radius-sm);
}

.entity-card.collapsed .entity-header {
  padding: var(--space-xs) var(--space-md);
  border-bottom: none;
}

.entity-card.collapsed .entity-body {
  display: none;
}

.entity-summary {
  display: none;
  align-items: center;
  gap: var(--space-md);
  margin-left: auto;
  margin-right: var(--space-md);
}

.entity-card.collapsed .entity-summary {
  display: flex;
}

.entity-card.collapsed .entity-stats {
  display: none;
}

.summary-metric {
  font-size: 12px;
  font-variant-numeric: tabular-nums;
  color: var(--text-secondary);
}

.summary-metric.req-rate {
  font-weight: 600;
  color: var(--text-primary);
}

.summary-metric.p99-value {
  color: var(--text-muted);
}

.summary-metric.success-rate {
  color: var(--color-ok);
}

.summary-metric.success-rate.warning {
  color: var(--color-warning);
}

.summary-metric.success-rate.error {
  color: var(--color-error);
}

.summary-spark {
  width: 60px;
  height: 16px;
}

.expand-toggle {
  background: none;
  border: none;
  color: var(--text-muted);
  cursor: pointer;
  padding: var(--space-xs);
  border-radius: var(--radius-sm);
  transition: background 0.15s;
}

.expand-toggle:hover {
  background: var(--bg-elevated);
  color: var(--text-primary);
}

.expand-icon {
  font-size: 10px;
  transition: transform 0.2s ease;
}

.entity-card:not(.collapsed) .expand-icon {
  transform: rotate(180deg);
}

/* Keyboard focus */
.entity-card:focus {
  outline: 2px solid var(--color-info);
  outline-offset: 2px;
}

.entity-card.keyboard-focus {
  box-shadow: 0 0 0 2px var(--color-info);
}
```

**Test Plan:**
- [ ] Collapsed card shows single-line layout
- [ ] Expanded card shows full body
- [ ] Transition animations are smooth
- [ ] Summary spark container has correct dimensions
- [ ] Focus outline visible on keyboard navigation

---

#### Task 3.3: Update Card Summary on Data Update
**File:** `src/modules/aio/debug/script.js`
**Description:** Update summary metrics when data changes.

```javascript
function updateServerCard(card, serverInfo, deltaSeconds) {
  // ... existing update code ...

  // Update summary metrics (for collapsed view)
  var summaryRate = card.querySelector('.entity-summary .req-rate');
  var summaryP99 = card.querySelector('.entity-summary .p99-value');
  var summarySuccess = card.querySelector('.entity-summary .success-rate');
  var summarySpark = card.querySelector('.summary-spark');

  if (summaryRate) {
    summaryRate.textContent = fmt(reqRate, 1) + '/s';
  }

  if (summaryP99 && p99 !== undefined) {
    summaryP99.textContent = 'P99:' + fmtLatency(p99);
  }

  if (summarySuccess) {
    var successRate = reqTotal > 0 ? ((req2xx / reqTotal) * 100) : 100;
    summarySuccess.textContent = successRate.toFixed(1) + '%';
    summarySuccess.className = 'summary-metric success-rate';
    if (successRate < 95) summarySuccess.classList.add('error');
    else if (successRate < 99) summarySuccess.classList.add('warning');
  }

  // Update summary sparkline
  if (summarySpark) {
    var hist = getEntityHistory('http-server', serverInfo.key);
    renderMiniSparkline(summarySpark, hist.requestRate.toArray(), {
      color: 'var(--color-info)',
      width: 60,
      height: 16
    });
  }
}
```

**Test Plan:**
- [ ] Summary rate updates in real-time
- [ ] Summary P99 formats correctly (ms/s)
- [ ] Success rate color changes at thresholds
- [ ] Summary sparkline renders and updates

---

### Phase 4: Response Code & Latency Sparklines

#### Task 4.1: Add Response Code Sparkline to Cards
**File:** `src/modules/aio/debug/script.js`
**Description:** Track and render status code trends.

```javascript
// In updateServerCard, track status code history
function updateServerCard(card, serverInfo, deltaSeconds) {
  // ... existing code ...

  // Track status code history
  var hist = getEntityHistory('http-server', serverInfo.key);

  // Calculate per-interval counts (delta from previous)
  var prev = hist.statusCodes.last() || { s2xx: 0, s4xx: 0, s5xx: 0, total2xx: 0, total4xx: 0, total5xx: 0 };
  var delta2xx = req2xx - (prev.total2xx || 0);
  var delta4xx = req4xx - (prev.total4xx || 0);
  var delta5xx = req5xx - (prev.total5xx || 0);

  hist.statusCodes.push({
    s2xx: Math.max(0, delta2xx),
    s4xx: Math.max(0, delta4xx),
    s5xx: Math.max(0, delta5xx),
    total2xx: req2xx,
    total4xx: req4xx,
    total5xx: req5xx
  });

  // Render status code sparkline (next to 4xx/5xx chips if errors exist)
  var statusSparkContainer = card.querySelector('.status-code-spark');
  if (statusSparkContainer && (req4xx > 0 || req5xx > 0)) {
    renderStatusCodeSparkline(statusSparkContainer, hist.statusCodes.toArray());
  }
}
```

**Test Plan:**
- [ ] Status code deltas calculated correctly
- [ ] Sparkline only shown when errors exist
- [ ] Sparkline shows correct proportions
- [ ] History wraps correctly at buffer limit

---

#### Task 4.2: Add Latency Trend Sparklines to Cards
**File:** `src/modules/aio/debug/script.js`
**Description:** Track and render P50/P95/P99 trends.

```javascript
// In updateServerCard, track latency history
function updateServerCard(card, serverInfo, deltaSeconds) {
  // ... existing percentile calculation ...

  // Track latency history
  var hist = getEntityHistory('http-server', serverInfo.key);
  hist.p50.push(p50 * 1000);  // Convert to ms
  hist.p95.push(p95 * 1000);
  hist.p99.push(p99 * 1000);

  // Render latency trend sparkline
  var latencyTrendContainer = card.querySelector('.latency-trend-spark');
  if (latencyTrendContainer && hist.p50.data.length >= 2) {
    renderPercentileSparkline(latencyTrendContainer, {
      p50: hist.p50.toArray(),
      p95: hist.p95.toArray(),
      p99: hist.p99.toArray()
    });
  }
}
```

**Test Plan:**
- [ ] Latency values converted to ms correctly
- [ ] All three percentile lines render
- [ ] Lines scale to max P99 value
- [ ] Sparkline updates on each data push

---

#### Task 4.3: Update Card HTML for Trend Sparklines
**File:** `src/modules/aio/debug/script.js` (createServerCard)
**Description:** Add containers for trend sparklines.

```javascript
// In createServerCard, update the entity-body HTML:

// Response Codes section update:
`<div class="entity-section">
  <div class="entity-section-title">Response Codes</div>
  <div class="status-row" role="list">
    <div class="status-chip s2xx">
      <div class="status-chip-value count-2xx">0</div>
      <div class="status-chip-label"><span class="icon">✓</span> 2xx</div>
    </div>
    <div class="status-chip s4xx">
      <div class="status-chip-value count-4xx">0</div>
      <div class="status-chip-label"><span class="icon">!</span> 4xx</div>
      <div class="status-chip-spark"></div>
    </div>
    <div class="status-chip s5xx">
      <div class="status-chip-value count-5xx">0</div>
      <div class="status-chip-label"><span class="icon">✕</span> 5xx</div>
      <div class="status-chip-spark"></div>
    </div>
  </div>
  <div class="status-bar">
    <div class="status-segment s2xx" style="width: 100%"></div>
    <div class="status-segment s4xx" style="width: 0%"></div>
    <div class="status-segment s5xx" style="width: 0%"></div>
  </div>
  <div class="status-code-spark-container">
    <div class="status-code-spark" title="Status code distribution over time"></div>
  </div>
</div>`

// Latency section update:
`<div class="entity-section">
  <div class="entity-section-title">Latency Distribution</div>
  <div class="latency-content">
    <div class="histogram-container">
      <div class="histogram"></div>
      <div class="percentiles">
        <div class="percentile"><span class="percentile-dot p50"></span> P50 <span class="p50-value">--</span></div>
        <div class="percentile"><span class="percentile-dot p95"></span> P95 <span class="p95-value">--</span></div>
        <div class="percentile"><span class="percentile-dot p99"></span> P99 <span class="p99-value">--</span></div>
      </div>
    </div>
    <div class="latency-trend">
      <div class="latency-trend-label">Trend (60s)</div>
      <div class="latency-trend-spark"></div>
    </div>
  </div>
</div>`
```

**Test Plan:**
- [ ] Status code spark container renders
- [ ] Latency trend container renders
- [ ] Layout accommodates both histogram and trend
- [ ] Responsive at narrow widths

---

### Phase 5: Keyboard Navigation

#### Task 5.1: Implement Keyboard Event Handler
**File:** `src/modules/aio/debug/script.js`
**Description:** Add vim-style keyboard navigation.

```javascript
// Keyboard navigation for entity cards
(function() {
  var focusedIndex = -1;

  function getEntityCards() {
    return Array.from(document.querySelectorAll('.entity-card'));
  }

  function setFocus(index) {
    var cards = getEntityCards();
    if (index < 0 || index >= cards.length) return;

    // Remove previous focus
    cards.forEach(function(c) { c.classList.remove('keyboard-focus'); });

    // Set new focus
    focusedIndex = index;
    cards[index].classList.add('keyboard-focus');
    cards[index].scrollIntoView({ block: 'nearest', behavior: 'smooth' });
  }

  function handleKeyDown(e) {
    // Ignore if typing in input
    if (e.target.tagName === 'INPUT' || e.target.tagName === 'TEXTAREA') return;

    var cards = getEntityCards();
    if (cards.length === 0) return;

    switch (e.key) {
      case 'j': // Down
        e.preventDefault();
        setFocus(Math.min(focusedIndex + 1, cards.length - 1));
        break;

      case 'k': // Up
        e.preventDefault();
        setFocus(Math.max(focusedIndex - 1, 0));
        break;

      case ' ': // Toggle expand
      case 'l': // Expand
      case 'h': // Collapse
        e.preventDefault();
        if (focusedIndex >= 0 && focusedIndex < cards.length) {
          var card = cards[focusedIndex];
          if (e.key === 'l') {
            card.classList.remove('collapsed');
          } else if (e.key === 'h') {
            card.classList.add('collapsed');
          } else {
            card.classList.toggle('collapsed');
          }
          card.setAttribute('aria-expanded', !card.classList.contains('collapsed'));
        }
        break;

      case 'g': // Go to first (gg)
        if (e.repeat) {
          e.preventDefault();
          setFocus(0);
        }
        break;

      case 'G': // Go to last
        e.preventDefault();
        setFocus(cards.length - 1);
        break;

      case '?': // Show help
        e.preventDefault();
        toggleKeyboardHelp();
        break;

      case 'Escape':
        // Clear focus
        cards.forEach(function(c) { c.classList.remove('keyboard-focus'); });
        focusedIndex = -1;
        hideKeyboardHelp();
        break;
    }
  }

  document.addEventListener('keydown', handleKeyDown);
})();
```

**Test Plan:**
- [ ] j/k navigates through cards
- [ ] Space toggles collapse state
- [ ] h collapses, l expands
- [ ] G goes to last card
- [ ] Escape clears focus
- [ ] Navigation wraps at boundaries
- [ ] Scroll follows focused card

---

#### Task 5.2: Add Keyboard Help Overlay
**File:** `src/modules/aio/debug/body.html`
**Description:** Help modal showing keyboard shortcuts.

```html
<!-- Add before closing </main> -->
<div class="keyboard-help-overlay" id="keyboard-help" role="dialog" aria-labelledby="keyboard-help-title" aria-hidden="true">
  <div class="keyboard-help-content">
    <h3 id="keyboard-help-title">Keyboard Shortcuts</h3>
    <button class="keyboard-help-close" onclick="hideKeyboardHelp()" aria-label="Close">&times;</button>
    <div class="keyboard-help-grid">
      <div class="shortcut-group">
        <h4>Navigation</h4>
        <div class="shortcut"><kbd>j</kbd> / <kbd>↓</kbd> <span>Next card</span></div>
        <div class="shortcut"><kbd>k</kbd> / <kbd>↑</kbd> <span>Previous card</span></div>
        <div class="shortcut"><kbd>G</kbd> <span>Last card</span></div>
        <div class="shortcut"><kbd>gg</kbd> <span>First card</span></div>
      </div>
      <div class="shortcut-group">
        <h4>Actions</h4>
        <div class="shortcut"><kbd>Space</kbd> <span>Toggle expand</span></div>
        <div class="shortcut"><kbd>l</kbd> <span>Expand card</span></div>
        <div class="shortcut"><kbd>h</kbd> <span>Collapse card</span></div>
        <div class="shortcut"><kbd>Esc</kbd> <span>Clear focus</span></div>
      </div>
      <div class="shortcut-group">
        <h4>Other</h4>
        <div class="shortcut"><kbd>?</kbd> <span>Show this help</span></div>
        <div class="shortcut"><kbd>r</kbd> <span>Refresh data</span></div>
      </div>
    </div>
  </div>
</div>
```

**Test Plan:**
- [ ] ? key opens help overlay
- [ ] Escape closes help overlay
- [ ] Click outside closes overlay
- [ ] All shortcuts listed correctly
- [ ] Screen reader announces dialog

---

### Phase 6: I/O Type Sections

#### Task 6.1: Create Section Component Factory
**File:** `src/modules/aio/debug/script.js`
**Description:** Reusable function to create I/O type sections.

```javascript
function createIOSection(config) {
  var section = document.createElement('div');
  section.className = 'io-section';
  section.id = 'io-section-' + config.type;
  section.setAttribute('data-io-type', config.type);

  section.innerHTML = `
    <div class="io-section-header" onclick="toggleIOSection('${config.type}')">
      <span class="io-section-icon">${config.icon}</span>
      <span class="io-section-title">${config.title}</span>
      <span class="io-section-stats">
        <span class="io-section-ops" id="${config.type}-ops">--</span> ops/s
      </span>
      <button class="io-section-toggle" aria-label="Toggle section">
        <span class="toggle-icon">−</span>
      </button>
    </div>
    <div class="io-section-body">
      ${config.subsections.map(function(sub) {
        return `
          <div class="io-subsection" id="${config.type}-${sub.id}">
            <div class="io-subsection-header">
              <span class="io-subsection-title">${sub.title}</span>
              <span class="io-subsection-count">(0)</span>
            </div>
            <div class="io-subsection-content">
              <!-- Cards will be injected here -->
            </div>
          </div>
        `;
      }).join('')}
    </div>
  `;

  return section;
}

// Create all I/O sections
function initIOSections() {
  var container = $('aio-systems-container');

  var sections = [
    {
      type: 'network',
      icon: '🌐',
      title: 'NETWORK',
      subsections: [
        { id: 'tcp-servers', title: 'TCP Servers' },
        { id: 'tcp-clients', title: 'TCP Clients' },
        { id: 'udp', title: 'UDP Sockets' },
        { id: 'http-servers', title: 'HTTP Servers' },
        { id: 'http-clients', title: 'HTTP Clients' }
      ]
    },
    {
      type: 'files',
      icon: '📁',
      title: 'FILES',
      subsections: [
        { id: 'async-ops', title: 'Async Operations' }
      ]
    },
    {
      type: 'ipc',
      icon: '🔗',
      title: 'IPC',
      subsections: [
        { id: 'unix-sockets', title: 'Unix Sockets' },
        { id: 'named-pipes', title: 'Named Pipes' }
      ]
    }
  ];

  sections.forEach(function(config) {
    container.appendChild(createIOSection(config));
  });
}
```

**Test Plan:**
- [ ] All three sections render
- [ ] Subsection containers exist
- [ ] Section toggle works
- [ ] Stats placeholder shows "--"

---

#### Task 6.2: Add I/O Section CSS
**File:** `src/modules/aio/debug/style.css`
**Description:** Styles for I/O type sections.

```css
/* ===== I/O TYPE SECTIONS ===== */
.io-section {
  background: var(--bg-secondary);
  border: 1px solid var(--border-default);
  border-radius: var(--radius-md);
  margin-bottom: var(--space-md);
  overflow: hidden;
}

.io-section-header {
  display: flex;
  align-items: center;
  gap: var(--space-md);
  padding: var(--space-sm) var(--space-md);
  background: var(--bg-tertiary);
  border-bottom: 1px solid var(--border-default);
  cursor: pointer;
  user-select: none;
}

.io-section-header:hover {
  background: var(--bg-elevated);
}

.io-section-icon {
  font-size: 14px;
}

.io-section-title {
  font-size: 11px;
  font-weight: 600;
  letter-spacing: 0.5px;
  color: var(--text-muted);
}

.io-section-stats {
  margin-left: auto;
  font-size: 12px;
  color: var(--text-secondary);
}

.io-section-ops {
  font-weight: 600;
  font-variant-numeric: tabular-nums;
  color: var(--text-primary);
}

.io-section-toggle {
  background: none;
  border: none;
  color: var(--text-muted);
  font-size: 16px;
  cursor: pointer;
  padding: 0 var(--space-xs);
}

.io-section.collapsed .io-section-body {
  display: none;
}

.io-section.collapsed .toggle-icon {
  transform: rotate(0deg);
}

.io-section:not(.collapsed) .toggle-icon::before {
  content: '−';
}

.io-section.collapsed .toggle-icon::before {
  content: '+';
}

.io-section-body {
  padding: var(--space-md);
}

/* Subsections */
.io-subsection {
  margin-bottom: var(--space-md);
}

.io-subsection:last-child {
  margin-bottom: 0;
}

.io-subsection-header {
  display: flex;
  align-items: center;
  gap: var(--space-sm);
  margin-bottom: var(--space-sm);
}

.io-subsection-title {
  font-size: 12px;
  font-weight: 500;
  color: var(--text-secondary);
}

.io-subsection-count {
  font-size: 11px;
  color: var(--text-muted);
}

.io-subsection-content {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
  gap: var(--space-md);
}
```

**Test Plan:**
- [ ] Sections have correct borders/backgrounds
- [ ] Header hover state works
- [ ] Collapse/expand toggles body
- [ ] Grid layout responsive to width
- [ ] Subsection spacing consistent

---

### Phase 7: New I/O Type Cards

#### Task 7.1: Create TCP Server/Client Card Templates
**File:** `src/modules/aio/debug/script.js`
**Description:** Card templates for raw TCP connections.

```javascript
function createTcpServerCard(info) {
  var card = document.createElement('article');
  card.className = 'entity-card tcp-server collapsed';
  card.id = 'tcp-server-' + info.port;

  card.innerHTML = `
    <div class="entity-header" onclick="toggleEntityCard(this.parentElement)">
      <div class="entity-status ok"><span class="status-shape">●</span></div>
      <h3 class="entity-name">:${info.port}</h3>
      <div class="entity-label">TCP</div>
      <div class="entity-summary">
        <span class="summary-metric conn-count">-- conn</span>
        <span class="summary-metric accept-rate">--/s</span>
        <div class="summary-spark"></div>
      </div>
      <button class="expand-toggle"><span class="expand-icon">▼</span></button>
    </div>
    <div class="entity-body">
      <div class="entity-section">
        <div class="entity-section-title">Connections</div>
        <div class="tcp-conn-stats">
          <span class="tcp-stat">●<span class="active-count">--</span> active</span>
          <span class="tcp-stat">○<span class="idle-count">--</span> idle</span>
          <span class="tcp-stat">◐<span class="closing-count">--</span> closing</span>
        </div>
      </div>
      <div class="entity-section">
        <div class="entity-section-title">Throughput</div>
        <div class="sparkline-container">
          <div class="sparkline tcp-throughput-spark"></div>
        </div>
        <div class="tcp-throughput-stats">
          <span>In: <span class="bytes-in">--</span>/s</span>
          <span>Out: <span class="bytes-out">--</span>/s</span>
        </div>
      </div>
    </div>
  `;

  return card;
}

function createTcpClientCard(info) {
  var card = document.createElement('article');
  card.className = 'entity-card tcp-client collapsed';
  card.id = 'tcp-client-' + info.name.replace(/[^a-z0-9]/gi, '-');

  card.innerHTML = `
    <div class="entity-header" onclick="toggleEntityCard(this.parentElement)">
      <div class="entity-status ok"><span class="status-shape">●</span></div>
      <h3 class="entity-name">${info.name}</h3>
      <div class="entity-label">TCP Client</div>
      <div class="entity-summary">
        <span class="summary-metric conn-count">-- conn</span>
        <span class="summary-metric latency">P99:--</span>
        <div class="summary-spark"></div>
      </div>
      <button class="expand-toggle"><span class="expand-icon">▼</span></button>
    </div>
    <div class="entity-body">
      <div class="entity-section">
        <div class="entity-section-title">Connection Pool</div>
        <div class="tcp-pool-bar">
          <div class="tcp-pool-fill" style="width: 0%"></div>
        </div>
        <div class="tcp-pool-stats">
          <span><span class="pool-active">--</span>/<span class="pool-max">--</span> connections</span>
        </div>
      </div>
      <div class="entity-section">
        <div class="entity-section-title">Latency</div>
        <div class="tcp-latency-stats">
          <span>P50: <span class="p50">--</span></span>
          <span>P99: <span class="p99">--</span></span>
        </div>
        <div class="latency-trend-spark"></div>
      </div>
    </div>
  `;

  return card;
}
```

**Test Plan:**
- [ ] TCP server card renders correctly
- [ ] TCP client card renders correctly
- [ ] Connection stats update
- [ ] Throughput sparkline renders
- [ ] Latency values format correctly

---

#### Task 7.2: Create UDP Socket Card Template
**File:** `src/modules/aio/debug/script.js`

```javascript
function createUdpSocketCard(info) {
  var card = document.createElement('article');
  card.className = 'entity-card udp-socket collapsed';
  card.id = 'udp-' + info.name.replace(/[^a-z0-9]/gi, '-');

  card.innerHTML = `
    <div class="entity-header" onclick="toggleEntityCard(this.parentElement)">
      <div class="entity-status ok"><span class="status-shape">●</span></div>
      <h3 class="entity-name">${info.name}</h3>
      <div class="entity-label">UDP</div>
      <div class="entity-summary">
        <span class="summary-metric recv-rate">--/s ↓</span>
        <span class="summary-metric send-rate">--/s ↑</span>
        <span class="summary-metric loss-rate">--% loss</span>
        <div class="summary-spark"></div>
      </div>
      <button class="expand-toggle"><span class="expand-icon">▼</span></button>
    </div>
    <div class="entity-body">
      <div class="entity-section">
        <div class="entity-section-title">Packet Statistics</div>
        <div class="udp-stats-grid">
          <div class="udp-stat">
            <div class="udp-stat-value recv-total">--</div>
            <div class="udp-stat-label">Recv Total</div>
          </div>
          <div class="udp-stat">
            <div class="udp-stat-value send-total">--</div>
            <div class="udp-stat-label">Send Total</div>
          </div>
          <div class="udp-stat">
            <div class="udp-stat-value dropped">--</div>
            <div class="udp-stat-label">Dropped</div>
          </div>
          <div class="udp-stat">
            <div class="udp-stat-value loss-pct">--%</div>
            <div class="udp-stat-label">Loss Rate</div>
          </div>
        </div>
      </div>
      <div class="entity-section">
        <div class="entity-section-title">Throughput</div>
        <div class="sparkline-container">
          <div class="sparkline udp-throughput-spark"></div>
        </div>
      </div>
    </div>
  `;

  return card;
}
```

**Test Plan:**
- [ ] UDP card renders correctly
- [ ] Recv/send rates show arrows
- [ ] Loss rate calculates correctly
- [ ] Dropped count highlights if > 0

---

#### Task 7.3: Create File I/O Card Template
**File:** `src/modules/aio/debug/script.js`

```javascript
function createFileIOCard(info) {
  var card = document.createElement('article');
  card.className = 'entity-card file-io';
  card.id = 'file-io-ops';

  card.innerHTML = `
    <div class="entity-header">
      <div class="entity-status ok"><span class="status-shape">●</span></div>
      <h3 class="entity-name">Async File Operations</h3>
    </div>
    <div class="entity-body">
      <div class="file-io-grid">
        <div class="file-io-row">
          <span class="file-io-label">Reads</span>
          <span class="file-io-rate" id="file-read-rate">--/s</span>
          <div class="file-io-spark" id="file-read-spark"></div>
          <span class="file-io-throughput" id="file-read-throughput">-- MB/s</span>
          <span class="file-io-latency">P99: <span id="file-read-p99">--</span></span>
        </div>
        <div class="file-io-row">
          <span class="file-io-label">Writes</span>
          <span class="file-io-rate" id="file-write-rate">--/s</span>
          <div class="file-io-spark" id="file-write-spark"></div>
          <span class="file-io-throughput" id="file-write-throughput">-- MB/s</span>
          <span class="file-io-latency">P99: <span id="file-write-p99">--</span></span>
        </div>
        <div class="file-io-row">
          <span class="file-io-label">Fsync</span>
          <span class="file-io-rate" id="file-fsync-rate">--/s</span>
          <div class="file-io-spark" id="file-fsync-spark"></div>
          <span class="file-io-throughput">--</span>
          <span class="file-io-latency">P99: <span id="file-fsync-p99">--</span></span>
        </div>
      </div>
      <div class="file-io-pending">
        Open FDs: <span id="file-open-fds">--</span>
        &nbsp;│&nbsp;
        Pending: <span id="file-pending-reads">--</span> read,
        <span id="file-pending-writes">--</span> write
      </div>
    </div>
  `;

  return card;
}
```

**Test Plan:**
- [ ] File I/O card renders
- [ ] Read/write/fsync rows display
- [ ] Throughput formats as MB/s
- [ ] Pending counts update
- [ ] Sparklines render per operation type

---

#### Task 7.4: Create IPC Card Templates
**File:** `src/modules/aio/debug/script.js`

```javascript
function createUnixSocketCard(info) {
  var card = document.createElement('article');
  card.className = 'entity-card unix-socket collapsed';
  card.id = 'unix-' + info.path.replace(/[^a-z0-9]/gi, '-');

  var typeLabel = info.isStream ? 'stream' : 'dgram';

  card.innerHTML = `
    <div class="entity-header" onclick="toggleEntityCard(this.parentElement)">
      <div class="entity-status ok"><span class="status-shape">●</span></div>
      <h3 class="entity-name">${info.path}</h3>
      <div class="entity-label">${typeLabel}</div>
      <div class="entity-summary">
        <span class="summary-metric conn-count">-- conn</span>
        <span class="summary-metric ops-rate">--/s</span>
        <span class="summary-metric latency">P99:--</span>
        <div class="summary-spark"></div>
      </div>
      <button class="expand-toggle"><span class="expand-icon">▼</span></button>
    </div>
    <div class="entity-body">
      <div class="entity-section">
        <div class="entity-section-title">Statistics</div>
        <div class="unix-socket-stats">
          <span>Ops: <span class="ops-total">--</span></span>
          <span>Bytes: <span class="bytes-total">--</span></span>
          ${info.isStream ? '<span>Connections: <span class="conn-count">--</span></span>' : ''}
        </div>
      </div>
      <div class="entity-section">
        <div class="entity-section-title">Throughput</div>
        <div class="sparkline-container">
          <div class="sparkline unix-throughput-spark"></div>
        </div>
      </div>
    </div>
  `;

  return card;
}

function createNamedPipeCard(info) {
  var card = document.createElement('article');
  card.className = 'entity-card named-pipe collapsed';
  card.id = 'pipe-' + info.path.replace(/[^a-z0-9]/gi, '-');

  var dirIcon = info.isWriter ? '→' : '←';
  var dirLabel = info.isWriter ? 'writer' : 'reader';

  card.innerHTML = `
    <div class="entity-header" onclick="toggleEntityCard(this.parentElement)">
      <div class="entity-status ok"><span class="status-shape">●</span></div>
      <h3 class="entity-name">${info.path}</h3>
      <div class="entity-label">${dirIcon} ${dirLabel}</div>
      <div class="entity-summary">
        <span class="summary-metric throughput">-- KB/s</span>
        <div class="summary-spark"></div>
      </div>
      <button class="expand-toggle"><span class="expand-icon">▼</span></button>
    </div>
    <div class="entity-body">
      <div class="entity-section">
        <div class="entity-section-title">Throughput</div>
        <div class="pipe-throughput">
          <span class="pipe-rate">-- KB/s</span>
          <div class="sparkline-container">
            <div class="sparkline pipe-spark"></div>
          </div>
        </div>
      </div>
      <div class="entity-section">
        <div class="entity-section-title">Buffer</div>
        <div class="pipe-buffer-bar">
          <div class="pipe-buffer-fill" style="width: 0%"></div>
        </div>
        <div class="pipe-buffer-label"><span class="buffer-pct">0</span>% full</div>
      </div>
    </div>
  `;

  return card;
}
```

**Test Plan:**
- [ ] Unix socket card shows stream/dgram type
- [ ] Named pipe card shows direction
- [ ] Path formatting handles special chars
- [ ] Buffer bar renders correctly
- [ ] Abstract socket paths display (@name)

---

## 4. Test Plan Summary

### 4.1 Unit Tests

| Component | Test File | Coverage |
|-----------|-----------|----------|
| History Buffer | `test/test_dashboard_history.js` | push, wrap, toArray |
| Mini Sparkline | `test/test_dashboard_sparkline.js` | render, empty, scale |
| Percentile Sparkline | `test/test_dashboard_sparkline.js` | multi-line, scale |
| Status Code Sparkline | `test/test_dashboard_sparkline.js` | stacked, proportions |
| Health Aggregation | `test/test_dashboard_health.js` | counts, rates, P99 |

### 4.2 Integration Tests

| Scenario | Steps | Expected |
|----------|-------|----------|
| Initial Load | Load dashboard with no data | All placeholders show "--" |
| Data Update | Push metrics via SSE | Values update, sparklines render |
| Card Collapse | Click card header | Body hides, summary shows |
| Card Expand | Click collapsed card | Body shows, summary hides |
| Keyboard Nav | Press j/k keys | Focus moves between cards |
| Section Toggle | Click section header | Section collapses/expands |
| Error State | Server returns 500 | Error banner shows |

### 4.3 Visual Tests

| Test | Method | Pass Criteria |
|------|--------|---------------|
| Responsive 1200px | Browser resize | 3-column grid |
| Responsive 900px | Browser resize | 2-column grid |
| Responsive 600px | Browser resize | 1-column stack |
| Color Contrast | WCAG checker | AA compliance |
| Status Shapes | Visual inspection | Distinct shapes visible |
| Sparkline Scaling | Inject max/min data | Lines fill container |

### 4.4 Performance Tests

| Test | Method | Target |
|------|--------|--------|
| Render 10 cards | Performance.measure | < 50ms |
| Update 10 cards | Performance.measure | < 20ms |
| 60s history buffer | Memory snapshot | < 1MB total |
| SSE reconnect | Network throttle | Auto-reconnect < 5s |

### 4.5 Accessibility Tests

| Test | Tool | Pass Criteria |
|------|------|---------------|
| Screen reader | NVDA/VoiceOver | All content announced |
| Keyboard only | Manual | All actions accessible |
| Focus visible | Manual | Focus ring visible |
| Color blindness | Sim Daltonism | Status distinguishable |

---

## 5. Migration Plan

### 5.1 Phase Rollout

| Phase | Features | Risk | Rollback |
|-------|----------|------|----------|
| 1 | Core infrastructure, sparklines | Low | Feature flag |
| 2 | Health bar, collapsible cards | Low | CSS toggle |
| 3 | Response/latency sparklines | Medium | Remove JS |
| 4 | Keyboard navigation | Low | Remove listener |
| 5 | I/O type sections | Medium | Revert HTML |
| 6 | New I/O cards (TCP, UDP, etc.) | High | Feature flag |

### 5.2 Feature Flags

```javascript
var DASHBOARD_FLAGS = {
  sparklines: true,
  collapsibleCards: true,
  keyboardNav: true,
  ioSections: false,  // Enable after backend support
  tcpMetrics: false,
  udpMetrics: false,
  fileMetrics: false,
  ipcMetrics: false
};
```

### 5.3 Backend Requirements

New metrics endpoints needed for full implementation:

| I/O Type | Endpoint | Status |
|----------|----------|--------|
| HTTP Server | `/debug/metrics` | ✓ Exists |
| HTTP Client | `/debug/metrics` | ✓ Exists |
| TCP Server | `/debug/metrics` | TODO |
| TCP Client | `/debug/metrics` | TODO |
| UDP Socket | `/debug/metrics` | TODO |
| File I/O | `/debug/metrics` | TODO |
| Unix Socket | `/debug/metrics` | TODO |
| Named Pipe | `/debug/metrics` | TODO |

---

## 6. Success Metrics

| Metric | Current | Target | Measurement |
|--------|---------|--------|-------------|
| Page height (10 servers) | ~2000px | ~1200px | DevTools |
| Time to assess health | ~10s | ~3s | User testing |
| Keyboard accessibility | None | Full | Manual test |
| Trend visibility | None | 60s history | Visual |
| I/O coverage | HTTP only | All types | Feature count |

---

## 7. Open Questions

1. **Backend priority**: Which new I/O metrics should be implemented first?
2. **History duration**: 60 seconds enough? Should it be configurable?
3. **Card default state**: Start collapsed or expanded?
4. **Mobile support**: Full responsive or desktop-only?
5. **Data export**: Add JSON/CSV export for sparkline data?

---

## Appendix A: File Changes Summary

| File | Changes |
|------|---------|
| `src/modules/aio/debug/body.html` | Health bar, keyboard help, I/O sections |
| `src/modules/aio/debug/style.css` | ~400 lines new CSS |
| `src/modules/aio/debug/script.js` | ~600 lines new JS |
| `src/aio_metrics.c` | New metric types (future) |
| `src/aio_metrics.h` | New struct definitions (future) |

## Appendix B: CSS Variable Additions

```css
/* New semantic colors for I/O types */
--color-tcp: #06b6d4;      /* Cyan */
--color-udp: #8b5cf6;      /* Purple */
--color-file: #f59e0b;     /* Amber */
--color-ipc: #ec4899;      /* Pink */
--color-http: #3b82f6;     /* Blue (existing) */
```
