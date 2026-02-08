# Valkyria Dashboard Design Document

## Overview

The Valkyria Dashboard is an observability interface for monitoring the Valkyria VM runtime, HTTP server infrastructure, and client connections. It provides real-time visibility into system health, performance metrics, and resource utilization across multiple subsystems.

**Demo:** `static/dashboard-demo.html`

---

## 1. Design Philosophy

### 1.1 Core Principles

| Principle | Description |
|-----------|-------------|
| **Entity-Centric** | Metrics are organized by logical entity (VM, AIO system, server, client) rather than metric type |
| **Glanceable** | Critical health indicators visible immediately; details available on demand |
| **Per-Instance** | Each server/client has its own visualizations; no aggregated-only views |
| **Semantic Colors** | Consistent color language: green=ok, yellow=warning, red=error, blue=info |
| **Dense but Readable** | Maximize information density without sacrificing clarity |
| **Accessible First** | Full WCAG compliance, color blindness support, keyboard navigation |
| **Redundant Indicators** | Never rely on color alone; use icons and patterns alongside colors |

### 1.2 Target Users

- **Operators**: Need quick health assessment and anomaly detection
- **Developers**: Need detailed metrics for debugging and optimization
- **SREs**: Need historical context and trend analysis

---

## 2. Information Architecture

### 2.1 Hierarchy

```
Dashboard
├── Skip Link (accessibility: keyboard jump to main content)
├── Header (global status, uptime, timestamp)
├── Health Overview Panel (RED metrics at a glance)
│   ├── Active Connections
│   ├── Request Rate
│   ├── Error Rate
│   └── P99 Latency
├── VM Section
│   ├── Garbage Collector
│   ├── Heap Memory
│   └── Interpreter
├── AIO Systems Section
│   ├── AIO System 1 (Main)
│   │   ├── Event Loop Stats
│   │   ├── Connection Pool Grid
│   │   └── Resource Pools (Arenas, Buffers)
│   └── AIO System 2 (Background)
│       └── ...
├── HTTP Servers Section
│   ├── Server 1 (0.0.0.0:8443)
│   │   ├── Response Codes
│   │   ├── Latency Histogram
│   │   └── Throughput Sparkline
│   ├── Server 2 (0.0.0.0:8080)
│   └── Server 3 (127.0.0.1:9090)
└── HTTP Clients Section
    ├── Client 1 (postgres-primary)
    │   ├── Connection/Query Stats
    │   ├── Latency Histogram
    │   └── Rate Sparkline
    ├── Client 2 (redis-cache)
    └── Client 3 (payment-gateway)
```

### 2.2 Section Purposes

| Section | Purpose | Key Metrics |
|---------|---------|-------------|
| **VM** | Language runtime health | GC cycles, heap utilization, eval counts |
| **AIO** | I/O subsystem health | Event loop iterations, connection pools, buffer usage |
| **HTTP Servers** | Inbound request handling | Response codes, latency percentiles, throughput |
| **HTTP Clients** | Outbound connection health | Connection count, latency, error rates |

---

## 3. Visual Design System

### 3.1 Color Palette

The dashboard uses a GitHub-dark inspired theme with semantic color coding:

```css
/* Background Hierarchy */
--bg-primary: #0d1117;     /* Page background */
--bg-secondary: #161b22;   /* Card background */
--bg-tertiary: #1c2128;    /* Headers, elevated elements */
--bg-elevated: #21262d;    /* Interactive elements */

/* Borders */
--border-default: #30363d; /* Primary borders */
--border-muted: #21262d;   /* Subtle separators */

/* Text Hierarchy */
--text-primary: #f0f6fc;   /* Headings, values */
--text-secondary: #c9d1d9; /* Body text */
--text-muted: #8b949e;     /* Labels */
--text-faint: #6e7681;     /* De-emphasized */

/* Semantic Colors */
--color-ok: #3fb950;       /* Success, healthy, active */
--color-warning: #d29922;  /* Warning, degraded */
--color-error: #f85149;    /* Error, critical */
--color-info: #58a6ff;     /* Informational, links */

/* Section Colors */
--color-purple: #a371f7;   /* VM section */
--color-cyan: #39d4d4;     /* AIO section */
--color-info: #58a6ff;     /* HTTP servers (blue) */
--color-pink: #db61a2;     /* HTTP clients */
```

### 3.2 Typography

```css
/* Font Stack */
font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif;

/* Monospace (for addresses, values) */
font-family: 'SF Mono', Monaco, monospace;

/* Size Scale (WCAG compliant - minimum 11px) */
11px  - Minimum size: micro labels, legends, percentile labels
12px  - Body text, metric labels, tags
13px  - Panel titles
14px  - Entity names, stat values
16px  - Section titles, large values
18px  - Logo text
20px  - Gauge center values
```

**Note:** Minimum font size is 11px for WCAG accessibility compliance. The previous 9px/10px sizes have been increased.

### 3.3 Spacing Scale

```css
--space-xs: 4px;   /* Tight spacing */
--space-sm: 8px;   /* Element gaps */
--space-md: 12px;  /* Section padding */
--space-lg: 16px;  /* Card padding */
--space-xl: 24px;  /* Section gaps */
--space-2xl: 32px; /* Major section margins */
```

### 3.4 Border Radius

```css
--radius-sm: 4px;  /* Small elements */
--radius-md: 6px;  /* Cards, panels */
--radius-lg: 8px;  /* Large containers */
999px              /* Pills, status badges */
```

---

## 4. Component Specifications

### 4.1 Skip Link

**Purpose:** Accessibility feature for keyboard users to bypass navigation

**Elements:**
- Hidden link that becomes visible on focus
- Jumps to main content area

**Behavior:**
- Invisible until focused (Tab key)
- Appears at top-left with high-contrast styling
- Keyboard shortcut to main content

```html
<a href="#main-content" class="skip-link">Skip to main content</a>
```

### 4.2 Header

**Purpose:** Global status overview and navigation anchor

**Elements:**
- Logo with gradient icon (blue → purple)
- Status badge with pulse animation ("All Systems Healthy")
- Status icon (✓/!/✕) alongside color for color blindness support
- Global stats (Uptime, Last Update timestamp)

**Behavior:**
- Sticky positioning (stays at top on scroll)
- Status badge changes color AND icon based on worst system status
- Timestamp updates every second
- ARIA live region for status announcements

```
┌─────────────────────────────────────────────────────────────────────┐
│ [V] Valkyria Dashboard   ✓ All Systems Healthy      Uptime: 2d 14h │
└─────────────────────────────────────────────────────────────────────┘
```

### 4.3 Health Overview Panel

**Purpose:** RED metrics (Rate, Errors, Duration) at a glance for quick health assessment

**Elements:**
- 4 summary cards in a row
- Active Connections (current count)
- Request Rate (requests/sec with trend arrow)
- Error Rate (percentage with color coding)
- P99 Latency (milliseconds)

**Behavior:**
- Always visible at top below header
- Color-coded values based on thresholds
- Icons alongside colors for accessibility

```
┌───────────────┬───────────────┬───────────────┬───────────────┐
│ 🔗 398        │ 📈 2.5K/s ↑   │ ⚠ 0.3%        │ ⏱ 42ms        │
│ Active Conns  │ Request Rate  │ Error Rate    │ P99 Latency   │
└───────────────┴───────────────┴───────────────┴───────────────┘
```

### 4.4 Section Header

**Purpose:** Identify metric groups and show aggregate status

**Elements:**
- Section icon (colored, matches section theme)
- Title and subtitle
- Status badges (summary metrics)

```
┌─────────────────────────────────────────────────────────────────────┐
│ [HTTP] HTTP Servers · Inbound Request Handling    [3 servers] [1.5K req/s]
└─────────────────────────────────────────────────────────────────────┘
```

### 4.5 Panel

**Purpose:** Container for related metrics within a section

**Structure:**
```
┌──────────────────────────────┐
│ [G] Garbage Collector  142   │ ← Header with icon, title, badge
├──────────────────────────────┤
│                              │
│    [GC Timeline Visual]      │ ← Body content
│                              │
│  Cycles  Max    Avg  Reclaimed│
│   142   2.4ms  0.8ms  24MB   │
└──────────────────────────────┘
```

**Variants:**
- Standard panel (metric rows)
- Gauge panel (circular progress)
- Timeline panel (GC events)
- Pool panel (connection grid + progress bars)

### 4.6 Entity Card

**Purpose:** Self-contained view of a server or client

**Structure:**
```
┌──────────────────────────────────────────────────────────────────┐
│ ● 0.0.0.0:8443  [HTTPS]                          247 Conns 1.2K/s │
├──────────────────────────────────────────────────────────────────┤
│ RESPONSE CODES                                                    │
│ ┌────────┐ ┌────────┐ ┌────────┐                                 │
│ │ 45,231 │ │   127  │ │    3   │                                 │
│ │  2xx   │ │  4xx   │ │  5xx   │                                 │
│ └────────┘ └────────┘ └────────┘                                 │
│ [████████████████████████████████░░]                              │
│                                                                   │
│ LATENCY DISTRIBUTION                                              │
│ ▁▂▅█▆▄▂▁▁▁  P50: 4ms  P95: 18ms  P99: 42ms                       │
│                                                                   │
│ THROUGHPUT                                                        │
│ [~~~~~sparkline~~~~~]  In: 2.1 MB/s  Out: 16.4 MB/s              │
└──────────────────────────────────────────────────────────────────┘
```

**Header Elements:**
- Status indicator (green/yellow/red dot)
- Entity name (monospace, e.g., `0.0.0.0:8443`)
- Label/type badge (e.g., "HTTPS", "Database")
- Quick stats (connections, request rate)

**Body Sections:**
- Each entity card has 2-3 visualization sections
- Sections have uppercase titles
- Content varies by entity type

---

## 5. Visualization Specifications

### 5.1 Histogram (Latency Distribution)

**Purpose:** Show request/query latency distribution with percentile markers

**Dimensions:** Full width, 50px height

**Elements:**
- 10 bars representing latency buckets
- Color coding: P50 (green), P95 (yellow), P99 (red)
- Percentile legend below

**Rendering:**
```javascript
function renderHistogram(id, buckets) {
  // buckets = [{ count: N, p?: 'p50'|'p95'|'p99' }, ...]
  const max = Math.max(...buckets.map(b => b.count));
  // Bars proportional to max, min 2px height
  // Add hover state for detail
}
```

**Bucket Ranges (example for HTTP):**
| Bucket | Range |
|--------|-------|
| 1 | 0-1ms |
| 2 | 1-2ms |
| 3 | 2-5ms |
| 4 | 5-10ms |
| 5 | 10-25ms |
| 6 | 25-50ms |
| 7 | 50-100ms |
| 8 | 100-250ms |
| 9 | 250-500ms |
| 10 | 500ms+ |

### 5.2 Sparkline (Throughput/Rate)

**Purpose:** Show time-series trend (last N minutes)

**Dimensions:** Full width, 40px height

**Elements:**
- SVG path for line
- Filled area under line (20% opacity)
- Dual lines for in/out (servers) or single line (clients)
- **Time range labels**: "-5m" on left, "now" on right for temporal context

**Rendering:**
```javascript
function renderSparkline(id, color1, color2) {
  // Generate SVG with:
  // - viewBox="0 0 200 40"
  // - preserveAspectRatio="none" for responsive scaling
  // - Smooth bezier or linear path
  // - Area fill for visual weight
}
```

**Time Labels:**
```
-5m ~~~~~~~~~~~~~~~~~~~~~~~~~~~~ now
```

**Colors:**
- Servers: Green (in) + Blue (out)
- Clients: Pink (single rate)

### 5.3 Gauge (Heap Memory)

**Purpose:** Show utilization percentage with thresholds

**Dimensions:** 100x100px

**Elements:**
- Background circle (stroke-width: 10)
- Progress arc (stroke-dasharray/dashoffset)
- Center value (20px bold)
- Unit label (11px muted)
- **Threshold markers**: Visual ticks at 70% and 90% boundaries on the arc

**Thresholds:**
| Range | Color |
|-------|-------|
| 0-70% | Green |
| 70-90% | Yellow |
| 90-100% | Red |

**Threshold Markers:**
Visible tick marks on the gauge arc at 70% and 90% positions help users understand when color changes occur.

**Rendering:**
```javascript
// Circle circumference = 2 * PI * radius = 2 * 3.14159 * 40 = 251.2
// For 67% fill: dashoffset = 251.2 * (1 - 0.67) = 82.9
// Threshold ticks at 70% and 90% of the arc
```

### 5.4 GC Timeline

**Purpose:** Visualize GC pause events over time

**Dimensions:** Full width, 60px height

**Elements:**
- Horizontal timeline with vertical bars
- Bar height = pause duration (scaled)
- Bar color: green (minor), yellow (major), red (long pause)
- **Time axis**: "-5m" on left, "now" on right
- **Threshold line**: Horizontal reference at 10ms level

**Rendering:**
```javascript
function renderGCTimeline() {
  // For each GC event:
  // - Position: x = event_time / window_duration * 100%
  // - Height: min(pause_ms * 15, 50)px
  // - Class: major if full GC, long if > threshold
  // Aggregate events when many occur close together
}
```

**Time Axis:**
```
-5m                                                now
│▁▂▅█▆▄▂▁▁▃▂▅▃▁▂▅▆▃▁▂▄▆█▅▃▂▁▃▅▆▄▂▁▃▅▇▅▃│
────────── 10ms threshold line ──────────
```

### 5.5 Connection Pool Visualization

**Purpose:** Visualize connection slot utilization

**Two-tier Approach:**
For large pools (>100 connections), a stacked bar provides better readability than a 500-square grid.

#### 5.5.1 Stacked Bar (Primary - for large pools)

**Dimensions:** Full width, 16px height

**Elements:**
- Horizontal stacked bar showing proportions
- Segments: Active (green), Idle (blue), Closing (yellow), Empty (gray)
- Percentage labels on each segment

```
[████████ Active 49% ████████][████ Idle 28% ████][█ 2%][████ Empty 21% ████]
```

#### 5.5.2 Mini Grid (Secondary - detail view)

**Dimensions:** 10 columns, compact

**Elements:**
- Small representative grid (10x3 = 30 slots)
- Same color coding as stacked bar
- Provides visual texture alongside the bar

**Legend with Icons (for color blindness):**
```
● Active  ○ Idle  ◐ Closing  ○ Empty
```

**Rendering:**
```javascript
function renderConnPool(id, total, active, idle, closing) {
  // Render stacked bar for proportions
  // Render mini grid for visual detail
  // Use icons alongside colors in legend
}
```

### 5.6 Progress Bar (Resource Pools)

**Purpose:** Show utilization of fixed-size pools

**Dimensions:** Full width, 6px height

**Elements:**
- Background track (rounded)
- Fill bar with color based on threshold

**Thresholds:**
| Usage | Color |
|-------|-------|
| 0-50% | Blue (default) |
| 50-75% | Blue |
| 75-90% | Yellow (warning) |
| 90-100% | Red (critical) |

### 5.7 Status Bar (Response Codes)

**Purpose:** Show proportional breakdown of HTTP status codes

**Dimensions:** Full width, 8px height (increased from 4px for better visibility)

**Elements:**
- Segmented bar with proportional widths
- Segment colors: green (2xx), yellow (4xx), red (5xx)
- **Striped pattern** on warning/error segments for color blindness

**Color Blindness Support:**
- 4xx segments use diagonal stripes pattern
- 5xx segments use denser diagonal stripes pattern
- Patterns visible regardless of color perception

```
[██████████████████████████████████░░]
     98.7% 2xx      1.1% 4xx   0.2% 5xx
```

**CSS for patterns:**
```css
.segment.warning {
  background-image: repeating-linear-gradient(
    45deg, transparent, transparent 3px,
    rgba(255,255,255,0.1) 3px, rgba(255,255,255,0.1) 6px
  );
}
```

---

## 6. Layout Specifications

### 6.1 Grid System

The dashboard uses CSS Grid for responsive layouts:

```css
.grid-4 { grid-template-columns: repeat(4, 1fr); }
.grid-3 { grid-template-columns: repeat(3, 1fr); }
.grid-2 { grid-template-columns: repeat(2, 1fr); }
```

**Breakpoints:**
| Width | Behavior |
|-------|----------|
| > 1400px | Full grid (4-col → 4, 3-col → 3, 2-col → 2) |
| 900-1400px | Reduced (4-col → 2, 3-col → 2, 2-col → 2) |
| < 900px | Single column |

### 6.2 Section Layouts

| Section | Grid | Rationale |
|---------|------|-----------|
| VM | 3-col | 3 equal panels (GC, Heap, Interpreter) |
| AIO | 2-col | 2 systems (expandable) |
| HTTP Servers | 3-col | Typical server count, entity cards |
| HTTP Clients | 3-col | Matches servers for visual consistency |

### 6.3 Card Sizing

**Panel (VM/AIO):**
- Min width: 280px
- Padding: 16px
- Gap: 16px

**Entity Card (Server/Client):**
- Min width: 320px
- Header: 48px
- Body padding: 16px
- Section margin: 16px

---

## 7. Metric Data Model

### 7.1 VM Metrics

```json
{
  "gc": {
    "cycles_total": 142,
    "pause_us_total": 234000,
    "pause_us_max": 2400,
    "pause_ms_avg": 0.8,
    "heap_used_bytes": 134217728,
    "heap_total_bytes": 201326592,
    "heap_utilization_pct": 66.7,
    "reclaimed_bytes_total": 25165824
  },
  "interpreter": {
    "evals_total": 1200000,
    "function_calls": 847000,
    "builtin_calls": 156000,
    "stack_depth_max": 42,
    "closures_created": 12847,
    "env_lookups": 2400000
  }
}
```

### 7.2 AIO Metrics

```json
{
  "aio_systems": [
    {
      "name": "Main AIO",
      "role": "primary",
      "event_loop": {
        "iterations": 847000,
        "events_processed": 1200000,
        "handles_active": 12,
        "idle_time_us": 45000000
      },
      "connection_pool": {
        "total": 500,
        "active": 247,
        "idle": 142,
        "closing": 8
      },
      "arenas": {
        "used": 24,
        "total": 32
      },
      "tcp_buffers": {
        "used": 156,
        "total": 256
      }
    }
  ]
}
```

### 7.3 HTTP Server Metrics

```json
{
  "servers": [
    {
      "address": "0.0.0.0",
      "port": 8443,
      "protocol": "HTTPS",
      "status": "healthy",
      "connections": {
        "active": 247,
        "total": 45361,
        "failed": 12
      },
      "requests": {
        "total": 45361,
        "rate_per_sec": 1200,
        "status_2xx": 45231,
        "status_4xx": 127,
        "status_5xx": 3
      },
      "latency": {
        "p50_ms": 4,
        "p95_ms": 18,
        "p99_ms": 42,
        "histogram": [80, 220, 480, 320, 180, 90, 25, 8, 2, 1]
      },
      "throughput": {
        "bytes_in_per_sec": 2200000,
        "bytes_out_per_sec": 17200000
      }
    }
  ]
}
```

### 7.4 HTTP Client Metrics

```json
{
  "clients": [
    {
      "name": "postgres-primary",
      "type": "Database",
      "status": "healthy",
      "connections": {
        "active": 12,
        "pool_size": 20
      },
      "operations": {
        "total": 4200,
        "rate_per_sec": 142,
        "errors": 0
      },
      "latency": {
        "p50_ms": 1.2,
        "p95_ms": 4.8,
        "p99_ms": 12,
        "histogram": [180, 420, 280, 120, 45, 12, 4, 1, 0, 0]
      }
    }
  ]
}
```

---

## 8. Real-Time Updates

### 8.1 Polling Strategy

```javascript
const POLL_INTERVAL = 1000; // 1 second
let retryDelay = 1000;
let pollTimer = null;

async function pollMetrics() {
  try {
    const response = await fetch('/debug/metrics');
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const data = await response.json();
    render(data);
    showError(false);
    retryDelay = 1000; // Reset on success
  } catch (error) {
    showError(true);
    // Exponential backoff on failure
    clearInterval(pollTimer);
    setTimeout(startPolling, retryDelay);
    retryDelay = Math.min(retryDelay * 2, 30000); // Max 30s
  }
}

function startPolling() {
  pollMetrics();
  pollTimer = setInterval(pollMetrics, POLL_INTERVAL);
}

// Visibility API for battery saving
document.addEventListener('visibilitychange', function() {
  if (document.hidden) {
    clearInterval(pollTimer);
  } else {
    startPolling();
  }
});

startPolling();
```

### 8.2 Update Behavior

| Element | Update Strategy |
|---------|-----------------|
| Timestamp | Local clock (1s) |
| Gauges | Smooth transition (0.5s) |
| Histograms | Instant redraw |
| Sparklines | Shift left, append new point |
| Counters | Animate number change |
| Status indicators | Instant color change |

### 8.3 Error Handling

- Network errors show error banner at top (dismissible)
- Status dot turns red with ✕ icon
- Metrics freeze until recovery
- **Exponential backoff**: 1s → 2s → 4s → ... → 30s max
- Auto-retry with increasing intervals
- Banner shows "Connection lost. Retrying..." with retry countdown

**Error Banner:**
```html
<div class="error-banner" role="alert" aria-live="assertive">
  ⚠ Connection to metrics server lost. Retrying in 4s...
  <button aria-label="Dismiss error">×</button>
</div>
```

---

## 9. Accessibility

### 9.1 Color Contrast

All text meets WCAG AA contrast ratios:
- Primary text on bg-primary: 13.8:1
- Muted text on bg-primary: 6.2:1
- Minimum font size: 11px (WCAG compliance)
- Semantic colors designed for colorblind accessibility

### 9.2 Color Blindness Support

**Critical:** Never rely on color alone to convey information.

| State | Color | Icon | Pattern |
|-------|-------|------|---------|
| Healthy | Green | ✓ | Solid |
| Warning | Yellow | ! | Diagonal stripes |
| Error | Red | ✕ | Dense diagonal stripes |

All status indicators include both color AND icon. Progress bars and status bars use patterns for warning/error states.

### 9.3 Semantic HTML

- Skip link for keyboard users to bypass navigation
- Proper heading hierarchy (h1 → h2 → h3)
- ARIA labels on all interactive elements
- ARIA live regions for dynamic status updates
- Role attributes on semantic sections (banner, main, navigation)

```html
<a href="#main-content" class="skip-link">Skip to main content</a>
<header role="banner" aria-label="Dashboard header">
<main id="main-content" role="main" aria-label="Dashboard metrics">
<div role="status" aria-live="polite" id="global-status">
```

### 9.4 Keyboard Navigation

- All interactive elements focusable via Tab
- Visible focus states (2px solid outline)
- Skip link appears on first Tab press
- Logical tab order following visual layout

### 9.5 Responsive Design

- Minimum touch target: 44x44px
- Readable at 200% zoom
- No horizontal scroll at any breakpoint

---

## 10. Implementation Notes

### 10.1 File Structure

```
src/modules/aio/debug/
├── style.css       # Existing styles (to be updated)
├── script.js       # Existing JS (to be updated)
├── body.html       # HTML fragment (to be updated)
└── handlers.c      # C handlers for /debug/* endpoints

static/
└── dashboard-demo.html  # Standalone demo (this design)
```

### 10.2 Dependencies

- No external libraries (vanilla JS/CSS)
- Modern browser features required:
  - CSS Grid
  - CSS Custom Properties
  - SVG
  - Fetch API
  - Visibility API (for battery saving)

**Browser Compatibility Fallbacks:**
```css
/* Fallback for browsers without `inset` support */
.element {
  top: 0; right: 0; bottom: 0; left: 0;
  inset: 0; /* Modern browsers override above */
}

/* Fallback for browsers without `aspect-ratio` */
.square {
  width: 8px; height: 8px;
  aspect-ratio: 1; /* Modern browsers override above */
}
```

### 10.3 Performance Considerations

- Minimize DOM operations (batch updates)
- Use CSS transforms for animations
- Debounce resize handlers
- Consider virtual scrolling for large connection pools

### 10.4 Future Enhancements

1. **Interactive features:** Expand/collapse sections, click-to-detail
2. **Time range selector:** 1m, 5m, 15m, 1h views
3. **Alerting integration:** Highlight metrics exceeding thresholds
4. **Export:** JSON/Prometheus format download
5. **WebSocket:** Replace polling for lower latency

---

## 11. Appendix

### A. CSS Variable Reference

See Section 3.1 for complete color palette.

### B. Icon Key

| Icon | Meaning |
|------|---------|
| V | Valkyria VM |
| G | Garbage Collector |
| M | Memory |
| I | Interpreter |
| A | Async I/O |
| S | HTTP Server |
| C | HTTP Client |

### C. Status Indicator States

| State | Color | Meaning |
|-------|-------|---------|
| Healthy | Green (#3fb950) | All metrics normal |
| Warning | Yellow (#d29922) | Elevated errors or latency |
| Error | Red (#f85149) | Critical failure or unreachable |

### D. Example Metric Thresholds

| Metric | Warning | Critical |
|--------|---------|----------|
| Heap Utilization | > 70% | > 90% |
| GC Pause | > 10ms | > 50ms |
| Error Rate | > 1% | > 5% |
| P99 Latency | > 100ms | > 500ms |
| Buffer Pool | > 85% | > 95% |

---

## 12. Prometheus Metrics Integration

The dashboard is backed by a comprehensive Prometheus metrics system. See `PROMETHEUS_METRICS_PLAN.md` for full implementation details.

### 12.1 Metrics Hierarchy

Metrics are organized at four hierarchical levels:

| Level | Scope | Prefix/Labels | Example |
|-------|-------|---------------|---------|
| **VM** | Process-wide | `valk_gc_*`, `valk_eval_*` | `valk_gc_heap_utilization_ratio` |
| **AIO System** | Subsystem-wide | `valk_aio_*` | `valk_aio_arenas_used` |
| **Per-Server** | Individual server | `http_*{server,port,protocol}` | `http_requests_total{server="0.0.0.0",port="8443",protocol="https"}` |
| **Per-Client** | Individual client | `http_client_*{client,type}` | `http_client_operations_total{client="postgres",type="Database"}` |

### 12.2 Endpoint Structure

The `/metrics` endpoint returns Prometheus text format (v0.0.4) with metrics from four sources:

```
# AIO HTTP aggregate metrics
valk_aio_uptime_seconds
valk_aio_connections_total
valk_aio_connections_active
valk_aio_connections_idle
valk_aio_connections_closing

# AIO system stats
valk_aio_servers_count
valk_aio_arenas_used / valk_aio_arenas_total
valk_aio_tcp_buffers_used / valk_aio_tcp_buffers_total

# Per-server modular metrics (with labels)
http_requests_total{server,port,protocol,status}
http_connections_active{server,port,protocol}
http_request_duration_seconds{server,port,protocol}  # histogram
http_bytes_sent_total{server,port,protocol}

# Per-client metrics (with labels)
http_client_connections_active{client,type}
http_client_operations_total{client,type}
http_client_errors_total{client,type}
http_client_latency_seconds_avg{client,type}

# VM metrics
valk_gc_cycles_total
valk_gc_heap_used_bytes
valk_gc_heap_utilization_ratio
valk_eval_total
valk_loop_iterations_total
```

### 12.3 Dashboard Data Sources

| Dashboard Section | Data Source | Endpoint |
|-------------------|-------------|----------|
| Health Overview | Aggregated from per-server metrics | `/metrics` |
| VM / GC | `valk_gc_*`, `valk_eval_*` | `/metrics` |
| VM / Heap | `valk_gc_heap_*` | `/metrics` |
| AIO Systems | `valk_aio_*` | `/metrics` |
| HTTP Servers | `http_*{server,port,protocol}` | `/metrics` |
| HTTP Clients | `http_client_*{client,type}` | `/metrics` |
| JSON (debug) | All metrics combined | `/debug/metrics` |

### 12.4 Lisp Builtins for Metrics

```lisp
; System metrics
(aio/metrics-prometheus sys)         ; AIO HTTP aggregates
(aio/system-stats-prometheus sys)    ; AIO system stats
(vm/metrics-prometheus)              ; VM/GC/interpreter
(metrics/prometheus)                 ; Modular per-server metrics

; HTTP client registration and tracking
(http-client/register sys name type pool-size)
(http-client/on-operation sys id duration-us error? retry?)
(http-client/on-cache sys id hit?)
(http-client/metrics-prometheus sys)
```

### 12.5 PromQL Examples for Dashboard

```promql
# Request Rate (req/s) - Health Overview
rate(http_requests_total[1m])

# Error Rate (%) - Health Overview
100 * rate(http_requests_total{status=~"4xx|5xx"}[1m])
    / rate(http_requests_total[1m])

# P99 Latency (ms) - Health Overview
histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m])) * 1000

# Heap Utilization (%) - VM Section
valk_gc_heap_utilization_ratio * 100

# Connection Pool Utilization (%) - AIO Section
100 * valk_aio_arenas_used / valk_aio_arenas_total

# GC Pause Avg (ms) - VM Section
(rate(valk_gc_pause_seconds_total[5m]) / rate(valk_gc_cycles_total[5m])) * 1000

# Per-server request rate
rate(http_requests_total{server="0.0.0.0",port="8443"}[1m])

# Per-client error rate
rate(http_client_errors_total{client="postgres-primary"}[1m])
```
