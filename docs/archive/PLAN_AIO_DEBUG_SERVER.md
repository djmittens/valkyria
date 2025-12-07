# PLAN: AIO Debug Server

**Status**: Draft
**Created**: 2025-12-02
**Goal**: Lightweight metrics and debug dashboard for Valkyria's async I/O system

## Overview

Add runtime observability for AIO system with:
- Atomic metrics collection in C (RED/USE method)
- Simple JSON/Prometheus endpoints
- Data-driven HTML dashboard with polling
- Compile-time opt-out via `#ifdef VALK_METRICS_ENABLED`

**Design Principles**:
- Security via reverse proxies (no auth in-language)
- Same HTML serves all routes, reacts to JSON
- Simple polling (1-2s) over SSE complexity
- Extensible routes with query param filtering
- Prometheus format for portability (no external deps)

## Architecture

### Routes

```
GET /debug/                    → Static HTML dashboard
GET /debug/metrics             → JSON metrics (all)
GET /debug/metrics?server=0    → JSON filtered to server 0
GET /debug/metrics?client=1    → JSON filtered to client 1
GET /metrics                   → Prometheus text format
```

**Dashboard Flow**:
1. Browser loads `/debug/` → receives static HTML
2. HTML polls `/debug/metrics` every 1-2 seconds
3. HTML renders whatever JSON it receives
4. Same HTML works for filtered views (reads endpoint from URL)

### Metrics Structure

```c
// src/aio_metrics.h
typedef struct {
  // RED Method (Rate, Errors, Duration)
  _Atomic uint64_t requests_total;
  _Atomic uint64_t requests_active;
  _Atomic uint64_t requests_errors;
  _Atomic uint64_t request_bytes_sent;
  _Atomic uint64_t request_bytes_recv;
  _Atomic uint64_t request_duration_us_sum;  // For avg latency

  // USE Method (Utilization, Saturation, Errors)
  _Atomic uint64_t connections_total;
  _Atomic uint64_t connections_active;
  _Atomic uint64_t connections_failed;
  _Atomic uint64_t streams_total;
  _Atomic uint64_t streams_active;

  // Resource usage
  _Atomic uint64_t bytes_sent_total;
  _Atomic uint64_t bytes_recv_total;

  uint64_t start_time_us;  // System boot time
} valk_aio_metrics_t;
```

**Why not per-server structs?** Most deployments have 1-3 servers. Adding per-server arrays adds complexity for marginal benefit. Filter at render time instead.

### Instrumentation Points

```c
// src/aio_uv.c - wrapped in #ifdef VALK_METRICS_ENABLED

// On connection accept/establish
void valk_aio_metrics_on_connection(valk_aio_metrics_t* m, bool success) {
  atomic_fetch_add(&m->connections_total, 1);
  if (success) {
    atomic_fetch_add(&m->connections_active, 1);
  } else {
    atomic_fetch_add(&m->connections_failed, 1);
  }
}

// On connection close
void valk_aio_metrics_on_close(valk_aio_metrics_t* m) {
  atomic_fetch_sub(&m->connections_active, 1);
}

// On HTTP/2 stream start
void valk_aio_metrics_on_stream_start(valk_aio_metrics_t* m) {
  atomic_fetch_add(&m->streams_total, 1);
  atomic_fetch_add(&m->streams_active, 1);
}

// On stream complete
void valk_aio_metrics_on_stream_end(valk_aio_metrics_t* m, bool error,
                                     uint64_t duration_us,
                                     uint64_t bytes_sent, uint64_t bytes_recv) {
  atomic_fetch_sub(&m->streams_active, 1);
  atomic_fetch_add(&m->requests_total, 1);
  if (error) {
    atomic_fetch_add(&m->requests_errors, 1);
  }
  atomic_fetch_add(&m->request_duration_us_sum, duration_us);
  atomic_fetch_add(&m->bytes_sent_total, bytes_sent);
  atomic_fetch_add(&m->bytes_recv_total, bytes_recv);
}
```

## Implementation Plan

### Phase 1: C Metrics Collection (~150 lines)

**Files**:
- `src/aio_metrics.h` - Structures and prototypes
- `src/aio_metrics.c` - Implementation

**Functions**:
```c
void valk_aio_metrics_init(valk_aio_metrics_t* m);
void valk_aio_metrics_on_connection(valk_aio_metrics_t* m, bool success);
void valk_aio_metrics_on_close(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_start(valk_aio_metrics_t* m);
void valk_aio_metrics_on_stream_end(valk_aio_metrics_t* m, bool error,
                                     uint64_t duration_us,
                                     uint64_t bytes_sent, uint64_t bytes_recv);

// Rendering
char* valk_aio_metrics_to_json(const valk_aio_metrics_t* m, allocator_t* alloc);
char* valk_aio_metrics_to_prometheus(const valk_aio_metrics_t* m, allocator_t* alloc);
```

**JSON Format**:
```json
{
  "uptime_seconds": 3600,
  "connections": {
    "total": 1234,
    "active": 5,
    "failed": 3
  },
  "streams": {
    "total": 5678,
    "active": 2
  },
  "requests": {
    "total": 5670,
    "active": 2,
    "errors": 8,
    "rate_per_sec": 1.58,
    "avg_latency_ms": 45.2
  },
  "bytes": {
    "sent_total": 1234567,
    "recv_total": 987654,
    "sent_rate_kbps": 12.5,
    "recv_rate_kbps": 8.3
  }
}
```

**Prometheus Format**:
```
# HELP valk_uptime_seconds System uptime
# TYPE valk_uptime_seconds gauge
valk_uptime_seconds 3600

# HELP valk_connections_total Total connections established
# TYPE valk_connections_total counter
valk_connections_total 1234

# HELP valk_connections_active Current active connections
# TYPE valk_connections_active gauge
valk_connections_active 5

# HELP valk_connections_failed_total Failed connection attempts
# TYPE valk_connections_failed_total counter
valk_connections_failed_total 3

# HELP valk_streams_total Total HTTP/2 streams created
# TYPE valk_streams_total counter
valk_streams_total 5678

# HELP valk_streams_active Current active streams
# TYPE valk_streams_active gauge
valk_streams_active 2

# HELP valk_requests_total Total requests processed
# TYPE valk_requests_total counter
valk_requests_total 5670

# HELP valk_requests_errors_total Failed requests
# TYPE valk_requests_errors_total counter
valk_requests_errors_total 8

# HELP valk_request_latency_microseconds_sum Request latency sum
# TYPE valk_request_latency_microseconds_sum counter
valk_request_latency_microseconds_sum 256340000

# HELP valk_bytes_sent_total Total bytes sent
# TYPE valk_bytes_sent_total counter
valk_bytes_sent_total 1234567

# HELP valk_bytes_received_total Total bytes received
# TYPE valk_bytes_received_total counter
valk_bytes_received_total 987654
```

**Instrumentation in `aio_uv.c`**:
```c
// In valk_aio_sys_t
#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_t metrics;
#endif

// In connection accept/establish callback
#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_on_connection(&sys->metrics, status == 0);
#endif

// In stream callbacks
#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_on_stream_start(&sys->metrics);
  // ... later ...
  valk_aio_metrics_on_stream_end(&sys->metrics, is_error, duration_us, bytes_sent, bytes_recv);
#endif
```

**Test**: `test/test_aio_metrics.c`
- Init metrics struct
- Increment counters
- Verify JSON/Prometheus output

---

### Phase 2: Lisp Builtins (~50 lines)

**Add to `src/parser.c`**:
```c
// (aio/metrics sys) → qexpr with metric values
valk_lval_t* valk_builtin_aio_metrics(valk_env_t* env, valk_lval_t* args) {
  LASSERT_NUM("aio/metrics", args, 1);
  LASSERT_TYPE("aio/metrics", args, 0, LVAL_REF);

  valk_aio_sys_t* sys = valk_lval_as_aio_sys(args->cell[0]);
  LASSERT(args, sys != NULL, "Expected AIO system");

#ifdef VALK_METRICS_ENABLED
  valk_lval_t* result = valk_lval_qexpr(env->scratch_arena);
  const valk_aio_metrics_t* m = &sys->metrics;

  // Build qexpr: {:uptime 3600 :connections {:total 1234 ...} ...}
  // Use valk_lval_add to build nested structures
  // ... implementation details ...

  return result;
#else
  return valk_lval_err(env->scratch_arena, "Metrics not enabled (compile with VALK_METRICS_ENABLED)");
#endif
}

// (aio/metrics-json sys) → JSON string
valk_lval_t* valk_builtin_aio_metrics_json(valk_env_t* env, valk_lval_t* args) {
  LASSERT_NUM("aio/metrics-json", args, 1);
  LASSERT_TYPE("aio/metrics-json", args, 0, LVAL_REF);

  valk_aio_sys_t* sys = valk_lval_as_aio_sys(args->cell[0]);
  LASSERT(args, sys != NULL, "Expected AIO system");

#ifdef VALK_METRICS_ENABLED
  char* json = valk_aio_metrics_to_json(&sys->metrics, env->scratch_arena);
  return valk_lval_str_move(env->scratch_arena, json);
#else
  return valk_lval_err(env->scratch_arena, "Metrics not enabled");
#endif
}

// (aio/metrics-prometheus sys) → Prometheus text
valk_lval_t* valk_builtin_aio_metrics_prometheus(valk_env_t* env, valk_lval_t* args) {
  LASSERT_NUM("aio/metrics-prometheus", args, 1);
  LASSERT_TYPE("aio/metrics-prometheus", args, 0, LVAL_REF);

  valk_aio_sys_t* sys = valk_lval_as_aio_sys(args->cell[0]);
  LASSERT(args, sys != NULL, "Expected AIO system");

#ifdef VALK_METRICS_ENABLED
  char* prom = valk_aio_metrics_to_prometheus(&sys->metrics, env->scratch_arena);
  return valk_lval_str_move(env->scratch_arena, prom);
#else
  return valk_lval_err(env->scratch_arena, "Metrics not enabled");
#endif
}
```

**Register in `valk_env_add_builtins`**:
```c
valk_env_def_builtin(env, "aio/metrics", valk_builtin_aio_metrics);
valk_env_def_builtin(env, "aio/metrics-json", valk_builtin_aio_metrics_json);
valk_env_def_builtin(env, "aio/metrics-prometheus", valk_builtin_aio_metrics_prometheus);
```

**Test**: `test/test_aio_builtins.valk`
```lisp
(load "src/prelude.valk")

(let ((sys (aio/init)))
  (print "Metrics qexpr:" (aio/metrics sys))
  (print "Metrics JSON:" (aio/metrics-json sys))
  (print "Metrics Prometheus:" (aio/metrics-prometheus sys)))
```

---

### Phase 3: Debug Routes (~30 lines Lisp)

**File**: `src/modules/aio/debug.valk`

```lisp
;; Debug dashboard routes
;; Load with: (load "src/modules/aio/debug.valk")

(def {aio/debug-routes} (fn {sys}
  {; Routes for debug dashboard
   (/debug/              (aio/debug-serve-static "static/debug/index.html"))
   (/debug/metrics       (aio/debug-metrics-json sys))
   (/metrics             (aio/debug-metrics-prometheus sys))
  }
))

;; Serve static HTML file
(def {aio/debug-serve-static} (fn {path}
  (fn {req}
    (let ((content (slurp path)))
      {:status 200
       :headers {"Content-Type" "text/html; charset=utf-8"}
       :body content}))
))

;; Serve JSON metrics with optional filtering
(def {aio/debug-metrics-json} (fn {sys}
  (fn {req}
    (let ((json (aio/metrics-json sys))
          ;; TODO: Filter by query params (?server=0, ?client=1)
          ;; Parse req.query-params and filter JSON accordingly
          )
      {:status 200
       :headers {"Content-Type" "application/json"
                 "Access-Control-Allow-Origin" "*"}
       :body json}))
))

;; Serve Prometheus format
(def {aio/debug-metrics-prometheus} (fn {sys}
  (fn {req}
    (let ((prom (aio/metrics-prometheus sys)))
      {:status 200
       :headers {"Content-Type" "text/plain; version=0.0.4"}
       :body prom}))
))
```

**Usage Example**: `examples/debug_server.valk`
```lisp
(load "src/prelude.valk")
(load "src/modules/aio/debug.valk")

(let ((sys (aio/init))
      (routes (join (aio/debug-routes sys)
                    {(/ (fn {req} {:status 200 :body "Hello"})))}))

  (aio/server sys {:host "127.0.0.1" :port 8080 :routes routes})
  (aio/run sys))
```

**Test**:
```bash
./build/valk examples/debug_server.valk &
curl http://localhost:8080/debug/metrics
curl http://localhost:8080/metrics
```

---

### Phase 4: Dashboard HTML (~100 lines)

**File**: `static/debug/index.html`

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Valkyria AIO Debug</title>
  <style>
    body {
      font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
      margin: 0;
      padding: 20px;
      background: #1e1e1e;
      color: #d4d4d4;
    }
    .container {
      max-width: 1200px;
      margin: 0 auto;
    }
    h1 {
      color: #4fc3f7;
      border-bottom: 2px solid #4fc3f7;
      padding-bottom: 10px;
    }
    .section {
      background: #2d2d2d;
      border-radius: 8px;
      padding: 20px;
      margin: 20px 0;
      border: 1px solid #3d3d3d;
    }
    .section h2 {
      margin-top: 0;
      color: #81c784;
    }
    .metric {
      display: grid;
      grid-template-columns: 200px 1fr;
      gap: 10px;
      padding: 8px 0;
      border-bottom: 1px solid #3d3d3d;
    }
    .metric:last-child {
      border-bottom: none;
    }
    .metric-label {
      font-weight: bold;
      color: #9e9e9e;
    }
    .metric-value {
      color: #ffffff;
      font-family: 'Courier New', monospace;
    }
    .error {
      background: #d32f2f;
      color: white;
      padding: 15px;
      border-radius: 8px;
      margin: 20px 0;
    }
    .timestamp {
      text-align: right;
      color: #9e9e9e;
      font-size: 0.9em;
      margin-top: 10px;
    }
  </style>
</head>
<body>
  <div class="container">
    <h1>Valkyria AIO Debug Dashboard</h1>

    <div id="error" class="error" style="display: none;"></div>

    <div class="section">
      <h2>System</h2>
      <div id="system-metrics"></div>
    </div>

    <div class="section">
      <h2>Connections</h2>
      <div id="connection-metrics"></div>
    </div>

    <div class="section">
      <h2>Streams</h2>
      <div id="stream-metrics"></div>
    </div>

    <div class="section">
      <h2>Requests</h2>
      <div id="request-metrics"></div>
    </div>

    <div class="section">
      <h2>Bytes</h2>
      <div id="bytes-metrics"></div>
    </div>

    <div class="timestamp">Last updated: <span id="timestamp">-</span></div>
  </div>

  <script src="dashboard.js"></script>
</body>
</html>
```

**File**: `static/debug/dashboard.js`

```javascript
// Valkyria AIO Debug Dashboard
// Polls /debug/metrics and renders JSON

const POLL_INTERVAL_MS = 1500; // 1.5 seconds
const METRICS_ENDPOINT = '/debug/metrics';

function renderMetric(label, value) {
  return `
    <div class="metric">
      <div class="metric-label">${label}</div>
      <div class="metric-value">${value}</div>
    </div>
  `;
}

function renderMetrics(data) {
  // System
  document.getElementById('system-metrics').innerHTML =
    renderMetric('Uptime', `${data.uptime_seconds}s`);

  // Connections
  const conn = data.connections;
  document.getElementById('connection-metrics').innerHTML =
    renderMetric('Total', conn.total) +
    renderMetric('Active', conn.active) +
    renderMetric('Failed', conn.failed);

  // Streams
  const streams = data.streams;
  document.getElementById('stream-metrics').innerHTML =
    renderMetric('Total', streams.total) +
    renderMetric('Active', streams.active);

  // Requests
  const req = data.requests;
  document.getElementById('request-metrics').innerHTML =
    renderMetric('Total', req.total) +
    renderMetric('Active', req.active) +
    renderMetric('Errors', req.errors) +
    renderMetric('Rate', `${req.rate_per_sec.toFixed(2)} req/s`) +
    renderMetric('Avg Latency', `${req.avg_latency_ms.toFixed(2)} ms`);

  // Bytes
  const bytes = data.bytes;
  document.getElementById('bytes-metrics').innerHTML =
    renderMetric('Sent Total', formatBytes(bytes.sent_total)) +
    renderMetric('Received Total', formatBytes(bytes.recv_total)) +
    renderMetric('Send Rate', `${bytes.sent_rate_kbps.toFixed(2)} KB/s`) +
    renderMetric('Recv Rate', `${bytes.recv_rate_kbps.toFixed(2)} KB/s`);

  // Timestamp
  document.getElementById('timestamp').textContent = new Date().toLocaleTimeString();
}

function formatBytes(bytes) {
  if (bytes < 1024) return `${bytes} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(2)} KB`;
  if (bytes < 1024 * 1024 * 1024) return `${(bytes / 1024 / 1024).toFixed(2)} MB`;
  return `${(bytes / 1024 / 1024 / 1024).toFixed(2)} GB`;
}

function showError(message) {
  const errorEl = document.getElementById('error');
  errorEl.textContent = `Error: ${message}`;
  errorEl.style.display = 'block';
}

function hideError() {
  document.getElementById('error').style.display = 'none';
}

async function pollMetrics() {
  try {
    // Read endpoint from URL query param or use default
    const params = new URLSearchParams(window.location.search);
    let endpoint = METRICS_ENDPOINT;

    // Forward query params (e.g., ?server=0)
    if (params.toString()) {
      endpoint += '?' + params.toString();
    }

    const response = await fetch(endpoint);
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}: ${response.statusText}`);
    }

    const data = await response.json();
    renderMetrics(data);
    hideError();
  } catch (err) {
    showError(err.message);
    console.error('Failed to fetch metrics:', err);
  }
}

// Start polling
pollMetrics();
setInterval(pollMetrics, POLL_INTERVAL_MS);
```

**Test**:
```bash
# Start server
./build/valk examples/debug_server.valk &

# Open browser
xdg-open http://localhost:8080/debug/

# Watch metrics update every 1.5 seconds
```

---

## Build System

**Update `Makefile`**:
```makefile
# Add compile flag for metrics
CFLAGS += -DVALK_METRICS_ENABLED

# Install static files
install: build
	mkdir -p $(PREFIX)/share/valkyria/static/debug
	cp static/debug/*.html static/debug/*.js $(PREFIX)/share/valkyria/static/debug/
```

**Disable metrics** (for production):
```makefile
# Remove or comment out
# CFLAGS += -DVALK_METRICS_ENABLED
```

---

## Testing Strategy

### Unit Tests (C)
- `test/test_aio_metrics.c`
  - Init metrics struct
  - Increment/decrement counters
  - Verify atomic operations
  - Validate JSON output format
  - Validate Prometheus format

### Integration Tests (Lisp)
- `test/test_aio_debug.valk`
  - Start debug server
  - Fetch `/debug/metrics`
  - Parse JSON response
  - Verify metric values
  - Test query param filtering

### Manual Testing
```bash
# Start demo server with debug routes
./build/valk examples/debug_server.valk

# Generate load
for i in {1..100}; do curl http://localhost:8080/ & done

# View dashboard
xdg-open http://localhost:8080/debug/

# Check Prometheus endpoint
curl http://localhost:8080/metrics
```

---

## Future Extensions

### Query Parameter Filtering
Add filtering to `aio/debug-metrics-json`:
```lisp
(def {aio/debug-filter-metrics} (fn {json query-params}
  ;; If query-params contains {:server "0"}, filter to server 0
  ;; If query-params contains {:client "1"}, filter to client 1
  ;; Return filtered JSON subset
))
```

### Per-Route Metrics
Add route-level breakdown:
```c
typedef struct {
  const char* route_pattern;  // "/api/users"
  uint64_t requests_total;
  uint64_t requests_errors;
  uint64_t duration_us_sum;
} valk_route_metrics_t;
```

### Histograms
Replace `duration_us_sum` with buckets:
```c
uint64_t latency_buckets[10];  // <1ms, <5ms, <10ms, <50ms, ...
```

### Custom Metrics
Allow user-defined metrics:
```lisp
(aio/metric-counter sys "my_custom_metric" 1)  ;; Increment by 1
(aio/metric-gauge sys "queue_depth" 42)        ;; Set to 42
```

---

## Design Rationale

### Why no SSE?
- Polling is simpler (no timer complexity)
- 1-2s updates are fine for debug dashboards
- Browser handles reconnection automatically
- Easier to debug (just curl the endpoint)

### Why no auth?
- Security is a reverse proxy concern (nginx, Caddy, etc.)
- Keeps implementation light
- Production setups already use proxies
- No secrets to manage

### Why Prometheus format?
- Industry standard for metrics
- Works with Grafana, Prometheus, etc.
- Simple text format (no external deps)
- Makes Valkyria metrics portable

### Why compile-time guards?
- Metrics have overhead (atomic ops, memory)
- Production builds can disable completely
- Debug builds enable by default
- No runtime flag checking on hot paths

### Why data-driven frontend?
- Same HTML serves all routes
- Backend controls what data to show
- Easy to extend with new filters
- No frontend redeployment needed

---

## Implementation Checklist

- [ ] Phase 1: C metrics collection
  - [ ] `src/aio_metrics.h` - structures
  - [ ] `src/aio_metrics.c` - implementation
  - [ ] Instrumentation in `src/aio_uv.c`
  - [ ] `test/test_aio_metrics.c` - unit tests
  - [ ] JSON rendering
  - [ ] Prometheus rendering

- [ ] Phase 2: Lisp builtins
  - [ ] `(aio/metrics sys)` - qexpr
  - [ ] `(aio/metrics-json sys)` - JSON string
  - [ ] `(aio/metrics-prometheus sys)` - Prometheus text
  - [ ] `test/test_aio_builtins.valk` - integration tests

- [ ] Phase 3: Debug routes
  - [ ] `src/modules/aio/debug.valk` - route handlers
  - [ ] Static file serving
  - [ ] JSON endpoint with filtering
  - [ ] Prometheus endpoint
  - [ ] `examples/debug_server.valk` - demo

- [ ] Phase 4: Dashboard
  - [ ] `static/debug/index.html` - UI
  - [ ] `static/debug/dashboard.js` - polling logic
  - [ ] Query param filtering support
  - [ ] Manual testing

- [ ] Documentation
  - [ ] Update `ROADMAP.md` with metrics feature
  - [ ] Add debug dashboard section to `README.md`
  - [ ] Document compile flags in `CONTRIBUTING.md`

---

## Estimated Effort

- **Phase 1**: 3-4 hours (C metrics + instrumentation)
- **Phase 2**: 1-2 hours (Lisp builtins)
- **Phase 3**: 1-2 hours (Debug routes)
- **Phase 4**: 2-3 hours (Dashboard HTML/JS)

**Total**: 7-11 hours (1-2 days)

---

## References

- [RED Method](https://www.weave.works/blog/the-red-method-key-metrics-for-microservices-architecture/)
- [USE Method](http://www.brendangregg.com/usemethod.html)
- [Prometheus Exposition Formats](https://prometheus.io/docs/instrumenting/exposition_formats/)
- [OpenTelemetry Metrics](https://opentelemetry.io/docs/concepts/signals/metrics/)
