# Prometheus Metrics Implementation Plan

## Executive Summary

This plan outlines the work required to ensure all metrics needed by the Valkyria Dashboard (per `DASHBOARD_DESIGN.md`) are properly collected and exposed through the `/metrics` Prometheus endpoint.

**Current State:** ✅ **IMPLEMENTED** - All phases complete.

The codebase now has a comprehensive metrics infrastructure with:
- `/metrics` endpoint serving Prometheus text format (v0.0.4)
- `/debug/metrics` endpoint serving combined JSON
- Core metrics framework with counters, gauges, histograms
- Lock-free atomic updates for thread safety
- Four metrics sources: AIO HTTP, AIO System Stats, Modular (per-server/client), VM

---

## Implementation Status

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | AIO System Stats Prometheus export | ✅ Complete |
| 2 | Connection State Tracking | ✅ Complete |
| 3 | HTTP Client Metrics | ✅ Complete |
| 4 | Protocol Labels for Server Metrics | ✅ Complete |
| 5 | Heap Utilization Gauge | ✅ Complete |
| 6 | Merge System Stats into Prometheus Output | ✅ Complete |

---

## 1. Current Infrastructure Summary

### 1.1 Existing Endpoints

| Endpoint | Format | Content-Type | Source |
|----------|--------|--------------|--------|
| `/metrics` | Prometheus | `text/plain; version=0.0.4` | `debug.valk:55` |
| `/debug/metrics` | JSON | `application/json` | `debug.valk:54` |
| `/debug/` | HTML | `text/html` | `debug.valk:53` |

### 1.2 Existing Metrics by Category

#### VM/GC Metrics (Complete)
- `valk_gc_cycles_total` - GC collection cycles
- `valk_gc_pause_seconds_total` - Cumulative pause time
- `valk_gc_pause_seconds_max` - Maximum single pause
- `valk_gc_reclaimed_bytes_total` - Memory reclaimed
- `valk_gc_heap_used_bytes` - Current heap usage
- `valk_gc_heap_total_bytes` - Total heap capacity

#### Interpreter Metrics (Complete)
- `valk_eval_total` - Expression evaluations
- `valk_function_calls_total` - User function calls
- `valk_builtin_calls_total` - Builtin function calls
- `valk_stack_depth_max` - Peak stack depth
- `valk_closures_created_total` - Closures created
- `valk_env_lookups_total` - Environment lookups

#### Event Loop Metrics (Complete)
- `valk_loop_iterations_total` - Event loop iterations
- `valk_events_processed_total` - Events processed
- `valk_loop_idle_seconds_total` - Idle time

#### AIO HTTP Metrics (Partially Complete)
- `valk_aio_connections_total/active/failed` - Connection tracking
- `valk_aio_streams_total/active` - Stream tracking
- `valk_aio_requests_total/active/errors` - Request tracking
- `valk_aio_bytes_sent/recv_total` - Byte counters

#### Per-Server Metrics (via modular metrics)
- `http_requests_total{server,port,status}` - Per-server request counts
- `http_connections_active{server,port}` - Active connections gauge
- `http_request_duration_seconds{server,port}` - Latency histogram
- `http_bytes_sent_total{server,port}` - Bytes sent
- `http_bytes_recv_total{server,port}` - Bytes received

---

## 2. Dashboard Requirements vs. Current State

### 2.1 Health Overview Panel (Section 4.3)

| Metric | Dashboard Needs | Current State | Gap |
|--------|-----------------|---------------|-----|
| Active Connections | Total across all servers | `valk_aio_connections_active` | **OK** |
| Request Rate | requests/sec | Calculated in JSON only | **Need Prometheus rate** |
| Error Rate | percentage | `requests_errors / requests_total` | **Need derived metric** |
| P99 Latency | milliseconds | Histogram exists | **Need summary or calc** |

### 2.2 VM Section (Section 4.5)

| Metric | Dashboard Needs | Current State | Gap |
|--------|-----------------|---------------|-----|
| GC Cycles | Count | `valk_gc_cycles_total` | **OK** |
| GC Max Pause | ms | `valk_gc_pause_seconds_max` | **OK** |
| GC Avg Pause | ms | Calculated | **OK** (use sum/count) |
| Heap Used | bytes | `valk_gc_heap_used_bytes` | **OK** |
| Heap Total | bytes | `valk_gc_heap_total_bytes` | **OK** |
| Heap Utilization | percentage | Not exposed | **Add as gauge** |
| Reclaimed | bytes | `valk_gc_reclaimed_bytes_total` | **OK** |
| Evals Total | count | `valk_eval_total` | **OK** |
| Function Calls | count | `valk_function_calls_total` | **OK** |
| Builtin Calls | count | `valk_builtin_calls_total` | **OK** |
| Stack Depth Max | count | `valk_stack_depth_max` | **OK** |
| Closures Created | count | `valk_closures_created_total` | **OK** |
| Env Lookups | count | `valk_env_lookups_total` | **OK** |

### 2.3 AIO Systems Section (Section 4.5)

| Metric | Dashboard Needs | Current State | Gap |
|--------|-----------------|---------------|-----|
| Event Loop Iterations | count | `valk_loop_iterations_total` | **OK** |
| Events Processed | count | `valk_events_processed_total` | **OK** |
| Handles Active | count | In system stats JSON only | **Add to Prometheus** |
| Idle Time | us | `valk_loop_idle_seconds_total` | **OK** |
| Connection Pool Total | count | `arenas_total` in JSON | **Add to Prometheus** |
| Connection Pool Active | count | `arenas_used` in JSON | **Add to Prometheus** |
| Connection Pool Idle | count | Not tracked | **Add calculation** |
| Connection Pool Closing | count | Not tracked | **Add tracking** |
| Arena Pool Used/Total | count | In JSON only | **Add to Prometheus** |
| TCP Buffer Used/Total | count | In JSON only | **Add to Prometheus** |

### 2.4 HTTP Servers Section (Section 4.6)

| Metric | Dashboard Needs | Current State | Gap |
|--------|-----------------|---------------|-----|
| Server Address:Port | label | `{server,port}` labels | **OK** |
| Protocol Label | e.g., HTTPS | Not tracked | **Add label** |
| Active Connections | per-server | `http_connections_active{server,port}` | **OK** |
| Request Rate | per-server req/s | Histogram count / time | **OK** (calculate) |
| Response 2xx Count | per-server | `http_requests_total{status="2xx"}` | **OK** |
| Response 4xx Count | per-server | `http_requests_total{status="4xx"}` | **OK** |
| Response 5xx Count | per-server | `http_requests_total{status="5xx"}` | **OK** |
| Latency P50 | per-server | From histogram | **OK** (Prometheus calc) |
| Latency P95 | per-server | From histogram | **OK** (Prometheus calc) |
| Latency P99 | per-server | From histogram | **OK** (Prometheus calc) |
| Latency Histogram Buckets | 10 buckets | 12 buckets exist | **OK** |
| Bytes In/Out | per-server | `http_bytes_sent/recv_total` | **OK** |
| Throughput Sparkline | time series | Client-side calculation | **OK** |

### 2.5 HTTP Clients Section (Section 4.6)

| Metric | Dashboard Needs | Current State | Gap |
|--------|-----------------|---------------|-----|
| Client Name | label | Not tracked | **Add client labels** |
| Client Type | label | Not tracked | **Add type label** |
| Status | healthy/degraded | Not tracked | **Add health check** |
| Connections Active | per-client | Not tracked | **Add tracking** |
| Pool Size | per-client | Not tracked | **Add tracking** |
| Operations Total | per-client | Not tracked | **Add tracking** |
| Operations Rate | per-client | Not tracked | **Add tracking** |
| Errors | per-client | Not tracked | **Add tracking** |
| Latency Histogram | per-client | Not tracked | **Add histogram** |

---

## 3. Implementation Tasks

### Phase 1: Complete AIO System Stats in Prometheus Format

**File:** `src/aio_metrics.c`

Add Prometheus export for system stats that are currently JSON-only:

```c
// Add to valk_aio_system_stats_to_prometheus() (new function)
valk_aio_servers_count          # gauge
valk_aio_clients_count          # gauge
valk_aio_handles_count          # gauge
valk_aio_arenas_used            # gauge
valk_aio_arenas_total           # gauge
valk_aio_tcp_buffers_used       # gauge
valk_aio_tcp_buffers_total      # gauge
valk_aio_queue_depth            # gauge
valk_aio_pending_requests       # gauge
valk_aio_pending_responses      # gauge
valk_aio_arena_pool_overflow    # counter
valk_aio_tcp_buffer_overflow    # counter
valk_aio_connections_rejected_load # counter
```

**Estimated Effort:** 2-3 hours

### Phase 2: Add Connection State Tracking

**Files:** `src/aio_uv.c`, `src/aio_metrics.h`

Track connection states for the dashboard's connection pool visualization:

1. Add connection state enum:
   ```c
   typedef enum {
     CONN_STATE_CONNECTING,
     CONN_STATE_ACTIVE,
     CONN_STATE_IDLE,
     CONN_STATE_CLOSING
   } valk_conn_state_e;
   ```

2. Add gauges for each state:
   ```c
   valk_aio_connections_connecting  # gauge
   valk_aio_connections_idle        # gauge (new)
   valk_aio_connections_closing     # gauge (new)
   ```

3. Instrument state transitions in connection lifecycle callbacks

**Estimated Effort:** 4-6 hours

### Phase 3: Add HTTP Client Metrics

**Files:** `src/aio_uv.c`, `src/aio_metrics.h`

The dashboard design shows HTTP clients (e.g., postgres-primary, redis-cache) with their own metrics. Currently only server metrics are tracked.

1. Add `valk_http_client_metrics_t` structure:
   ```c
   typedef struct {
     const char* name;        // e.g., "postgres-primary"
     const char* type;        // e.g., "Database"
     _Atomic uint64_t connections_active;
     uint64_t pool_size;
     _Atomic uint64_t operations_total;
     _Atomic uint64_t errors_total;
     valk_histogram_t* latency;  // Reference to registered histogram
   } valk_http_client_metrics_t;
   ```

2. Register client-labeled metrics:
   ```c
   http_client_connections_active{client="postgres-primary",type="Database"}
   http_client_operations_total{client="postgres-primary",type="Database"}
   http_client_errors_total{client="postgres-primary",type="Database"}
   http_client_request_duration_seconds{client="...",type="..."}  # histogram
   ```

3. Add Lisp builtins to create/update client metrics:
   ```lisp
   (http-client/register "postgres-primary" "Database" 20)  ; name, type, pool_size
   (http-client/on-request client-handle duration-us error?)
   ```

**Estimated Effort:** 8-12 hours

### Phase 4: Add Protocol Labels to Server Metrics

**File:** `src/aio_uv.c`

Add `protocol` label to distinguish HTTP vs HTTPS servers:

```c
http_requests_total{server="0.0.0.0",port="8443",protocol="https",status="2xx"}
http_connections_active{server="0.0.0.0",port="8443",protocol="https"}
```

This requires:
1. Pass TLS configuration flag through to metric registration
2. Add "protocol" to the labels when registering server metrics

**Estimated Effort:** 1-2 hours

### Phase 5: Add Heap Utilization Gauge

**File:** `src/aio_metrics.c`

Add pre-calculated utilization gauge for simpler Prometheus queries:

```c
valk_gc_heap_utilization_ratio  # gauge (0.0-1.0)
```

Calculate in `valk_vm_metrics_to_prometheus()`:
```c
double util = (double)m->gc_heap_used / (double)m->gc_heap_total;
```

**Estimated Effort:** 30 minutes

### Phase 6: Merge System Stats into Prometheus Output

**Files:** `src/aio_metrics.c`, `src/modules/aio/debug.valk`

Currently the Prometheus output from `aio/metrics-prometheus` only includes HTTP metrics, not system stats. Need to:

1. Create `valk_aio_system_stats_to_prometheus()` function
2. Create new builtin `aio/system-stats-prometheus`
3. Update `aio/debug-merge-metrics-prometheus` to include it:
   ```lisp
   (fun {aio/debug-merge-metrics-prometheus sys}
     {
       (= {aio-prom} (aio/metrics-prometheus sys))
       (= {sys-prom} (aio/system-stats-prometheus sys))  ; NEW
       (= {modular-prom} (metrics/prometheus))
       (= {vm-prom} (vm/metrics-prometheus))
       (str aio-prom "\n" sys-prom "\n# Modular metrics\n" modular-prom "\n# VM metrics\n" vm-prom)
     })
   ```

**Estimated Effort:** 2-3 hours

---

## 4. New Prometheus Metrics Summary

After implementation, the `/metrics` endpoint will expose:

### VM/GC (17 metrics)
```
valk_gc_cycles_total
valk_gc_pause_seconds_total
valk_gc_pause_seconds_max
valk_gc_reclaimed_bytes_total
valk_gc_heap_used_bytes
valk_gc_heap_total_bytes
valk_gc_heap_utilization_ratio          # NEW
valk_eval_total
valk_function_calls_total
valk_builtin_calls_total
valk_stack_depth_max
valk_closures_created_total
valk_env_lookups_total
valk_loop_iterations_total
valk_events_processed_total
valk_loop_idle_seconds_total
```

### AIO System (13 metrics) - NEW
```
valk_aio_servers_count
valk_aio_clients_count
valk_aio_handles_count
valk_aio_arenas_used
valk_aio_arenas_total
valk_aio_tcp_buffers_used
valk_aio_tcp_buffers_total
valk_aio_queue_depth
valk_aio_pending_requests
valk_aio_pending_responses
valk_aio_arena_pool_overflow_total
valk_aio_tcp_buffer_overflow_total
valk_aio_connections_rejected_load_total
```

### AIO HTTP (12 metrics)
```
valk_aio_uptime_seconds
valk_aio_connections_total
valk_aio_connections_active
valk_aio_connections_failed
valk_aio_connections_idle               # NEW
valk_aio_connections_closing            # NEW
valk_aio_streams_total
valk_aio_streams_active
valk_aio_requests_total
valk_aio_requests_active
valk_aio_requests_errors
valk_aio_bytes_sent_total
valk_aio_bytes_recv_total
```

### Per-Server (labeled, 6 metric families)
```
http_requests_total{server,port,protocol,status}
http_connections_active{server,port,protocol}
http_request_duration_seconds{server,port,protocol}  # histogram
http_bytes_sent_total{server,port,protocol}
http_bytes_recv_total{server,port,protocol}
http_overload_responses_total{server,port,protocol}
```

### Per-Client (labeled, 4 metric families) - NEW
```
http_client_connections_active{client,type}
http_client_operations_total{client,type}
http_client_errors_total{client,type}
http_client_request_duration_seconds{client,type}  # histogram
```

---

## 5. Implementation Order

| Phase | Description | Priority | Effort | Dependencies |
|-------|-------------|----------|--------|--------------|
| 1 | AIO System Stats Prometheus | High | 2-3h | None |
| 5 | Heap Utilization Gauge | High | 30m | None |
| 6 | Merge System Stats | High | 2-3h | Phase 1 |
| 4 | Protocol Labels | Medium | 1-2h | None |
| 2 | Connection State Tracking | Medium | 4-6h | None |
| 3 | HTTP Client Metrics | Low | 8-12h | Phase 2 |

**Recommended Order:** 1 → 5 → 6 → 4 → 2 → 3

**Total Estimated Effort:** 18-27 hours

---

## 6. Testing Strategy

### Unit Tests
- Add tests to `test/test_aio_metrics.c` for new Prometheus output functions
- Verify metric format compliance with Prometheus text format spec

### Integration Tests
- Add tests to `test/test_aio_debug.valk`:
  ```lisp
  (test/define "prometheus-includes-system-stats"
    {do
      (= {prom} (aio/debug-merge-metrics-prometheus mock-sys))
      (test/assert (str/contains? prom "valk_aio_arenas_used"))
      (test/assert (str/contains? prom "valk_aio_tcp_buffers_total"))
      true
    })
  ```

### End-to-End Tests
- Verify Prometheus can scrape `/metrics` endpoint
- Confirm Grafana can visualize all metrics
- Test dashboard displays all required visualizations

---

## 7. Prometheus Scrape Configuration

Example `prometheus.yml` for scraping Valkyria:

```yaml
scrape_configs:
  - job_name: 'valkyria'
    static_configs:
      - targets: ['localhost:8443']
    metrics_path: '/metrics'
    scheme: 'https'
    tls_config:
      insecure_skip_verify: true  # For self-signed certs
```

---

## 8. Grafana Dashboard Queries

Example PromQL queries for dashboard panels:

```promql
# Request Rate (req/s)
rate(http_requests_total{status="2xx"}[1m])

# Error Rate (%)
100 * rate(http_requests_total{status=~"4xx|5xx"}[1m])
    / rate(http_requests_total[1m])

# P99 Latency (ms)
histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m])) * 1000

# Heap Utilization (%)
valk_gc_heap_utilization_ratio * 100

# Connection Pool Utilization (%)
100 * valk_aio_arenas_used / valk_aio_arenas_total

# GC Pause Avg (ms)
(rate(valk_gc_pause_seconds_total[5m]) / rate(valk_gc_cycles_total[5m])) * 1000
```

---

## 9. Files to Modify

| File | Changes |
|------|---------|
| `src/aio_metrics.h` | Add connection state enum, client metrics struct |
| `src/aio_metrics.c` | Add `valk_aio_system_stats_to_prometheus()`, client metrics |
| `src/aio_uv.c` | Add protocol labels, connection state tracking, client instrumentation |
| `src/parser.c` | Add new builtins for system stats prometheus, client metrics |
| `src/modules/aio/debug.valk` | Update merge function to include system stats |
| `test/test_aio_metrics.c` | Add tests for new Prometheus output |
| `test/test_aio_debug.valk` | Add integration tests |

---

## 10. Acceptance Criteria

1. `/metrics` endpoint returns all metrics listed in Section 4
2. All metrics follow Prometheus naming conventions (`snake_case`, `_total` suffix for counters)
3. All metrics include proper HELP and TYPE annotations
4. Prometheus can successfully scrape the endpoint
5. Dashboard HTML can render all visualizations from metric data
6. No performance regression (metrics updates remain lock-free)
7. All tests pass

---

## Appendix A: Prometheus Naming Conventions

- Counter names end with `_total`
- Histogram names end with `_seconds` or `_bytes` (base unit)
- Gauges use descriptive names without suffix
- Labels use lowercase with underscores
- Metric names use `valk_` prefix for VM metrics, `http_` for HTTP metrics

---

## Appendix B: Complete Dashboard Metric Cross-Reference

This appendix maps every metric displayed in `static/dashboard-demo.html` to the required Prometheus metric.

### B.1 Header Section (lines 1132-1152)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| Global Status | "All Systems Healthy" | Derived from error rates | **Derive in JS** |
| Uptime | "2d 14h 32m" | `valk_aio_uptime_seconds` | **OK** |
| Last Update | timestamp | Client-side clock | **N/A** |

### B.2 Health Overview Panel (lines 1164-1191)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| Request Rate | "1,552/s" | `rate(http_requests_total[1m])` | **OK** (PromQL) |
| Error Rate | "0.28%" | `rate(http_requests_total{status=~"4xx\|5xx"}[1m]) / rate(http_requests_total[1m])` | **OK** (PromQL) |
| P99 Latency | "42ms" | `histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))` | **OK** (PromQL) |
| Heap Usage | "67%" | `valk_gc_heap_utilization_ratio` | **Add gauge** |
| Heap Usage subtitle | "128 MB / 192 MB" | `valk_gc_heap_used_bytes`, `valk_gc_heap_total_bytes` | **OK** |

### B.3 VM Section - Garbage Collector (lines 1207-1246)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| GC Cycles badge | "142 cycles" | `valk_gc_cycles_total` | **OK** |
| GC Timeline events | Visual bars | Need per-event data | **Not feasible** (streaming) |
| Cycles stat | "142" | `valk_gc_cycles_total` | **OK** |
| Max Pause | "2.4ms" | `valk_gc_pause_seconds_max * 1000` | **OK** |
| Avg Pause | "0.8ms" | `valk_gc_pause_seconds_total / valk_gc_cycles_total * 1000` | **OK** (derive) |
| Reclaimed | "24MB" | `valk_gc_reclaimed_bytes_total` | **OK** |

**Note:** The GC Timeline showing individual GC events with their pause times cannot be done via Prometheus (which only exposes aggregates). This would require either:
- A separate `/debug/gc-events` endpoint returning recent GC events as JSON
- Or client-side simulation (as demo does)

### B.4 VM Section - Heap Memory (lines 1249-1293)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| Gauge percentage | "67%" | `valk_gc_heap_utilization_ratio * 100` | **Add gauge** |
| Gauge trend arrow | "→" (stable) | Derived from rate of change | **Derive in JS** |
| Used | "128 MB" | `valk_gc_heap_used_bytes` | **OK** |
| Total | "192 MB" | `valk_gc_heap_total_bytes` | **OK** |
| Peak | "156 MB" | Not tracked | **Add: valk_gc_heap_peak_bytes** |
| GC Trigger | "160 MB" | Not tracked | **Add: valk_gc_trigger_bytes** |

### B.5 VM Section - Interpreter (lines 1296-1331)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| Evals (total) | "1.2M" | `valk_eval_total` | **OK** |
| Fn Calls (total) | "847K" | `valk_function_calls_total` | **OK** |
| Builtins (total) | "156K" | `valk_builtin_calls_total` | **OK** |
| Max Stack Depth | "42" | `valk_stack_depth_max` | **OK** |
| Closures Created | "12,847" | `valk_closures_created_total` | **OK** |
| Env Lookups | "2.4M" | `valk_env_lookups_total` | **OK** |

### B.6 AIO Systems Section (lines 1348-1473)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| Loop Iters | "847K" | `valk_loop_iterations_total` | **OK** |
| Events | "1.2M" | `valk_events_processed_total` | **OK** |
| Handles | "12" | `valk_aio_handles_count` | **Add to Prometheus** |
| Connection Pool total | "500" | `valk_aio_connection_pool_total` | **Add gauge** |
| Connection Pool used | "397" | `valk_aio_connection_pool_used` | **Add gauge** |
| Active connections | "247" | `valk_aio_connections_active` | **OK** |
| Idle connections | "142" | `valk_aio_connections_idle` | **Add gauge** |
| Closing connections | "8" | `valk_aio_connections_closing` | **Add gauge** |
| Stream Arenas used | "24" | `valk_aio_arenas_used` | **Add to Prometheus** |
| Stream Arenas total | "32" | `valk_aio_arenas_total` | **Add to Prometheus** |
| TCP Buffers used | "156" | `valk_aio_tcp_buffers_used` | **Add to Prometheus** |
| TCP Buffers total | "256" | `valk_aio_tcp_buffers_total` | **Add to Prometheus** |

**Note:** Dashboard shows 2 AIO systems (Main, Background). Current implementation has single system stats. Need to consider:
- Adding `aio_system` label to metrics: `valk_aio_arenas_used{system="main"}`
- Or single-system metrics if only one event loop exists

### B.7 HTTP Servers Section (lines 1491-1761)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| Server status dot | green/yellow/red | Derived from error rate/latency | **Derive in JS** |
| Server address | "0.0.0.0:8443" | `{server="0.0.0.0",port="8443"}` labels | **OK** |
| Protocol label | "HTTPS" | `{protocol="https"}` label | **Add label** |
| Active Conns | "247" | `http_connections_active{server,port}` | **OK** |
| Request rate | "1.2K/s" | `rate(http_requests_total{server,port}[1m])` | **OK** (PromQL) |
| 2xx count | "45,231" | `http_requests_total{status="2xx"}` | **OK** |
| 4xx count | "127" | `http_requests_total{status="4xx"}` | **OK** |
| 5xx count | "3" | `http_requests_total{status="5xx"}` | **OK** |
| Status bar segments | proportional widths | Derived from counts | **Derive in JS** |
| Histogram bars | 10 bars | `http_request_duration_seconds_bucket` | **OK** |
| P50 latency | "4ms" | `histogram_quantile(0.50, ...)` | **OK** (PromQL) |
| P95 latency | "18ms" | `histogram_quantile(0.95, ...)` | **OK** (PromQL) |
| P99 latency | "42ms" | `histogram_quantile(0.99, ...)` | **OK** (PromQL) |
| Throughput sparkline | SVG chart | Time series of byte rates | **Store in JS** |
| Bytes In | "2.1 MB/s" | `rate(http_bytes_recv_total[1m])` | **OK** (PromQL) |
| Bytes Out | "16.4 MB/s" | `rate(http_bytes_sent_total[1m])` | **OK** (PromQL) |

### B.8 HTTP Clients Section (lines 1777-1990)

| Dashboard Element | Display Value | Prometheus Metric | Status |
|-------------------|---------------|-------------------|--------|
| Client status dot | green/yellow/red | Derived from errors/latency | **Derive in JS** |
| Client name | "postgres-primary" | `{client="postgres-primary"}` label | **Add** |
| Client type | "Database" | `{type="Database"}` label | **Add** |
| Active Conns | "12" | `http_client_connections_active{client}` | **Add** |
| Queries/Ops (total) | "4.2K" | `http_client_operations_total{client}` | **Add** |
| Errors | "0" | `http_client_errors_total{client}` | **Add** |
| Hit Rate (Redis) | "94.2%" | `http_client_cache_hits / http_client_cache_total` | **Add** (optional) |
| Histogram bars | 10 bars | `http_client_request_duration_seconds_bucket{client}` | **Add** |
| P50/P95/P99 latency | "1.2ms/4.8ms/12ms" | `histogram_quantile(0.xx, ...)` | **Add** (PromQL) |
| Rate sparkline | SVG chart | Time series | **Store in JS** |
| Current rate | "142/s" | `rate(http_client_operations_total[1m])` | **Add** (PromQL) |
| Peak rate | "287/s" | `max_over_time(rate(...)[5m])` | **Derive** (PromQL) |
| Retries | "3%" | `http_client_retries_total / http_client_operations_total` | **Add** (optional) |

---

## Appendix C: Additional Metrics Identified

Based on the dashboard cross-reference, these additional metrics should be added:

### C.1 GC/Heap Metrics (Phase 5 expansion)

```
valk_gc_heap_peak_bytes         # gauge - Maximum heap size ever reached
valk_gc_trigger_bytes           # gauge - GC trigger threshold
```

### C.2 Connection Pool Metrics (Phase 2 expansion)

The dashboard shows a detailed connection pool with distinct states. Update Phase 2:

```
valk_aio_connection_pool_total       # gauge - Total pool capacity
valk_aio_connection_pool_used        # gauge - Total used (active + idle + closing)
valk_aio_connections_connecting      # gauge - Connections being established
valk_aio_connections_active          # gauge - Active request processing (exists)
valk_aio_connections_idle            # gauge - Idle, awaiting reuse
valk_aio_connections_closing         # gauge - Graceful shutdown in progress
```

### C.3 Multi-AIO System Support (New Phase)

If the runtime supports multiple event loops, add `system` label:

```
valk_aio_arenas_used{system="main"}
valk_aio_arenas_total{system="main"}
valk_aio_arenas_used{system="background"}
...
```

### C.4 HTTP Client Metrics (Phase 3 expansion)

Add cache-specific metrics for cache clients:

```
http_client_cache_hits_total{client}      # counter
http_client_cache_misses_total{client}    # counter
http_client_retries_total{client}         # counter
http_client_pool_size{client}             # gauge
```

---

## Appendix D: Metrics NOT Feasible via Prometheus

Some dashboard visualizations require data that Prometheus cannot provide:

1. **GC Timeline with individual events** - Prometheus aggregates; would need separate JSON endpoint
2. **Sparkline historical data** - Client must maintain time-series buffer; Prometheus provides rates
3. **Real-time status derivation** - Client calculates from thresholds

These are handled by:
- Client-side time-series buffers (sparklines store last N data points)
- Threshold-based status calculation in JavaScript
- For GC events: either mock data or optional `/debug/gc-events` endpoint

---

## Appendix E: Updated Implementation Phases

Based on complete cross-reference, updated phase list:

| Phase | Description | Metrics Added | Effort |
|-------|-------------|---------------|--------|
| 1 | AIO System Stats Prometheus | 13 metrics | 2-3h |
| 2 | Connection State Tracking | 4 connection state gauges | 4-6h |
| 3 | HTTP Client Metrics | 8+ client metrics | 8-12h |
| 4 | Protocol Labels | 1 label addition | 1-2h |
| 5 | Heap/GC Gauges | 3 gauges (util, peak, trigger) | 1h |
| 6 | Merge System Stats | Integration | 2-3h |
| 7 | Multi-AIO Labels (optional) | Labels for multi-loop | 2-4h |

**Revised Total:** 20-31 hours

---

## Appendix F: Implementation Details (Completed)

This appendix documents the actual implementation of all phases.

### F.1 Metrics Hierarchy

Metrics are organized at the correct hierarchical levels:

```
VM (process-wide)
├── valk_gc_* (GC metrics)
├── valk_gc_heap_utilization_ratio (NEW - Phase 5)
├── valk_eval_total, valk_function_calls_total, etc.
└── valk_loop_iterations_total, valk_events_processed_total

AIO System (subsystem-wide)
├── valk_aio_servers_count, valk_aio_clients_count (NEW - Phase 1)
├── valk_aio_arenas_*, valk_aio_tcp_buffers_* (NEW - Phase 1)
├── valk_aio_connections_* (active, idle, closing - Phase 2)
└── valk_aio_*_overflow_total (NEW - Phase 1)

Per-Server (labeled with {server,port,protocol})
├── http_requests_total{server,port,protocol,status}
├── http_connections_active{server,port,protocol}
├── http_request_duration_seconds{server,port,protocol} (histogram)
├── http_bytes_sent_total{server,port,protocol}
├── http_bytes_recv_total{server,port,protocol}
└── http_overload_responses_total{server,port,protocol}
    └── protocol label added in Phase 4 (http/https)

Per-Client (labeled with {client,type})
├── http_client_connections_active{client,type} (NEW - Phase 3)
├── http_client_pool_size{client,type} (NEW - Phase 3)
├── http_client_operations_total{client,type} (NEW - Phase 3)
├── http_client_errors_total{client,type} (NEW - Phase 3)
├── http_client_retries_total{client,type} (NEW - Phase 3)
├── http_client_cache_hits_total{client,type} (NEW - Phase 3)
├── http_client_cache_misses_total{client,type} (NEW - Phase 3)
└── http_client_latency_seconds_avg{client,type} (NEW - Phase 3)
```

### F.2 Files Modified

| File | Changes |
|------|---------|
| `src/aio_metrics.h` | Added connection state fields, HTTP client structs, function declarations |
| `src/aio_metrics.c` | Implemented `valk_aio_system_stats_to_prometheus()`, connection state helpers, HTTP client metrics, heap utilization ratio |
| `src/aio_uv.c` | Added protocol label to server metrics, HTTP clients registry, connection state instrumentation hooks |
| `src/aio.h` | Added `valk_aio_get_http_clients_registry()` declaration |
| `src/parser.c` | Added builtins: `aio/system-stats-prometheus`, `http-client/register`, `http-client/on-operation`, `http-client/on-cache`, `http-client/metrics-prometheus` |
| `src/modules/aio/debug.valk` | Updated `aio/debug-merge-metrics-prometheus` to include system stats |

### F.3 New Lisp Builtins

#### System Stats
```lisp
(aio/system-stats-prometheus sys)  ; Returns Prometheus text for AIO system stats
```

#### HTTP Client Metrics
```lisp
(http-client/register sys name type pool-size)        ; Register client, returns ID
(http-client/on-operation sys id duration-us err? retry?)  ; Record operation
(http-client/on-cache sys id hit?)                    ; Record cache hit/miss
(http-client/metrics-prometheus sys)                  ; Export client metrics
```

### F.4 Prometheus Endpoint Structure

The `/metrics` endpoint now returns metrics from four sources, merged by `aio/debug-merge-metrics-prometheus`:

```
# AIO HTTP metrics (valk_aio_*)
valk_aio_uptime_seconds ...
valk_aio_connections_total ...
valk_aio_connections_active ...
valk_aio_connections_idle ...        # NEW
valk_aio_connections_closing ...     # NEW
...

# AIO system stats                   # NEW SECTION
valk_aio_servers_count ...
valk_aio_clients_count ...
valk_aio_arenas_used ...
valk_aio_arenas_total ...
valk_aio_tcp_buffers_used ...
valk_aio_tcp_buffers_total ...
...

# Modular metrics (per-server with labels)
http_requests_total{server="0.0.0.0",port="8443",protocol="https",status="2xx"} ...
http_connections_active{server="0.0.0.0",port="8443",protocol="https"} ...
http_request_duration_seconds_bucket{...,le="0.001"} ...
...

# VM metrics
valk_gc_cycles_total ...
valk_gc_heap_used_bytes ...
valk_gc_heap_total_bytes ...
valk_gc_heap_utilization_ratio ...   # NEW
valk_eval_total ...
...
```

### F.5 Connection State Machine

Phase 2 added instrumentation hooks for the connection lifecycle:

```
                 valk_aio_metrics_on_connecting()
    [new conn] ─────────────────────────────────────► [CONNECTING]
                                                           │
                 valk_aio_metrics_on_connected()           │
                           ┌───────────────────────────────┘
                           ▼
                      [ACTIVE] ◄────────────────────────┐
                           │                            │
    valk_aio_metrics_on_idle()              valk_aio_metrics_on_reactivate()
                           │                            │
                           ▼                            │
                       [IDLE] ──────────────────────────┘
                           │
    valk_aio_metrics_on_closing()
                           │
                           ▼
                      [CLOSING]
                           │
    valk_aio_metrics_on_closed()
                           │
                           ▼
                       [removed]
```

### F.6 Testing

All implementations verified with:
- `make build` - Successful compilation
- `make test` - All tests passing
- Metrics structure validated against Prometheus text format specification
