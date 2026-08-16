# Metrics & Observability

Valkyria exposes runtime metrics for GC, interpreter, and async I/O.

## Metric Categories

### GC Metrics

```lisp
(mem/gc/stats)      ; Prints a human-readable report (returns nil)
(mem/gc/metrics)    ; Structured metrics
(mem/gc/usage)      ; Current usage in bytes
(mem/stats)         ; Prints all memory subsystems
```

Covers collection cycles, pause times, objects marked/swept, bytes reclaimed,
peak usage, and emergency GC count.

Note `mem/gc/stats` and `mem/stats` *print* their report rather than returning a
string — don't try to pass them to `str/*` functions.

### Memory Introspection

```lisp
(mem/arena/usage)       (mem/arena/capacity)    (mem/arena/high-water)
(mem/heap/usage)        (mem/heap/hard-limit)
(mem/checkpoint/stats)  ; Arena checkpoint/evacuation counters
```

### Interpreter Metrics

Total evaluations, function calls (builtin vs user-defined), stack depth,
closures created, environment lookups.

### AIO/HTTP Metrics

RED method (Request, Error, Duration) and USE method (Utilization, Saturation,
Errors), plus connection tracking: total, active, failed, and rejected
(load-shed) connections.

```lisp
(aio/metrics-json)          (aio/metrics-json-compact)
(aio/pool-stats aio)        (aio/slab-buckets)
(aio/systems-json)
(aio/diagnostics-state-json)
```

## Export Formats

### JSON

```lisp
(metrics/json)
(vm/metrics-json)
(aio/metrics-json)
(metrics/registry-json)
```

### Prometheus

```lisp
(metrics/prometheus)
(vm/metrics-prometheus)
```

Note: there is no `aio/metrics-prometheus` — use `metrics/prometheus`.

Example output:

```
# HELP valk_gc_cycles_total Total GC cycles
# TYPE valk_gc_cycles_total counter
valk_gc_cycles_total 42

# HELP valk_connections_active Active connections
# TYPE valk_connections_active gauge
valk_connections_active 15
```

## Custom Metrics

Create a **handle** first, then operate on the handle. Labels are flat string
key/value pairs on the constructor — not a nested list.

```lisp
(metrics/counter name k v ...)     ; -> handle
(metrics/counter-inc h)            ; += 1
(metrics/counter-inc h n)          ; += n

(metrics/gauge name k v ...)       ; -> handle
(metrics/gauge-set h v)
(metrics/gauge-inc h)              ; no amount argument
(metrics/gauge-dec h)

(metrics/histogram name k v ...)   ; -> handle
(metrics/histogram-observe h v)
```

Working example:

```lisp
(= {c} (metrics/counter "http_requests" "method" "GET"))
(metrics/counter-inc c)
(metrics/counter-inc c 5)

(= {g} (metrics/gauge "inflight"))
(metrics/gauge-set g 42)

(= {h} (metrics/histogram "latency_ms"))
(metrics/histogram-observe h 12)
```

## Deltas & Streaming

For SSE/streaming consumers that need only what changed:

```lisp
(metrics/baseline)
(metrics/collect-delta)
(metrics/collect-delta-stateless)
(metrics/delta-json)
```

## HTTP Endpoints

When an HTTP server is running:

| Endpoint | Purpose |
|---|---|
| `/metrics` | Prometheus text format |
| `/metrics/snapshot` | Point-in-time snapshot |
| `/debug/` | Debug dashboard |
| `/debug/metrics` | Combined JSON metrics |
| `/debug/metrics/state` | Metric registry state |
| `/debug/diagnostics/memory` | Memory diagnostics (SSE) |
| `/debug/slab/buckets` | Slab allocator occupancy |

## Implementation Files

- `src/metrics_v2.c`, `src/metrics_v2.h` - Core registry (counters, gauges, histograms)
- `runtime/src/metrics_builtins.c` - Lisp builtins
- `runtime/src/metrics_delta.c` - Delta computation for streaming
- `runtime/src/aio/aio_metrics.c`, `runtime/src/aio/aio_metrics_v2.c` - AIO metrics
- `runtime/src/event_loop_metrics.c` - Event loop instrumentation
- `runtime/src/pool_metrics.c` - Pool/slab metrics
- `stdlib/aio/metrics-stream.valk` - SSE metrics streaming
