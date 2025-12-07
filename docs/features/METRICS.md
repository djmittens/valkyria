# Metrics & Observability

Valkyria provides comprehensive metrics for monitoring runtime behavior.

## Metric Categories

### GC Metrics

```lisp
(mem/gc/stats)
```

Returns:
- Collection cycles
- Pause times
- Objects marked/swept
- Bytes reclaimed
- Peak usage
- Emergency GC count

### Interpreter Metrics

- Total evaluations
- Function calls (builtin vs user-defined)
- Stack depth tracking
- Closures created
- Environment lookups

### AIO/HTTP Metrics

RED method (Request, Error, Duration):
- Request rate
- Error rate
- Response duration

USE method (Utilization, Saturation, Errors):
- Connection utilization
- Queue saturation
- Error counts

Connection tracking:
- Total connections
- Active connections
- Failed connections
- Rejected connections (load shedding)

## Export Formats

### JSON

```lisp
(aio/metrics-json)
(vm/metrics-json)
```

### Prometheus

```lisp
(aio/metrics-prometheus)
(vm/metrics-prometheus)
```

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

```lisp
(metrics/counter-inc "my_counter" '(("label" "value")))
```

## Debug Endpoints

When running an HTTP server:
- `/debug/` - Debug dashboard
- `/metrics` - Prometheus metrics

## Implementation Files

- `src/aio_metrics.h` - AIO metrics definitions
- `src/gc.h` - GC metrics
- `src/parser.h` - Interpreter metrics
