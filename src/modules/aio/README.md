# AIO Debug Module

Debug dashboard routes for Valkyria's async I/O system.

## Files

- `debug.valk` - Debug dashboard route handlers

## Usage

```lisp
(load "src/prelude.valk")
(load "src/modules/aio/debug.valk")

; Create AIO system
(def {sys} aio)

; Create debug handler
(def {debug-handler} (aio/debug-handler sys))

; Create application handler
(def {app-handler}
  (\ {req}
    ; Your application logic here
    `{:status "200" :body "Hello World"}))

; Combine handlers (debug routes take precedence)
(def {combined-handler}
  (\ {req}
    (= {debug-response} (debug-handler req))
    (if (== debug-response nil)
      (app-handler req)
      debug-response)))

; Start server
(http2/server-listen sys 8443 combined-handler)
(aio/run sys)
```

## Routes

The debug handler provides the following routes:

- `GET /debug/` - HTML debug dashboard
- `GET /debug/metrics` - JSON metrics endpoint
- `GET /metrics` - Prometheus format metrics

## Implementation Status

**Phase 3 (Current): Debug Routes in Lisp**
- ✓ Basic route structure
- ✓ Placeholder HTML dashboard
- ✓ Placeholder JSON metrics
- ✓ Placeholder Prometheus metrics

**Phase 2 (Pending): Lisp Builtins**
- TODO: `(aio/metrics-json sys)` - Get JSON metrics from C
- TODO: `(aio/metrics-prometheus sys)` - Get Prometheus metrics from C

**Phase 4 (Pending): Dashboard HTML**
- TODO: Interactive dashboard with polling
- TODO: Real-time metrics display
- TODO: Load from `static/debug/index.html`

## Example

See `examples/debug_server.valk` for a complete working example.

Test with:
```bash
./build/valk examples/debug_server.valk
curl -k https://localhost:8443/debug/
curl -k https://localhost:8443/debug/metrics
curl -k https://localhost:8443/metrics
```
