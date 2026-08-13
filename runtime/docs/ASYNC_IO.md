# Async I/O

Async I/O is built on libuv. Operations are represented as **handles** that
compose via combinators.

Nearly every operation takes an AIO system as its first argument:

```lisp
(def {aio} (aio/await (aio/start)))
; ... schedule work ...
(aio/run aio)
```

## Handle Lifecycle

```
PENDING → RUNNING → COMPLETED
                  → FAILED
                  → CANCELLED
```

Inspect with `(aio/status h)`, `(aio/result h)`, `(aio/error h)`.

## Core Combinators

```lisp
; Creation
(aio/pure val)              ; Completed handle
(aio/fail err)              ; Failed handle
(aio/never)                 ; Never resolves

; Sequencing
(aio/then h fn)             ; Continue when h resolves
(aio/catch h fn)            ; Handle errors
(aio/finally h fn)          ; Always runs

; Combining
(aio/all handles)           ; Wait for all
(aio/all-settled handles)   ; Wait for all, keep failures
(aio/race handles)          ; First to settle
(aio/any handles)           ; First success
(aio/within ms h)           ; Timeout
(aio/retry ...)             ; Retry on failure

; Mapping
(aio/pmap ...)              ; Parallel map
(aio/traverse ...)          ; Traverse with async fn

; Cancellation
(aio/cancel h)              ; Cancel
(aio/cancelled? h)          ; Check
(aio/on-cancel h fn)        ; Register callback

; Resources
(aio/bracket acquire release use)
(aio/scope fn)
```

`aio/bracket` takes three async-producing arguments:

```lisp
(aio/bracket
  (aio/then (aio/sleep aio 5) (\ {_} {"resource"}))   ; acquire
  (\ {r} {(aio/then (aio/sleep aio 5) (\ {_} {nil}))}) ; release
  (\ {r} {(aio/pure "used")}))                         ; use
```

## Sequencing Sugar

### aio/do

Bindings use `<-`; the body is the final expression.

```lisp
(aio/do {
  (<- x (aio/sleep aio 5))
  (<- y (aio/sleep aio 5))
  {:status "200" :body "done"}})
```

### aio/let

Bindings in one group run **in parallel**. Use `:then` to force sequencing.

```lisp
; Parallel
(aio/let {((a (aio/sleep aio 5)) (b (aio/sleep aio 10)))}
  {:status "200" :body "parallel"})

; Sequential
(aio/let {((x (aio/sleep aio 5)) :then (y (aio/sleep aio 5)))}
  {:status "200" :body "sequential"})
```

## Timers & Scheduling

```lisp
(aio/sleep aio ms)          ; Async sleep
(aio/interval aio ms fn)    ; Repeating timer
(aio/schedule aio ...)      ; Schedule work
(time-us)                   ; Current time, microseconds
```

There is no `aio/delay`.

## Dispatch & Execution

```lisp
(aio/dispatch ...)          ; Dispatch onto the loop
(aio/exec ...)              ; Execute
(aio/on-loop-thread? aio)   ; Am I on the event loop thread?
```

## System Management

```lisp
(aio/start)                 ; -> handle; await it to get the system
(aio/await h)               ; Block until resolved (main thread only)
(aio/run aio)               ; Run the event loop
(aio/stop aio)              ; Stop
(aio/status h)              ; Handle status
(aio/pool-stats aio)        ; Pool statistics
(aio/systems-json)          ; Systems as JSON
```

## Metrics

```lisp
(aio/metrics-json)          ; AIO metrics as JSON
(aio/metrics-json-compact)
(metrics/prometheus)        ; Prometheus text format
(metrics/json)
```

There is no `aio/metrics` or `aio/metrics-prometheus`. See [METRICS.md](METRICS.md).

## HTTP/2

See [HTTP_API.md](HTTP_API.md). Briefly:

```lisp
; Client
(aio/then (http2/client-request aio "example.com" 443 "/") (\ {resp} {
  (print (http2/response-status resp))
}))

; Server - port 0 picks a free port
(def {srv} (http2/server-listen aio 0 (\ {req} {
  `{:status "200" :body "Hello"}
})))
```

## Load Shedding

The server sheds load automatically:

- Connection rejection at capacity
- 503 responses under overload
- Buffer backpressure monitoring

Tuning is covered in [CAPACITY_PLANNING.md](CAPACITY_PLANNING.md).

## Implementation Files

- `runtime/src/aio/` - Async I/O subsystem
- `runtime/src/aio/aio_uv.c` - libuv backend
- `runtime/src/aio/aio_async.c` - Handles and combinators
- `runtime/src/aio/http2/` - HTTP/2 client, server, sessions
- `runtime/src/aio/http2/aio_ssl.c` - TLS
- `stdlib/aio/handles.valk` - Handle utilities
- `stdlib/aio/monadic.valk` - Monadic combinators
- `stdlib/http/api.valk` - High-level HTTP API
