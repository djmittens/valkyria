# Async I/O

Valkyria provides async I/O built on libuv with composable async handles.

## Overview

The async system supports two programming models:
1. **Handle-based** - Composable async operations with combinators
2. **Continuation-based** - shift/reset delimited continuations

## Async Handles

Handles represent async operations with status tracking and composition.

### Status Lifecycle

```
PENDING → RUNNING → COMPLETED
                  → FAILED
                  → CANCELLED
```

### Core Combinators

```lisp
; Create handles
(aio/pure val)         ; Wrap value in completed handle
(aio/fail err)         ; Create failed handle

; Composition
(aio/then handle fn)   ; Sequential composition (flatMap)
(aio/catch handle fn)  ; Error handling
(aio/finally h fn)     ; Cleanup (always runs)

; Parallel operations
(aio/all handles)      ; Wait for all
(aio/race handles)     ; First to complete
(aio/any handles)      ; Any success (skip failures)

; Cancellation
(aio/cancel handle)    ; Cancel operation
(aio/cancelled? h)     ; Check if cancelled
(aio/on-cancel h fn)   ; Register callback

; Resource management
(aio/bracket acquire release use)  ; Safe resource handling
(aio/scope fn)         ; Scope-based cancellation
```

### Do-Notation

Monadic syntax for sequential async operations:

```lisp
(aio/do
  (<- response (fetch "https://api.example.com"))
  (<- body (response-body response))
  (aio/pure body))
```

### Async Let

Parallel binding:

```lisp
(aio/let
  ((a (fetch url1))
   (b (fetch url2)))
  (aio/pure (list a b)))
```

## Continuations

Shift/reset delimited continuations for advanced control flow:

```lisp
(async-reset
  (+ 1 (async-shift k (k 10))))  ; => 11

; k captures "add 1 to hole"
```

## HTTP/2 Client

Full HTTP/2 client with TLS:

```lisp
; High-level API
(fetch "https://example.com")
(fetch-text "https://example.com")

; With custom request
(def req (-> (http-get "https://api.example.com")
             (with-header "Authorization" "Bearer token")))
(fetch-with-request req)

; Parallel requests
(fetch-all '("url1" "url2" "url3"))
```

## HTTP/2 Server

HTTP/2 server with TLS:

```lisp
(aio/start)

(http2/server-listen 8443 "cert.pem" "key.pem"
  (lambda (req)
    (http2/response 200
      '(("content-type" "text/plain"))
      "Hello, World!")))

(aio/run)
```

## System Management

```lisp
(aio/start)            ; Initialize async system
(aio/run)              ; Run event loop
(aio/metrics)          ; Get metrics
(aio/metrics-json)     ; JSON format
(aio/metrics-prometheus) ; Prometheus format
```

## Timing

```lisp
(aio/sleep ms)         ; Async sleep
(aio/delay ms val)     ; Delay returning value
(time-us)              ; Current time in microseconds
```

## Load Shedding

The server implements automatic load shedding:
- Connection rejection at capacity
- 503 responses under overload
- Buffer backpressure monitoring

## Implementation Files

- `src/aio.h` - Async I/O interface
- `src/aio_uv.c` - libuv backend
- `src/aio_ssl.c` - TLS support
- `src/http_api.valk` - High-level HTTP API
- `src/async_handles.valk` - Handle utilities
