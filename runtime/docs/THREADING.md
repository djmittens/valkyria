# Threading Model

Valk uses a two-thread architecture for async I/O operations.

## Threads

| Thread | Purpose | Created by |
|--------|---------|------------|
| **Main thread** | Script initialization, `aio/run` blocking | User process |
| **Event loop thread** | libuv event loop, all async callbacks | `valk_aio_start()` via `uv_thread_create_ex` |

## Execution Flow

```
Main thread                    Event loop thread
-----------                    -----------------
(load "script.valk")
  ↓
(def {handler} ...)           
  ↓
(http2/server-listen ...)
  ↓
(aio/run aio)
  ↓ blocks
                               libuv accepts connection
                               ↓
                               HTTP/2 request arrives
                               ↓
                               valk_eval(handler, sandboxed_env)
                               ↓
                               Response sent
                               ↓
(aio/run returns)
```

## Thread Safety Rules

### Safe Operations

| Operation | Why Safe |
|-----------|----------|
| Reading global bindings | Immutable after load-time initialization |
| `dict` operations | Serialized through 64 striped mutexes keyed by lval pointer |
| `aio/cancel` from any thread | Uses atomic flag + `uv_async_send` to wake loop |

### Unsafe Operations

| Operation | Problem |
|-----------|---------|
| `(def {x} ...)` in callbacks | `valk_lenv_put` has no locking; data race with reader |
| Mutating closure-captured state | Same environment may be accessed from multiple requests |

### Sandbox Protection

HTTP handlers execute in a **sandboxed environment** where `def` is replaced with an error-returning stub:

```lisp
; In handler callback - returns an error (surfaces as a 500)
(def {x} 42)
; => def cannot be used in request handler context. Use = for local bindings instead.
```

This prevents accidental global mutation from request handlers but doesn't protect other async callbacks.

## Safe Patterns

### Dicts for Cross-Thread State

Dicts are the supported shared-mutable structure. Every builtin dict operation
takes a striped lock, so they are safe to mutate from handlers and worker
threads. There is no `atom` type.

```lisp
(def {state} (dict/new))

(fun {handler req} {
  (dict/set! state "hits" (+ 1 (dict/get state "hits")))
  ...
})
```

Available: `dict/new`, `dict/get`, `dict/set!`, `dict/put!`, `dict/remove!`,
`dict/has?`, `dict/keys`, `dict/values`, `dict/entries`, `dict/count`,
`dict/from-keys`.

### Immutable Bindings

```lisp
; OK - defined once at load time
(def {config} {:port 8080 :host "localhost"})

; Handler reads config (safe - never mutated)
(fun {handler req} {
  (printf "Running on port %d" (get :port config))
})
```

### Local Bindings in Callbacks

```lisp
(fun {handler req} {
  ; OK - local binding, not global
  (= {result} (process-request req))
  result
})
```

## GC Coordination

The garbage collector uses stop-the-world coordination:

1. Allocation pressure sets `VALK_SP_GC_COLLECT` in a thread's `safepoint_flags`
2. `valk_gc_heap_request_stw()` CASes the system phase `IDLE -> PREPARING`,
   freezes the participant set, then moves to `STW_REQUESTED` and sets
   `VALK_SP_STW` on every registered thread
3. Threads notice the flag at a safe point and enter
   `valk_gc_safe_point_slow()`; the event loop thread is woken via
   `uv_async_send` on its `gc_wakeup` handle
4. Participants rendezvous on a phase-counting barrier, then mark and sweep in
   parallel (`valk_gc_participate_in_parallel_gc()`)
5. Phase returns to `IDLE` and threads resume

Phases: `IDLE`, `PREPARING`, `STW_REQUESTED`, `MARKING`, `SWEEPING`.

## Detecting Thread Context

Branches must be qexprs:

```lisp
(if (aio/on-loop-thread? aio)
  {(handle-async ...)}    ; On event loop - callbacks execute here
  {(blocking-call ...)})  ; On main thread - blocking calls work here
```

## Summary

- **Don't** use `def` to mutate globals after initialization
- **Do** use a `dict` for counters and shared mutable state
- **Do** use local bindings (`=`) in callbacks
- HTTP handlers are sandboxed and cannot use `def`
- All Lisp evaluation in async callbacks happens on the event loop thread
