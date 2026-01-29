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
| `atom` operations | Internally uses `_Atomic int64_t` |
| `aio/cancel` from any thread | Uses atomic flag + `uv_async_send` to wake loop |

### Unsafe Operations

| Operation | Problem |
|-----------|---------|
| `(def {x} ...)` in callbacks | `valk_lenv_put` has no locking; data race with reader |
| Mutating closure-captured state | Same environment may be accessed from multiple requests |

### Sandbox Protection

HTTP handlers execute in a **sandboxed environment** where `def` is replaced with an error-returning stub:

```lisp
; In handler callback - throws error
(def {x} 42)  ; => Error: def not allowed in sandboxed environment
```

This prevents accidental global mutation from request handlers but doesn't protect other async callbacks.

## Safe Patterns

### Atoms for Cross-Thread State

```lisp
(def {counter} (atom 0))

(fun {handler req} {
  (atom/add! counter 1)  ; Safe - atomic operation
  ...
})
```

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

1. GC thread sets `gc_requested` flag
2. Event loop thread checks flag at safe points (between callbacks)
3. Event loop acknowledges via `gc_acknowledged` atomic
4. GC runs while event loop is paused
5. GC signals completion; event loop resumes

## Detecting Thread Context

```lisp
(if (aio/on-loop-thread? aio)
  ; Running on event loop - callbacks execute here
  (handle-async ...)
  ; Running on main thread - blocking calls work here
  (blocking-call ...))
```

## Summary

- **Don't** use `def` to mutate globals after initialization
- **Do** use `atom` for counters and shared mutable state
- **Do** use local bindings (`=`) in callbacks
- HTTP handlers are sandboxed and cannot use `def`
- All Lisp evaluation in async callbacks happens on the event loop thread
