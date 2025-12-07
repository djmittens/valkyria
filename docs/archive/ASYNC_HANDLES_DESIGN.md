# Async Handles Design (Option A)

## Executive Summary

This document specifies an **eager async system with cancellable handles** for Valkyria's webserver. The design builds on the existing `aio/delay` primitive, extending it with composition, cancellation, and resource management.

**Goals:**
1. Composable async operations (chain, parallel, race)
2. Cancellation with propagation
3. Resource cleanup guarantees
4. Clean `do-async` syntax
5. Minimal implementation effort (builds on existing libuv integration)

**Non-Goals:**
- Lazy effect descriptions (see FIBER_EFFECT_DESIGN.md for that)
- Effect reification/inspection
- Full structured concurrency with automatic fiber management

---

## Design Philosophy

### Eager vs Lazy

This design uses **eager evaluation**: async operations start immediately when called.

```lisp
; EAGER (this design) - operation starts NOW
(def handle (aio/http-get "https://api.com/users"))
; Request is already in flight

; LAZY (effect system) - operation is just a description
(def effect (http/get "https://api.com/users"))
; Nothing happens until (run! effect)
```

**Trade-off:** Eager is simpler to implement and reason about for most webserver use cases. Lazy is more powerful for complex dataflow pipelines.

### Comparison to JavaScript

This design is similar to **JavaScript Promises with AbortController**:

| JavaScript | Valkyria |
|------------|----------|
| `new Promise((resolve, reject) => ...)` | `(aio/async (\ {resolve reject} ...))` |
| `promise.then(fn)` | `(aio/then handle fn)` |
| `Promise.all([...])` | `(aio/all (list ...))` |
| `Promise.race([...])` | `(aio/race (list ...))` |
| `AbortController.abort()` | `(aio/cancel handle)` |
| `signal.aborted` | `(aio/cancelled? handle)` |

---

## Core Concepts

### What is a Handle?

A **Handle** is a reference to a running async operation:
- Represents an in-flight operation (timer, HTTP request, DB query, etc.)
- Can be queried for status
- Can be cancelled
- Can have callbacks registered for completion or cancellation

```lisp
; Create a handle by starting an async operation
(def h (aio/delay 2000 (\ {} "done")))

; Query status
(aio/status h)      ; => :pending | :running | :completed | :cancelled | :failed

; Cancel it
(aio/cancel h)      ; => true (if cancelled) | false (if already done)

; Check if cancelled
(aio/cancelled? h)  ; => true | false
```

### Handle Lifecycle

```
                    ┌──────────────┐
                    │   PENDING    │
                    └──────┬───────┘
                           │ start
                           ▼
                    ┌──────────────┐
         ┌──────────│   RUNNING    │──────────┐
         │          └──────────────┘          │
         │ cancel                      complete/error
         ▼                                    ▼
┌──────────────┐                      ┌──────────────┐
│  CANCELLED   │                      │  COMPLETED   │
└──────────────┘                      │  or FAILED   │
                                      └──────────────┘
```

---

## Type Specification

### Handle Structure

**File: `src/aio_uv.c` (or new `src/aio_handle.h`)**

```c
typedef enum {
  AIO_PENDING,      // Created but not started
  AIO_RUNNING,      // Operation in progress
  AIO_COMPLETED,    // Finished successfully
  AIO_FAILED,       // Finished with error
  AIO_CANCELLED,    // Cancelled before completion
} valk_aio_status_t;

typedef struct valk_aio_handle {
  // Identity
  uint64_t id;
  valk_aio_status_t status;

  // Cancellation
  _Atomic int cancel_requested;

  // libuv integration
  uv_handle_t *uv_handle;         // Timer, TCP, FS, etc.
  uv_loop_t *loop;

  // Callbacks
  valk_lval_t *on_complete;       // (\ {result} ...)
  valk_lval_t *on_error;          // (\ {error} ...)
  valk_lval_t *on_cancel;         // (\ {} ...)
  valk_lenv_t *env;               // Environment for callbacks

  // Result storage
  valk_lval_t *result;            // Success value
  valk_lval_t *error;             // Error value

  // Structured cancellation
  struct valk_aio_handle *parent;
  struct {
    struct valk_aio_handle **items;
    size_t count;
    size_t capacity;
  } children;

  // Memory management
  valk_mem_allocator_t *allocator;
} valk_aio_handle_t;
```

### LVAL_HANDLE Type

Add to `parser.h`:

```c
typedef enum {
  // ... existing types ...
  LVAL_HANDLE,    // Async operation handle
} valk_ltype_e;

// In valk_lval_t union:
struct {
  valk_aio_handle_t *handle;
} handle;
```

---

## API Specification

### Core Operations

| Builtin | Signature | Description |
|---------|-----------|-------------|
| `aio/delay` | `(aio/delay ms callback)` → handle | Timer that calls callback after ms |
| `aio/cancel` | `(aio/cancel handle)` → bool | Request cancellation |
| `aio/cancelled?` | `(aio/cancelled? handle)` → bool | Check if cancelled |
| `aio/status` | `(aio/status handle)` → symbol | Get current status |
| `aio/await` | `(aio/await handle)` → value | Block until complete (REPL only) |

### Composition

| Builtin | Signature | Description |
|---------|-----------|-------------|
| `aio/then` | `(aio/then handle fn)` → handle | Chain: run fn with result |
| `aio/catch` | `(aio/catch handle fn)` → handle | Handle errors |
| `aio/finally` | `(aio/finally handle fn)` → handle | Always run cleanup |
| `aio/all` | `(aio/all handles)` → handle | Parallel, wait for all |
| `aio/race` | `(aio/race handles)` → handle | Parallel, first wins |
| `aio/any` | `(aio/any handles)` → handle | Parallel, first success wins |

### Resource Management

| Builtin | Signature | Description |
|---------|-----------|-------------|
| `aio/bracket` | `(aio/bracket acquire release use)` → handle | Safe resource usage |
| `aio/scope` | `(aio/scope fn)` → handle | Create child scope |
| `aio/on-cancel` | `(aio/on-cancel handle fn)` → handle | Register cancel callback |

### Creation

| Builtin | Signature | Description |
|---------|-----------|-------------|
| `aio/pure` | `(aio/pure value)` → handle | Immediately completed handle |
| `aio/fail` | `(aio/fail error)` → handle | Immediately failed handle |
| `aio/async` | `(aio/async fn)` → handle | Create from callback fn |

---

## Detailed Semantics

### `aio/delay`

```lisp
(aio/delay ms callback)
```

Creates a timer that fires after `ms` milliseconds, then calls `callback` with no arguments.

**Example:**
```lisp
(def h (aio/delay 2000 (\ {} {:status "200" :body "waited 2s"})))
```

**Returns:** Handle that completes with callback's return value.

**Cancellation:** If cancelled before timer fires, callback is never called.

### `aio/then`

```lisp
(aio/then handle fn)
```

Chains an operation: when `handle` completes, call `fn` with the result.

**Example:**
```lisp
(def h (aio/then
         (aio/delay 1000 (\ {} 42))
         (\ {x} (* x 2))))
; After 1000ms, h completes with 84
```

**Cancellation:** Cancelling the returned handle cancels the source handle (if still running) and prevents `fn` from being called.

**Error propagation:** If source fails, `fn` is not called and error propagates.

### `aio/all`

```lisp
(aio/all handles)
```

Runs all handles in parallel, waits for all to complete.

**Example:**
```lisp
(def h (aio/all (list
         (aio/delay 1000 (\ {} "a"))
         (aio/delay 2000 (\ {} "b"))
         (aio/delay 1500 (\ {} "c")))))
; After 2000ms (slowest), h completes with ("a" "b" "c")
```

**Cancellation:** Cancelling `h` cancels ALL child handles.

**Error handling:** If ANY child fails, all others are cancelled and the error propagates.

### `aio/race`

```lisp
(aio/race handles)
```

Runs all handles in parallel, returns first to complete (success OR failure).

**Example:**
```lisp
(def h (aio/race (list
         (aio/delay 1000 (\ {} "fast"))
         (aio/delay 5000 (\ {} "slow")))))
; After 1000ms, h completes with "fast"
; The 5000ms timer is automatically cancelled
```

**Cancellation:** Cancelling `h` cancels all children.

**Winner selection:** First to reach COMPLETED or FAILED state wins.

### `aio/bracket`

```lisp
(aio/bracket acquire release use)
```

Safe resource management: acquire resource, use it, ALWAYS release.

**Example:**
```lisp
(aio/bracket
  ; Acquire - returns handle that completes with resource
  (aio/db-connect "postgres://...")

  ; Release - ALWAYS called, even on error or cancel
  (\ {conn} (aio/db-close conn))

  ; Use - main operation
  (\ {conn} (aio/db-query conn "SELECT * FROM users")))
```

**Guarantees:**
- `release` is called if `acquire` succeeds, regardless of whether `use` succeeds, fails, or is cancelled
- `release` runs in `uncancellable` context (cannot be interrupted)

### `aio/scope`

```lisp
(aio/scope fn)
```

Creates a cancellation scope. All handles created inside `fn` are children of this scope.

**Example:**
```lisp
(def parent (aio/scope (\ {s}
  ; These are children of parent
  (def h1 (aio/delay 1000 (\ {} "a")))
  (def h2 (aio/delay 2000 (\ {} "b")))
  (aio/all (list h1 h2)))))

; Cancel parent → cancels h1 and h2
(aio/cancel parent)
```

---

## Webserver Integration

### Handler Returns Handle

When a handler returns a handle instead of a response map, the server waits for completion:

```lisp
(def {handler} (\ {req sys}
  (match (req :path)
    ; Immediate response
    "/health"
    {:status "200" :body "ok"}

    ; Async response - returns handle
    "/slow"
    (aio/delay 2000 (\ {} {:status "200" :body "waited 2s"}))

    ; Chained async
    "/users/:id"
    (aio/then
      (aio/db-query db "SELECT * FROM users WHERE id = ?" (list id))
      (\ {user} {:status "200" :body (json user)}))

    ; Parallel fetch
    "/dashboard"
    (aio/then
      (aio/all (list
        (aio/db-query db "SELECT * FROM posts")
        (aio/db-query db "SELECT * FROM stats")))
      (\ {results}
        (def posts (nth results 0))
        (def stats (nth results 1))
        {:status "200" :body (json {:posts posts :stats stats})}))

    ; With timeout
    "/api/slow"
    (aio/race (list
      (aio/then (fetch-slow-data) (\ {d} {:status "200" :body d}))
      (aio/delay 5000 (\ {} {:status "504" :body "timeout"}))))
)))
```

### Request Cancellation

When a client disconnects, the server cancels the handler's handle:

```c
// In HTTP/2 RST_STREAM callback or connection close
void on_stream_close(int32_t stream_id) {
  valk_aio_handle_t *h = get_handler_handle(stream_id);
  if (h && h->status == AIO_RUNNING) {
    valk_aio_cancel(h);
  }
}
```

This automatically:
1. Cancels any pending timers
2. Cancels any pending I/O operations
3. Runs cleanup callbacks registered with `aio/on-cancel` or `aio/bracket`

---

## `do-async` Macro

### Syntax

```lisp
(do-async
  stmt1
  stmt2
  ...
  stmtN)
```

### Transformation Rules

1. **Plain expression** → evaluate and continue
2. **`(def name expr)`** where expr returns handle → chain with `aio/then`
3. **`(def name expr)`** where expr is immediate → bind and continue
4. **Last expression** → return value

### Example Expansion

```lisp
; This:
(do-async
  (def user (aio/http-get "/user"))
  (def posts (aio/http-get (str "/posts?user=" (user :id))))
  {:user user :posts posts})

; Expands to:
(aio/then
  (aio/http-get "/user")
  (\ {user}
    (aio/then
      (aio/http-get (str "/posts?user=" (user :id)))
      (\ {posts}
        (aio/pure {:user user :posts posts})))))
```

### Implementation

**File: `lib/std/async.valk`**

```lisp
(def {do-async} (macro {. stmts}
  (do-async-expand stmts)))

(def {do-async-expand} (\ {stmts}
  (if (nil? stmts)
    '(aio/pure nil)
    (if (== (len stmts) 1)
      (do-async-single (head stmts))
      (do-async-chain (head stmts) (tail stmts))))))

(def {do-async-single} (\ {stmt}
  (if (is-def? stmt)
    `(aio/then ~(def-expr stmt) (\ {~(def-name stmt)} (aio/pure ~(def-name stmt))))
    `(aio/then (as-handle ~stmt) (\ {_result} (aio/pure _result))))))

(def {do-async-chain} (\ {stmt rest}
  (if (is-def? stmt)
    `(aio/then (as-handle ~(def-expr stmt)) (\ {~(def-name stmt)} (do-async ~@rest)))
    `(aio/then (as-handle ~stmt) (\ {_} (do-async ~@rest))))))

; Helper: wrap non-handle in aio/pure
(def {as-handle} (\ {x}
  (if (handle? x)
    x
    (aio/pure x))))
```

---

## Error Handling

### Error Propagation

Errors propagate through chains automatically:

```lisp
(aio/then
  (aio/then
    (aio/fail "something went wrong")  ; Error here
    (\ {x} (print "never printed")))   ; Skipped
  (\ {x} (print "also skipped")))      ; Skipped
; Handle completes with error "something went wrong"
```

### Catching Errors

```lisp
(aio/catch
  (aio/then
    (might-fail)
    (\ {x} (process x)))
  (\ {err}
    {:status "500" :body (str "Error: " err)}))
```

### Try Pattern

```lisp
(aio/then
  (aio/try (might-fail))  ; Returns {:ok value} or {:err error}
  (\ {result}
    (if (result :ok)
      (process (result :ok))
      (handle-error (result :err)))))
```

---

## Cancellation Patterns

### Timeout

```lisp
(def {with-timeout} (\ {ms handle}
  (aio/race (list
    handle
    (aio/then (aio/delay ms) (\ {_} (aio/fail :timeout)))))))

; Usage
(with-timeout 5000 (aio/http-get url))
```

### Retry with Backoff

```lisp
(def {retry-backoff} (\ {n base-ms handle-fn}
  (if (<= n 0)
    (handle-fn)
    (aio/catch
      (handle-fn)
      (\ {err}
        (aio/then
          (aio/delay base-ms)
          (\ {_} (retry-backoff (- n 1) (* base-ms 2) handle-fn))))))))

; Usage
(retry-backoff 3 1000 (\ {} (aio/http-get url)))
```

### Graceful Shutdown

```lisp
(def {graceful-shutdown} (\ {handles timeout-ms}
  ; Give handles time to complete naturally
  (aio/race (list
    (aio/all handles)
    (aio/then
      (aio/delay timeout-ms)
      (\ {_}
        ; Force cancel remaining
        (map aio/cancel handles)
        :timeout))))))
```

---

## Implementation Plan

### Phase 1: Core Handle System (Week 1)

| Task | File | Description |
|------|------|-------------|
| 1.1 | `parser.h` | Add `LVAL_HANDLE` type |
| 1.2 | `aio_uv.c` | Define `valk_aio_handle_t` struct |
| 1.3 | `aio_uv.c` | Implement `valk_aio_handle_new()` |
| 1.4 | `aio_uv.c` | Modify `aio/delay` to return handle |
| 1.5 | `aio_uv.c` | Implement `aio/cancel` |
| 1.6 | `aio_uv.c` | Implement `aio/cancelled?` |
| 1.7 | `aio_uv.c` | Implement `aio/status` |
| 1.8 | `gc.c` | Add handle to GC marking |
| 1.9 | `test/test_aio_handle.c` | Unit tests |

### Phase 2: Composition (Week 2)

| Task | File | Description |
|------|------|-------------|
| 2.1 | `aio_uv.c` | Implement `aio/pure` |
| 2.2 | `aio_uv.c` | Implement `aio/fail` |
| 2.3 | `aio_uv.c` | Implement `aio/then` with cancel propagation |
| 2.4 | `aio_uv.c` | Implement `aio/catch` |
| 2.5 | `aio_uv.c` | Implement `aio/finally` |
| 2.6 | `aio_uv.c` | Implement `aio/all` |
| 2.7 | `aio_uv.c` | Implement `aio/race` |
| 2.8 | `test/test_aio_compose.c` | Composition tests |

### Phase 3: Resource Safety (Week 3)

| Task | File | Description |
|------|------|-------------|
| 3.1 | `aio_uv.c` | Implement parent/child tracking |
| 3.2 | `aio_uv.c` | Implement `aio/scope` |
| 3.3 | `aio_uv.c` | Implement `aio/bracket` |
| 3.4 | `aio_uv.c` | Implement `aio/on-cancel` |
| 3.5 | `aio_uv.c` | Implement cascade cancellation |
| 3.6 | `test/test_aio_resources.c` | Resource safety tests |

### Phase 4: Syntactic Sugar (Week 4)

| Task | File | Description |
|------|------|-------------|
| 4.1 | `lib/std/async.valk` | Implement `do-async` macro |
| 4.2 | `lib/std/async.valk` | Implement `with-timeout` |
| 4.3 | `lib/std/async.valk` | Implement `retry-backoff` |
| 4.4 | `lib/std/async.valk` | Helper utilities |
| 4.5 | `examples/webserver_demo.valk` | Convert to new API |
| 4.6 | `test/test_async.valk` | Lisp-level tests |

### Phase 5: Integration & Migration

| Task | File | Description |
|------|------|-------------|
| 5.1 | `aio_uv.c` | Update handler to detect LVAL_HANDLE |
| 5.2 | `aio_uv.c` | Cancel handle on client disconnect |
| 5.3 | `src/async_lib.valk` | Deprecate old stubs |
| 5.4 | `docs/` | Update documentation |

---

## Migration from `:deferred`

### Old Pattern

```lisp
; Returns :deferred, uses callback
(\ {req sys}
  (aio/delay sys 2000 (\ {} {:status "200" :body "done"}))
  :deferred)
```

### New Pattern

```lisp
; Returns handle directly
(\ {req sys}
  (aio/delay 2000 (\ {} {:status "200" :body "done"})))
```

### Compatibility

During migration, both patterns work:
1. Handler returns map → immediate response
2. Handler returns `:deferred` → old async pattern (deprecated)
3. Handler returns handle → new async pattern

---

## Comparison to Effect System

| Feature | Async Handles | Effect System |
|---------|---------------|---------------|
| **Evaluation** | Eager | Lazy |
| **Mental model** | Promises | Descriptions |
| **Cancellation** | ✅ Yes | ✅ Yes |
| **Composition** | ✅ then/all/race | ✅ do!/par!/race! |
| **Resource safety** | ✅ bracket | ✅ bracket! |
| **Rerunnable** | ❌ No | ✅ Yes |
| **Inspectable** | ❌ No | ✅ Effect trees |
| **Implementation** | ~2000 lines | ~5000+ lines |

**When to use Handles:** Webserver handlers, simple async I/O, timeout patterns.

**When to use Effects:** Dataflow pipelines, complex retry logic, effect inspection/transformation.

---

## References

### Existing Code

| File | Description |
|------|-------------|
| `src/aio_uv.c:234-260` | Current `valk_http_request_ctx_t` |
| `src/aio_uv.c:245-260` | Current `valk_delay_timer_t` |
| `src/aio_uv.c:3143-3240` | Current `aio/delay` implementation |
| `src/concurrency.h` | Thread pool, futures, ARC |

### External References

- [JavaScript AbortController](https://developer.mozilla.org/en-US/docs/Web/API/AbortController)
- [JavaScript Promise.race/all](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Promise)
- [libuv handles](http://docs.libuv.org/en/v1.x/handle.html)
