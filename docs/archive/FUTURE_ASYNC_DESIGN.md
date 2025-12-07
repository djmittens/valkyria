# Future/Monadic Async API Design Plan

## Executive Summary

This document proposes evolving Valkyria's async model from the current ad-hoc `:deferred` symbol pattern to a proper **Future-based monadic API**. The goal is to enable composable async operations with clean syntax while maintaining the performance benefits of continuation-passing style.

---

## Current State Analysis

### How `:deferred` Works Today

**Handler invocation** (`src/aio_uv.c:1278-1297`):
```c
// Handler called synchronously in event loop
response = valk_lval_eval_call(sandbox_env, handler, args);
```

**Response check** (`src/aio_uv.c:1302-1307`):
```c
if (LVAL_TYPE(response) == LVAL_SYM && strcmp(response->str, ":deferred") == 0) {
  // Timer will send response later
  return 0;
}
```

**Timer setup** (`src/aio_uv.c:3193-3235`):
- `aio/delay` captures request context (session, stream_id, arena)
- Stores continuation lambda on malloc heap
- Returns `:deferred` symbol immediately
- Timer callback sends response when it fires

**Usage** (`examples/webserver_demo.valk:203`):
```lisp
{(== path "/slow")
 {(aio/delay sys 2000 (\ {} {{:status "200" :body "slept 2s (async)"}}))}}
```

### Problems with Current Approach

1. **Not composable** - Can't chain multiple async operations
2. **Magic symbol** - `:deferred` is a special case, not a real type
3. **No error handling** - No way to recover from async failures
4. **No cancellation** - Can't cancel pending operations
5. **Callback hell** - Nested async operations become unreadable

---

## Proposed Design

### Target API

**Finagle-style chaining:**
```lisp
(>>= (aio/delay sys 2000)
     (fn [_] (fetch-user id))
     (fn [user] (fetch-posts (user :id)))
     (fn [posts] {:status "200" :body posts}))
```

**Async/await style (with shift/reset):**
```lisp
(async
  (let [user (await (fetch-user id))]
    (let [posts (await (fetch-posts (user :id)))]
      {:status "200" :body posts})))
```

### Core Design Question

> **DECISION REQUIRED: Which approach should we prioritize?**

| Option | Description | Pros | Cons |
|--------|-------------|------|------|
| **A: Future Type** | First-class Future values with map/flatMap | Standard pattern, familiar to Scala/JS devs | Requires new LVAL type, GC integration |
| **B: CPS Monadic** | Keep current continuation style, add sugar | Already working (`async_monadic.valk`), no C changes | Less intuitive, manual threading |
| **C: Hybrid** | Future type backed by CPS internally | Best of both worlds | More complex implementation |

**Recommendation:** Option C (Hybrid) - Expose Future as the user-facing API while using CPS internally for efficiency.

---

## Detailed Implementation Plan

### Phase 1: Future Type Foundation

**Files to modify:**
- `src/parser.h` - Add LVAL_FUTURE type
- `src/parser.c` - Future builtins
- `src/gc.c` - GC marking for futures

#### 1.1 Add Future Value Type

**File: `src/parser.h` (after line 49)**
```c
typedef enum {
  // ... existing types ...
  LVAL_FUTURE,   // Async future value
} valk_ltype_e;
```

**File: `src/parser.h` (after line 109)**
```c
struct {
  int resolved;                    // 0 = pending, 1 = success, -1 = failure
  valk_lval_t *value;              // Result when resolved (or error)
  struct {
    valk_lval_t **callbacks;       // List of (fn [result] ...) callbacks
    size_t count;
    size_t capacity;
  } on_resolve;
  pthread_mutex_t mutex;           // Thread safety for resolution
} future;
```

#### 1.2 Core Future Builtins

**File: `src/parser.c`**

| Builtin | Signature | Description |
|---------|-----------|-------------|
| `future/new` | `(future/new)` | Create pending future |
| `future/resolve` | `(future/resolve f value)` | Resolve with success value |
| `future/reject` | `(future/reject f error)` | Resolve with failure |
| `future/pure` | `(future/pure value)` | Create already-resolved future |
| `future/map` | `(future/map f fn)` | Transform success value |
| `future/flat-map` | `(future/flat-map f fn)` | Chain futures (flatMap/bind) |
| `future/recover` | `(future/recover f fn)` | Handle failures |
| `future/on-complete` | `(future/on-complete f fn)` | Register callback |
| `future?` | `(future? x)` | Type predicate |

**Implementation sketch:**
```c
// future/map: (future/map f fn) -> Future
static valk_lval_t* valk_builtin_future_map(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* future = valk_lval_list_nth(a, 0);
  valk_lval_t* fn = valk_lval_list_nth(a, 1);

  // Create new future for result
  valk_lval_t* result_future = valk_future_new();

  // If already resolved, apply fn immediately
  if (future->future.resolved == 1) {
    valk_lval_t* mapped = valk_lval_eval_call(e, fn,
                            valk_lval_list(future->future.value));
    result_future->future.resolved = 1;
    result_future->future.value = mapped;
  } else if (future->future.resolved == -1) {
    // Propagate failure
    result_future->future.resolved = -1;
    result_future->future.value = future->future.value;
  } else {
    // Register callback to map when resolved
    valk_future_add_callback(future, result_future, fn, e);
  }

  return result_future;
}
```

#### 1.3 GC Integration

**File: `src/gc.c` (modify `valk_gc_mark_value`)**
```c
case LVAL_FUTURE:
  if (v->future.value) {
    valk_gc_mark_value(v->future.value);
  }
  for (size_t i = 0; i < v->future.on_resolve.count; i++) {
    valk_gc_mark_value(v->future.on_resolve.callbacks[i]);
  }
  break;
```

---

### Phase 2: Webserver Integration

**Goal:** Handlers can return `Future<Response>` and server auto-resolves

#### 2.1 Handler Return Detection

**File: `src/aio_uv.c` (modify lines 1302-1330)**
```c
// Check handler return type
if (LVAL_TYPE(response) == LVAL_FUTURE) {
  // Register callback to send response when future resolves
  __http_register_future_response(session, stream_id, response,
                                   req->stream_arena, conn);
  return 0;  // Don't send yet
}
```

#### 2.2 Future Response Callback

**File: `src/aio_uv.c` (new function)**
```c
typedef struct {
  nghttp2_session *session;
  int32_t stream_id;
  valk_aio_http_conn *conn;
  valk_mem_arena_t *stream_arena;
  valk_lenv_t *env;
} http_future_ctx_t;

static void __http_future_response_cb(valk_lval_t* result, void* ctx) {
  http_future_ctx_t* http_ctx = (http_future_ctx_t*)ctx;

  // Queue response for event loop thread
  // (Future might resolve from different thread)
  valk_http_queue_response(http_ctx->conn->response_queue,
                           result, http_ctx->stream_id, http_ctx->stream_arena);

  // Signal event loop
  uv_async_send(&http_ctx->conn->response_async);
}
```

#### 2.3 Response Queue Processing

**File: `src/aio_uv.c` (new async handler)**
```c
static void __http_response_queue_cb(uv_async_t* handle) {
  valk_aio_http_conn* conn = (valk_aio_http_conn*)handle->data;

  pthread_mutex_lock(&conn->response_queue.mutex);
  while (conn->response_queue.count > 0) {
    http_queued_response_t* item = &conn->response_queue.items[--conn->response_queue.count];

    __http_send_response(conn->session, item->stream_id,
                         item->response, item->stream_arena);
  }
  pthread_mutex_unlock(&conn->response_queue.mutex);

  __http_continue_pending_send(conn);
}
```

---

### Phase 3: Async/Await Sugar

**Goal:** Clean syntax using existing shift/reset

#### 3.1 Async Macro

**File: `lib/std/async.valk` (new file)**
```lisp
; async: Establish async context, auto-lift result to Future
(def {async} (macro {body} {
  (async-reset {
    (future/pure (eval body))
  })
}))

; await: Suspend until future resolves
(def {await} (macro {future-expr} {
  (async-shift {k}
    (future/on-complete (eval future-expr)
      (fn [result]
        (if (future/failed? result)
          (k (future/reject (future/new) result))
          (k (future/value result))))))
}))
```

#### 3.2 Monadic Operators

**File: `lib/std/async.valk`**
```lisp
; >>= : Monadic bind (flatMap chain)
; (>>= future f1 f2 f3 ...)
(def {>>=} (fn {future . fns} {
  (fold (fn {f fn} {(future/flat-map f fn)}) future fns)
}))

; >> : Sequence, ignore intermediate results
; (>> future1 future2 future3)
(def {>>} (fn {. futures} {
  (fold (fn {f1 f2} {(future/flat-map f1 (fn [_] {f2}))})
        (head futures) (tail futures))
}))

; <$> : Map (functor)
; (<$> fn future)
(def {<$>} (fn {fn future} {(future/map future fn)}))

; <*> : Applicative apply
; (<*> fn-future arg-future)
(def {<*>} (fn {fn-future arg-future} {
  (future/flat-map fn-future
    (fn [f] {(future/map arg-future f)}))
}))
```

#### 3.3 Collection Operations

**File: `lib/std/async.valk`**
```lisp
; future/all : Wait for all futures, collect results as list
(def {future/all} (fn {futures} {
  (if (nil? futures)
    (future/pure '())
    (future/flat-map (head futures)
      (fn [x] {
        (future/map (future/all (tail futures))
          (fn [xs] {(cons x xs)}))
      })))
}))

; future/race : Return first future to resolve
(def {future/race} (fn {futures} {
  (let [result (future/new)]
    (do
      (each (fn [f] {
        (future/on-complete f
          (fn [v] {(future/resolve result v)}))
      }) futures)
      result))
}))

; future/sequence : Run futures in sequence
(def {future/sequence} (fn {futures} {
  (future/all futures)  ; Already sequential due to flatMap
}))
```

---

### Phase 4: HTTP Client Integration

**Goal:** HTTP/2 client returns Futures

#### 4.1 Async HTTP Client

**File: `src/aio_uv.c` (modify http2/fetch)**
```c
// http2/fetch-async: (http2/fetch-async url) -> Future<Response>
static valk_lval_t* valk_builtin_http2_fetch_async(valk_lenv_t* e, valk_lval_t* a) {
  valk_lval_t* url = valk_lval_list_nth(a, 0);

  // Create future for response
  valk_lval_t* future = valk_future_new();

  // Start HTTP/2 connection with callback that resolves future
  valk_http2_client_request(sys, url->str,
    (valk_http2_callback_t){
      .on_response = __http2_future_response_cb,
      .ctx = future
    });

  return future;
}
```

#### 4.2 Usage Example

```lisp
(def {fetch-user-posts} (fn [user-id] {
  (async
    (let [user (await (http2/fetch-async
                        (str "https://api.example.com/users/" user-id)))]
      (let [posts (await (http2/fetch-async
                           (str "https://api.example.com/users/" user-id "/posts")))]
        {:user user :posts posts})))
}))

; Or using >>=
(def {fetch-user-posts} (fn [user-id] {
  (>>= (http2/fetch-async (str "https://api.example.com/users/" user-id))
       (fn [user] {
         (future/map
           (http2/fetch-async (str "https://api.example.com/users/" user-id "/posts"))
           (fn [posts] {{:user user :posts posts}}))
       }))
}))
```

---

### Phase 5: Error Handling

#### 5.1 Try/Recover Pattern

**File: `lib/std/async.valk`**
```lisp
; future/try : Catch errors, return Either-like result
(def {future/try} (fn {future} {
  (future/map future (fn [v] {{:ok v}}))
  |> (fn [f] {(future/recover f (fn [e] {{:err e}}))})
}))

; future/recover : Handle failure with fallback
(def {future/recover} (fn {future fallback-fn} {
  (let [result (future/new)]
    (do
      (future/on-complete future
        (fn [v] {
          (if (future/failed? v)
            (future/resolve result (fallback-fn v))
            (future/resolve result v))
        }))
      result))
}))

; future/ensure : Always run cleanup
(def {future/ensure} (fn {future cleanup-fn} {
  (future/on-complete future (fn [_] {(cleanup-fn)}))
  future
}))
```

#### 5.2 Timeout Support

**File: `lib/std/async.valk`**
```lisp
; future/timeout : Fail if not resolved within ms
(def {future/timeout} (fn {future ms} {
  (future/race
    (list future
          (>>= (aio/delay-future sys ms)
               (fn [_] {(future/reject (future/new) "Timeout")}))))
}))
```

---

## Task Breakdown

### Milestone 1: Core Future Type (Est. complexity: Medium)

| Task | Files | Description |
|------|-------|-------------|
| 1.1 | `parser.h` | Add `LVAL_FUTURE` enum value |
| 1.2 | `parser.h` | Add future struct to union |
| 1.3 | `parser.c` | Implement `valk_future_new()` |
| 1.4 | `parser.c` | Implement `future/pure` builtin |
| 1.5 | `parser.c` | Implement `future/resolve` builtin |
| 1.6 | `parser.c` | Implement `future/reject` builtin |
| 1.7 | `parser.c` | Implement `future?` predicate |
| 1.8 | `gc.c` | Add `LVAL_FUTURE` to GC marking |
| 1.9 | `parser.c` | Add future print format |
| 1.10 | `test/test_futures.c` | Unit tests for core future ops |

### Milestone 2: Future Combinators (Est. complexity: Medium)

| Task | Files | Description |
|------|-------|-------------|
| 2.1 | `parser.c` | Implement `future/map` |
| 2.2 | `parser.c` | Implement `future/flat-map` |
| 2.3 | `parser.c` | Implement `future/on-complete` |
| 2.4 | `parser.c` | Implement `future/recover` |
| 2.5 | `parser.c` | Implement `future/failed?` |
| 2.6 | `parser.c` | Implement `future/value` |
| 2.7 | `lib/std/async.valk` | Implement `>>=` macro |
| 2.8 | `lib/std/async.valk` | Implement `future/all` |
| 2.9 | `lib/std/async.valk` | Implement `future/race` |
| 2.10 | `test/test_futures.valk` | Lisp tests for combinators |

### Milestone 3: Async/Await Sugar (Est. complexity: Low)

| Task | Files | Description |
|------|-------|-------------|
| 3.1 | `lib/std/async.valk` | Implement `async` macro |
| 3.2 | `lib/std/async.valk` | Implement `await` macro |
| 3.3 | `parser.c` | Integrate with existing shift/reset |
| 3.4 | `test/test_async.valk` | Tests for async/await |

### Milestone 4: Webserver Integration (Est. complexity: High)

| Task | Files | Description |
|------|-------|-------------|
| 4.1 | `aio_uv.c` | Add future detection in handler response |
| 4.2 | `aio_uv.c` | Add response queue structure |
| 4.3 | `aio_uv.c` | Add uv_async_t for queue signals |
| 4.4 | `aio_uv.c` | Implement `__http_register_future_response` |
| 4.5 | `aio_uv.c` | Implement `__http_response_queue_cb` |
| 4.6 | `aio_uv.c` | Thread-safe future resolution |
| 4.7 | `examples/webserver_demo.valk` | Update to use futures |
| 4.8 | `test/test_networking.c` | Integration tests |

### Milestone 5: HTTP Client Futures (Est. complexity: Medium)

| Task | Files | Description |
|------|-------|-------------|
| 5.1 | `aio_uv.c` | Implement `http2/fetch-async` |
| 5.2 | `aio_uv.c` | Wire HTTP/2 callbacks to future resolution |
| 5.3 | `examples/` | Add async HTTP client example |
| 5.4 | `test/test_http_client.valk` | Client integration tests |

---

## Design Decisions Required

### Decision 1: Threading Model

> **How should futures be resolved across threads?**

| Option | Description | Complexity |
|--------|-------------|------------|
| **A: Event loop only** | All futures resolve in libuv thread | Low |
| **B: Multi-thread with queue** | Futures can resolve anywhere, queue to event loop | Medium |
| **C: Thread-local futures** | Each thread has its own future pool | High |

**Recommendation:** Option B - Matches current architecture, enables true async

### Decision 2: Memory Management

> **Where should pending future callbacks be stored?**

| Option | Description | Trade-off |
|--------|-------------|-----------|
| **A: GC heap** | Callbacks in GC heap, marked during collection | Simple, may cause leaks if future never resolves |
| **B: Malloc heap** | Callbacks on malloc, manual free on resolve | Manual memory, but predictable |
| **C: Hybrid** | Future on GC, callbacks on malloc | Complex but optimal |

**Recommendation:** Option A for simplicity, with timeout to prevent leaks

### Decision 3: Error Propagation

> **How should errors propagate through future chains?**

| Option | Description | Behavior |
|--------|-------------|----------|
| **A: Short-circuit** | First error stops chain, propagates to end | Like Scala Future |
| **B: Collect errors** | Continue chain, collect all errors | Like Promise.allSettled |
| **C: Either type** | Each step returns `{:ok val}` or `{:err e}` | Explicit handling |

**Recommendation:** Option A for default, Option C available via `future/try`

### Decision 4: Cancellation Support

> **Should futures support cancellation?**

| Option | Description | Complexity |
|--------|-------------|------------|
| **A: No cancellation** | Once started, futures complete or fail | Low |
| **B: Cooperative cancellation** | Check cancellation flag periodically | Medium |
| **C: Interrupt-based** | Cancel pending I/O operations | High |

**Recommendation:** Option A initially, add B later if needed

---

## Migration Path

### Backward Compatibility

The existing `:deferred` pattern will continue to work:

```lisp
; OLD - still works
(aio/delay sys 2000 (\ {} {{:status "200" :body "..."}}))

; NEW - preferred
(>>= (aio/delay-future sys 2000)
     (fn [_] {:status "200" :body "..."}))
```

### Deprecation Timeline

1. **Phase 1:** Add futures alongside `:deferred`
2. **Phase 2:** Add deprecation warning to `aio/delay` callback form
3. **Phase 3:** Remove callback form, keep only future form

---

## Example: Complete Handler

```lisp
(def {api-handler} (fn [req sys] {
  (let [path (req :path)]
    (select
      ; Immediate response
      {(== path "/health")
       {:status "200" :body "OK"}}

      ; Async with future chain
      {(== path "/user/:id")
       (let [id (path-param path ":id")]
         (>>= (db/query-async sys (str "SELECT * FROM users WHERE id = " id))
              (fn [user]
                (if (nil? user)
                  {:status "404" :body "Not found"}
                  {:status "200" :body (json-encode user)}))))}

      ; Async with await syntax
      {(== path "/dashboard")
       (async
         (let [user (await (auth/validate-token (req :headers "Authorization")))]
           (let [stats (await (analytics/get-stats user))]
             (let [notifications (await (notifications/get-unread user))]
               {:status "200"
                :body (json-encode {:user user
                                    :stats stats
                                    :notifications notifications})}))))}

      ; Fallback
      {otherwise
       {:status "404" :body "Not found"}}))
}))
```

---

## References

### Existing Code

| File | Lines | Description |
|------|-------|-------------|
| `src/parser.h` | 49, 105-109 | Current LVAL_CONT type |
| `src/parser.c` | 3095-3282 | async-shift, async-reset, async-resume |
| `src/aio_uv.c` | 1302-1330 | Handler response check |
| `src/aio_uv.c` | 3143-3240 | aio/delay implementation |
| `src/async_monadic.valk` | 1-332 | Existing monadic combinators |
| `src/concurrency.h` | 126-158 | Existing C future type |

### External References

- [Finagle Futures](https://twitter.github.io/finagle/guide/Futures.html)
- [Scala Futures](https://docs.scala-lang.org/overviews/core/futures.html)
- [Racket Delimited Continuations](https://docs.racket-lang.org/reference/cont.html)
