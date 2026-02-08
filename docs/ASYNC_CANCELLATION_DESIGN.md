# Async Cancellation Design: Finagle-Style Future/Promise Graph

## Executive Summary

This document describes the redesign of Valkyria's async handle cancellation system. The current `is_closed` callback mechanism is fundamentally flawed - it's a passive polling approach that creates race conditions and use-after-free bugs.

**Key Design Principles:**

1. **Futures/Promises are GC-managed** - Allocated via TLAB/parallel GC, not refcounted
2. **Cancellation propagates through the async graph** - Not tied to HTTP/IO layers
3. **Iterative (non-recursive) callbacks** - Stack-safe processing of large graphs
4. **Cross-system graphs** - Futures may span multiple AIO systems
5. **Cooperative cancellation** - Workers poll cancellation status periodically

---

## Table of Contents

1. [Requirements](#1-requirements)
2. [Current Architecture Problems](#2-current-architecture-problems)
3. [Proposed Architecture](#3-proposed-architecture)
4. [Data Structure Changes](#4-data-structure-changes)
5. [API Reference](#5-api-reference)
6. [Cancellation Flow](#6-cancellation-flow)
7. [Implementation Plan](#7-implementation-plan)
8. [Test Plan](#8-test-plan)

---

## 1. Requirements

### 1.1 Functional Requirements

| ID | Requirement | Priority |
|----|-------------|----------|
| FR-1 | Calling `cancel` on a Future immediately transitions it to `:cancelled` state | Must |
| FR-2 | Cancellation propagates DOWN to the Promise (or combinator) that created the Future | Must |
| FR-3 | Combinators (`aio/all`, `aio/race`, `aio/then`) cancel their child operations when cancelled | Must |
| FR-4 | Workers (timers, HTTP, IO) poll their Promise's cancellation status cooperatively | Must |
| FR-5 | `on_cancel` callbacks execute when a handle transitions to cancelled | Must |
| FR-6 | Resources associated with cancelled handles are cleaned up | Must |
| FR-7 | Futures/Promises can span multiple AIO systems | Should |
| FR-8 | HTTP layer cancels async graph when connection/stream closes | Must |
| FR-9 | Cancelled operations do not invoke success/error callbacks | Must |

### 1.2 Non-Functional Requirements

| ID | Requirement | Priority |
|----|-------------|----------|
| NFR-1 | No use-after-free bugs | Must |
| NFR-2 | No memory leaks on cancellation | Must |
| NFR-3 | Callback processing must be iterative (no recursion) | Must |
| NFR-4 | Async handles allocated via GC heap with TLAB fast path | Should |
| NFR-5 | Cancellation check is O(1) atomic load | Must |
| NFR-6 | Thread-safe cancellation from any thread | Should |

### 1.3 Constraints

| ID | Constraint |
|----|------------|
| C-1 | Single-threaded event loop per AIO system |
| C-2 | Multiple AIO systems may exist concurrently |
| C-3 | Lisp callbacks execute on event loop thread |
| C-4 | GC may run during async operation |

---

## 2. Current Architecture Problems

### 2.1 Race Conditions Identified

| ID | Issue | Severity | Location |
|----|-------|----------|----------|
| RACE-1 | `cancel_requested` was `int`, not `_Atomic int` | Fixed | `aio.h:28` |
| RACE-2 | `is_closed_ctx` freed while other handles reference it | Critical | `aio_async.c:35-110` |
| RACE-3 | Children array mutated during iteration | High | `aio_combinators.c:697` |
| RACE-4 | `is_closed` check without memory barriers | Medium | `aio_async.c:13-22` |

### 2.2 Use-After-Free Vulnerabilities

| ID | Issue | Location |
|----|-------|----------|
| UAF-1 | Children point to freed parent | `aio_async.c:185-193` |
| UAF-2 | HTTP context used after connection close | `aio_async.c:35-110` |
| UAF-3 | Combinator contexts never freed | `aio_combinators.c:1151-1159` |
| UAF-4 | Parent freed while children still running | Various |

### 2.3 Root Cause: Passive "Is Closed" Polling

The current design uses `is_closed` callback to **poll** whether a resource is dead:

```c
// Current: PASSIVE polling (BROKEN)
bool valk_async_is_resource_closed(valk_async_handle_t *handle) {
  if (handle->is_closed) {
    return handle->is_closed(handle->is_closed_ctx);  // May access freed memory!
  }
  return false;
}
```

Problems:
- **Reactive, not proactive** - Waits for caller to check
- **Shared context** - Multiple handles share same `is_closed_ctx` pointer
- **No ownership** - Unclear who frees the context and when
- **Race window** - Context can be freed between check and use

### 2.4 Recursive Callback Processing

The current `valk_async_propagate_completion` uses recursion:

```c
// Current: RECURSIVE (stack overflow risk)
void valk_async_propagate_completion(valk_async_handle_t *source) {
  for (u64 i = 0; i < source->children.count; i++) {
    // ... process child ...
    valk_async_propagate_completion(child);  // RECURSIVE!
  }
}
```

Deep async graphs can overflow the stack.

---

## 3. Proposed Architecture

### 3.1 Finagle-Style Future/Promise Model

```
User code:
  (aio/then (http/request ...)
    (lambda (resp)
      (aio/delay 1000 (lambda () ...))))

Graph structure:
  
  Future[http-response] ──────► Future[delay] ──────► Future[result]
         │                           │                     │
         ▼                           ▼                     ▼
     Promise A                   Promise B             Promise C
    (http layer)               (timer layer)          (user code)
```

**Key insight:** The `valk_async_handle_t` represents BOTH the Future (consumer-facing) and Promise (producer-facing) in one struct. The `parent/children` links form the graph.

### 3.2 Cancellation Flow

```
1. External trigger (e.g., HTTP connection closes)
   │
   ▼
2. HTTP layer calls: valk_async_handle_cancel(root_handle)
   │
   ├──► Sets cancel_requested = 1 (atomic)
   ├──► Sets status = CANCELLED
   ├──► Adds to work queue for iterative processing
   │
   ▼
3. Work queue processes children iteratively (no recursion)
   │
   ├──► Each child: set cancel_requested, add children to queue
   ├──► Stop any libuv timers/handles
   ├──► Invoke on_cancel Lisp callbacks
   │
   ▼
4. Workers check cancel_requested before doing work
   │
   └──► If cancelled, clean up and exit early
```

### 3.3 Memory Management Strategy

**Current (broken):**
- Handles allocated with `malloc()`
- Manual `free()` in various callbacks
- `is_closed_ctx` shared and races

**Proposed:**
- Handles allocated via GC heap with TLAB fast path
- GC traces async graph from roots (active operations, event loop)
- No manual free - GC reclaims when unreachable
- Cleanup callbacks for non-GC resources (timers, file handles)

```c
// Allocation path
valk_async_handle_t *handle = valk_gc_heap2_alloc(heap, sizeof(valk_async_handle_t));

// GC roots include:
// - Active async handles registered with event loop
// - HTTP request contexts
// - Timer callbacks
```

### 3.4 Cross-System Graph Support

Futures may span multiple AIO systems:

```
AIO System A (main server)        AIO System B (background worker)
┌─────────────────────┐          ┌─────────────────────────────┐
│ Future[http-req]    │──────────│► Future[db-query]           │
│   └─► on_done       │          │    └─► on_complete          │
└─────────────────────┘          └─────────────────────────────┘
```

The async handle graph is independent of AIO systems. Each handle stores its `loop` pointer for scheduling callbacks, but cancellation works across systems.

---

## 4. Data Structure Changes

### 4.1 Modified `valk_async_handle_t`

```c
struct valk_async_handle_t {
  // === IDENTIFICATION ===
  u64 id;
  valk_async_status_t status;

  // === CANCELLATION (atomic for cross-thread safety) ===
  _Atomic int cancel_requested;

  // === EVENT LOOP BINDING ===
  void *uv_handle_ptr;    // libuv timer/handle if any
  void *loop;             // Which event loop this runs on (may be NULL)

  // === LISP CALLBACKS ===
  struct valk_lval_t *on_complete;
  struct valk_lval_t *on_error;
  struct valk_lval_t *on_cancel;
  struct valk_lenv_t *env;

  // === RESULT ===
  struct valk_lval_t *result;
  struct valk_lval_t *error;

  // === MEMORY ===
  valk_mem_allocator_t *allocator;  // For Lisp value allocation

  // === COMPLETION NOTIFICATION ===
  valk_async_done_fn on_done;       // C callback when terminal
  void *on_done_ctx;

  // === GRAPH STRUCTURE ===
  struct valk_async_handle_t *parent;
  struct {
    struct valk_async_handle_t **items;
    u64 count;
    u64 capacity;
  } children;

  // === LINKED LIST (for event loop tracking) ===
  struct valk_async_handle_t *prev;
  struct valk_async_handle_t *next;

  // === CLEANUP (for non-GC resources) ===
  struct {
    valk_async_cleanup_fn fn;
    void *ctx;
  } *cleanup_callbacks;
  u32 cleanup_count;
  u32 cleanup_capacity;

  // === REMOVED ===
  // valk_async_is_closed_fn is_closed;    // REMOVED - use cancel_requested
  // void *is_closed_ctx;                   // REMOVED
};
```

### 4.2 Work Queue for Iterative Processing

```c
// Work queue for non-recursive graph traversal
typedef struct valk_async_work_queue {
  valk_async_handle_t **items;
  u64 head;
  u64 tail;
  u64 capacity;
} valk_async_work_queue_t;

// Thread-local work queue (reused across operations)
extern _Thread_local valk_async_work_queue_t valk_async_work_queue;
```

### 4.3 Removed Types

```c
// REMOVE from aio_types.h:
// typedef bool (*valk_async_is_closed_fn)(void *ctx);  // REMOVED
```

---

## 5. API Reference

### 5.1 Cancellation

```c
// Cancel handle and all descendants (iterative, non-recursive)
// Returns: true if cancellation was initiated, false if already terminal
bool valk_async_handle_cancel(valk_async_handle_t *handle);

// Fast cancellation check (inline, atomic)
static inline bool valk_async_handle_is_cancelled(valk_async_handle_t *handle) {
  if (!handle) return false;
  return atomic_load_explicit(&handle->cancel_requested, memory_order_acquire) != 0;
}
```

### 5.2 Cleanup Registration

```c
// Register cleanup callback (runs when handle reaches terminal state)
// Multiple callbacks can be registered, run in LIFO order
// Used for non-GC resources: timers, file handles, HTTP contexts
void valk_async_handle_on_cleanup(valk_async_handle_t *handle,
                                   valk_async_cleanup_fn fn,
                                   void *ctx);
```

### 5.3 Completion (Iterative)

```c
// Complete handle and propagate (iterative, non-recursive)
void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);

// Fail handle and propagate (iterative, non-recursive)
void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
```

### 5.4 Graph Traversal

```c
// Initialize thread-local work queue
void valk_async_work_queue_init(void);

// Push handle to work queue
void valk_async_work_queue_push(valk_async_handle_t *handle);

// Pop handle from work queue (returns NULL if empty)
valk_async_handle_t *valk_async_work_queue_pop(void);

// Process work queue until empty
void valk_async_work_queue_drain(void);
```

---

## 6. Cancellation Flow

### 6.1 HTTP Connection Close

```
HTTP connection closes (TCP RST, timeout, client disconnect)
    │
    ▼
valk_http2_on_stream_close_callback(session, stream_id)
    │
    ├──► Get async handle from stream user data
    │
    ▼
valk_async_handle_cancel(handle)
    │
    ├──► atomic_store(&handle->cancel_requested, 1)
    ├──► handle->status = VALK_ASYNC_CANCELLED
    ├──► valk_async_work_queue_push(handle)  // Queue for processing
    │
    ▼
valk_async_work_queue_drain()  // Iterative processing
    │
    ├──► while (item = work_queue_pop()) {
    │        for each child:
    │            if (child->status is pending/running) {
    │                atomic_store(&child->cancel_requested, 1)
    │                child->status = CANCELLED
    │                stop_uv_handle(child)
    │                invoke_on_cancel_callback(child)
    │                work_queue_push(child)  // Process children next
    │            }
    │        run_cleanup_callbacks(item)
    │    }
    │
    ▼
All handles in subtree are cancelled, resources cleaned up
```

### 6.2 Timer Callback Cooperative Cancellation

```c
static void __timer_callback(uv_timer_t *handle) {
  valk_async_handle_t *async = get_handle_from_timer(handle);
  
  // Cooperative check: abort if cancelled
  if (valk_async_handle_is_cancelled(async)) {
    uv_timer_stop(handle);
    uv_close((uv_handle_t *)handle, __timer_close_cb);
    return;  // Don't invoke completion
  }
  
  // Normal completion path
  valk_async_handle_complete(async, valk_lval_nil());
}
```

### 6.3 Combinator Cancellation

When `aio/all` is cancelled:

```
aio/all handle cancelled
    │
    ├──► Set cancel_requested on all handle
    ├──► Set status = CANCELLED
    │
    ▼
For each child handle (via work queue):
    │
    ├──► Set cancel_requested
    ├──► Set status = CANCELLED
    ├──► Stop any timers
    ├──► Queue children for processing
    │
    ▼
All child operations are cancelled
```

---

## 7. Implementation Plan

### Phase 1: Core Infrastructure (COMPLETED)

- [x] Add `_Atomic int cancel_requested` to struct
- [x] Add cleanup callback array to struct
- [x] Add `valk_async_cleanup_fn` typedef
- [x] Implement `valk_async_handle_is_cancelled()` inline
- [x] Update `valk_async_handle_cancel()` to use atomic store

### Phase 2: Iterative Processing

- [ ] **2.1** Implement `valk_async_work_queue_t` with push/pop/drain
- [ ] **2.2** Refactor `valk_async_propagate_completion()` to use work queue
- [ ] **2.3** Refactor `valk_async_handle_cancel()` to use work queue
- [ ] **2.4** Update all recursive graph traversals

### Phase 3: Remove is_closed Mechanism

- [ ] **3.1** Remove `is_closed` and `is_closed_ctx` from struct
- [ ] **3.2** Remove `valk_async_is_resource_closed()` function
- [ ] **3.3** Remove `valk_http_async_is_closed_callback()` function
- [ ] **3.4** Remove `clear_is_closed_ctx_recursive()` function
- [ ] **3.5** Update all callers to use `valk_async_handle_is_cancelled()`
- [ ] **3.6** Remove `is_closed` propagation in combinators

### Phase 4: HTTP Layer Integration

- [ ] **4.1** Store async handle reference on `valk_http2_server_request_t`
- [ ] **4.2** In `on_stream_close`, call `valk_async_handle_cancel()`
- [ ] **4.3** In `on_connection_close`, cancel all stream handles
- [ ] **4.4** Register cleanup callbacks instead of `is_closed_ctx`
- [ ] **4.5** Remove `http_ctx` freeing from done callback (use cleanup)

### Phase 5: Timer/IO Cooperative Cancellation

- [ ] **5.1** Add cancellation check to `__sleep_timer_cb`
- [ ] **5.2** Add cancellation check to `__delay_timer_cb`
- [ ] **5.3** Add cancellation check to `__schedule_timer_cb`
- [ ] **5.4** Add cancellation check to HTTP client callbacks

### Phase 6: GC Integration (Future)

- [ ] **6.1** Allocate async handles from GC heap
- [ ] **6.2** Register async graph roots with GC
- [ ] **6.3** Remove manual `free()` calls
- [ ] **6.4** Update cleanup callbacks for GC compatibility

### Phase 7: Testing & Validation

- [ ] **7.1** Add unit tests per test plan
- [ ] **7.2** Run ASAN/UBSAN tests
- [ ] **7.3** Stress tests with connection churn
- [ ] **7.4** Memory leak detection

---

## 8. Test Plan

### 8.1 Unit Tests

| Test ID | Description | Validates |
|---------|-------------|-----------|
| UT-01 | Cancel pending handle, verify status | FR-1 |
| UT-02 | Cancel parent, verify children cancelled | FR-2, FR-3 |
| UT-03 | Cancel `aio/all`, verify all children cancelled | FR-3 |
| UT-04 | Cancel `aio/race`, verify all children cancelled | FR-3 |
| UT-05 | Timer checks cancellation, aborts early | FR-4 |
| UT-06 | `on_cancel` callback invoked on cancel | FR-5 |
| UT-07 | Cleanup callbacks run on cancellation | FR-6 |
| UT-08 | Cancel completed handle returns false | FR-1 |
| UT-09 | Cancel failed handle returns false | FR-1 |
| UT-10 | Deep graph (1000 nodes) processes iteratively | NFR-3 |
| UT-11 | Cancellation check is atomic | NFR-5 |
| UT-12 | Work queue handles large graphs | NFR-3 |

### 8.2 Integration Tests

| Test ID | Description | Validates |
|---------|-------------|-----------|
| IT-01 | HTTP connection close cancels pending handler | FR-8 |
| IT-02 | HTTP stream RST cancels stream handler | FR-8 |
| IT-03 | Client disconnect during async operation | FR-8 |
| IT-04 | GOAWAY cancels all stream handlers | FR-8 |
| IT-05 | Cancelled handler doesn't send response | FR-9 |
| IT-06 | Concurrent requests with some cancellations | NFR-1, NFR-2 |

### 8.3 ASAN/UBSAN Tests

| Test ID | Description | Validates |
|---------|-------------|-----------|
| AS-01 | No UAF on connection close | NFR-1 |
| AS-02 | No UAF on stream close | NFR-1 |
| AS-03 | No memory leaks after cancellation | NFR-2 |
| AS-04 | No leaks with deep async graphs | NFR-2 |
| AS-05 | No data races on cancellation | NFR-6 |

### 8.4 Stress Tests

| Test ID | Description | Duration |
|---------|-------------|----------|
| ST-01 | 1000 concurrent requests with random cancellations | 60s |
| ST-02 | Rapid connection open/close (100/s) | 60s |
| ST-03 | Deep async chains (100 levels) with cancellation | 30s |
| ST-04 | Mixed success/failure/cancel patterns | 60s |

### 8.5 Test Implementation Priority

1. **Phase 1:** UT-01, UT-08, UT-09 (basic cancellation)
2. **Phase 2:** UT-02, UT-10, UT-12 (iterative processing)
3. **Phase 3:** UT-03, UT-04, UT-05, UT-06, UT-07 (full cancellation)
4. **Phase 4:** IT-01 through IT-06 (HTTP integration)
5. **Phase 5:** AS-01 through AS-05, ST-01 through ST-04 (validation)

---

## Appendix A: Migration Guide

### A.1 Removing `is_closed_ctx` Usage

**Before:**
```c
handle->is_closed = valk_http_async_is_closed_callback;
handle->is_closed_ctx = http_ctx;
```

**After:**
```c
// Store handle reference on request for active cancellation
req->async_handle = handle;

// Register cleanup for http_ctx (runs on terminal state)
valk_async_handle_on_cleanup(handle, http_ctx_cleanup, http_ctx);
```

### A.2 Checking Cancellation

**Before:**
```c
if (valk_async_is_resource_closed(handle)) {
  // Handle closed
}
```

**After:**
```c
if (valk_async_handle_is_cancelled(handle)) {
  // Handle cancelled
}
```

### A.3 HTTP Stream Close Handler

**Before:**
```c
// No active cancellation - relies on polling is_closed
```

**After:**
```c
void on_stream_close(nghttp2_session *session, i32 stream_id) {
  valk_http2_server_request_t *req = get_stream_data(session, stream_id);
  if (req && req->async_handle) {
    valk_async_handle_cancel(req->async_handle);
    req->async_handle = NULL;
  }
}
```

---

## Appendix B: Work Queue Implementation

```c
#define VALK_ASYNC_WORK_QUEUE_INITIAL_CAPACITY 64

typedef struct valk_async_work_queue {
  valk_async_handle_t **items;
  u64 head;
  u64 tail;
  u64 capacity;
} valk_async_work_queue_t;

_Thread_local valk_async_work_queue_t valk_async_work_queue = {0};

void valk_async_work_queue_init(void) {
  if (valk_async_work_queue.items) return;
  valk_async_work_queue.items = malloc(
      VALK_ASYNC_WORK_QUEUE_INITIAL_CAPACITY * sizeof(valk_async_handle_t *));
  valk_async_work_queue.head = 0;
  valk_async_work_queue.tail = 0;
  valk_async_work_queue.capacity = VALK_ASYNC_WORK_QUEUE_INITIAL_CAPACITY;
}

void valk_async_work_queue_push(valk_async_handle_t *handle) {
  valk_async_work_queue_t *q = &valk_async_work_queue;
  
  // Grow if needed
  u64 size = q->tail - q->head;
  if (size >= q->capacity) {
    u64 new_cap = q->capacity * 2;
    valk_async_handle_t **new_items = malloc(new_cap * sizeof(valk_async_handle_t *));
    
    // Copy existing items
    for (u64 i = 0; i < size; i++) {
      new_items[i] = q->items[(q->head + i) % q->capacity];
    }
    
    free(q->items);
    q->items = new_items;
    q->head = 0;
    q->tail = size;
    q->capacity = new_cap;
  }
  
  q->items[q->tail % q->capacity] = handle;
  q->tail++;
}

valk_async_handle_t *valk_async_work_queue_pop(void) {
  valk_async_work_queue_t *q = &valk_async_work_queue;
  if (q->head >= q->tail) return NULL;
  
  valk_async_handle_t *handle = q->items[q->head % q->capacity];
  q->head++;
  
  // Reset indices if queue is empty (prevents unbounded growth)
  if (q->head == q->tail) {
    q->head = 0;
    q->tail = 0;
  }
  
  return handle;
}

void valk_async_work_queue_drain(void) {
  valk_async_handle_t *handle;
  while ((handle = valk_async_work_queue_pop()) != NULL) {
    // Process this handle's children
    for (u64 i = 0; i < handle->children.count; i++) {
      valk_async_handle_t *child = handle->children.items[i];
      if (child->status == VALK_ASYNC_PENDING || 
          child->status == VALK_ASYNC_RUNNING) {
        // Will be processed by caller's specific logic
        valk_async_work_queue_push(child);
      }
    }
  }
}
```

---

## Appendix C: Thread Safety Analysis

### C.1 Atomic Operations Required

| Field | Access Pattern | Memory Order |
|-------|----------------|--------------|
| `cancel_requested` | Read: any thread, Write: cancelling thread | Acquire/Release |
| `status` | Read/Write: event loop thread only | Relaxed |
| `children` | Read/Write: event loop thread only | N/A |

### C.2 Safe Cross-Thread Cancellation

Cancellation from a different thread (e.g., timeout thread) is safe because:

1. `cancel_requested` uses atomic store with release semantics
2. Event loop thread uses atomic load with acquire semantics
3. Status transitions only happen on event loop thread
4. libuv handles are only touched from event loop thread

```c
// Thread A (timeout):
atomic_store_explicit(&handle->cancel_requested, 1, memory_order_release);
uv_async_send(loop_wakeup);  // Wake event loop

// Thread B (event loop):
if (atomic_load_explicit(&handle->cancel_requested, memory_order_acquire)) {
  // Safe to access handle->status, stop timers, etc.
  handle->status = VALK_ASYNC_CANCELLED;
  uv_timer_stop(...);
}
```

---

## Appendix D: GC Integration Notes (Future)

When async handles are GC-managed:

1. **Root Registration:** Active handles registered with `valk_gc_add_global_root()`
2. **Tracing:** GC marks `parent`, `children`, `on_complete`, `on_error`, `on_cancel`, `result`, `error`
3. **Cleanup:** Non-GC resources (timers, file handles) use cleanup callbacks
4. **Finalization:** Cleanup callbacks run when GC determines handle is unreachable

```c
// Future allocation path
valk_async_handle_t *handle = valk_gc_heap2_alloc(heap, sizeof(valk_async_handle_t));

// Register as root while active
valk_gc_add_global_root((valk_lval_t **)&handle);

// When operation completes, unregister
valk_gc_remove_global_root((valk_lval_t **)&handle);
// GC will reclaim when unreachable
```
