# Phase 0.2: Async/Await in Lisp - Implementation Plan

**Status**: Planning
**Started**: 2025-11-13
**Prerequisites**: ✅ Phase 0.1 (TCO) complete

---

## Overview

Expose the existing C-level futures/promises infrastructure to Lisp, enabling async/await programming patterns for non-blocking I/O and concurrent operations.

## Existing Infrastructure (Already Built)

### C-Level Concurrency (src/concurrency.h/c)
- ✅ **valk_future** - Async computation result (lines 126-144)
  - Thread-safe with mutex/cond var
  - ARC reference counting
  - Supports `andThen` callbacks for chaining
  - `valk_future_await()` blocks until resolved
  - `valk_future_await_timeout()` with timeout support

- ✅ **valk_promise** - Write side of future (line 154-156)
  - `valk_promise_respond()` resolves the future
  - One-shot: can only resolve once

- ✅ **valk_arc_box** - Thread-safe value container (lines 102-113)
  - Generic container for any data
  - Atomic reference counting
  - Can hold success (`VALK_SUC`) or error (`VALK_ERR`)

- ✅ **valk_worker_pool** - Thread pool with work queue (lines 196-203)
  - 4 workers by default (`VALK_NUM_WORKERS`)
  - `valk_schedule()` submits async work
  - Returns future immediately
  - Workers execute tasks in background

### Async I/O Integration (src/aio_*.c)
- ✅ HTTP/2 operations return futures
  - `valk_aio_http2_request_send()` returns future
  - `valk_aio_read_file()` returns future
  - All I/O is non-blocking

---

## Implementation Plan

### Phase 1: Add LVAL_FUTURE Type

**Files**: `src/parser.h`, `src/parser.c`

#### 1.1 Type Definition
Add to `valk_ltype_e` enum (parser.h):
```c
typedef enum {
  // ... existing types ...
  LVAL_FUTURE,  // Async computation result
} valk_ltype_e;
```

Add to `valk_lval_t` union (parser.h):
```c
struct {
  valk_future* future;  // Pointer to C future
} fut;
```

#### 1.2 Constructor
```c
valk_lval_t* valk_lval_future(valk_future* future) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_FUTURE | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(res);
  res->fut.future = future;
  valk_arc_retain(future);  // Retain the future
  return res;
}
```

#### 1.3 Type Operations
Update:
- `valk_lval_copy()` - retain future
- `valk_lval_eq()` - compare future pointers
- `valk_ltype_name()` - return "Future"
- `valk_lval_print()` - print `<Future:pending>` or `<Future:resolved>`
- `valk_lval_delete()` - release future

---

### Phase 2: Builtin Functions for Futures

**Files**: `src/parser.c`

#### 2.1 `(future body)` - Create Future
```lisp
(future (+ 1 2))  ; Returns immediately with future
```

**Implementation**:
```c
valk_lval_t* valk_builtin_future(valk_lenv_t* env, valk_lval_t* args) {
  // Validate: (future body)
  LVAL_ASSERT_ARG_COUNT("future", args, 1);

  valk_lval_t* body = valk_lval_list_nth(args, 0);

  // Create task to evaluate body
  // Need to capture: env, body
  // Submit to worker pool
  // Return LVAL_FUTURE immediately

  // TODO: How to pass Lisp environment to worker thread?
  // Option A: Copy environment (slow)
  // Option B: Make environment thread-safe (complex)
  // Option C: Evaluate in main thread but return future (defeats purpose)
}
```

**Challenge**: Worker threads need access to Lisp environment for evaluation.

**Proposed Solution**:
- Make `valk_lenv_t` thread-safe with read-write locks
- Or: Only allow futures for pre-defined async operations (HTTP, file I/O)
- Or: Evaluate body immediately but wrap result in future (simpler, less useful)

#### 2.2 `(await future)` - Block Until Resolved
```lisp
(def {result} (await my-future))
```

**Implementation**:
```c
valk_lval_t* valk_builtin_await(valk_lenv_t* env, valk_lval_t* args) {
  LVAL_ASSERT_ARG_COUNT("await", args, 1);

  valk_lval_t* fut_lval = valk_lval_list_nth(args, 0);
  LVAL_ASSERT_TYPE("await", fut_lval, 0, LVAL_FUTURE);

  valk_future* fut = fut_lval->fut.future;

  // Block until future resolves
  valk_arc_box* result = valk_future_await(fut);

  // Convert arc_box back to lval_t
  // How to store result in arc_box? Need bridge function
  if (result->type == VALK_ERR) {
    return valk_lval_err((char*)result->item);
  } else {
    // Extract valk_lval_t* from result->item
    return (valk_lval_t*)result->item;
  }
}
```

**Challenge**: Need to store `valk_lval_t*` in `valk_arc_box` for interop.

#### 2.3 `(then future callback)` - Chain Futures
```lisp
(then my-future (\ {result} {(print result)}))
```

**Implementation**:
```c
valk_lval_t* valk_builtin_then(valk_lenv_t* env, valk_lval_t* args) {
  LVAL_ASSERT_ARG_COUNT("then", args, 2);

  valk_lval_t* fut_lval = valk_lval_list_nth(args, 0);
  valk_lval_t* callback = valk_lval_list_nth(args, 1);

  LVAL_ASSERT_TYPE("then", fut_lval, 0, LVAL_FUTURE);
  LVAL_ASSERT_TYPE("then", callback, 1, LVAL_FUN);

  // Register callback with future
  struct valk_future_and_then cb = {
    .arg = callback,  // Lisp function
    .cb = lisp_callback_wrapper  // C wrapper that calls Lisp function
  };

  valk_future_and_then(fut_lval->fut.future, &cb);

  return valk_lval_nil();
}

// Wrapper that calls Lisp function from C
void lisp_callback_wrapper(void* arg, valk_arc_box* result) {
  valk_lval_t* callback = (valk_lval_t*)arg;
  valk_lval_t* lval_result = arc_box_to_lval(result);

  // Call Lisp function with result
  // valk_lval_call(callback, lval_result);
  // Problem: Need environment! Which environment?
}
```

**Challenge**: Callbacks need environment reference.

---

### Phase 3: Integration with Existing Async I/O

#### 3.1 HTTP Requests Return Futures
Modify `valk_builtin_http2_request_send()` to return `LVAL_FUTURE`:

```c
valk_lval_t* valk_builtin_http2_request_send(...) {
  // ... existing code ...

  valk_future* future = valk_aio_http2_request_send(client, request);

  // Wrap C future in Lisp future
  return valk_lval_future(future);
}
```

Usage:
```lisp
(def {response-future} (http2/request-send client request))
(def {response} (await response-future))
(print (http2/response-body response))
```

#### 3.2 File I/O Returns Futures
```lisp
(def {content-future} (file/read "data.txt"))
(def {content} (await content-future))
(print content)
```

---

## Design Decisions & Trade-offs

### Decision 1: Environment Threading
**Problem**: Worker threads need access to Lisp environment for evaluation.

**Options**:
1. **Make environment thread-safe** (RWLock on all env operations)
   - Pro: Full async evaluation of arbitrary code
   - Con: Complex, performance overhead

2. **Copy environment for each task**
   - Pro: Simpler, thread-safe by default
   - Con: Expensive, doesn't see global updates

3. **Restrict futures to pre-defined async operations**
   - Pro: Simple, just wrap existing C futures
   - Con: Can't do `(future (+ 1 2))`, only `(future (http/get url))`

**Recommendation**: Start with **Option 3**. Expose existing async I/O as futures, defer general `(future body)` to later.

### Decision 2: Await Behavior
**Problem**: Should `await` block the REPL?

**Options**:
1. **Block current thread** (simple)
   - Pro: Simple implementation
   - Con: REPL hangs during await

2. **Integrate with libuv event loop** (complex)
   - Pro: Non-blocking REPL
   - Con: Requires scheduler, event loop integration

**Recommendation**: Start with **Option 1**. Blocking is fine for scripts. REPL integration can come later.

### Decision 3: Arc Box ↔ Lval Bridge
**Problem**: C futures use `valk_arc_box`, Lisp uses `valk_lval_t`.

**Solution**: Store `valk_lval_t*` directly in arc_box:
```c
valk_arc_box* lval_to_arc_box(valk_lval_t* lval) {
  valk_arc_box* box = valk_arc_box_new(VALK_SUC, sizeof(valk_lval_t*));
  *(valk_lval_t**)box->item = lval;
  valk_retain(lval);  // Keep lval alive
  return box;
}

valk_lval_t* arc_box_to_lval(valk_arc_box* box) {
  if (box->type == VALK_ERR) {
    return valk_lval_err((char*)box->item);
  }
  return *(valk_lval_t**)box->item;
}
```

---

## Minimal Viable Implementation (MVP)

### Scope
1. ✅ Add `LVAL_FUTURE` type
2. ✅ `(await future)` builtin - blocks until resolved
3. ✅ Modify HTTP builtins to return futures
4. ❌ Defer: `(future body)` - general async evaluation
5. ❌ Defer: `(then future callback)` - chaining
6. ❌ Defer: `(async fn)` - async function marker

### Validation Test
```lisp
; Test: Async HTTP request
(def {client} (http2/connect aio "httpbin.org" 443))
(def {req} (http2/request :method "GET" :path "/get"))

(def {response-future} (http2/request-send client req))
(print "Request sent, waiting...")

(def {response} (await response-future))
(print "Response received:")
(print (http2/response-status response))
(print (http2/response-body response))
```

**Expected**:
- Request sent immediately (non-blocking)
- `await` blocks until response arrives
- Response printed successfully

---

## Implementation Checklist

### Phase 1: Type Infrastructure
- [ ] Add `LVAL_FUTURE` to `valk_ltype_e` enum
- [ ] Add `fut` field to `valk_lval_t` union
- [ ] Implement `valk_lval_future()` constructor
- [ ] Update `valk_lval_copy()` for futures
- [ ] Update `valk_lval_eq()` for futures
- [ ] Update `valk_ltype_name()` for futures
- [ ] Update `valk_lval_print()` for futures
- [ ] Update `valk_lval_delete()` for futures

### Phase 2: Builtin Functions
- [ ] Implement `valk_builtin_await()`
- [ ] Add arc_box ↔ lval bridge functions
- [ ] Register `await` in builtin environment

### Phase 3: HTTP Integration
- [ ] Modify `valk_builtin_http2_request_send()` to return future
- [ ] Test with httpbin.org
- [ ] Verify non-blocking behavior

### Phase 4: Documentation
- [ ] Update `IMPLEMENTATION_CHECKLIST.md` with progress
- [ ] Add examples to `docs/ASYNC_EXAMPLES.md`
- [ ] Document limitations (no general `future`, blocks REPL)

---

## Future Work (Post-MVP)

### General Async Evaluation
- Make `valk_lenv_t` thread-safe with RWLock
- Implement `(future body)` for arbitrary expressions
- Copy/capture environment for worker threads

### Callback Chaining
- Implement `(then future callback)`
- Solve environment capture for callbacks
- Support callback chains: `(then (then fut cb1) cb2)`

### Async Functions
- `(async fn)` syntax to mark async functions
- Automatic future wrapping of return values
- Static checking: `await` only in async context

### Promise Combinators (Phase 0.3)
- `(promise/all futures)` - wait for all
- `(promise/race futures)` - first one wins
- `(promise/map fn futures)` - map over futures
- `(promise/timeout ms future)` - timeout wrapper

### REPL Integration
- Integrate with libuv event loop
- Non-blocking `await` in REPL
- Show "waiting..." indicator during await

---

## Timeline Estimate

**MVP**: 2-3 days
- Day 1: Type infrastructure + builtin functions
- Day 2: HTTP integration + testing
- Day 3: Bug fixes + documentation

**Full Phase 0.2**: 1 week
- MVP: 3 days
- General futures: 2 days
- Callback chaining: 2 days

**Phase 0.3** (Promise combinators): 3-4 days

---

## Files to Modify

**New Files**:
- `docs/ASYNC_AWAIT_PLAN.md` (this file)
- `docs/ASYNC_EXAMPLES.md` (usage examples)
- `test/test_async.valk` (test cases)

**Modified Files**:
- `src/parser.h` - Add LVAL_FUTURE type
- `src/parser.c` - Add constructor, builtin functions, type operations
- `src/aio_uv.c` (maybe) - If HTTP functions need modification
- `docs/IMPLEMENTATION_CHECKLIST.md` - Mark tasks complete
- `docs/SESSION_NOTES.md` - Document progress

---

**Last Updated**: 2025-11-13
**Status**: Planning complete, ready to implement MVP
**Next Step**: Add LVAL_FUTURE type to parser.h
