# Explicit Context Passing Refactor

## Overview

This document describes the refactoring effort to remove implicit global state from the AIO system in preparation for compilation to LLVM. The goal is to make all context passing explicit, similar to Scala's implicit parameters that are resolved at compile time.

## Motivation

The original design used two globals:
- `valk_aio_active_system` - Set when AIO system starts, used everywhere
- `g_last_started_aio_system` - Fallback for async completion paths

Problems:
1. **Race conditions** - Multiple systems or concurrent requests could clobber context
2. **Hidden dependencies** - Functions silently depend on global state
3. **Compilation barrier** - LLVM codegen needs explicit data flow

## Completed Refactors

### Phase 1: Chase-Lev Work-Stealing Deque & Task Queue

Created unified task scheduling:
- `src/aio/aio_chase_lev.h` - Lock-free deque header
- `src/aio/aio_chase_lev.c` - Lock-free deque implementation
- `src/aio/aio_task_queue.c` - Task queue using Chase-Lev deque

### Phase 2: Unified Async Cancellation & Completion

- Removed thread-local work queue from `aio_async.c`
- `valk_async_handle_cancel()` uses task queue, not global
- `valk_async_propagate_completion()` uses `handle->sys`, not global

### Phase 3: Explicit `sys` Parameter

Changed builtins from implicit global to explicit parameter:

| Builtin | Before | After |
|---------|--------|-------|
| `aio/sleep` | `(aio/sleep 100)` | `(aio/sleep sys 100)` |
| `vm/metrics-json` | `(vm/metrics-json)` | `(vm/metrics-json)` or `(vm/metrics-json sys)` |
| `vm/metrics-prometheus` | `(vm/metrics-prometheus)` | `(vm/metrics-prometheus)` or `(vm/metrics-prometheus sys)` |
| `aio/slab-buckets` | `(aio/slab-buckets name ...)` | `(aio/slab-buckets sys name ...)` |
| `aio/diagnostics-state-json` | `(aio/diagnostics-state-json)` | `(aio/diagnostics-state-json sys)` |

### Phase 4: TCP Alloc Callbacks

Removed global fallback from `__vtable_alloc_cb` in:
- `src/aio/aio_http2_client.c`
- `src/aio/aio_http2_server.c`
- `src/aio/aio_http2_conn.c`

Now requires valid `conn->sys` - errors if not present.

### Phase 5: Remove `g_last_started_aio_system`

Completely removed this global:
- `src/aio/aio_uv.c` - Removed definition
- `src/aio/aio_system.c` - Removed extern and usage
- `src/aio/aio_internal.h` - Removed extern declaration

### Phase 6: Unified HTTP Request Ref

**Problem**: Originally HTTP handlers received two arguments: a request (as a qexpr/plist) and a context (as a ref for SSE). This was confusing and the context was only needed for SSE.

**Solution**: Merge request and context into a single `http_request` ref type.

#### API Changes

HTTP handlers now receive a single request ref:
```lisp
; Old: handler received two arguments
(def {handler} (\ {req ctx} {
  (= {path} (plist/get req :path))      ; Access via plist
  (= {stream} (sse/open ctx))           ; SSE needed separate ctx
  ...
}))

; New: handler receives single request ref
(def {handler} (\ {req} {
  (= {path} (req/path req))             ; Access via builtin
  (= {stream} (sse/open req))           ; SSE uses same req
  ...
}))
```

#### Request Accessor Builtins

New builtins in `src/aio/aio_http_builtins.c`:
- `req/method` - Get HTTP method
- `req/path` - Get request path
- `req/authority` - Get authority (host)
- `req/scheme` - Get scheme (https)
- `req/headers` - Get all headers as list of pairs
- `req/header` - Get specific header by name (case-insensitive)
- `req/body` - Get request body
- `req/stream-id` - Get HTTP/2 stream ID

#### Files Modified

1. `src/aio/aio_http2_session.c` - Handler invocation creates `http_request` ref
2. `src/aio/aio_sse_builtins.c` - `sse/open` takes request ref
3. `src/aio/aio_http_builtins.c` - New request accessor builtins
4. `src/modules/aio/sse.valk` - `sse/handler` wrapper uses single req arg
5. `src/modules/aio/debug.valk` - Debug handler uses `ref?` for compatibility

### Phase 7: Remove `aio/delay` C Builtin

**Problem**: `aio/delay` was implemented in C and depended on `sys->current_request_ctx` being set during handler invocation. This was a hidden dependency and conflated timer functionality with HTTP response handling.

**Solution**: Reimplement `aio/delay` in Lisp as a composition of `aio/sleep` + `aio/then`.

#### Changes

1. **Removed C builtin** (`src/parser.c`):
   - Removed `valk_builtin_aio_delay` function
   - Removed registration of `aio/delay` and `aio/defer` builtins

2. **Removed C implementation** (`src/aio/aio_combinators.c`):
   - Removed `valk_aio_delay()` function
   - Removed `__delay_timer_cb` callback
   - Removed `__delay_timer_close_cb` callback

3. **Removed unused types** (`src/aio/aio_internal.h`):
   - Removed `valk_delay_timer_t` struct
   - Removed `valk_http_request_ctx_t` struct
   - Removed `current_request_ctx` field from `valk_aio_system_t`

4. **Removed declaration** (`src/aio/aio.h`):
   - Removed `valk_aio_delay()` declaration

5. **Added Lisp implementation** (`src/async_handles.valk`):
   ```lisp
   (fun {aio/delay sys ms continuation}
     {(aio/then (aio/sleep sys ms) (\ {_} {(continuation)}))})
   ```

6. **Updated helper functions** to take `sys` as first argument:
   - `with-timeout sys ms handle`
   - `retry-backoff sys n base-ms handle-fn`
   - `graceful-shutdown sys handles timeout-ms`
   - `delay-value sys ms value`

7. **Loaded async_handles in prelude** (`src/prelude.valk`):
   - Added `(load "src/async_handles.valk")` at end of prelude

### Phase 8: Remove `valk_aio_active_system` Global

Removed the last remaining global:

1. **Removed definition** (`src/aio/aio_uv.c`):
   - Removed `valk_aio_system_t *valk_aio_active_system = NULL;`

2. **Removed declarations** (`src/aio/aio.h`, `src/aio/aio_internal.h`):
   - Removed `extern valk_aio_system_t* valk_aio_active_system;`

3. **Removed usage** (`src/aio/aio_system.c`):
   - Removed setting `valk_aio_active_system = sys;` in start
   - Removed clearing `valk_aio_active_system = NULL;` in cleanup

4. **Removed test** (`test/unit/test_aio_uv.c`):
   - Removed `test_aio_active_system_initially_null` test

## Remaining Global Usage

**None.** All implicit global state has been removed from the AIO system.

## Future Work

1. **Compiler support** - When compiling to LLVM, the compiler will:
   - Track `Aio` effect in the type system
   - Resolve which `sys` is in scope at each call site
   - Insert `sys` parameter automatically

## Summary

All implicit global state has been eliminated from the AIO system:

| Global | Status |
|--------|--------|
| `g_last_started_aio_system` | Removed (Phase 5) |
| `current_request_ctx` | Removed (Phase 7) |
| `valk_http_request_ctx_t` | Removed (Phase 7) |
| `valk_delay_timer_t` | Removed (Phase 7) |
| `valk_aio_active_system` | Removed (Phase 8) |

The AIO system now uses fully explicit context passing, making it ready for LLVM compilation where data flow must be explicit.

## Testing

All tests pass after refactoring:
- `test/test_async_http_handlers.valk` - 52 tests (all pass)
- `test/test_sse_integration.valk` - 9 tests (all pass)
- `test/test_prelude.valk` - 32 tests (all pass)
- `test/test_delay_continuation_error.valk` - Verifies aio/delay error handling
