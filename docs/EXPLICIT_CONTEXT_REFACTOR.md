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

### Phase 6: Explicit HTTP Request Context

**Problem**: SSE builtins read request context from `sys->current_request_ctx`, which is set/cleared around handler invocation. This is racy and prevents concurrent request handling.

**Solution**: Pass request context explicitly to handlers and SSE builtins.

#### API Changes

HTTP handlers now receive two arguments:
```lisp
; Old: handler receives only request
(def {handler} (\ {req} { ... }))

; New: handler receives request AND context
(def {handler} (\ {req ctx} {
  (= {stream} (sse/open ctx))  ; Pass ctx to sse/open
  ...
}))
```

SSE builtin changes:
```lisp
; Old
(sse/open)

; New
(sse/open ctx)
```

#### Backwards Compatibility

Handlers with arity 1 continue to work - context is only passed when handler accepts 2+ arguments:
```lisp
; Still works (arity 1)
(def {simple-handler} (\ {req} {{:status "200" :body "hello"}}))

; New style (arity 2) - required for SSE
(def {sse-handler} (\ {req ctx} {
  (= {stream} (sse/open ctx))
  (sse/send stream "hello")
  :deferred
}))
```

#### Files Modified

1. `src/aio/aio_http2_session.c` - Handler invocation creates `http_req_ctx` ref
2. `src/aio/aio_sse_builtins.c` - `sse/open` takes ctx argument
3. `src/modules/aio/sse.valk` - `sse/handler` wrapper passes ctx
4. `src/modules/aio/debug.valk` - Debug handler accepts ctx
5. `src/modules/aio/metrics-stream.valk` - Metrics handler accepts ctx

## Remaining Global Usage

`valk_aio_active_system` is still used for:

1. **System startup/cleanup** (`aio_system.c`) - Sets/clears when system starts/stops
2. **aio/delay builtin** - Needs request context for deferred responses

The `current_request_ctx` field remains on `valk_aio_system_t` for `aio/delay` compatibility, but SSE no longer uses it.

## Future Work

1. **Remove `valk_aio_active_system` entirely** - Pass sys through environment or make it a parameter to all AIO builtins
2. **Thread-local sys** - For multi-system scenarios, use thread-local storage keyed by thread ID
3. **Compiler support** - When compiling to LLVM, the compiler will:
   - Track `Aio` effect in the type system
   - Resolve which `sys` is in scope at each call site
   - Insert `sys` parameter automatically

## Testing

All tests pass after refactoring:
- `test/test_async_http_handlers.valk` - 52 tests
- `test/test_aio_builtins_coverage.valk` - 82 tests
- `test/test_sse_integration.valk` - SSE with explicit context
- `test/test_prelude.valk` - 32 tests
