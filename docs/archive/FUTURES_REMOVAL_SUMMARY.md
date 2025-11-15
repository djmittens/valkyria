# Futures/Promises Removal Summary

## What Was Removed

### From Parser/Language Layer
✅ **Removed old `await` builtin** - Used pthread_cond_wait and ARCs
✅ **Removed futures-based HTTP/2 functions**:
  - `http2/listen` (returned future)
  - `http2/connect` (returned future)
  - `http2/send` (returned future)

### What Was Replaced
- Old `await` → New `async-shift`/`async-reset` continuations
- Old `http2/connect` → New `http2/connect-async` (takes continuation)
- Old `http2/send` → New `http2/send-async` (takes continuation)

### What Remains (For Now)
- `concurrency.c` - Still needed by AIO layer (libuv integration)
- `aio_uv.c` - Still uses futures internally
- Will be removed once AIO is updated to use continuations directly

## New System

### Continuation-Based Async/Await
```lisp
; Old way (removed)
(def {fut} (http2/connect aio "google.com" 443))
(def {client} (await fut))  ; pthread_cond_wait

; New way
(async {
  (def {client} (await-async (http2/connect-async aio "google.com" 443)))
  ; Continuation captured and resumed when ready
})
```

### New Builtins
- `async-shift` - Captures continuation
- `async-reset` - Establishes async boundary
- `async-resume` - Resumes continuation with value
- `http2/connect-async` - Async connect with continuation
- `http2/send-async` - Async send with continuation

## Benefits Achieved

1. **No ARCs in language layer** - Removed atomic reference counting from Lisp
2. **No pthread synchronization in language** - No mutexes/condvars in Lisp code
3. **Simpler async model** - Continuations instead of futures
4. **Works with GC** - No special thread-safe allocators needed

## Migration Notes

### For Users
- Use new `async`/`await-async` macros instead of old `await`
- Use `http2/connect-async` instead of `http2/connect`
- All async operations now take continuations as last argument

### For Developers
- AIO layer still uses futures internally (temporary)
- Next step: Update libuv integration to use continuations directly
- Then remove `concurrency.c` completely

## Test Files Cleaned Up

Removed old futures-based tests:
- `test_async_await.valk`
- `test_await_*.valk`
- `test_*google*.valk` (futures versions)
- `test_http2_await.valk`
- `test_simple_await.valk`

Kept new continuation-based tests:
- `test_new_async.valk`
- `test_new_async_http.valk`
- `test_cont_*.valk`

## Code Reduction

- Removed ~200 lines of futures code from parser.c
- Simplified async operations
- No longer need special allocator switching for futures
- Cleaner, more maintainable codebase

## Status

✅ **Language layer is futures-free**
⏳ AIO layer still uses futures (next cleanup target)
✅ All tests pass with new continuation system
✅ No user-visible futures/promises remain