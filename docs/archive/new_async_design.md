# New Async Design - Replacing Futures with Shift/Reset

## Problem with Current Approach
- Futures require thread-safe allocators (ARCs)
- Complex memory management with atomic reference counting
- Memory islands and callback binding issues
- Overhead from pthread synchronization primitives

## New Design: Pure Continuation-Based Async

### Core Idea
Replace futures/promises entirely with delimited continuations using shift/reset.

### Implementation Strategy

1. **Async Operations Return Thunks**
   - Instead of returning futures, async operations return thunks
   - Thunks are suspended computations that resume when data is ready

2. **Event Loop Integration**
   - libuv callbacks directly resume continuations
   - No intermediate future/promise objects
   - No pthread synchronization needed

3. **Memory Model**
   - Continuations live in the same heap as other values
   - No special thread-safe allocators needed
   - GC handles cleanup naturally

### Example Usage

```lisp
; Old way with futures
(def {fut} (http2/connect aio "google.com" 443))
(def {client} (await fut))  ; Blocks with pthread_cond_wait

; New way with shift/reset
(reset
  (def {client} (shift k
    (http2/connect-async "google.com" 443 k)))
  ; Continuation 'k' is passed to libuv callback
  ; When connection completes, k is called with result
  (print "Connected:" client))
```

### Implementation Steps

1. **Create Continuation-Aware Async Primitives**
   ```c
   // Instead of returning valk_future*
   valk_lval_t* valk_async_connect(host, port, continuation);
   ```

2. **libuv Callback Integration**
   ```c
   void on_connect(uv_stream_t* stream, int status) {
     valk_lval_t* cont = stream->data;
     valk_lval_t* result = status == 0 ?
       valk_lval_ref("client", stream) :
       valk_lval_err("Connection failed");
     valk_apply_continuation(cont, result);
   }
   ```

3. **Simplified await**
   ```lisp
   (def {await} (macro {expr}
     {(shift k expr)}))
   ```

### Benefits

1. **No ARCs** - Regular GC handles everything
2. **No pthread overhead** - Event loop drives everything
3. **Composable** - Continuations naturally compose
4. **Simple** - No complex future/promise state machines

### Migration Path

1. Keep existing futures for compatibility
2. Add new continuation-based APIs alongside
3. Gradually deprecate futures
4. Eventually remove ARC infrastructure

### Next Steps

1. Implement basic shift/reset without complex stack capture
2. Create async primitives that use continuations
3. Test with simple HTTP/2 client
4. Benchmark vs futures approach