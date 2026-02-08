# GC Heap Usage Refactoring Plan

## Overview

Migrate unjustified heap allocations to appropriate memory strategies:
- **Arenas** for request-scoped allocations
- **Pools/Slabs** for bounded long-lived objects
- **Checkpoint-based reset** for SSE streaming

### Memory Strategy Guidelines

| Strategy | Use When | Examples |
|----------|----------|----------|
| Arena | Grouped lifetimes, scoped to request/operation | Request headers, response building |
| Pool/Slab | Long-lived, bounded count, predictable size | Connections, timers, handles |
| Static | Program lifetime | Global config, root environment |
| Heap (GC) | Truly unknown lifetime, escapes all scopes | Lisp values, closures |

---

## Phase 1: Arena Checkpoint Infrastructure

**Files:** `src/memory.h`, `src/memory.c`

### Goal
Add checkpoint API to arenas, enabling partial reset (stack-like behavior).

### Changes

1. Add checkpoint type:
```c
typedef struct {
  sz offset;
} valk_arena_checkpoint_t;
```

2. Add checkpoint API:
```c
valk_arena_checkpoint_t valk_arena_checkpoint_save(valk_mem_arena_t *arena);
void valk_arena_checkpoint_restore(valk_mem_arena_t *arena, valk_arena_checkpoint_t cp);
```

3. Implementation:
```c
valk_arena_checkpoint_t valk_arena_checkpoint_save(valk_mem_arena_t *arena) {
  return (valk_arena_checkpoint_t){ .offset = arena->offset };
}

void valk_arena_checkpoint_restore(valk_mem_arena_t *arena, valk_arena_checkpoint_t cp) {
  arena->offset = cp.offset;
}
```

### Validation
- Unit test: save checkpoint, allocate, restore, verify offset reset
- Verify allocations after restore reuse reclaimed space

---

## Phase 2: SSE Stream Body to Arena

**Files:** 
- `src/aio/http2/stream/aio_stream_body.h`
- `src/aio/http2/stream/aio_stream_body.c`
- `src/aio/http2/stream/aio_stream_builtins.c`

### Current (malloc)
```
valk_stream_body_new()     → malloc(sizeof(valk_stream_body_t))
                           → malloc(pending_capacity)  // 64KB default
valk_stream_body_write()   → malloc(sizeof(chunk) + len) per SSE event
```

### Target (arena with checkpoint)
```
stream open  → body allocated from stream arena
             → pending_data allocated from stream arena
             → checkpoint saved
SSE write    → chunk allocated from arena (after checkpoint)
queue drain  → checkpoint restore (reclaims chunks, preserves body)
stream close → arena released to pool
```

### Changes

1. Add fields to `valk_stream_body_t`:
```c
valk_mem_arena_t *arena;
valk_arena_checkpoint_t chunk_checkpoint;
```

2. Modify `valk_stream_body_new()`:
   - Add `valk_mem_arena_t *arena` parameter
   - Allocate body from arena: `valk_mem_arena_alloc(arena, sizeof(valk_stream_body_t))`
   - Allocate pending_data from arena
   - Save checkpoint: `body->chunk_checkpoint = valk_arena_checkpoint_save(arena)`
   - Store arena reference: `body->arena = arena`

3. Modify `valk_stream_body_write()`:
   - Replace `malloc(sizeof(valk_stream_chunk_t) + len + 1)` with arena alloc

4. Modify `__stream_data_read_callback()`:
   - Before `data_deferred = true`, add checkpoint restore:
```c
if (!body->queue_head) {
  if (body->state == VALK_STREAM_CLOSING) {
    // ... existing close logic
  }
  // Reclaim chunk memory - all data copied to TCP buffers
  valk_arena_checkpoint_restore(body->arena, body->chunk_checkpoint);
  body->data_deferred = true;
  return NGHTTP2_ERR_DEFERRED;
}
```

5. Modify `__stream_body_finish_close()`:
   - Remove `free(body->pending_data)` - arena handles it
   - Remove chunk free loop - arena handles it
   - Keep `valk_http2_release_stream_arena()` call

6. Modify `valk_stream_body_free()`:
   - Remove `free(body)` - arena handles it

7. Update callers (`aio_stream_builtins.c`):
   - Pass stream arena to `valk_stream_body_new()`
   - Get arena from request: `req->arena_ref`

### Safety Notes
- Chunk data is copied to `tcpBufferSlab` before TCP write
- By queue drain, no in-flight references to arena chunks
- `pending_data` is before checkpoint, not affected by restore

### Validation
- SSE stress test: 10K events over 1 minute, verify memory stable
- ASAN test for use-after-free
- Verify backpressure still works (queue_max enforcement)

---

## Phase 3: Timer Data Pool

**Files:**
- `src/aio/aio_types.h`
- `src/aio/system/aio_system.c`
- `src/aio/aio_combinators.c`
- `src/aio/aio.h`

### Current
```c
// aio_combinators.c:178, 294
valk_timer_data_t *data = aligned_alloc(16, sizeof(valk_timer_data_t));
```

### Target
Slab pool for timer callback data structs.

### Changes

1. Add to `valk_aio_system_config_t` in `aio.h`:
```c
u32 max_timers;  // Default: max_handles / 4
```

2. Add to `valk_aio_system` (internal):
```c
valk_slab_t *timerDataSlab;
```

3. Initialize in `valk_aio_system_init()`:
```c
if (cfg->max_timers == 0) {
  cfg->max_timers = cfg->max_handles / 4;
}
sys->timerDataSlab = valk_slab_new(sizeof(valk_timer_data_t), cfg->max_timers);
```

4. Free in `valk_aio_system_free()`:
```c
valk_slab_free(sys->timerDataSlab);
```

5. Modify `valk_aio_delay()`:
```c
// Before:
valk_timer_data_t *data = aligned_alloc(16, sizeof(valk_timer_data_t));

// After:
valk_slab_item_t *item = valk_slab_aquire(sys->timerDataSlab);
if (!item) {
  return valk_lval_err("Timer pool exhausted");
}
valk_timer_data_t *data = (valk_timer_data_t *)item->data;
```

6. Modify timer close callback:
```c
// Before:
free(data);

// After:
valk_slab_release_ptr(sys->timerDataSlab, data);
```

7. Same changes for `valk_aio_interval()`

### Validation
- Test with max_timers concurrent timers
- Verify pool exhaustion returns error gracefully
- Verify timers still fire correctly after pooling

---

## Phase 4: Async Handle Pool

**Files:**
- `src/aio/aio_async.c`
- `src/aio/system/aio_system.c`

### Current
`valk_async_handle_t` (~200 bytes) allocated inline or via malloc in various places.

### Target
Dedicated slab pool for async handles.

### Changes

1. Add to `valk_aio_system`:
```c
valk_slab_t *asyncHandleSlab;
```

2. Size calculation:
```c
u32 async_handle_count = cfg->max_concurrent_streams * cfg->max_connections;
sys->asyncHandleSlab = valk_slab_new(sizeof(valk_async_handle_t), async_handle_count);
```

3. Add allocation helper:
```c
valk_async_handle_t *valk_async_handle_alloc(valk_aio_system_t *sys);
void valk_async_handle_release(valk_async_handle_t *handle);
```

4. Modify all async handle creation sites to use `valk_async_handle_alloc()`

5. Release in `valk_async_handle_unref()` when refcount hits 0

### Validation
- Verify all async operations still work
- Stress test with many concurrent operations
- Check pool exhaustion handling

---

## Phase 5: HTTP Client Request Context to Arena

**Files:** `src/aio/aio_combinators.c`

### Current
`aio/http-request` allocates request context via malloc.

### Target
Use client connection's arena.

### Changes

1. In `valk_aio_http_request_impl()`:
   - Get arena from client connection context
   - Allocate request context from arena
   - Context freed when response complete (arena reset)

2. Identify arena source:
   - Client connections should have associated arena
   - May need to add arena to client handle structure

### Validation
- HTTP client tests pass
- ASAN clean
- Verify no leaks on request completion

---

## Phase 6: Combinator Parse State to Scratch Arena

**Files:** `src/aio/aio_combinators.c`

### Current
`aio/let` and similar combinators allocate temporary parse structures on heap.

### Target
Use thread-local scratch arena for parsing.

### Changes

1. Wrap parsing in scratch arena scope:
```c
VALK_WITH_ALLOC(valk_thread_ctx.scratch) {
  // Parse binding names
  // Build temporary lists
  // ...
}
// Evacuate final result to heap if needed
valk_lval_t *result = valk_evacuate_to_heap(parsed_lambda);
```

2. Identify parse-time allocations in:
   - `builtin_aio_let()` - binding name/value pairs
   - `builtin_aio_all()` - child handle array building
   - `builtin_aio_race()` - same
   - `builtin_aio_any()` - same

3. Ensure final values that escape are evacuated

### Validation
- All combinator tests pass
- Scratch arena stats show allocations
- No heap growth during repeated combinator use

---

## Phase 7: Combinator Result Arrays to Arena

**Files:** `src/aio/aio_combinators.c`

### Current
`aio/all`, `aio/race`, `aio/any` malloc arrays for collecting results.

### Target
Allocate from parent async handle's associated arena.

### Changes

1. Result arrays allocated from arena:
```c
// Before:
results = malloc(sizeof(valk_lval_t *) * child_count);

// After:
results = valk_mem_arena_alloc(handle->arena, sizeof(valk_lval_t *) * child_count);
```

2. Array size is bounded (known at creation time)

3. Freed automatically when combinator completes and arena resets

### Validation
- Combinator tests pass
- Memory stable under repeated combinator use

---

## Phase 8: Task Queue Ring Buffer

**Files:** `src/aio/system/aio_task_queue.c`

### Current
```c
// malloc per queued task
valk_task_item_t *item = malloc(sizeof(valk_task_item_t));
```

### Target
Fixed-capacity ring buffer with pre-allocated slots.

### Changes

1. Define ring buffer structure:
```c
typedef struct {
  valk_task_item_t *items;  // Pre-allocated array
  u32 capacity;
  _Atomic u32 head;
  _Atomic u32 tail;
} valk_task_ring_t;
```

2. Initialize based on `config->queue_capacity`:
```c
ring->items = calloc(config->queue_capacity, sizeof(valk_task_item_t));
ring->capacity = config->queue_capacity;
```

3. Enqueue: write to `items[tail % capacity]`, increment tail
4. Dequeue: read from `items[head % capacity]`, increment head
5. Full check: `(tail - head) >= capacity`

### Validation
- Task queue tests pass
- Verify backpressure when queue full
- Verify no memory growth under load

---

## Validation Checklist

After each phase:
- [ ] `make build` - compilation succeeds
- [ ] `make test` - all tests pass
- [ ] `make test-valk-asan` - no memory errors
- [ ] `make test-c-asan` - no memory errors

Phase 2 specific:
- [ ] SSE stress test: 10K events/minute for 10 minutes
- [ ] Memory usage stable (no growth)
- [ ] Backpressure triggers correctly

---

## Memory Impact Summary

| Allocation Site | Current | Target | Bounded By |
|----------------|---------|--------|------------|
| SSE body struct | malloc | arena | concurrent streams |
| SSE pending buffer | malloc (64KB) | arena | concurrent streams |
| SSE chunks | malloc/event | arena + checkpoint | queue depth, resets on drain |
| Timer data | aligned_alloc | slab | max_timers config |
| Async handles | malloc | slab | max_streams x max_connections |
| HTTP client ctx | malloc | arena | concurrent requests |
| Combinator parse | malloc | scratch arena | single-threaded, resets |
| Result arrays | malloc | arena | child count |
| Task queue items | malloc | ring buffer | queue_capacity config |

---

## Implementation Order

1. **Phase 1** - Foundation for all arena-based phases
2. **Phase 2** - Highest impact (SSE memory stability)
3. **Phase 3** - Simple win (timer pool)
4. **Phase 4** - Moderate complexity (async handle pool)
5. **Phase 5-7** - Incremental improvements
6. **Phase 8** - Optional optimization (task queue)

Phases 3-4 can be done in parallel. Phases 5-7 depend on Phase 1.
