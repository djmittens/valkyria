# Valkyria Memory Management Guide

This guide explains how memory management works in Valkyria, why it's designed this way, and how to use it correctly in your code.

## Table of Contents

1. [The Big Picture](#the-big-picture)
2. [Allocator Types](#allocator-types)
3. [The Scratch Arena](#the-scratch-arena)
4. [The GC Heap](#the-gc-heap)
5. [Checkpoints: Moving Values to Safety](#checkpoints-moving-values-to-safety)
6. [Handles: Protecting Values from GC](#handles-protecting-values-from-gc)
7. [Putting It Together: Async Callbacks](#putting-it-together-async-callbacks)
8. [VALK_WITH_ALLOC: Switching Allocators](#valk_with_alloc-switching-allocators)
9. [Common Patterns](#common-patterns)
10. [Debugging Memory Issues](#debugging-memory-issues)

---

## The Big Picture

Valkyria's memory system is designed around one key insight: **most allocations are temporary**.

When you evaluate a Lisp expression like `(map (fn (x) (* x 2)) (range 1000))`, thousands of intermediate values are created - cons cells, numbers, partial lists - but only the final result matters. Traditional malloc/free would be incredibly slow for this.

Our solution:

```
┌─────────────────────────────────────────────────────────────────┐
│                        Memory Flow                               │
│                                                                  │
│   Expression Evaluation          Long-lived Values              │
│   ──────────────────────         ────────────────               │
│                                                                  │
│   ┌─────────────────┐            ┌─────────────────┐            │
│   │  Scratch Arena  │ ─────────> │    GC Heap      │            │
│   │  (super fast)   │ checkpoint │  (garbage       │            │
│   │                 │ or evacuate│   collected)    │            │
│   └─────────────────┘            └─────────────────┘            │
│          │                              │                        │
│          │                              │                        │
│          v                              v                        │
│      Wiped after               Survives until                   │
│      each eval                 no longer referenced             │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**The mental model:**
1. Fast allocations go to scratch (bump pointer, nearly free)
2. Values that need to survive get evacuated to the GC heap
3. The GC heap is garbage-collected periodically

---

## Allocator Types

Every `valk_lval_t` has flags indicating where it was allocated:

```c
// In parser.h
#define LVAL_ALLOC_SCRATCH  (0ULL << LVAL_ALLOC_SHIFT)  // Scratch arena (ephemeral)
#define LVAL_ALLOC_GLOBAL   (1ULL << LVAL_ALLOC_SHIFT)  // Global arena (persistent)
#define LVAL_ALLOC_HEAP     (2ULL << LVAL_ALLOC_SHIFT)  // GC heap (persistent)

// Check where a value lives:
#define LVAL_ALLOC(lval) ((lval)->flags & LVAL_ALLOC_MASK)
```

### Why This Matters

The allocation type determines **lifetime semantics**:

| Type | Lifetime | When to Use |
|------|----------|-------------|
| `LVAL_ALLOC_SCRATCH` | Until next checkpoint/eval | Temporary computations |
| `LVAL_ALLOC_HEAP` | Until GC collects it | Values that must survive |
| `LVAL_ALLOC_GLOBAL` | Forever (immortal) | Builtins, stdlib |

---

## The Scratch Arena

The scratch arena is a simple bump allocator. It's incredibly fast because allocation is just:

```c
// Simplified - actual code handles alignment and overflow
void *valk_mem_arena_alloc(valk_mem_arena_t *arena, sz bytes) {
    void *ptr = arena->heap + arena->offset;
    arena->offset += bytes;  // Just bump the pointer!
    return ptr;
}
```

### How the Thread Context Works

Each thread has a context with the current allocator:

```c
// In memory.h
typedef struct {
  valk_mem_allocator_t *allocator;  // Current allocator for valk_mem_alloc()
  void *heap;                       // Fallback GC heap for overflow
  valk_mem_arena_t *scratch;        // Scratch arena
  struct valk_lenv_t *root_env;     // Root environment for checkpointing
  // ...
} valk_thread_context_t;

extern __thread valk_thread_context_t valk_thread_ctx;
```

When you call `valk_lval_num(42)`, it allocates from `valk_thread_ctx.allocator`.

### What Happens on Overflow?

If the scratch arena fills up, allocations **automatically fall back to the GC heap**:

```c
// In memory.c - simplified
void *valk_mem_arena_alloc(valk_mem_arena_t *self, sz bytes) {
  if (self->offset + bytes > self->capacity) {
    // Overflow! Fall back to GC heap
    return valk_gc_malloc_heap_alloc(valk_thread_ctx.heap, bytes);
  }
  // Normal bump allocation...
}
```

This is transparent - you don't need to handle it.

---

## The GC Heap

The GC heap (`valk_gc_heap2_t`) is a proper garbage-collected heap with:

- **Size classes**: 16, 32, 64, 128, 256, 512, 1024, 2048, 4096 bytes
- **Thread-local allocation buffers (TLABs)**: Fast per-thread allocation
- **Mark-sweep collection**: Traces from roots, frees unreachable objects
- **Page-based management**: Memory returned to OS when pages become empty

### When Values End Up on the GC Heap

1. **Overflow**: Scratch arena full, allocation falls back
2. **Checkpoint**: Reachable values copied from scratch to heap
3. **Evacuation**: Explicit `valk_evacuate_to_heap()` call
4. **Direct allocation**: Using `VALK_WITH_ALLOC((void*)gc_heap)`

---

## Checkpoints: Moving Values to Safety

A **checkpoint** is when we:
1. Walk all reachable values from the root environment
2. Copy scratch-allocated values to the GC heap
3. Fix all pointers to point to new locations
4. Reset the scratch arena

```c
// Triggered automatically when scratch > 75% full
void valk_checkpoint(valk_mem_arena_t* scratch, 
                     valk_gc_malloc_heap_t* heap,
                     valk_lenv_t* root_env);

// Or check manually:
bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold);
```

### The Problem with Checkpoints

Checkpoints only save values **reachable from the root environment**. If you store a callback pointer in a C struct, the checkpoint doesn't know about it:

```c
// DANGER: This callback might be in scratch!
timer_data->callback = callback;  // Raw pointer stored

// Later, after a checkpoint...
valk_lval_t *cb = timer_data->callback;  // CRASH! Memory was wiped!
```

This is where evacuation and handles come in.

---

## Handles: Protecting Values from GC

A **handle** is a safe reference to a GC heap value. Unlike raw pointers:

- Handles survive GC (the handle table is a GC root)
- Handles detect stale references via generation counters
- Handles are thread-safe

```c
// The handle type
typedef struct {
  u32 index;       // Slot in handle table
  u32 generation;  // Detects stale handles
} valk_handle_t;

// Create a handle (value MUST be on GC heap first!)
valk_handle_t valk_handle_create(valk_handle_table_t *table, valk_lval_t *val);

// Get the value back (returns NULL if stale)
valk_lval_t *valk_handle_resolve(valk_handle_table_t *table, valk_handle_t h);

// Release when done (allows slot reuse)
void valk_handle_release(valk_handle_table_t *table, valk_handle_t h);
```

### The Global Handle Table

There's a global handle table for cross-region references:

```c
extern valk_handle_table_t valk_global_handle_table;
```

---

## Putting It Together: Async Callbacks

Here's the complete pattern for storing a Lisp callback in C code:

### Step 1: Evacuate to Heap

The callback might be in scratch. Move it to the GC heap:

```c
valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);
```

This is a no-op if already on heap, otherwise copies the value and all its dependencies.

### Step 2: Create a Handle

Now protect it from GC:

```c
timer_data->callback_handle = valk_handle_create(&valk_global_handle_table, heap_callback);
```

### Step 3: Store Both (Belt and Suspenders)

```c
timer_data->callback = heap_callback;         // For direct access
timer_data->callback_handle = handle;          // For safety
```

### Step 4: Resolve When Needed

```c
static void timer_callback(uv_timer_t *handle) {
  timer_data_t *data = handle->data;
  
  // Resolve the handle - returns NULL if something went wrong
  valk_lval_t *callback = valk_handle_resolve(&valk_global_handle_table, 
                                               data->callback_handle);
  if (!callback) {
    // Handle was released or value was collected - clean up
    return;
  }
  
  // Safe to use callback now
  valk_lval_t *result = valk_lval_eval_call(callback->fun.env, callback, args);
}
```

### Step 5: Release When Done

```c
static void timer_close_cb(uv_handle_t *handle) {
  timer_data_t *data = handle->data;
  
  // Release the handle - allows GC to collect the value
  valk_handle_release(&valk_global_handle_table, data->callback_handle);
  
  // Free the timer data itself
  free(data);
}
```

### Complete Example

From `aio_combinators.c`:

```c
valk_lval_t* valk_aio_interval(valk_aio_system_t* sys, u64 interval_ms,
                               valk_lval_t* callback, valk_lenv_t* env) {
  // Allocate timer data from slab or malloc
  valk_interval_timer_t *timer_data = /* allocation */;

  // CRITICAL: Evacuate callback to heap and create handle
  valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);
  timer_data->callback = heap_callback;
  timer_data->callback_handle = valk_handle_create(&valk_global_handle_table, 
                                                    heap_callback);
  
  // ... setup timer ...
  
  return valk_lval_num((long)timer_data->interval_id);
}

static void __interval_timer_cb(uv_timer_t *handle) {
  valk_interval_timer_t *timer_data = handle->data;
  
  // Resolve handle to get callback
  valk_lval_t *callback = valk_handle_resolve(&valk_global_handle_table, 
                                               timer_data->callback_handle);
  if (!callback) {
    // Stale handle - stop the timer
    uv_timer_stop(handle);
    uv_close((uv_handle_t *)handle, __interval_timer_close_cb);
    return;
  }
  
  // Call it!
  valk_lval_t *result = valk_lval_eval_call(callback->fun.env, callback, 
                                             valk_lval_nil());
}

static void __interval_timer_close_cb(uv_handle_t *handle) {
  valk_interval_timer_t *timer_data = handle->data;
  
  // Release the handle
  valk_handle_release(&valk_global_handle_table, timer_data->callback_handle);
  
  // Free timer data
  free(timer_data);
}
```

---

## VALK_WITH_ALLOC: Switching Allocators

The `VALK_WITH_ALLOC` macro temporarily switches the thread's allocator:

```c
#define VALK_WITH_ALLOC(_alloc_) \
  for (struct { int exec; void *old_alloc; } __ctx = {1, valk_thread_ctx.allocator}; \
       __ctx.exec; valk_thread_ctx.allocator = __ctx.old_alloc) \
    for (valk_thread_ctx.allocator = (_alloc_); __ctx.exec; __ctx.exec = 0)
```

### Usage

```c
// Allocate from GC heap instead of scratch
VALK_WITH_ALLOC((void*)valk_thread_ctx.heap) {
  valk_lval_t *val = valk_lval_num(42);  // Goes to GC heap
}

// Allocate from a specific slab
VALK_WITH_ALLOC((valk_mem_allocator_t*)sys->handleSlab) {
  handle = valk_mem_alloc(sizeof(my_handle_t));
}

// Allocate from a region
VALK_WITH_ALLOC((valk_mem_allocator_t*)&request->region) {
  header = valk_mem_alloc(header_size);
}

// Use raw malloc (rare - for bootstrapping)
VALK_WITH_ALLOC(&valk_malloc_allocator) {
  buffer = valk_mem_alloc(size);
}
```

### When to Use

| Situation | Allocator |
|-----------|-----------|
| Normal Lisp code | Default (scratch) |
| Values that must survive | GC heap |
| Fixed-size I/O handles | Slab allocator |
| Per-request data | Request region/arena |

---

## Common Patterns

### Pattern 1: Simple Builtin Function

Most builtins don't need special handling - values are naturally in scratch:

```c
valk_lval_t *builtin_add(valk_lenv_t *env, valk_lval_t *args) {
  // These allocations go to scratch - that's fine!
  // The result will survive because it's reachable from the environment
  double sum = 0;
  for (int i = 0; i < args->cells.count; i++) {
    sum += args->cells.items[i]->num;
  }
  return valk_lval_num(sum);  // Scratch allocation, checkpoint will save it
}
```

### Pattern 2: Storing Callback for Later

```c
void setup_async_operation(valk_lval_t *callback) {
  my_context_t *ctx = malloc(sizeof(my_context_t));
  
  // MUST evacuate and handle!
  valk_lval_t *heap_cb = valk_evacuate_to_heap(callback);
  ctx->callback_handle = valk_handle_create(&valk_global_handle_table, heap_cb);
  
  // ... setup async ...
}

void async_complete(my_context_t *ctx) {
  valk_lval_t *cb = valk_handle_resolve(&valk_global_handle_table, 
                                         ctx->callback_handle);
  if (cb) {
    valk_lval_eval_call(cb->fun.env, cb, valk_lval_nil());
  }
  valk_handle_release(&valk_global_handle_table, ctx->callback_handle);
  free(ctx);
}
```

### Pattern 3: Building a Response in a Region

```c
void handle_http_request(http_request_t *req) {
  // Allocate response data in request's region - freed when request ends
  VALK_WITH_ALLOC((valk_mem_allocator_t*)&req->region) {
    char *body = valk_mem_alloc(body_size);
    // ... build response ...
  }
  // When request completes, region is destroyed, body is freed
}
```

### Pattern 4: GC Safe Points in Callbacks

Long-running callbacks should have GC safe points:

```c
static void event_loop_callback(uv_timer_t *handle) {
  VALK_GC_SAFE_POINT();  // Allow GC to run if needed
  
  // ... do work ...
}
```

---

## Debugging Memory Issues

### Symptom: Crash after timer fires

**Cause**: Callback was in scratch, got wiped by checkpoint.

**Fix**: Use `valk_evacuate_to_heap()` + handle pattern.

### Symptom: Memory leak (heap keeps growing)

**Cause**: Handles not being released, or values retained in environment.

**Debug**:
```c
// Check handle table usage
printf("Handles in use: %u\n", valk_global_handle_table.count);
```

### Symptom: Stale pointer crash

**Cause**: Using raw pointer instead of handle after GC.

**Fix**: Always use handles for cross-region references.

### Symptom: Allocation returns NULL

**Cause**: Out of memory.

**Check**: Arena stats, heap stats:
```c
valk_arena_print_stats(scratch, stderr);
```

---

## Summary

| What You Want | How to Do It |
|---------------|--------------|
| Temporary value | Just allocate (scratch default) |
| Value survives eval | Bind to environment |
| Store callback in C | `valk_evacuate_to_heap()` + `valk_handle_create()` |
| Access stored callback | `valk_handle_resolve()` |
| Done with callback | `valk_handle_release()` |
| Allocate from specific allocator | `VALK_WITH_ALLOC(allocator) { ... }` |
| Allow GC in callback | `VALK_GC_SAFE_POINT()` |

The key insight: **scratch is fast but ephemeral; heap is permanent but needs GC; handles bridge the gap.**
