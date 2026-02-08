# GC Marking Algorithm Design

This document describes the type-safe garbage collection marking algorithm for Valkyria Lisp.

## Table of Contents

1. [Problem Statement](#problem-statement)
2. [Design Goals](#design-goals)
3. [Object Model](#object-model)
4. [Algorithm Overview](#algorithm-overview)
5. [Data Structures](#data-structures)
6. [Marking Functions](#marking-functions)
7. [Arena Integration](#arena-integration)
8. [Parallel Marking](#parallel-marking)
9. [Implementation Checklist](#implementation-checklist)

---

## Problem Statement

### The Bug We're Fixing

The previous GC implementation had a **type confusion bug** in the parallel mark phase:

```c
// BUGGY: mark_and_push2_parallel() accepts void* and pushes to queue
static void mark_and_push2_parallel(void *ptr, valk_gc_mark_ctx2_t *ctx) {
  // ... mark the pointer ...
  valk_gc_mark_queue_push(ctx->queue, ptr);  // BUG: pushes ANY pointer type
}

// BUGGY: mark_env2_parallel() pushes non-lval pointers to the lval queue
static void mark_env2_parallel(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx) {
  mark_and_push2_parallel(env, ctx);              // Pushes lenv* (WRONG!)
  mark_and_push2_parallel(env->symbols.items, ctx); // Pushes char** (WRONG!)
  mark_and_push2_parallel(env->vals.items, ctx);    // Pushes lval** (WRONG!)
}

// BUGGY: Queue consumer assumes all items are valk_lval_t*
while ((obj = valk_gc_mark_queue_pop(queue)) != NULL) {
  mark_children2_parallel(obj, ctx);  // Calls LVAL_TYPE() on non-lval!
}
```

When `mark_children2_parallel()` receives a non-lval pointer (env, string, array), it reads garbage for the type field, leading to memory corruption and crashes.

### Root Cause

**Type erasure**: The queue is typed as `valk_lval_t*` but code pushes arbitrary `void*` pointers.

---

## Design Goals

1. **Type Safety**: The mark queue must only contain objects of known, uniform type
2. **Correctness**: All reachable objects must be marked; no false positives
3. **Performance**: Minimize overhead; cache-friendly traversal
4. **Parallelism**: Support concurrent marking with work stealing
5. **Arena Support**: Handle references from active request arenas to GC heap

---

## Object Model

### Object Types in the GC Heap

| Type | C Type | Contains References To |
|------|--------|----------------------|
| **lval** | `valk_lval_t*` | Other lvals, envs, strings (depending on lval type) |
| **lenv** | `valk_lenv_t*` | Parent env, fallback env, symbol array, value array |
| **string** | `char*` | Nothing (leaf node) |
| **array** | `T**` | Elements of type T |

### Reference Graph

```
┌─────────────────────────────────────────────────────────────────┐
│                        GC Heap Objects                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   valk_lenv_t (environment)                                     │
│   ┌──────────────────────────────────────────────┐              │
│   │ flags, allocator                             │              │
│   │ parent ──────────────────────────► lenv      │              │
│   │ fallback ────────────────────────► lenv      │              │
│   │ symbols.items ───────────────────► char**    │              │
│   │   └── symbols.items[i] ──────────► char*     │              │
│   │ vals.items ──────────────────────► lval**    │              │
│   │   └── vals.items[i] ─────────────► lval      │              │
│   └──────────────────────────────────────────────┘              │
│                                                                 │
│   valk_lval_t (value) - type-dependent references               │
│   ┌──────────────────────────────────────────────┐              │
│   │ flags, origin_allocator, gc_next             │              │
│   │                                              │              │
│   │ LVAL_CONS/QEXPR:                             │              │
│   │   cons.head ─────────────────────► lval      │              │
│   │   cons.tail ─────────────────────► lval      │              │
│   │                                              │              │
│   │ LVAL_FUN (lambda):                           │              │
│   │   fun.name ──────────────────────► char*     │              │
│   │   fun.env ───────────────────────► lenv      │              │
│   │   fun.formals ───────────────────► lval      │              │
│   │   fun.body ──────────────────────► lval      │              │
│   │                                              │              │
│   │ LVAL_SYM/STR/ERR:                            │              │
│   │   str ───────────────────────────► char*     │              │
│   │                                              │              │
│   │ LVAL_HANDLE:                                 │              │
│   │   async.handle ──────────────────► handle    │              │
│   │     └── handle->result ──────────► lval      │              │
│   │     └── handle->error ───────────► lval      │              │
│   │     └── handle->env ─────────────► lenv      │              │
│   │     └── handle->on_complete ─────► lval      │              │
│   │     └── handle->on_error ────────► lval      │              │
│   │                                              │              │
│   │ LVAL_NUM/NIL: (no references)                │              │
│   └──────────────────────────────────────────────┘              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Algorithm Overview

### Tri-Color Abstraction

We use the standard tri-color marking abstraction:

| Color | Meaning | Implementation |
|-------|---------|----------------|
| **White** | Not yet visited; potentially garbage | Mark bit = 0 |
| **Gray** | Visited but children not processed | In mark queue |
| **Black** | Visited and all children processed | Mark bit = 1, not in queue |

### Invariant

**Strong Tri-Color Invariant**: No black object may point directly to a white object.

This is maintained by processing all gray objects until none remain.

### Key Design Decision: LVAL-Only Queue

**The mark queue contains ONLY `valk_lval_t*` pointers.**

This is the critical fix. Non-lval objects (envs, strings, arrays) are either:
1. Processed immediately via recursion (envs)
2. Marked without queuing (strings, arrays - they're leaf nodes)

### Marking Strategy by Object Type

| Object Type | Marking Strategy |
|-------------|------------------|
| `valk_lval_t*` | Mark + push to queue; `mark_children` dispatches on type |
| `valk_lenv_t*` | Mark + recurse immediately (no queue) |
| `char*` (string) | Mark only (leaf - no children) |
| `T**` (array) | Mark array pointer + mark each element appropriately |
| `valk_async_handle_t*` | Mark + recurse to contained lvals/envs |

---

## Data Structures

### Mark Queue (Chase-Lev Work-Stealing Deque)

```c
#define VALK_GC_MARK_QUEUE_SIZE 8192

typedef struct valk_gc_mark_queue {
  _Atomic(valk_lval_t*) items[VALK_GC_MARK_QUEUE_SIZE];
  _Atomic sz top;     // Thieves steal from here (FIFO)
  _Atomic sz bottom;  // Owner pushes/pops here (LIFO)
} valk_gc_mark_queue_t;
```

**Important**: The queue is typed as `valk_lval_t*` - we MUST NOT push other types.

### Mark Context

```c
typedef struct valk_gc_mark_ctx2 {
  valk_gc_heap2_t *heap;           // The heap being collected
  valk_gc_mark_queue_t *queue;     // Thread-local mark queue
} valk_gc_mark_ctx2_t;
```

### Bitmap Operations

Mark bits are stored in a separate bitmap per page, not inline in object headers:

```c
// Try to atomically set mark bit (returns true if newly marked)
static inline bool valk_gc_page2_try_mark(valk_gc_page2_t *page, u32 slot) {
  return valk_gc_bitmap_try_set_atomic(valk_gc_page2_mark_bitmap(page), slot);
}
```

This allows bulk-clearing via memset and avoids dirtying object cache lines.

---

## Marking Functions

### Core Principle: Separate Functions for Separate Types

```
mark_lval()     - Marks lval and pushes to queue
mark_env()      - Marks env and recurses immediately (no queue)
mark_ptr_only() - Just marks, doesn't push or recurse (for leaf pointers)
mark_children() - Called from queue consumer, dispatches on lval type
```

### Function: `mark_ptr_only`

Marks a raw pointer without pushing to queue. Used for:
- Strings (`char*`)
- Arrays (`char**`, `lval**`)
- Any pointer that doesn't need child traversal

```c
static bool mark_ptr_only(void *ptr, valk_gc_mark_ctx2_t *ctx) {
  if (ptr == NULL) return false;
  
  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(ctx->heap, ptr, &loc)) {
    // Regular heap object - try to mark in page bitmap
    return valk_gc_page2_try_mark(loc.page, loc.slot);
  } else {
    // Large object - mark in large object list
    return valk_gc_mark_large_object(ctx->heap, ptr);
  }
}
```

### Function: `mark_lval`

Marks an lval and pushes to queue for later child processing.

```c
static void mark_lval(valk_lval_t *lval, valk_gc_mark_ctx2_t *ctx) {
  if (lval == NULL) return;
  
  // Try to mark - returns false if already marked
  if (!mark_ptr_only(lval, ctx)) return;
  
  // Push to queue for child processing
  // Queue contains ONLY valk_lval_t* pointers
  if (!valk_gc_mark_queue_push(ctx->queue, lval)) {
    // Queue full - process children inline as fallback
    mark_children(lval, ctx);
  }
}
```

### Function: `mark_env`

Marks an environment and all its contents. **Does NOT push to queue** - processes immediately via iteration.

Uses iteration for the parent chain to avoid stack overflow on deep env chains. The fallback chain (rarely deep) uses recursion only when non-NULL.

```c
static void mark_env(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx) {
  while (env != NULL) {
    // Try to mark - returns false if already marked (cycle detection)
    if (!mark_ptr_only(env, ctx)) return;
    
    // Mark symbol array and its contents (strings are leaves)
    mark_ptr_only(env->symbols.items, ctx);
    for (u64 i = 0; i < env->symbols.count; i++) {
      mark_ptr_only(env->symbols.items[i], ctx);  // char* - leaf
    }
    
    // Mark value array and its contents
    mark_ptr_only(env->vals.items, ctx);
    for (u64 i = 0; i < env->vals.count; i++) {
      mark_lval(env->vals.items[i], ctx);  // Push lvals to queue
    }
    
    // Handle fallback (rarely deep, so recursion is fine)
    if (env->fallback != NULL) {
      mark_env(env->fallback, ctx);
    }
    
    // Iterate to parent (avoids deep recursion)
    env = env->parent;
  }
}
```

### Function: `mark_async_handle`

Marks an async handle and its contained references.

```c
static void mark_async_handle(valk_async_handle_t *handle, valk_gc_mark_ctx2_t *ctx) {
  if (handle == NULL) return;
  
  // The handle struct itself may or may not be GC-managed
  // But its contents definitely need marking
  
  mark_lval(handle->result, ctx);
  mark_lval(handle->error, ctx);
  mark_lval(handle->on_complete, ctx);
  mark_lval(handle->on_error, ctx);
  mark_lval(handle->on_cancel, ctx);
  mark_env(handle->env, ctx);
}
```

### Function: `mark_children`

Dispatches on lval type to mark child references. **Called ONLY from queue consumer.**

```c
static void mark_children(valk_lval_t *lval, valk_gc_mark_ctx2_t *ctx) {
  if (lval == NULL) return;
  
  switch (LVAL_TYPE(lval)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      mark_lval(lval->cons.head, ctx);
      mark_lval(lval->cons.tail, ctx);
      break;
      
    case LVAL_FUN:
      if (lval->fun.builtin == NULL) {
        // Lambda - has closure references
        mark_ptr_only(lval->fun.name, ctx);  // char* - leaf
        mark_env(lval->fun.env, ctx);        // Recurse, don't queue
        mark_lval(lval->fun.formals, ctx);
        mark_lval(lval->fun.body, ctx);
      } else {
        // Builtin - only name is a reference
        mark_ptr_only(lval->fun.name, ctx);
      }
      break;
      
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      mark_ptr_only(lval->str, ctx);  // char* - leaf
      break;
      
    case LVAL_HANDLE:
      mark_async_handle(lval->async.handle, ctx);
      break;
      
    case LVAL_REF:
      mark_ptr_only(lval->ref.type, ctx);  // char* - leaf
      // ref.ptr is opaque - don't mark
      break;
      
    case LVAL_NUM:
    case LVAL_NIL:
    case LVAL_FORWARD:
    case LVAL_UNDEFINED:
      // No children to mark
      break;
  }
}
```

### Main Mark Loop

```c
void valk_gc_heap2_mark_roots(valk_gc_heap2_t *heap) {
  valk_gc_mark_queue_t local_queue;
  valk_gc_mark_queue_init(&local_queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = &local_queue,
  };
  
  // Phase 1: Mark from root environment
  mark_env(heap->root_env, &ctx);
  
  // Phase 2: Mark from global roots (registered handlers, etc.)
  valk_gc_visit_global_roots(visit_root_lval, &ctx);
  
  // Phase 3: Mark from thread roots (if applicable)
  valk_gc_visit_thread_roots(visit_root_lval, &ctx);
  
  // Phase 4: Mark from active request arenas (see Arena Integration)
  valk_gc_visit_arena_roots(visit_root_lval, &ctx);
  
  // Phase 5: Process mark queue until empty
  valk_lval_t *obj;
  while ((obj = valk_gc_mark_queue_pop(&local_queue)) != NULL) {
    mark_children(obj, &ctx);  // obj is ALWAYS valk_lval_t*
  }
}

static void visit_root_lval(valk_lval_t *root, void *ctx_ptr) {
  valk_gc_mark_ctx2_t *ctx = ctx_ptr;
  mark_lval(root, ctx);
}
```

---

## Arena Integration

### Problem

HTTP request arenas may contain objects that reference GC heap objects:

```
┌─────────────────────────┐     ┌─────────────────────────┐
│   Request Arena (temp)   │     │     GC Heap (perm)       │
├─────────────────────────┤     ├─────────────────────────┤
│                         │     │                         │
│  request_data ──────────┼────►│  handler_lambda         │
│  response_builder ──────┼────►│  cached_config          │
│  temp_results ──────────┼────►│  connection_state       │
│                         │     │                         │
└─────────────────────────┘     └─────────────────────────┘
```

If GC runs while a request is active, we must scan the arena for heap references.

### Arena Registry

```c
typedef struct valk_arena_registry {
  pthread_mutex_t lock;
  struct {
    valk_mem_arena_t *arena;
    valk_lval_t *root;           // Root lval to scan (e.g., handler lambda)
    valk_lenv_t *env;            // Environment to scan (e.g., request env)
    bool active;
  } entries[VALK_MAX_REQUEST_ARENAS];
  u32 count;
} valk_arena_registry_t;

extern valk_arena_registry_t valk_arena_registry;
```

### Arena Root Registration

When a request starts:

```c
void valk_gc_register_request_arena(valk_mem_arena_t *arena, 
                                     valk_lval_t *handler,
                                     valk_lenv_t *request_env) {
  pthread_mutex_lock(&valk_arena_registry.lock);
  
  // Find empty slot
  for (u32 i = 0; i < VALK_MAX_REQUEST_ARENAS; i++) {
    if (!valk_arena_registry.entries[i].active) {
      valk_arena_registry.entries[i] = (typeof(valk_arena_registry.entries[0])){
        .arena = arena,
        .root = handler,
        .env = request_env,
        .active = true,
      };
      valk_arena_registry.count++;
      break;
    }
  }
  
  pthread_mutex_unlock(&valk_arena_registry.lock);
}
```

When request completes:

```c
void valk_gc_unregister_request_arena(valk_mem_arena_t *arena) {
  pthread_mutex_lock(&valk_arena_registry.lock);
  
  for (u32 i = 0; i < VALK_MAX_REQUEST_ARENAS; i++) {
    if (valk_arena_registry.entries[i].arena == arena) {
      valk_arena_registry.entries[i].active = false;
      valk_arena_registry.count--;
      break;
    }
  }
  
  pthread_mutex_unlock(&valk_arena_registry.lock);
}
```

### Arena Root Visiting

During GC mark phase:

```c
void valk_gc_visit_arena_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  pthread_mutex_lock(&valk_arena_registry.lock);
  
  for (u32 i = 0; i < VALK_MAX_REQUEST_ARENAS; i++) {
    if (valk_arena_registry.entries[i].active) {
      // Mark the handler lambda and request environment
      if (valk_arena_registry.entries[i].root) {
        visitor(valk_arena_registry.entries[i].root, ctx);
      }
      if (valk_arena_registry.entries[i].env) {
        // Need an env visitor or cast through the mark_env function
        valk_gc_mark_env_from_visitor(valk_arena_registry.entries[i].env, ctx);
      }
    }
  }
  
  pthread_mutex_unlock(&valk_arena_registry.lock);
}
```

### Design Invariant

**No arena-allocated object may be referenced by a heap object that outlives the arena.**

This invariant is maintained by:
1. Request handlers returning fresh results (allocated in arena)
2. Arena destruction happening only after request completion
3. Any values that need to persist being copied to heap first

---

## Parallel Marking

### Parallel Mark Functions

The parallel versions follow the same type-safety rules:

```c
// Parallel version - same contract as single-threaded
static void mark_lval_parallel(valk_lval_t *lval, valk_gc_mark_ctx2_t *ctx) {
  if (lval == NULL) return;
  if (!mark_ptr_only_parallel(lval, ctx)) return;  // Atomic CAS
  
  if (!valk_gc_mark_queue_push(ctx->queue, lval)) {
    mark_children_parallel(lval, ctx);
  }
}

static void mark_env_parallel(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx) {
  if (env == NULL) return;
  if (!mark_ptr_only_parallel(env, ctx)) return;  // Atomic CAS
  
  // Same structure as single-threaded - mark arrays, recurse on parent
  mark_ptr_only_parallel(env->symbols.items, ctx);
  for (u64 i = 0; i < env->symbols.count; i++) {
    mark_ptr_only_parallel(env->symbols.items[i], ctx);
  }
  
  mark_ptr_only_parallel(env->vals.items, ctx);
  for (u64 i = 0; i < env->vals.count; i++) {
    mark_lval_parallel(env->vals.items[i], ctx);  // Queue lvals
  }
  
  mark_env_parallel(env->parent, ctx);
  mark_env_parallel(env->fallback, ctx);
}

static void mark_children_parallel(valk_lval_t *lval, valk_gc_mark_ctx2_t *ctx) {
  // Identical dispatch logic to single-threaded version
  // Uses mark_lval_parallel and mark_env_parallel
}
```

### Work Stealing

When a thread's local queue is empty, it steals from other threads:

```c
void valk_gc_parallel_mark_worker(valk_gc_heap2_t *heap, int thread_id) {
  valk_gc_mark_queue_t *my_queue = &valk_gc_coord.threads[thread_id].mark_queue;
  valk_gc_mark_ctx2_t ctx = { .heap = heap, .queue = my_queue };
  
  while (true) {
    // 1. Process local queue
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != NULL) {
      mark_children_parallel(obj, &ctx);
    }
    
    // 2. Try to steal from other threads
    bool found_work = false;
    for (int i = 0; i < valk_gc_coord.threads_registered; i++) {
      if (i == thread_id) continue;
      
      obj = valk_gc_mark_queue_steal(&valk_gc_coord.threads[i].mark_queue);
      if (obj != NULL) {
        mark_children_parallel(obj, &ctx);
        found_work = true;
        break;
      }
    }
    
    // 3. Check termination
    if (!found_work && valk_gc_check_termination()) {
      break;
    }
  }
}
```

### Termination Detection

Use a global counter of "busy" threads:

```c
_Atomic u32 valk_gc_busy_threads = 0;

bool valk_gc_check_termination(void) {
  // Decrement busy count
  u32 prev = atomic_fetch_sub(&valk_gc_busy_threads, 1);
  
  if (prev == 1) {
    // We were the last busy thread - signal termination
    return true;
  }
  
  // Wait for either termination or new work
  // (implementation depends on synchronization primitive)
  
  // If we got new work, increment busy count and return false
  atomic_fetch_add(&valk_gc_busy_threads, 1);
  return false;
}
```

---

## Implementation Checklist

### Phase 1: Fix Single-Threaded Mark (gc.c ~line 2824-2927)

- [ ] Verify `mark_ptr_only()` exists and only marks, doesn't push
- [ ] Verify `mark_lval2()` marks and pushes ONLY lvals
- [ ] Verify `mark_env2()` recurses immediately, doesn't push env to queue
- [ ] Verify `mark_children2()` calls `mark_lval2` for lval fields, `mark_ptr_only` for strings
- [ ] Remove unused `mark_and_push2()` if present
- [ ] Add `mark_async_handle()` function

### Phase 2: Fix Parallel Mark (gc.c ~line 3173-3265)

- [ ] Create `mark_ptr_only_parallel()` - atomic mark, no queue
- [ ] Create `mark_lval_parallel()` - atomic mark + push lval to queue
- [ ] Create `mark_env_parallel()` - atomic mark + recurse immediately
- [ ] Create `mark_children_parallel()` - dispatch on lval type
- [ ] Remove `mark_and_push2_parallel()` (buggy)
- [ ] Fix `mark_env2_parallel()` to use new functions
- [ ] Fix queue consumer loop to use `mark_children_parallel`

### Phase 3: Arena Integration

- [ ] Create `valk_arena_registry_t` structure
- [ ] Add `valk_gc_register_request_arena()` function
- [ ] Add `valk_gc_unregister_request_arena()` function
- [ ] Add `valk_gc_visit_arena_roots()` function
- [ ] Call arena root visitor from `valk_gc_heap2_mark_roots()`
- [ ] Register arenas in HTTP2 stream begin handler
- [ ] Unregister arenas in HTTP2 stream end handler

### Phase 4: Testing

- [ ] Run `make test` - all tests pass
- [ ] Run `make test-valk-asan` - no ASAN errors
- [ ] Run HTTP server under load with GC stress
- [ ] Verify no memory leaks with valgrind

### Phase 5: Cleanup

- [ ] Remove debug fprintf statements
- [ ] Remove any workarounds added during debugging
- [ ] Update comments to reflect new design
- [ ] Run `make lint` - no warnings

---

## Summary

### Key Invariants

1. **Queue Type Safety**: Mark queue contains ONLY `valk_lval_t*` pointers
2. **Immediate Recursion for Envs**: Environments are processed via recursion, not queued
3. **Leaf Marking for Strings/Arrays**: Strings and arrays are marked but not queued (no children)
4. **Arena Liveness**: Active request arenas are registered as roots during GC

### Function Responsibilities

| Function | Marks? | Queues? | Recurses? | Used For |
|----------|--------|---------|-----------|----------|
| `mark_ptr_only` | Yes | No | No | Strings, arrays, env structs |
| `mark_lval` | Yes | Yes (lval only) | No | lval references |
| `mark_env` | Yes | No | Yes (parent/fallback) | Environment chains |
| `mark_children` | No | Calls mark_lval | Calls mark_env | Queue consumer dispatch |
| `mark_async_handle` | Calls above | Via mark_lval | Via mark_env | Async handle contents |

This design ensures type safety by maintaining a clear separation between:
- Objects that go in the queue (lvals only)
- Objects that are processed immediately (envs)
- Objects that are leaves (strings, arrays)
