# Parallel GC Implementation Plan

## Overview

This document outlines the implementation plan for a parallel stop-the-world (STW) garbage collector for Valkyria Lisp. The goal is to enable safe multi-threaded access to the Lisp heap from multiple AIO event loops while minimizing GC pause times through parallel marking and sweeping.

## Current State

- Single-threaded GC in `gc.c`
- Futures/promises use refcounting (`valk_arc_box`, `valk_future`)
- No safe points in AIO threads
- No coordination between GC and AIO threads
- Lisp values (`valk_lval_t`) are not thread-safe

## Goals

1. **Thread-safe heap access** - Multiple AIO threads can hold `valk_lval_t` references
2. **Parallel STW GC** - All threads pause, all threads help with GC
3. **Unified lifetime management** - Futures become `valk_lval_t`, eliminating double refcounting
4. **< 10ms pause times** - For heaps up to 100MB with 4-8 threads

## Non-Goals (Future Work)

- Concurrent GC (requires write barriers)
- Generational GC
- Compacting GC

---

## Architecture

### Heap Structure

```
┌─────────────────────────────────────────────────────────┐
│                     Global Heap                          │
├─────────────┬─────────────┬─────────────┬───────────────┤
│   Chunk 0   │   Chunk 1   │   Chunk 2   │   Chunk N     │
│   64 KB     │   64 KB     │   64 KB     │   64 KB       │
├─────────────┼─────────────┼─────────────┼───────────────┤
│  Free List  │  Free List  │  Free List  │  Free List    │
│  (local)    │  (local)    │  (local)    │  (local)      │
└─────────────┴─────────────┴─────────────┴───────────────┘

┌─────────────┐  ┌─────────────┐  ┌─────────────┐
│  Thread 0   │  │  Thread 1   │  │  Thread N   │
│    TLAB     │  │    TLAB     │  │    TLAB     │
│  (4 KB)     │  │  (4 KB)     │  │  (4 KB)     │
└─────────────┘  └─────────────┘  └─────────────┘
```

**TLAB (Thread-Local Allocation Buffer):**
- Each thread allocates from its own buffer
- No locking on fast path (bump pointer)
- When exhausted, acquire new chunk from global pool

**Chunks:**
- Fixed-size memory regions (64 KB default)
- Each chunk has its own free list for sweeping
- Chunks can be swept in parallel without contention

### Thread Coordination

```
┌────────────────────────────────────────────────────────────┐
│                      GC Coordinator                         │
│                                                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │
│  │ gc_requested│  │threads_ready│  │  gc_phase   │         │
│  │  (atomic)   │  │  (atomic)   │  │  (atomic)   │         │
│  └─────────────┘  └─────────────┘  └─────────────┘         │
│                                                             │
│  ┌─────────────────────────────────────────────┐           │
│  │              Thread Barrier                  │           │
│  │  (pthread_barrier or custom)                │           │
│  └─────────────────────────────────────────────┘           │
└────────────────────────────────────────────────────────────┘

     │              │              │              │
     ▼              ▼              ▼              ▼
┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐
│ Lisp    │   │ AIO-1   │   │ AIO-2   │   │ AIO-N   │
│ Thread  │   │ Thread  │   │ Thread  │   │ Thread  │
│         │   │         │   │         │   │         │
│ roots[] │   │ roots[] │   │ roots[] │   │ roots[] │
└─────────┘   └─────────┘   └─────────┘   └─────────┘
```

### GC Phases

```
Phase 0: IDLE
    │
    ▼ (allocation pressure or explicit trigger)
Phase 1: STW_REQUESTED
    │
    ▼ (all threads reach safe point)
Phase 2: MARK
    │   - Each thread marks its own roots
    │   - Work-stealing for shared marking
    │
    ▼ (mark queue empty)
Phase 3: SWEEP  
    │   - Divide chunks among threads
    │   - Each thread sweeps assigned chunks
    │
    ▼ (sweep complete)
Phase 4: RESUME
    │
    ▼ (all threads released)
Phase 0: IDLE
```

---

## Implementation Phases

### Phase 1: Heap Restructuring

**Goal:** Replace current heap with chunk-based allocator.

#### 1.1 Chunk Allocator

```c
// src/gc.h

#define VALK_GC_CHUNK_SIZE (64 * 1024)  // 64 KB
#define VALK_GC_TLAB_SIZE  (4 * 1024)   // 4 KB

typedef struct valk_gc_chunk {
  struct valk_gc_chunk *next;
  _Atomic uint32_t num_allocated;
  uint32_t num_objects;
  uint8_t mark_bits[];  // bitmap: 1 bit per object slot
  // followed by object slots
} valk_gc_chunk_t;

typedef struct valk_gc_heap {
  valk_mutex_t lock;
  valk_gc_chunk_t *chunks;        // all chunks
  valk_gc_chunk_t *free_chunks;   // chunks with free space
  size_t num_chunks;
  size_t total_allocated;
  size_t gc_threshold;
  // ... stats
} valk_gc_heap_t;
```

#### 1.2 Thread-Local Allocation Buffers

```c
// src/gc.h

typedef struct valk_gc_tlab {
  uint8_t *start;
  uint8_t *ptr;      // bump pointer
  uint8_t *limit;
  valk_gc_chunk_t *chunk;
} valk_gc_tlab_t;

// In thread context
typedef struct valk_thread_gc_ctx {
  valk_gc_tlab_t tlab;
  valk_lval_t **root_stack;
  size_t root_stack_count;
  size_t root_stack_capacity;
} valk_thread_gc_ctx_t;

extern __thread valk_thread_gc_ctx_t valk_gc_thread_ctx;
```

#### 1.3 Allocation Fast Path

```c
// src/gc.c

static inline valk_lval_t *valk_gc_alloc_fast(size_t size) {
  valk_gc_tlab_t *tlab = &valk_gc_thread_ctx.tlab;
  size_t aligned = ALIGN_UP(size, 16);
  
  if (LIKELY(tlab->ptr + aligned <= tlab->limit)) {
    void *result = tlab->ptr;
    tlab->ptr += aligned;
    return result;
  }
  
  return valk_gc_alloc_slow(size);
}
```

#### Test Artifacts - Phase 1

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_chunk_alloc` | Allocate and free chunks | No memory leaks, correct sizing |
| `test_gc_tlab_bump` | TLAB bump allocation | O(1) allocation, no locks on fast path |
| `test_gc_tlab_refill` | TLAB exhaustion and refill | Seamless transition to new chunk |
| `test_gc_multithread_alloc` | 4 threads allocating concurrently | No races, no corruption, all allocations valid |

---

### Phase 2: Safe Points and Thread Coordination

**Goal:** Implement mechanism for all threads to pause for GC.

#### 2.1 GC State Machine

```c
// src/gc.h

typedef enum {
  VALK_GC_IDLE,
  VALK_GC_STW_REQUESTED,
  VALK_GC_MARKING,
  VALK_GC_SWEEPING,
} valk_gc_phase_e;

typedef struct valk_gc_coordinator {
  _Atomic valk_gc_phase_e phase;
  _Atomic size_t threads_registered;
  _Atomic size_t threads_paused;
  valk_mutex_t lock;
  valk_cond_t all_paused;
  valk_cond_t gc_done;
} valk_gc_coordinator_t;

extern valk_gc_coordinator_t valk_gc_coord;
```

#### 2.2 Safe Point Implementation

```c
// src/gc.h

#define VALK_GC_SAFE_POINT() \
  do { \
    if (UNLIKELY(atomic_load_explicit(&valk_gc_coord.phase, \
                 memory_order_acquire) != VALK_GC_IDLE)) { \
      valk_gc_safe_point_slow(); \
    } \
  } while (0)

// src/gc.c

void valk_gc_safe_point_slow(void) {
  // Signal we've reached safe point
  size_t paused = atomic_fetch_add(&valk_gc_coord.threads_paused, 1,
                                    memory_order_acq_rel) + 1;
  
  // If we're the last thread, signal coordinator
  if (paused == atomic_load(&valk_gc_coord.threads_registered)) {
    valk_cond_signal(&valk_gc_coord.all_paused);
  }
  
  // Wait for GC to complete
  valk_mutex_lock(&valk_gc_coord.lock);
  while (atomic_load(&valk_gc_coord.phase) != VALK_GC_IDLE) {
    valk_cond_wait(&valk_gc_coord.gc_done, &valk_gc_coord.lock);
  }
  valk_mutex_unlock(&valk_gc_coord.lock);
  
  atomic_fetch_sub(&valk_gc_coord.threads_paused, 1, memory_order_release);
}
```

#### 2.3 Safe Point Placement

```c
// In AIO event loop (src/aio/aio_system.c)
while (running) {
  VALK_GC_SAFE_POINT();
  uv_run(loop, UV_RUN_ONCE);
  process_completions();
}

// In eval loop (src/parser.c or eval.c)
valk_lval_t *valk_lval_eval(valk_lenv_t *e, valk_lval_t *v) {
  VALK_GC_SAFE_POINT();
  // ... eval logic
}

// In builtin that might run long
valk_lval_t *builtin_map(valk_lenv_t *e, valk_lval_t *args) {
  for (size_t i = 0; i < count; i++) {
    VALK_GC_SAFE_POINT();
    // ... process element
  }
}
```

#### 2.4 Thread Registration

```c
// src/gc.c

void valk_gc_thread_register(void) {
  atomic_fetch_add(&valk_gc_coord.threads_registered, 1, memory_order_release);
  // Initialize thread-local GC context
  valk_gc_thread_ctx.tlab = (valk_gc_tlab_t){0};
  valk_gc_thread_ctx.root_stack = malloc(sizeof(valk_lval_t*) * 256);
  valk_gc_thread_ctx.root_stack_capacity = 256;
  valk_gc_thread_ctx.root_stack_count = 0;
}

void valk_gc_thread_unregister(void) {
  // Must be at safe point
  VALK_GC_SAFE_POINT();
  atomic_fetch_sub(&valk_gc_coord.threads_registered, 1, memory_order_release);
  free(valk_gc_thread_ctx.root_stack);
}
```

#### Test Artifacts - Phase 2

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_safe_point_single` | Single thread hits safe point | Thread pauses, resumes after GC |
| `test_gc_stw_basic` | 4 threads, trigger STW | All threads pause within 10ms |
| `test_gc_stw_under_load` | Threads allocating during STW request | All threads eventually pause, no deadlock |
| `test_gc_thread_register` | Threads joining/leaving during GC | Correct counting, no races |
| `test_gc_safe_point_eval` | GC triggered during deep eval | Eval pauses cleanly, resumes correctly |

---

### Phase 3: Root Enumeration

**Goal:** Each thread can enumerate its roots for GC scanning.

#### 3.1 Root Stack (for temporaries during eval)

```c
// src/gc.h

#define VALK_GC_ROOT_PUSH(val) \
  valk_gc_root_push_impl(val)

#define VALK_GC_ROOT_POP() \
  valk_gc_root_pop_impl()

#define VALK_GC_WITH_ROOT(val, body) \
  do { \
    VALK_GC_ROOT_PUSH(val); \
    body; \
    VALK_GC_ROOT_POP(); \
  } while (0)

// src/gc.c

static inline void valk_gc_root_push_impl(valk_lval_t *val) {
  valk_thread_gc_ctx_t *ctx = &valk_gc_thread_ctx;
  if (ctx->root_stack_count >= ctx->root_stack_capacity) {
    ctx->root_stack_capacity *= 2;
    ctx->root_stack = realloc(ctx->root_stack, 
                               sizeof(valk_lval_t*) * ctx->root_stack_capacity);
  }
  ctx->root_stack[ctx->root_stack_count++] = val;
}

static inline void valk_gc_root_pop_impl(void) {
  valk_gc_thread_ctx.root_stack_count--;
}
```

#### 3.2 Global Roots Registry

```c
// src/gc.h

typedef struct valk_gc_roots {
  valk_mutex_t lock;
  valk_lval_t ***roots;      // array of pointers to root pointers
  size_t count;
  size_t capacity;
} valk_gc_roots_t;

extern valk_gc_roots_t valk_gc_global_roots;

// For environments, global symbols, etc.
void valk_gc_add_global_root(valk_lval_t **root);
void valk_gc_remove_global_root(valk_lval_t **root);
```

#### 3.3 Per-Thread Root Enumeration

```c
// src/gc.c

typedef void (*valk_gc_root_visitor)(valk_lval_t *root, void *ctx);

void valk_gc_visit_thread_roots(valk_gc_root_visitor visitor, void *ctx) {
  valk_thread_gc_ctx_t *tc = &valk_gc_thread_ctx;
  
  // Visit root stack
  for (size_t i = 0; i < tc->root_stack_count; i++) {
    visitor(tc->root_stack[i], ctx);
  }
}

void valk_gc_visit_global_roots(valk_gc_root_visitor visitor, void *ctx) {
  valk_gc_roots_t *roots = &valk_gc_global_roots;
  
  valk_mutex_lock(&roots->lock);
  for (size_t i = 0; i < roots->count; i++) {
    visitor(*roots->roots[i], ctx);
  }
  valk_mutex_unlock(&roots->lock);
}
```

#### Test Artifacts - Phase 3

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_root_push_pop` | Push/pop roots during eval | Stack correctly maintained |
| `test_gc_root_overflow` | Exceed initial root stack capacity | Resizes correctly |
| `test_gc_global_roots` | Add/remove global roots | No leaks, correct enumeration |
| `test_gc_roots_multithread` | Each thread has separate root stack | No interference between threads |
| `test_gc_enumerate_all` | Full root enumeration | All roots found, no duplicates |

---

### Phase 4: Parallel Mark

**Goal:** All threads participate in marking phase using work-stealing.

#### 4.1 Mark Queue (Work-Stealing Deque)

```c
// src/gc.h

#define VALK_GC_MARK_QUEUE_SIZE 4096

typedef struct valk_gc_mark_queue {
  _Atomic(valk_lval_t *) items[VALK_GC_MARK_QUEUE_SIZE];
  _Atomic size_t top;     // owner pushes/pops here
  _Atomic size_t bottom;  // thieves steal from here
} valk_gc_mark_queue_t;

// Per-thread mark queue
extern __thread valk_gc_mark_queue_t valk_gc_mark_queue;

// Work-stealing operations
bool valk_gc_mark_queue_push(valk_lval_t *val);
valk_lval_t *valk_gc_mark_queue_pop(void);      // local pop
valk_lval_t *valk_gc_mark_queue_steal(valk_gc_mark_queue_t *victim);
```

#### 4.2 Work-Stealing Implementation

```c
// src/gc.c

// Chase-Lev deque (simplified)

bool valk_gc_mark_queue_push(valk_lval_t *val) {
  valk_gc_mark_queue_t *q = &valk_gc_mark_queue;
  size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  
  if (b - t >= VALK_GC_MARK_QUEUE_SIZE) {
    return false;  // queue full, need to process some
  }
  
  atomic_store_explicit(&q->items[b % VALK_GC_MARK_QUEUE_SIZE], val,
                        memory_order_relaxed);
  atomic_thread_fence(memory_order_release);
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  return true;
}

valk_lval_t *valk_gc_mark_queue_pop(void) {
  valk_gc_mark_queue_t *q = &valk_gc_mark_queue;
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed) - 1;
  atomic_store_explicit(&q->bottom, b, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);
  size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
  
  if (t <= b) {
    valk_lval_t *val = atomic_load_explicit(&q->items[b % VALK_GC_MARK_QUEUE_SIZE],
                                             memory_order_relaxed);
    if (t == b) {
      if (!atomic_compare_exchange_strong(&q->top, &t, t + 1)) {
        val = NULL;  // lost race with stealer
      }
      atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
    }
    return val;
  }
  
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  return NULL;  // empty
}

valk_lval_t *valk_gc_mark_queue_steal(valk_gc_mark_queue_t *victim) {
  size_t t = atomic_load_explicit(&victim->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  size_t b = atomic_load_explicit(&victim->bottom, memory_order_acquire);
  
  if (t >= b) {
    return NULL;  // empty
  }
  
  valk_lval_t *val = atomic_load_explicit(
      &victim->items[t % VALK_GC_MARK_QUEUE_SIZE], memory_order_relaxed);
  
  if (!atomic_compare_exchange_strong(&victim->top, &t, t + 1)) {
    return NULL;  // lost race
  }
  
  return val;
}
```

#### 4.3 Parallel Mark Algorithm

```c
// src/gc.c

void valk_gc_parallel_mark(void) {
  // Phase 1: Each thread marks its own roots
  valk_gc_visit_thread_roots(mark_and_push, NULL);
  
  // Thread 0 also marks global roots
  if (valk_gc_thread_id == 0) {
    valk_gc_visit_global_roots(mark_and_push, NULL);
  }
  
  // Barrier: wait for all threads to finish root marking
  valk_gc_barrier_wait();
  
  // Phase 2: Work-stealing mark loop
  while (true) {
    // Try local work first
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop()) != NULL) {
      mark_children(obj);
    }
    
    // Try stealing from others
    bool found_work = false;
    for (size_t i = 0; i < num_gc_threads; i++) {
      if (i == valk_gc_thread_id) continue;
      
      obj = valk_gc_mark_queue_steal(&all_mark_queues[i]);
      if (obj != NULL) {
        mark_children(obj);
        found_work = true;
        break;
      }
    }
    
    if (!found_work) {
      // Check termination condition
      if (valk_gc_try_terminate()) {
        break;
      }
    }
  }
}

static void mark_and_push(valk_lval_t *obj, void *ctx) {
  (void)ctx;
  if (obj == NULL) return;
  
  // Atomically set mark bit
  if (!valk_gc_try_mark(obj)) {
    return;  // already marked
  }
  
  valk_gc_mark_queue_push(obj);
}

static void mark_children(valk_lval_t *obj) {
  switch (obj->type) {
    case LVAL_CONS:
      mark_and_push(obj->cell.car, NULL);
      mark_and_push(obj->cell.cdr, NULL);
      break;
    case LVAL_FUN:
      mark_and_push(obj->fun.formals, NULL);
      mark_and_push(obj->fun.body, NULL);
      mark_and_push((valk_lval_t*)obj->fun.env, NULL);
      break;
    case LVAL_FUTURE:
      mark_and_push(obj->future.result, NULL);
      // ... mark callbacks if they hold lvals
      break;
    // ... other types
  }
}
```

#### 4.4 Termination Detection

```c
// src/gc.c

// Dijkstra's termination detection
typedef struct {
  _Atomic size_t idle_count;
  _Atomic bool terminated;
} valk_gc_termination_t;

static valk_gc_termination_t term_state;

bool valk_gc_try_terminate(void) {
  size_t idle = atomic_fetch_add(&term_state.idle_count, 1, memory_order_acq_rel) + 1;
  
  if (idle == num_gc_threads) {
    // Everyone is idle, check if really done
    bool all_empty = true;
    for (size_t i = 0; i < num_gc_threads; i++) {
      if (!mark_queue_empty(&all_mark_queues[i])) {
        all_empty = false;
        break;
      }
    }
    
    if (all_empty) {
      atomic_store(&term_state.terminated, true, memory_order_release);
      return true;
    }
  }
  
  // Wait briefly, then check termination flag
  for (int i = 0; i < 100; i++) {
    if (atomic_load(&term_state.terminated, memory_order_acquire)) {
      return true;
    }
    __builtin_ia32_pause();  // spin hint
  }
  
  atomic_fetch_sub(&term_state.idle_count, 1, memory_order_release);
  return false;
}
```

#### Test Artifacts - Phase 4

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_mark_queue_basic` | Single-thread push/pop | FIFO behavior correct |
| `test_gc_work_stealing` | Producer/consumer with stealing | All items processed exactly once |
| `test_gc_parallel_mark_simple` | Mark simple object graph | All reachable marked, unreachable not |
| `test_gc_parallel_mark_deep` | Mark deeply nested structure | No stack overflow, correct marking |
| `test_gc_parallel_mark_wide` | Mark wide structure (big list) | Work distributed across threads |
| `test_gc_termination` | Detect when marking complete | Terminates correctly, no premature exit |
| `test_gc_mark_cycles` | Graph with cycles | Marks each object once, terminates |

---

### Phase 5: Parallel Sweep

**Goal:** Threads divide chunks and sweep in parallel.

#### 5.1 Chunk Assignment

```c
// src/gc.c

void valk_gc_parallel_sweep(void) {
  valk_gc_heap_t *heap = &global_heap;
  
  // Simple static partitioning
  size_t chunks_per_thread = heap->num_chunks / num_gc_threads;
  size_t my_start = valk_gc_thread_id * chunks_per_thread;
  size_t my_end = (valk_gc_thread_id == num_gc_threads - 1) 
                  ? heap->num_chunks 
                  : my_start + chunks_per_thread;
  
  // Sweep my chunks
  for (size_t i = my_start; i < my_end; i++) {
    sweep_chunk(&heap->chunks[i]);
  }
  
  // Barrier: wait for all sweeping to complete
  valk_gc_barrier_wait();
}
```

#### 5.2 Chunk Sweeping

```c
// src/gc.c

static void sweep_chunk(valk_gc_chunk_t *chunk) {
  size_t slot_size = /* determined by chunk type or fixed */;
  size_t num_slots = (VALK_GC_CHUNK_SIZE - sizeof(valk_gc_chunk_t)) / slot_size;
  
  chunk->free_list = NULL;
  chunk->num_free = 0;
  
  uint8_t *slots = (uint8_t*)(chunk + 1);
  
  for (size_t i = 0; i < num_slots; i++) {
    if (!bitmap_test(chunk->mark_bits, i)) {
      // Not marked -> free
      valk_lval_t *obj = (valk_lval_t*)(slots + i * slot_size);
      
      // Call finalizer if needed
      if (obj->type == LVAL_REF && obj->ref.free) {
        obj->ref.free(obj->ref.data);
      }
      
      // Add to chunk's free list
      obj->cell.cdr = (valk_lval_t*)chunk->free_list;
      chunk->free_list = obj;
      chunk->num_free++;
    } else {
      // Marked -> clear for next cycle
      bitmap_clear(chunk->mark_bits, i);
    }
  }
  
  // Update stats
  atomic_fetch_sub(&global_heap.total_allocated, chunk->num_free * slot_size,
                   memory_order_relaxed);
}
```

#### Test Artifacts - Phase 5

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_sweep_empty` | Sweep with nothing marked | All objects freed |
| `test_gc_sweep_all_live` | Sweep with everything marked | Nothing freed |
| `test_gc_sweep_mixed` | Some live, some dead | Correct objects freed |
| `test_gc_sweep_parallel` | 4 threads sweeping | No races, correct free counts |
| `test_gc_sweep_finalizers` | Objects with finalizers | Finalizers called once |

---

### Phase 6: Integration

**Goal:** Wire everything together, make futures use GC.

#### 6.1 New Future Type

```c
// src/parser.h (or types.h)

typedef enum {
  // ... existing types ...
  LVAL_FUTURE,
} valk_lval_type_e;

typedef struct {
  _Atomic bool done;
  _Atomic bool is_error;
  valk_lval_t *result;        // GC-managed
  valk_mutex_t mutex;
  valk_cond_t resolved;
  struct valk_future_callback *callbacks;  // intrusive list
} valk_future_data_t;

// In valk_lval_t union
struct {
  valk_future_data_t *data;  // separately allocated, but GC-managed
} future;
```

#### 6.2 GC-Aware Future Operations

```c
// src/concurrency.c

valk_lval_t *valk_future_new(void) {
  valk_lval_t *f = valk_gc_alloc(sizeof(valk_lval_t));
  f->type = LVAL_FUTURE;
  f->future.data = valk_gc_alloc(sizeof(valk_future_data_t));
  
  valk_future_data_t *d = f->future.data;
  atomic_store(&d->done, false);
  atomic_store(&d->is_error, false);
  d->result = NULL;
  valk_mutex_init(&d->mutex);
  valk_cond_init(&d->resolved);
  d->callbacks = NULL;
  
  return f;
}

void valk_future_resolve(valk_lval_t *future, valk_lval_t *result) {
  valk_future_data_t *d = future->future.data;
  
  valk_mutex_lock(&d->mutex);
  if (atomic_exchange(&d->done, true)) {
    valk_mutex_unlock(&d->mutex);
    return;  // already resolved
  }
  
  d->result = result;  // GC will trace this
  
  // Fire callbacks
  struct valk_future_callback *cb = d->callbacks;
  d->callbacks = NULL;
  valk_cond_broadcast(&d->resolved);
  valk_mutex_unlock(&d->mutex);
  
  while (cb != NULL) {
    struct valk_future_callback *next = cb->next;
    cb->fn(cb->ctx, result);
    cb = next;
  }
}
```

#### 6.3 GC Marking for Futures

```c
// src/gc.c

static void mark_children(valk_lval_t *obj) {
  switch (obj->type) {
    // ... other cases ...
    
    case LVAL_FUTURE: {
      valk_future_data_t *d = obj->future.data;
      mark_and_push((valk_lval_t*)d, NULL);  // mark the data struct
      if (d->result) {
        mark_and_push(d->result, NULL);
      }
      // Note: callbacks may hold lval refs, need to trace those too
      break;
    }
  }
}
```

#### 6.4 AIO Integration

```c
// src/aio/aio_system.c

void valk_aio_thread_main(void *arg) {
  valk_aio_system_t *sys = arg;
  
  // Register with GC
  valk_gc_thread_register();
  
  while (!sys->shutdown) {
    VALK_GC_SAFE_POINT();
    
    int r = uv_run(&sys->loop, UV_RUN_ONCE);
    // ...
  }
  
  valk_gc_thread_unregister();
}
```

#### Test Artifacts - Phase 6

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_future_basic` | Create/resolve future | No leaks, correct lifecycle |
| `test_gc_future_callback` | Future with and_then | Callback fires, result correct |
| `test_gc_future_collect` | GC while futures pending | Pending futures not collected |
| `test_gc_future_resolved_collect` | GC after future resolved | Resolved futures can be collected when unreachable |
| `test_gc_future_cross_thread` | Future created on AIO, consumed on Lisp thread | Correct GC behavior |
| `test_gc_future_join` | Join two futures from different AIOs | Both results accessible |
| `test_gc_integration_http` | Full HTTP request/response cycle | No leaks over 1000 requests |

---

## Testing Strategy

### Unit Tests

Located in `test/unit/test_gc_parallel.c`:

```c
void test_gc_chunk_alloc(VALK_TEST_ARGS());
void test_gc_tlab_bump(VALK_TEST_ARGS());
void test_gc_safe_point_single(VALK_TEST_ARGS());
void test_gc_stw_basic(VALK_TEST_ARGS());
void test_gc_parallel_mark_simple(VALK_TEST_ARGS());
void test_gc_work_stealing(VALK_TEST_ARGS());
void test_gc_parallel_sweep(VALK_TEST_ARGS());
void test_gc_future_basic(VALK_TEST_ARGS());
// ... etc
```

### Stress Tests

Located in `test/stress/`:

| Test File | Description | Duration |
|-----------|-------------|----------|
| `stress_gc_alloc.c` | Continuous allocation across threads | 60s |
| `stress_gc_churn.c` | High allocation + GC rate | 60s |
| `stress_gc_futures.c` | Many concurrent futures | 60s |
| `stress_gc_http.c` | HTTP server under load with GC | 120s |

### Correctness Verification

1. **ASAN/TSAN builds**: Run all tests with sanitizers
2. **Deterministic replay**: Record allocation order, replay to verify consistency
3. **Mark verification**: After mark, verify no unmarked object is reachable from roots

### Performance Benchmarks

| Benchmark | Metric | Target |
|-----------|--------|--------|
| `bench_gc_pause_time` | Max pause time | < 10ms for 100MB heap |
| `bench_gc_throughput` | Allocations/sec during GC | > 50% of no-GC rate |
| `bench_gc_parallel_speedup` | N-thread vs 1-thread pause | > 0.7 * N speedup |

---

## Rollout Plan

### Stage 1: Foundation (2-3 weeks)
- [ ] Phase 1: Chunk allocator + TLABs
- [ ] Phase 2: Safe points + STW coordination
- [ ] Unit tests passing
- [ ] ASAN/TSAN clean

### Stage 2: Parallel GC (2-3 weeks)
- [ ] Phase 3: Root enumeration
- [ ] Phase 4: Parallel mark with work-stealing
- [ ] Phase 5: Parallel sweep
- [ ] Stress tests passing

### Stage 3: Integration (2 weeks)
- [ ] Phase 6: Futures as lvals
- [ ] AIO integration
- [ ] Remove old refcounting code
- [ ] Full test suite passing

### Stage 4: Optimization (1-2 weeks)
- [ ] Profile and optimize hot paths
- [ ] Tune chunk sizes, TLAB sizes
- [ ] Benchmark against targets

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Work-stealing bugs | Missed objects, corruption | Extensive testing, formal verification of deque |
| Safe point placement | Deadlock or long pauses | Audit all blocking calls, add timeout detection |
| Cross-thread races | Memory corruption | TSAN, careful review of atomics |
| Performance regression | Slower than refcounting | Benchmark early, optimize TLABs |
| Finalizer ordering | Resource leaks | Document ordering guarantees, test thoroughly |

---

## References

1. [The Garbage Collection Handbook](https://gchandbook.org/) - Jones, Hosking, Moss
2. [Chase-Lev Deque](https://www.dre.vanderbilt.edu/~schmidt/PDF/work-stealing-dequeue.pdf) - Work-stealing algorithm
3. [V8 Orinoco GC](https://v8.dev/blog/trash-talk) - Parallel GC in practice
4. [Go GC](https://go.dev/blog/ismmkeynote) - Concurrent GC design
5. [JVM G1 GC](https://www.oracle.com/technetwork/tutorials/tutorials-1876574.html) - Parallel + concurrent hybrid
