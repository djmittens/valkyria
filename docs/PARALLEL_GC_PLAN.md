# Parallel GC Implementation Plan

## Overview

This document outlines the implementation plan for a parallel stop-the-world (STW) garbage collector for Valkyria Lisp. The goal is to enable safe multi-threaded access to the Lisp heap from multiple AIO event loops while minimizing GC pause times through parallel marking and sweeping.

## Current State Analysis

### Existing Memory Architecture

The current system uses a **three-tier memory model**:

```
┌─────────────────────────────────────────────────────────────────┐
│                     CURRENT MEMORY LAYOUT                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────┐    Checkpoint     ┌──────────────────┐ │
│  │   SCRATCH ARENA     │ ──────────────────▶│    GC HEAP       │ │
│  │   (Bump allocator)  │    Evacuation     │  (Mark & Sweep)  │ │
│  │                     │                    │                  │ │
│  │  • Ephemeral values │                    │  • lval slab     │ │
│  │  • Fast O(1) alloc  │                    │    (256K slots)  │ │
│  │  • Reset after eval │                    │  • lenv slab     │ │
│  │                     │                    │    (64K slots)   │ │
│  └─────────────────────┘                    │  • malloc overflow│ │
│                                             │                  │ │
│                                             │  Objects tracked │ │
│                                             │  via gc_header_t │ │
│                                             │  linked list     │ │
│                                             └──────────────────┘ │
└─────────────────────────────────────────────────────────────────┘
```

**Key components in `gc.c`:**

1. **`valk_gc_malloc_heap_t`** - Main GC heap with:
   - `lval_slab` - Slab allocator for `valk_lval_t` (256K objects)
   - `lenv_slab` - Slab allocator for `valk_lenv_t` (64K objects)  
   - `objects` - Linked list of all allocations via `valk_gc_header_t`
   - `root_env` - Single root for mark phase

2. **`valk_mem_arena_t`** (scratch) - Bump allocator for ephemeral values
   - Evacuated to GC heap at checkpoint boundaries
   - Values get `LVAL_ALLOC_SCRATCH` flag, changed to `LVAL_ALLOC_HEAP` after evacuation

3. **Marking** uses iterative worklist (`valk_lval_worklist_t`, `valk_env_worklist_t`)
   - `valk_gc_mark_lval_single()` - type-switch over `LVAL_TYPE`
   - Already handles all object types correctly

4. **Single-threaded limitations:**
   - No safe points in AIO threads
   - No coordination between GC and AIO threads
   - Single root environment only
   - Futures/promises use separate refcounting (`valk_arc_box`)

### What Works Well (Keep)

- **Scratch → Heap evacuation model** - Clean separation of ephemeral vs long-lived
- **Type-based object scanning** - `switch(LVAL_TYPE(v))` already handles all children
- **Slab allocators** - Fast fixed-size allocation for common objects
- **Iterative worklist marking** - No recursion stack overflow

### What Needs to Change (Parallel GC)

| Current | Parallel GC |
|---------|-------------|
| Single `heap->root_env` | Per-thread root stacks + global roots registry |
| `heap->objects` linked list | Per-chunk object arrays with mark bitmaps |
| Local worklist (`valk_lval_worklist_t`) | Work-stealing deques (Chase-Lev) |
| Single-threaded mark/sweep | Parallel with barrier synchronization |
| No safe points | Safe points in eval loop + AIO loops |
| Implicit GC timing | Coordinated STW with all threads |

---

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

### Memory Layout (Parallel)

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        PARALLEL GC MEMORY LAYOUT                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  Per-Thread (TLS)                          Global (Shared)               │
│  ═══════════════                           ═══════════════               │
│                                                                          │
│  ┌────────────────┐                        ┌────────────────────────┐   │
│  │  Thread 0      │                        │      Chunk Pool        │   │
│  │  ┌──────────┐  │                        │  ┌────────┬────────┐   │   │
│  │  │  TLAB    │  │ ◀── acquire ──────────▶│  │Chunk 0 │Chunk 1 │...│   │
│  │  │ (4 KB)   │  │                        │  │ 64KB   │ 64KB   │   │   │
│  │  └──────────┘  │                        │  │        │        │   │   │
│  │  ┌──────────┐  │                        │  │mark_   │mark_   │   │   │
│  │  │Root Stack│  │                        │  │bits[]  │bits[]  │   │   │
│  │  │  (eval   │  │                        │  └────────┴────────┘   │   │
│  │  │ temps)   │  │                        └────────────────────────┘   │
│  │  └──────────┘  │                                                      │
│  │  ┌──────────┐  │                        ┌────────────────────────┐   │
│  │  │Mark Queue│  │ ◀── steal ────────────▶│   Other Thread Queues  │   │
│  │  │(Chase-Lev│  │                        └────────────────────────┘   │
│  │  │ deque)   │  │                                                      │
│  │  └──────────┘  │                        ┌────────────────────────┐   │
│  │  ┌──────────┐  │                        │    Global Roots        │   │
│  │  │ Scratch  │  │                        │  • root_env            │   │
│  │  │ Arena    │  │ ──── evacuate ────────▶│  • registered roots    │   │
│  │  │(optional)│  │     (at checkpoint)    │  • pending futures     │   │
│  │  └──────────┘  │                        └────────────────────────┘   │
│  └────────────────┘                                                      │
│                                                                          │
│  ┌────────────────┐                        ┌────────────────────────┐   │
│  │  Thread 1      │                        │    GC Coordinator      │   │
│  │  (same layout) │                        │  • phase (atomic)      │   │
│  └────────────────┘                        │  • threads_registered  │   │
│                                            │  • threads_paused      │   │
│  ┌────────────────┐                        │  • barrier             │   │
│  │  Thread N      │                        └────────────────────────┘   │
│  │  (same layout) │                                                      │
│  └────────────────┘                                                      │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Root Discovery (Critical for Parallel GC)

The key challenge is **finding all roots** across multiple threads. Here's the complete root enumeration:

```
ROOT SOURCES
════════════

Per-Thread Roots (enumerated by each thread at safe point):
├── Root Stack
│   └── Explicit pushes: VALK_GC_ROOT_PUSH(val) during eval
│       - Function arguments before eval
│       - Intermediate results
│       - Loop variables in builtins
│
├── Scratch Arena (if not using checkpoint-first model)
│   └── All LVAL_ALLOC_SCRATCH objects in arena bounds
│   └── NOTE: Current design evacuates BEFORE GC, so scratch is empty
│
└── TLAB In-Flight Allocations
    └── Objects allocated since last safe point
    └── Tracked via TLAB bump pointer range

Global Roots (enumerated by thread 0):
├── root_env (global Lisp environment)
│   └── All def'd symbols and their values
│
├── Global Roots Registry
│   └── valk_gc_add_global_root(&ptr) - for C-side persistent refs
│   └── Callback functions, constants, module exports
│
└── Pending Async Handles
    └── LVAL_HANDLE objects with active I/O
    └── Their callbacks, results, environments
```

### Object Scanning (Already Well-Structured)

The existing `valk_gc_mark_lval_single()` handles all object types. For parallel GC, we just need **atomic mark bits** and **push to work-stealing queue** instead of local worklist:

```c
static void mark_children(valk_lval_t *obj) {
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      mark_and_push(obj->cons.head);  // Push to thread's work-stealing queue
      mark_and_push(obj->cons.tail);
      break;
      
    case LVAL_FUN:
      if (obj->fun.builtin == NULL) {  // Lambda, not builtin
        mark_and_push(obj->fun.formals);
        mark_and_push(obj->fun.body);
        mark_env(obj->fun.env);  // Closure environment
      }
      break;
      
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_and_push(obj->async.handle->on_complete);
        mark_and_push(obj->async.handle->on_error);
        mark_and_push(obj->async.handle->result);
        mark_env(obj->async.handle->env);
      }
      break;
      
    case LVAL_ENV:
      mark_env(&obj->env);
      break;
      
    // Leaf types - no children
    case LVAL_NUM:
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
    case LVAL_NIL:
    case LVAL_REF:
      break;
  }
}
```

### GC Phases

```
                    ┌─────────────────────────────────────────┐
                    │              GC CYCLE                    │
                    └─────────────────────────────────────────┘

Phase 0: IDLE ──────────────────────────────────────────────────────▶
    │                                                                │
    │ (allocation pressure OR explicit trigger)                      │
    ▼                                                                │
Phase 1: STW_REQUESTED ─────────────────────────────────────────────▶
    │                                                                │
    │ • Set gc_phase = STW_REQUESTED (atomic)                       │
    │ • Threads check phase at safe points                          │
    │ • Each thread: evacuate scratch → heap (optional)             │
    │ • Each thread: increment threads_paused                       │
    │ • Last thread signals coordinator                              │
    │                                                                │
    ▼ (all threads at safe point)                                   │
Phase 2: MARK ──────────────────────────────────────────────────────▶
    │                                                                │
    │ • Each thread marks its own root stack                        │
    │ • Thread 0 marks global roots (root_env, registry)            │
    │ • Barrier: wait for root marking complete                      │
    │ • Work-stealing loop: pop local queue, steal from others      │
    │ • Termination detection (all queues empty, all idle)          │
    │                                                                │
    ▼ (all mark queues empty)                                       │
Phase 3: SWEEP ─────────────────────────────────────────────────────▶
    │                                                                │
    │ • Partition chunks among threads                               │
    │ • Each thread sweeps its assigned chunks                      │
    │ • Bitmap scan: unmarked → free, marked → clear bit            │
    │ • Call finalizers for LVAL_REF objects                        │
    │ • Barrier: wait for all sweeping complete                      │
    │                                                                │
    ▼ (sweep complete)                                               │
Phase 4: RESUME ────────────────────────────────────────────────────▶
    │                                                                │
    │ • Set gc_phase = IDLE                                         │
    │ • Broadcast gc_done condition                                  │
    │ • Threads resume execution                                     │
    │                                                                │
    └────────────────────────────────────────────────────────────────┘
```

---

## Implementation Phases

### Phase 0: Prerequisites (Current Work)

**Goal:** Prepare codebase for parallel GC without breaking existing functionality.

#### 0.1 Atomic Mark Bit

Replace the current mark bit check with atomic operations:

```c
// src/gc.h

// Mark bit is already in flags: LVAL_FLAG_GC_MARK = (1ULL << 10)

static inline bool valk_gc_try_mark(valk_lval_t *obj) {
  uint64_t expected = obj->flags;
  do {
    if (expected & LVAL_FLAG_GC_MARK) {
      return false;  // Already marked
    }
    // CAS to set mark bit atomically
  } while (!atomic_compare_exchange_weak(&obj->flags, &expected,
                                          expected | LVAL_FLAG_GC_MARK));
  return true;  // We marked it
}

static inline bool valk_gc_is_marked(valk_lval_t *obj) {
  return (atomic_load(&obj->flags) & LVAL_FLAG_GC_MARK) != 0;
}

static inline void valk_gc_clear_mark(valk_lval_t *obj) {
  atomic_fetch_and(&obj->flags, ~LVAL_FLAG_GC_MARK);
}
```

#### 0.2 Thread Context Extension

Extend `valk_thread_context_t` in `memory.h`:

```c
// src/memory.h

typedef struct valk_thread_gc_ctx {
  // Existing fields
  valk_mem_allocator_t *allocator;
  void *heap;
  valk_mem_arena_t *scratch;
  struct valk_lenv_t *root_env;
  float checkpoint_threshold;
  bool checkpoint_enabled;
  size_t call_depth;
  
  // NEW: Parallel GC fields
  valk_gc_tlab_t *tlab;           // Thread-local allocation buffer
  valk_lval_t **root_stack;       // Explicit root stack for eval temps
  size_t root_stack_count;
  size_t root_stack_capacity;
  size_t gc_thread_id;            // Index in thread registry
  bool gc_registered;             // Whether registered with GC
} valk_thread_context_t;
```

#### Test Artifacts - Phase 0

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_atomic_mark` | Multiple threads racing to mark same object | Exactly one succeeds |
| `test_gc_context_init` | Initialize thread GC context | All fields properly set |
| `test_gc_existing_compat` | Run existing test suite | All tests still pass |

---

### Phase 1: Heap Restructuring

**Goal:** Replace linked-list tracking with chunk-based allocator + mark bitmaps.

#### 1.1 Chunk Structure

```c
// src/gc.h

#define VALK_GC_CHUNK_SIZE   (64 * 1024)   // 64 KB per chunk
#define VALK_GC_CHUNK_ALIGN  64            // Cache line alignment
#define VALK_GC_TLAB_SIZE    (4 * 1024)    // 4 KB per TLAB

// Object slot size - exactly sizeof(valk_lval_t) = 104 bytes
// lenv (80 bytes) also fits with 24 bytes unused
#define VALK_GC_SLOT_SIZE    104

// Number of slots per chunk
#define VALK_GC_SLOTS_PER_CHUNK \
  ((VALK_GC_CHUNK_SIZE - sizeof(valk_gc_chunk_t)) / VALK_GC_SLOT_SIZE)

// Bitmap size in bytes (1 bit per slot)
#define VALK_GC_BITMAP_SIZE  ((VALK_GC_SLOTS_PER_CHUNK + 7) / 8)

typedef struct valk_gc_chunk {
  struct valk_gc_chunk *next;     // Next chunk in pool
  _Atomic uint32_t num_allocated; // Slots currently in use
  uint32_t chunk_id;              // For debugging
  uint8_t mark_bits[VALK_GC_BITMAP_SIZE];  // Mark bitmap
  uint8_t alloc_bits[VALK_GC_BITMAP_SIZE]; // Allocation bitmap
  // Padding to align slots
  uint8_t _padding[VALK_GC_CHUNK_ALIGN - 
                   (sizeof(void*) + sizeof(uint32_t)*2 + VALK_GC_BITMAP_SIZE*2) 
                   % VALK_GC_CHUNK_ALIGN];
  uint8_t slots[];  // Object slots start here
} valk_gc_chunk_t;

typedef struct valk_gc_chunk_pool {
  valk_mutex_t lock;
  valk_gc_chunk_t *all_chunks;     // All allocated chunks (for sweep)
  valk_gc_chunk_t *free_chunks;    // Chunks with free space
  size_t num_chunks;
  size_t total_slots;
  size_t used_slots;
  _Atomic size_t gc_threshold;     // Trigger GC when used_slots exceeds
} valk_gc_chunk_pool_t;
```

#### 1.2 TLAB (Thread-Local Allocation Buffer)

```c
// src/gc.h

typedef struct valk_gc_tlab {
  valk_gc_chunk_t *chunk;      // Current chunk
  uint32_t next_slot;          // Next slot index to allocate
  uint32_t limit_slot;         // Last slot in TLAB range
} valk_gc_tlab_t;

// Fast path: bump allocator within TLAB
static inline void *valk_gc_tlab_alloc(valk_gc_tlab_t *tlab) {
  if (LIKELY(tlab->next_slot < tlab->limit_slot)) {
    uint32_t slot = tlab->next_slot++;
    // Set allocation bit
    tlab->chunk->alloc_bits[slot / 8] |= (1 << (slot % 8));
    atomic_fetch_add(&tlab->chunk->num_allocated, 1, memory_order_relaxed);
    return &tlab->chunk->slots[slot * VALK_GC_SLOT_SIZE];
  }
  return NULL;  // TLAB exhausted, need slow path
}

// Slow path: get new TLAB from chunk pool
void *valk_gc_alloc_slow(size_t size);
```

#### 1.3 Two-Tier Memory Model

The parallel GC uses a two-tier allocation strategy:

**Tier 1: TLAB (for lval/lenv - 104 bytes or less)**
- Lock-free bump-pointer allocation
- Page-based with mark bitmaps for parallel sweep
- ~629 slots per 64KB page

**Tier 2: Per-Thread Malloc Lists (for strings, arrays, large objects)**
- Objects >104 bytes go through malloc()
- Each thread maintains its own linked list (no contention)
- Lists merged during STW before sweep

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    TWO-TIER ALLOCATION MODEL                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  Allocation Request                                                      │
│         │                                                                │
│         ▼                                                                │
│  ┌─────────────────┐                                                    │
│  │ bytes <= 104?   │                                                    │
│  └────────┬────────┘                                                    │
│           │                                                              │
│     YES   │   NO                                                         │
│     ▼     │   ▼                                                          │
│  ┌────────┴────────┐  ┌────────────────────────────────────────┐       │
│  │  TLAB Alloc     │  │  malloc() + append to thread's list    │       │
│  │  (lock-free)    │  │  (thread-local, no contention)         │       │
│  │                 │  │                                         │       │
│  │  • valk_lval_t  │  │  • strings (char*)                     │       │
│  │  • valk_lenv_t  │  │  • large arrays                        │       │
│  └─────────────────┘  │  • any allocation > 104 bytes          │       │
│                       └────────────────────────────────────────┘       │
│                                                                          │
│  During STW (Stop-The-World):                                           │
│  ┌──────────────────────────────────────────────────────────────────┐  │
│  │  1. Merge all per-thread malloc lists into global_malloc_list    │  │
│  │  2. Parallel mark: traverse from roots, mark reachable objects   │  │
│  │  3. Parallel sweep:                                               │  │
│  │     - Pages: scan alloc_bits, clear unmarked slots               │  │
│  │     - Malloc list: traverse, free() unmarked, keep marked        │  │
│  └──────────────────────────────────────────────────────────────────┘  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

#### 1.4 Per-Thread Malloc List

```c
// src/gc.h

// Header for malloc'd objects (strings, arrays, large allocations)
typedef struct valk_gc_malloc_obj {
  struct valk_gc_malloc_obj *next;  // Thread-local list link
  size_t size;                       // Allocation size
  _Atomic uint8_t marked;            // Mark bit for GC
  // User data follows
} valk_gc_malloc_obj_t;

// Per-thread malloc tracking (added to valk_thread_context_t)
typedef struct {
  valk_gc_malloc_obj_t *malloc_list;  // Head of thread-local list
  size_t malloc_bytes;                 // Total bytes in thread's list
} valk_gc_thread_malloc_t;
```

#### 1.5 Malloc List Operations

```c
// src/gc.c

// Thread-local allocation for large objects (no lock needed)
void *valk_gc_malloc_alloc(size_t bytes) {
  size_t total = sizeof(valk_gc_malloc_obj_t) + bytes;
  valk_gc_malloc_obj_t *obj = malloc(total);
  if (!obj) return NULL;
  
  obj->size = bytes;
  atomic_store(&obj->marked, 0);
  
  // Prepend to thread's list (thread-local, no lock)
  obj->next = valk_thread_ctx.malloc_list;
  valk_thread_ctx.malloc_list = obj;
  valk_thread_ctx.malloc_bytes += bytes;
  
  return (void*)(obj + 1);  // Return pointer past header
}

// Called during STW to merge all thread lists into global list
void valk_gc_merge_malloc_lists(valk_gc_malloc_obj_t **global_list) {
  for (size_t i = 0; i < valk_gc_coord.threads_registered; i++) {
    valk_thread_context_t *ctx = valk_gc_coord.threads[i].ctx;
    if (!ctx || !ctx->malloc_list) continue;
    
    // Find tail of thread's list
    valk_gc_malloc_obj_t *tail = ctx->malloc_list;
    while (tail->next) tail = tail->next;
    
    // Append global list to thread's tail, then swap
    tail->next = *global_list;
    *global_list = ctx->malloc_list;
    ctx->malloc_list = NULL;
    ctx->malloc_bytes = 0;
  }
}

// Sweep malloc list (during parallel sweep)
void valk_gc_sweep_malloc_list(valk_gc_malloc_obj_t **list) {
  valk_gc_malloc_obj_t **curr = list;
  while (*curr) {
    valk_gc_malloc_obj_t *obj = *curr;
    if (atomic_load(&obj->marked)) {
      // Keep: clear mark for next cycle
      atomic_store(&obj->marked, 0);
      curr = &obj->next;
    } else {
      // Reclaim: unlink and free
      *curr = obj->next;
      free(obj);
    }
  }
}
```

#### 1.6 Distinguishing TLAB vs Malloc Objects

During marking, we need to know whether a pointer points to a TLAB slot or a malloc'd object:

```c
// src/gc.c

// Check if pointer is within any page's slot range
static inline bool valk_gc_is_page_ptr(void *ptr) {
  // Pages are 64KB aligned, so we can check alignment
  // and verify it's in our page pool
  uintptr_t addr = (uintptr_t)ptr;
  
  // Fast path: check if aligned to slot boundary within a page
  // Page header is ~128 bytes, slots start after
  // Each slot is 104 bytes
  
  // Walk page list (could optimize with hash set for O(1))
  valk_gc_page_t *page = valk_gc_global_pool.all_pages;
  while (page) {
    uintptr_t page_start = (uintptr_t)page->slots;
    uintptr_t page_end = page_start + (VALK_GC_SLOTS_PER_PAGE * VALK_GC_SLOT_SIZE);
    if (addr >= page_start && addr < page_end) {
      return true;
    }
    page = page->next;
  }
  return false;
}

// Mark an object (handles both TLAB and malloc'd)
void valk_gc_mark_object(void *ptr) {
  if (valk_gc_is_page_ptr(ptr)) {
    // TLAB object: set mark bit in page bitmap
    valk_gc_page_t *page = /* find containing page */;
    uint32_t slot_idx = /* compute slot index */;
    valk_gc_bitmap_set(page->mark_bits, slot_idx);
  } else {
    // Malloc'd object: set mark flag in header
    valk_gc_malloc_obj_t *obj = ((valk_gc_malloc_obj_t*)ptr) - 1;
    atomic_store(&obj->marked, 1);
  }
}
```

#### 1.7 Migration Strategy

To migrate from current slab + linked-list to the two-tier model:

1. Keep existing `lval_slab` and `lenv_slab` initially
2. Add TLAB + per-thread malloc lists alongside
3. Migrate incrementally:
   - New lval/lenv allocations go to TLAB
   - New large allocations go to per-thread malloc list
   - Sweep handles both old slabs and new structures
4. Remove old slabs once all objects migrated

#### Test Artifacts - Phase 1

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_chunk_create` | Create and initialize chunk | Bitmaps zeroed, slots accessible |
| `test_gc_chunk_pool_grow` | Pool grows when exhausted | New chunks added, no corruption |
| `test_gc_tlab_alloc` | TLAB bump allocation | O(1), no locks, correct slot |
| `test_gc_tlab_refill` | TLAB exhaustion and refill | Seamless, new chunk acquired |
| `test_gc_bitmap_ops` | Set/clear/test bitmap bits | Correct bit manipulation |
| `test_gc_multithread_alloc` | 4 threads allocating concurrently | No races, all allocations valid |

---

### Phase 2: Safe Points and Thread Coordination

**Goal:** Implement mechanism for all threads to pause for GC.

#### 2.1 GC Coordinator

```c
// src/gc.h

typedef enum {
  VALK_GC_IDLE = 0,
  VALK_GC_STW_REQUESTED,
  VALK_GC_MARKING,
  VALK_GC_SWEEPING,
} valk_gc_phase_e;

typedef struct valk_gc_coordinator {
  _Atomic valk_gc_phase_e phase;
  _Atomic size_t threads_registered;
  _Atomic size_t threads_paused;
  
  // Synchronization primitives
  pthread_mutex_t lock;
  pthread_cond_t all_paused;     // Signaled when all threads at safe point
  pthread_cond_t gc_done;        // Signaled when GC complete
  pthread_barrier_t barrier;     // For sync between GC phases
  
  // Thread registry (for work stealing)
  struct valk_gc_thread_info {
    valk_thread_context_t *ctx;
    pthread_t thread_id;
    bool active;
  } threads[VALK_GC_MAX_THREADS];
  
  // Statistics
  _Atomic uint64_t cycles_total;
  _Atomic uint64_t pause_us_total;
} valk_gc_coordinator_t;

extern valk_gc_coordinator_t valk_gc_coord;
```

#### 2.2 Safe Point Macro

```c
// src/gc.h

// Fast-path check: just read atomic phase
#define VALK_GC_SAFE_POINT() \
  do { \
    if (UNLIKELY(atomic_load_explicit(&valk_gc_coord.phase, \
                 memory_order_acquire) != VALK_GC_IDLE)) { \
      valk_gc_safe_point_slow(); \
    } \
  } while (0)

// For long-running builtins, check periodically
#define VALK_GC_SAFE_POINT_PERIODIC(counter, interval) \
  do { \
    if (UNLIKELY(++(counter) >= (interval))) { \
      (counter) = 0; \
      VALK_GC_SAFE_POINT(); \
    } \
  } while (0)
```

#### 2.3 Safe Point Slow Path

```c
// src/gc.c

void valk_gc_safe_point_slow(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);
  
  // If STW requested, participate in GC
  if (phase == VALK_GC_STW_REQUESTED) {
    // Evacuate our scratch arena first (if using checkpoint model)
    if (valk_thread_ctx.scratch && valk_thread_ctx.scratch->offset > 0) {
      valk_checkpoint(valk_thread_ctx.scratch, 
                      valk_thread_ctx.heap,
                      valk_thread_ctx.root_env);
    }
    
    // Signal we've reached safe point
    size_t paused = atomic_fetch_add(&valk_gc_coord.threads_paused, 1,
                                      memory_order_acq_rel) + 1;
    
    // If we're the last thread, signal coordinator
    if (paused == atomic_load(&valk_gc_coord.threads_registered)) {
      pthread_mutex_lock(&valk_gc_coord.lock);
      pthread_cond_signal(&valk_gc_coord.all_paused);
      pthread_mutex_unlock(&valk_gc_coord.lock);
    }
    
    // Participate in GC work (mark/sweep)
    valk_gc_participate();
    
    // Wait for GC to complete
    pthread_mutex_lock(&valk_gc_coord.lock);
    while (atomic_load(&valk_gc_coord.phase) != VALK_GC_IDLE) {
      pthread_cond_wait(&valk_gc_coord.gc_done, &valk_gc_coord.lock);
    }
    pthread_mutex_unlock(&valk_gc_coord.lock);
    
    atomic_fetch_sub(&valk_gc_coord.threads_paused, 1, memory_order_release);
  }
}
```

#### 2.4 Safe Point Placement

```c
// In eval loop (src/parser.c)
valk_lval_t *valk_lval_eval(valk_lenv_t *env, valk_lval_t *lval) {
  VALK_GC_SAFE_POINT();
  
  // ... existing eval logic ...
}

// In AIO event loop (src/aio/aio_system.c)
void valk_aio_run(valk_aio_system_t *sys) {
  while (!sys->shutdown) {
    VALK_GC_SAFE_POINT();
    uv_run(&sys->loop, UV_RUN_ONCE);
    // ... process completions ...
  }
}

// In long-running builtins
valk_lval_t *builtin_map(valk_lenv_t *env, valk_lval_t *args) {
  size_t gc_counter = 0;
  valk_lval_t *list = /* ... */;
  
  while (!valk_lval_list_is_empty(list)) {
    VALK_GC_SAFE_POINT_PERIODIC(gc_counter, 100);  // Check every 100 iterations
    // ... process element ...
  }
  
  return result;
}
```

#### 2.5 Thread Registration

```c
// src/gc.c

void valk_gc_thread_register(void) {
  size_t idx = atomic_fetch_add(&valk_gc_coord.threads_registered, 1,
                                 memory_order_acq_rel);
  
  if (idx >= VALK_GC_MAX_THREADS) {
    VALK_ERROR("Too many threads registered with GC");
    abort();
  }
  
  // Initialize thread-local GC context
  valk_thread_ctx.gc_thread_id = idx;
  valk_thread_ctx.gc_registered = true;
  valk_thread_ctx.tlab = (valk_gc_tlab_t){0};
  
  // Allocate root stack
  valk_thread_ctx.root_stack = malloc(sizeof(valk_lval_t*) * 256);
  valk_thread_ctx.root_stack_capacity = 256;
  valk_thread_ctx.root_stack_count = 0;
  
  // Register in coordinator
  valk_gc_coord.threads[idx].ctx = &valk_thread_ctx;
  valk_gc_coord.threads[idx].thread_id = pthread_self();
  valk_gc_coord.threads[idx].active = true;
}

void valk_gc_thread_unregister(void) {
  if (!valk_thread_ctx.gc_registered) return;
  
  // Must be at safe point to unregister
  VALK_GC_SAFE_POINT();
  
  size_t idx = valk_thread_ctx.gc_thread_id;
  valk_gc_coord.threads[idx].active = false;
  
  atomic_fetch_sub(&valk_gc_coord.threads_registered, 1, memory_order_release);
  
  free(valk_thread_ctx.root_stack);
  valk_thread_ctx.root_stack = NULL;
  valk_thread_ctx.gc_registered = false;
}
```

#### Test Artifacts - Phase 2

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_safe_point_noop` | Safe point when IDLE | No blocking, fast return |
| `test_gc_safe_point_stw` | Safe point when STW requested | Thread pauses, resumes after |
| `test_gc_stw_basic` | 4 threads, trigger STW | All threads pause within 10ms |
| `test_gc_stw_under_load` | Threads allocating during STW | Eventually pause, no deadlock |
| `test_gc_thread_register` | Register/unregister threads | Correct counting, no races |
| `test_gc_thread_unregister_during_gc` | Thread exits during GC | Clean shutdown, no hang |

---

### Phase 3: Root Enumeration

**Goal:** Each thread can enumerate its roots for GC scanning.

#### 3.1 Root Stack Macros

```c
// src/gc.h

// Push a root to protect it during potential GC
#define VALK_GC_ROOT(val) \
  valk_gc_root_t __gc_root_##__LINE__ __attribute__((cleanup(valk_gc_root_cleanup))) = \
    valk_gc_root_push(val)

// For multiple values in sequence
#define VALK_GC_ROOT_PUSH(val) valk_gc_root_push(val)
#define VALK_GC_ROOT_POP()     valk_gc_root_pop()

// Block-scoped root (automatically popped at end of scope)
#define VALK_GC_WITH_ROOTS(...) \
  for (size_t __gc_saved = valk_thread_ctx.root_stack_count, __gc_once = 1; \
       __gc_once; \
       valk_thread_ctx.root_stack_count = __gc_saved, __gc_once = 0)

// src/gc.c

typedef struct { size_t saved_count; } valk_gc_root_t;

static inline valk_gc_root_t valk_gc_root_push(valk_lval_t *val) {
  valk_thread_context_t *ctx = &valk_thread_ctx;
  
  if (ctx->root_stack_count >= ctx->root_stack_capacity) {
    ctx->root_stack_capacity *= 2;
    ctx->root_stack = realloc(ctx->root_stack,
                               sizeof(valk_lval_t*) * ctx->root_stack_capacity);
  }
  
  size_t saved = ctx->root_stack_count;
  ctx->root_stack[ctx->root_stack_count++] = val;
  return (valk_gc_root_t){ saved };
}

static inline void valk_gc_root_pop(void) {
  valk_thread_ctx.root_stack_count--;
}

static inline void valk_gc_root_cleanup(valk_gc_root_t *r) {
  valk_thread_ctx.root_stack_count = r->saved_count;
}
```

#### 3.2 Global Roots Registry

```c
// src/gc.h

#define VALK_GC_MAX_GLOBAL_ROOTS 1024

typedef struct valk_gc_global_roots {
  pthread_mutex_t lock;
  valk_lval_t **roots[VALK_GC_MAX_GLOBAL_ROOTS];  // Pointers to root pointers
  size_t count;
} valk_gc_global_roots_t;

extern valk_gc_global_roots_t valk_gc_global_roots;

// Register a global root (for C-side persistent references)
void valk_gc_add_global_root(valk_lval_t **root);
void valk_gc_remove_global_root(valk_lval_t **root);
```

#### 3.3 Root Enumeration

```c
// src/gc.c

typedef void (*valk_gc_root_visitor_t)(valk_lval_t *root, void *ctx);

// Visit all roots for this thread
void valk_gc_visit_thread_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  valk_thread_context_t *tc = &valk_thread_ctx;
  
  // Visit explicit root stack
  for (size_t i = 0; i < tc->root_stack_count; i++) {
    if (tc->root_stack[i] != NULL) {
      visitor(tc->root_stack[i], ctx);
    }
  }
  
  // Visit TLAB in-flight objects (allocated since last safe point)
  // These are already marked as allocated in chunk bitmap
}

// Visit global roots (called by thread 0)
void valk_gc_visit_global_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  // Root environment
  valk_lenv_t *root_env = /* get global root env */;
  if (root_env) {
    valk_gc_visit_env_roots(root_env, visitor, ctx);
  }
  
  // Registered global roots
  pthread_mutex_lock(&valk_gc_global_roots.lock);
  for (size_t i = 0; i < valk_gc_global_roots.count; i++) {
    valk_lval_t *val = *valk_gc_global_roots.roots[i];
    if (val != NULL) {
      visitor(val, ctx);
    }
  }
  pthread_mutex_unlock(&valk_gc_global_roots.lock);
}

// Visit all values in an environment
static void valk_gc_visit_env_roots(valk_lenv_t *env, 
                                     valk_gc_root_visitor_t visitor, 
                                     void *ctx) {
  if (env == NULL) return;
  
  // Visit all values
  for (size_t i = 0; i < env->vals.count; i++) {
    if (env->vals.items[i] != NULL) {
      visitor(env->vals.items[i], ctx);
    }
  }
  
  // Visit parent chain
  valk_gc_visit_env_roots(env->parent, visitor, ctx);
  valk_gc_visit_env_roots(env->fallback, visitor, ctx);
}
```

#### Test Artifacts - Phase 3

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_root_push_pop` | Push/pop roots during eval | Stack correctly maintained |
| `test_gc_root_overflow` | Exceed initial root stack capacity | Resizes correctly |
| `test_gc_root_scoped` | VALK_GC_ROOT auto-cleanup | Root popped at scope end |
| `test_gc_global_roots` | Add/remove global roots | No leaks, correct enumeration |
| `test_gc_roots_multithread` | Each thread has separate root stack | No interference |
| `test_gc_enumerate_all` | Full root enumeration | All roots found, no duplicates |

---

### Phase 4: Parallel Mark

**Goal:** All threads participate in marking phase using work-stealing.

#### 4.1 Work-Stealing Deque (Chase-Lev)

```c
// src/gc.h

#define VALK_GC_MARK_QUEUE_SIZE 8192  // Power of 2 for fast modulo

typedef struct valk_gc_mark_queue {
  _Atomic(valk_lval_t *) items[VALK_GC_MARK_QUEUE_SIZE];
  _Atomic size_t top;     // Thieves steal from here (FIFO end)
  _Atomic size_t bottom;  // Owner pushes/pops here (LIFO end)
} valk_gc_mark_queue_t;

// Per-thread mark queue (in thread context)
// Owner operations (local thread only)
bool valk_gc_mark_queue_push(valk_gc_mark_queue_t *q, valk_lval_t *val);
valk_lval_t *valk_gc_mark_queue_pop(valk_gc_mark_queue_t *q);

// Thief operation (other threads)
valk_lval_t *valk_gc_mark_queue_steal(valk_gc_mark_queue_t *q);
```

#### 4.2 Chase-Lev Implementation

```c
// src/gc.c

bool valk_gc_mark_queue_push(valk_gc_mark_queue_t *q, valk_lval_t *val) {
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  
  if (b - t >= VALK_GC_MARK_QUEUE_SIZE) {
    return false;  // Queue full
  }
  
  atomic_store_explicit(&q->items[b % VALK_GC_MARK_QUEUE_SIZE], val,
                        memory_order_relaxed);
  atomic_thread_fence(memory_order_release);
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  return true;
}

valk_lval_t *valk_gc_mark_queue_pop(valk_gc_mark_queue_t *q) {
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed) - 1;
  atomic_store_explicit(&q->bottom, b, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);
  
  size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
  
  if (t <= b) {
    // Non-empty
    valk_lval_t *val = atomic_load_explicit(
        &q->items[b % VALK_GC_MARK_QUEUE_SIZE], memory_order_relaxed);
    
    if (t == b) {
      // Last element, race with stealers
      if (!atomic_compare_exchange_strong(&q->top, &t, t + 1)) {
        val = NULL;  // Lost race
      }
      atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
    }
    return val;
  }
  
  // Empty
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  return NULL;
}

valk_lval_t *valk_gc_mark_queue_steal(valk_gc_mark_queue_t *q) {
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  size_t b = atomic_load_explicit(&q->bottom, memory_order_acquire);
  
  if (t >= b) {
    return NULL;  // Empty
  }
  
  valk_lval_t *val = atomic_load_explicit(
      &q->items[t % VALK_GC_MARK_QUEUE_SIZE], memory_order_relaxed);
  
  if (!atomic_compare_exchange_strong(&q->top, &t, t + 1)) {
    return NULL;  // Lost race with other thief or owner
  }
  
  return val;
}
```

#### 4.3 Parallel Mark Algorithm

```c
// src/gc.c

void valk_gc_parallel_mark(void) {
  size_t my_id = valk_thread_ctx.gc_thread_id;
  valk_gc_mark_queue_t *my_queue = &valk_gc_coord.threads[my_id].mark_queue;
  
  // Phase 1: Mark own roots
  valk_gc_visit_thread_roots(mark_and_push, my_queue);
  
  // Thread 0 also marks global roots
  if (my_id == 0) {
    valk_gc_visit_global_roots(mark_and_push, my_queue);
  }
  
  // Barrier: wait for all threads to finish root marking
  pthread_barrier_wait(&valk_gc_coord.barrier);
  
  // Phase 2: Work-stealing mark loop
  size_t idle_spins = 0;
  const size_t MAX_IDLE_SPINS = 1000;
  
  while (true) {
    // Try local work first (LIFO - better cache locality)
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != NULL) {
      mark_children(obj, my_queue);
      idle_spins = 0;
    }
    
    // Try stealing from others (round-robin)
    bool found_work = false;
    size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
    
    for (size_t i = 1; i <= num_threads; i++) {
      size_t victim = (my_id + i) % num_threads;
      if (!valk_gc_coord.threads[victim].active) continue;
      
      obj = valk_gc_mark_queue_steal(&valk_gc_coord.threads[victim].mark_queue);
      if (obj != NULL) {
        mark_children(obj, my_queue);
        found_work = true;
        idle_spins = 0;
        break;
      }
    }
    
    if (!found_work) {
      idle_spins++;
      if (idle_spins >= MAX_IDLE_SPINS) {
        // Check global termination
        if (valk_gc_check_termination()) {
          break;
        }
        idle_spins = 0;
      }
      // Yield to other threads
      sched_yield();
    }
  }
}

static void mark_and_push(valk_lval_t *obj, void *ctx) {
  valk_gc_mark_queue_t *queue = ctx;
  
  if (obj == NULL) return;
  if (!valk_gc_try_mark(obj)) return;  // Already marked
  
  if (!valk_gc_mark_queue_push(queue, obj)) {
    // Queue full, process immediately
    mark_children(obj, queue);
  }
}

static void mark_children(valk_lval_t *obj, valk_gc_mark_queue_t *queue) {
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      mark_and_push(obj->cons.head, queue);
      mark_and_push(obj->cons.tail, queue);
      break;
      
    case LVAL_FUN:
      if (obj->fun.builtin == NULL) {
        mark_and_push(obj->fun.formals, queue);
        mark_and_push(obj->fun.body, queue);
        if (obj->fun.env) {
          mark_env(obj->fun.env, queue);
        }
      }
      break;
      
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_and_push(obj->async.handle->on_complete, queue);
        mark_and_push(obj->async.handle->on_error, queue);
        mark_and_push(obj->async.handle->on_cancel, queue);
        mark_and_push(obj->async.handle->result, queue);
        mark_and_push(obj->async.handle->error, queue);
        if (obj->async.handle->env) {
          mark_env(obj->async.handle->env, queue);
        }
      }
      break;
      
    case LVAL_ENV:
      mark_env(&obj->env, queue);
      break;
      
    // Leaf types - no children
    default:
      break;
  }
}

static void mark_env(valk_lenv_t *env, valk_gc_mark_queue_t *queue) {
  if (env == NULL) return;
  
  // Mark environment as GC object (if chunk-allocated)
  // TODO: environments need to be GC objects too
  
  // Mark all values
  for (size_t i = 0; i < env->vals.count; i++) {
    mark_and_push(env->vals.items[i], queue);
  }
  
  // Mark parent and fallback
  mark_env(env->parent, queue);
  mark_env(env->fallback, queue);
}
```

#### 4.4 Termination Detection

```c
// src/gc.c

// Simple termination: all threads idle and all queues empty
static bool valk_gc_check_termination(void) {
  // Use atomic counter for idle threads
  static _Atomic size_t idle_count = 0;
  static _Atomic bool terminated = false;
  
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  size_t idle = atomic_fetch_add(&idle_count, 1, memory_order_acq_rel) + 1;
  
  if (idle == num_threads) {
    // Everyone thinks they're idle - verify all queues are empty
    bool all_empty = true;
    for (size_t i = 0; i < num_threads; i++) {
      valk_gc_mark_queue_t *q = &valk_gc_coord.threads[i].mark_queue;
      size_t t = atomic_load(&q->top);
      size_t b = atomic_load(&q->bottom);
      if (t < b) {
        all_empty = false;
        break;
      }
    }
    
    if (all_empty) {
      atomic_store(&terminated, true, memory_order_release);
    }
  }
  
  // Spin briefly waiting for termination
  for (int i = 0; i < 100; i++) {
    if (atomic_load(&terminated, memory_order_acquire)) {
      return true;
    }
    __builtin_ia32_pause();
  }
  
  // Not terminated, decrement idle count and continue
  atomic_fetch_sub(&idle_count, 1, memory_order_release);
  return false;
}
```

#### Test Artifacts - Phase 4

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_mark_queue_basic` | Single-thread push/pop | LIFO behavior correct |
| `test_gc_mark_queue_steal` | Stealer takes from other queue | FIFO order, no duplicates |
| `test_gc_work_stealing_stress` | 8 threads, high contention | All items processed exactly once |
| `test_gc_parallel_mark_list` | Mark long linked list | All nodes marked, work distributed |
| `test_gc_parallel_mark_tree` | Mark balanced tree | All nodes marked, parallel speedup |
| `test_gc_parallel_mark_cycles` | Graph with cycles | No infinite loop, each marked once |
| `test_gc_termination_detection` | Detect when all queues empty | Terminates correctly |

---

### Phase 5: Parallel Sweep

**Goal:** Threads divide chunks and sweep in parallel.

#### 5.1 Chunk Partitioning

```c
// src/gc.c

void valk_gc_parallel_sweep(void) {
  size_t my_id = valk_thread_ctx.gc_thread_id;
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  valk_gc_chunk_pool_t *pool = &global_chunk_pool;
  
  // Count chunks
  size_t num_chunks = pool->num_chunks;
  if (num_chunks == 0) return;
  
  // Static partitioning
  size_t chunks_per_thread = (num_chunks + num_threads - 1) / num_threads;
  size_t my_start = my_id * chunks_per_thread;
  size_t my_end = (my_id + 1) * chunks_per_thread;
  if (my_end > num_chunks) my_end = num_chunks;
  
  // Sweep my chunks
  size_t freed_slots = 0;
  valk_gc_chunk_t *chunk = pool->all_chunks;
  
  for (size_t i = 0; i < my_end && chunk != NULL; i++) {
    if (i >= my_start) {
      freed_slots += sweep_chunk(chunk);
    }
    chunk = chunk->next;
  }
  
  // Update global stats
  atomic_fetch_sub(&pool->used_slots, freed_slots, memory_order_relaxed);
  
  // Barrier: wait for all sweeping to complete
  pthread_barrier_wait(&valk_gc_coord.barrier);
}
```

#### 5.2 Chunk Sweeping with Bitmap

```c
// src/gc.c

static size_t sweep_chunk(valk_gc_chunk_t *chunk) {
  size_t freed = 0;
  
  // Iterate bitmap - much faster than linked list
  for (size_t word_idx = 0; word_idx < VALK_GC_BITMAP_SIZE / sizeof(uint64_t); word_idx++) {
    uint64_t alloc_word = ((uint64_t*)chunk->alloc_bits)[word_idx];
    uint64_t mark_word = ((uint64_t*)chunk->mark_bits)[word_idx];
    
    // Allocated but not marked = garbage
    uint64_t garbage = alloc_word & ~mark_word;
    
    if (garbage == 0) {
      // Clear mark bits for next cycle
      ((uint64_t*)chunk->mark_bits)[word_idx] = 0;
      continue;
    }
    
    // Process garbage bits
    while (garbage) {
      size_t bit = __builtin_ctzll(garbage);  // Find lowest set bit
      size_t slot_idx = word_idx * 64 + bit;
      
      if (slot_idx < VALK_GC_SLOTS_PER_CHUNK) {
        valk_lval_t *obj = (valk_lval_t*)&chunk->slots[slot_idx * VALK_GC_SLOT_SIZE];
        
        // Call finalizer for LVAL_REF
        if (LVAL_TYPE(obj) == LVAL_REF && obj->ref.free) {
          obj->ref.free(obj->ref.ptr);
        }
        
        // Clear allocation bit
        chunk->alloc_bits[slot_idx / 8] &= ~(1 << (slot_idx % 8));
        freed++;
      }
      
      garbage &= garbage - 1;  // Clear lowest set bit
    }
    
    // Clear mark bits for next cycle
    ((uint64_t*)chunk->mark_bits)[word_idx] = 0;
  }
  
  atomic_fetch_sub(&chunk->num_allocated, freed, memory_order_relaxed);
  return freed;
}
```

#### Test Artifacts - Phase 5

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_sweep_empty_chunk` | Sweep chunk with nothing marked | All slots freed |
| `test_gc_sweep_full_chunk` | Sweep chunk with everything marked | Nothing freed |
| `test_gc_sweep_mixed` | Some live, some dead | Correct slots freed |
| `test_gc_sweep_parallel` | 4 threads sweeping 16 chunks | No races, correct counts |
| `test_gc_sweep_finalizers` | Objects with LVAL_REF finalizers | Finalizers called exactly once |
| `test_gc_bitmap_efficiency` | Large chunk with sparse live objects | Faster than linked list |

---

### Phase 6: Integration

**Goal:** Wire everything together, make futures use GC, integrate with AIO.

#### 6.1 Unified Async Handle

Replace separate refcounting with GC-managed `LVAL_HANDLE`:

```c
// src/parser.h - already exists

// LVAL_HANDLE is already defined, just ensure GC traces it properly
case LVAL_HANDLE:
  if (obj->async.handle) {
    mark_and_push(obj->async.handle->on_complete, queue);
    mark_and_push(obj->async.handle->on_error, queue);
    mark_and_push(obj->async.handle->on_cancel, queue);
    mark_and_push(obj->async.handle->result, queue);
    mark_and_push(obj->async.handle->error, queue);
    if (obj->async.handle->env) {
      mark_env(obj->async.handle->env, queue);
    }
  }
  break;
```

#### 6.2 AIO Thread Integration

```c
// src/aio/aio_system.c

void *valk_aio_thread_main(void *arg) {
  valk_aio_system_t *sys = arg;
  
  // Register with GC
  valk_gc_thread_register();
  
  // Set up thread-local allocator
  valk_thread_ctx.heap = sys->gc_heap;
  valk_thread_ctx.scratch = valk_aio_get_scratch(sys);
  
  while (!atomic_load(&sys->shutdown)) {
    // Safe point: may pause for GC
    VALK_GC_SAFE_POINT();
    
    // Run event loop iteration
    int r = uv_run(&sys->loop, UV_RUN_ONCE);
    if (r == 0 && !atomic_load(&sys->shutdown)) {
      // No events, wait briefly
      uv_sleep(1);
    }
  }
  
  // Unregister from GC before exit
  valk_gc_thread_unregister();
  return NULL;
}
```

#### 6.3 GC Trigger

```c
// src/gc.c

void valk_gc_maybe_collect(valk_gc_malloc_heap_t *heap) {
  // Check if collection needed
  size_t used = atomic_load(&heap->chunk_pool.used_slots);
  size_t threshold = atomic_load(&heap->chunk_pool.gc_threshold);
  
  if (used < threshold) return;
  
  // Try to become the GC leader
  valk_gc_phase_e expected = VALK_GC_IDLE;
  if (!atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected,
                                       VALK_GC_STW_REQUESTED)) {
    return;  // Another thread is handling it
  }
  
  // We're the leader - wait for all threads to pause
  pthread_mutex_lock(&valk_gc_coord.lock);
  while (atomic_load(&valk_gc_coord.threads_paused) < 
         atomic_load(&valk_gc_coord.threads_registered)) {
    pthread_cond_wait(&valk_gc_coord.all_paused, &valk_gc_coord.lock);
  }
  pthread_mutex_unlock(&valk_gc_coord.lock);
  
  // Start mark phase
  uint64_t start_us = uv_hrtime() / 1000;
  atomic_store(&valk_gc_coord.phase, VALK_GC_MARKING, memory_order_release);
  
  // Reinitialize barrier for mark phase
  pthread_barrier_destroy(&valk_gc_coord.barrier);
  pthread_barrier_init(&valk_gc_coord.barrier, NULL,
                       atomic_load(&valk_gc_coord.threads_registered));
  
  // All threads participate in marking (including leader)
  valk_gc_parallel_mark();
  
  // Mark phase complete, start sweep
  atomic_store(&valk_gc_coord.phase, VALK_GC_SWEEPING, memory_order_release);
  valk_gc_parallel_sweep();
  
  // Record stats
  uint64_t end_us = uv_hrtime() / 1000;
  uint64_t pause_us = end_us - start_us;
  atomic_fetch_add(&valk_gc_coord.cycles_total, 1, memory_order_relaxed);
  atomic_fetch_add(&valk_gc_coord.pause_us_total, pause_us, memory_order_relaxed);
  
  // Release all threads
  atomic_store(&valk_gc_coord.phase, VALK_GC_IDLE, memory_order_release);
  pthread_mutex_lock(&valk_gc_coord.lock);
  pthread_cond_broadcast(&valk_gc_coord.gc_done);
  pthread_mutex_unlock(&valk_gc_coord.lock);
  
  VALK_INFO("GC: cycle complete, pause=%llu us", (unsigned long long)pause_us);
}
```

#### Test Artifacts - Phase 6

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| `test_gc_handle_basic` | Create/resolve async handle | No leaks, correct lifecycle |
| `test_gc_handle_callback` | Handle with completion callback | Callback fires, result correct |
| `test_gc_handle_collect` | GC while handles pending | Pending handles not collected |
| `test_gc_aio_integration` | AIO thread registers/unregisters | Clean lifecycle |
| `test_gc_aio_safe_point` | GC triggered from AIO thread | All AIO threads pause |
| `test_gc_full_cycle` | Complete GC cycle with multiple threads | Correct mark/sweep |
| `test_gc_http_stress` | HTTP server under load | No leaks over 10K requests |

---

## Migration Path

### Step 1: Parallel Infrastructure (No Breaking Changes)

1. Add atomic mark bit operations (can coexist with current GC)
2. Add thread context extensions
3. Add safe point macro (initially no-op)
4. Add thread registration (initially single-thread only)

### Step 2: Chunk Allocator (Parallel with Old)

1. Add chunk pool alongside existing slabs
2. New allocations go to chunks
3. Old objects remain in slabs until collected
4. Sweep handles both

### Step 3: Enable Parallelism

1. Enable safe points in eval/AIO loops
2. Register AIO threads
3. Enable parallel mark/sweep
4. Remove old single-threaded code path

### Step 4: Remove Old Infrastructure

1. Remove `heap->objects` linked list
2. Remove old slab allocators (or keep as optimization)
3. Remove old mark/sweep functions

---

## Testing Strategy

### Unit Tests (`test/unit/test_gc_parallel.c`)

```c
void test_gc_atomic_mark(VALK_TEST_ARGS());
void test_gc_chunk_create(VALK_TEST_ARGS());
void test_gc_tlab_alloc(VALK_TEST_ARGS());
void test_gc_safe_point_noop(VALK_TEST_ARGS());
void test_gc_safe_point_stw(VALK_TEST_ARGS());
void test_gc_root_push_pop(VALK_TEST_ARGS());
void test_gc_mark_queue_basic(VALK_TEST_ARGS());
void test_gc_work_stealing_stress(VALK_TEST_ARGS());
void test_gc_parallel_mark_list(VALK_TEST_ARGS());
void test_gc_sweep_mixed(VALK_TEST_ARGS());
void test_gc_full_cycle(VALK_TEST_ARGS());
```

### Stress Tests (`test/stress/`)

| Test File | Description | Duration |
|-----------|-------------|----------|
| `stress_gc_alloc.c` | Continuous allocation across threads | 60s |
| `stress_gc_churn.c` | High allocation + GC rate | 60s |
| `stress_gc_work_steal.c` | Work-stealing under contention | 60s |
| `stress_gc_http.c` | HTTP server under load with GC | 120s |

### Sanitizers

- **ASAN**: Run all tests with `-fsanitize=address`
- **TSAN**: Run all tests with `-fsanitize=thread`
- **MSAN**: Run all tests with `-fsanitize=memory`

### Performance Benchmarks

| Benchmark | Metric | Target |
|-----------|--------|--------|
| `bench_gc_pause_time` | Max pause time | < 10ms for 100MB heap |
| `bench_gc_throughput` | Allocations/sec during GC | > 50% of no-GC rate |
| `bench_gc_parallel_speedup` | N-thread vs 1-thread | > 0.7 * N speedup |
| `bench_gc_work_steal_overhead` | Stealing vs non-parallel | < 5% overhead |

---

## Rollout Plan

### Stage 1: Foundation (2-3 weeks)
- [ ] Phase 0: Atomic marks, thread context extension
- [ ] Phase 1: Chunk allocator, TLAB
- [ ] Phase 2: Safe points, thread coordination
- [ ] All existing tests still pass
- [ ] ASAN/TSAN clean

### Stage 2: Parallel GC (2-3 weeks)
- [ ] Phase 3: Root enumeration
- [ ] Phase 4: Parallel mark with work-stealing
- [ ] Phase 5: Parallel sweep
- [ ] Stress tests passing
- [ ] < 10ms pause time achieved

### Stage 3: Integration (2 weeks)
- [ ] Phase 6: AIO integration
- [ ] Remove old refcounting for futures
- [ ] Full test suite passing
- [ ] HTTP benchmark stable

### Stage 4: Optimization (1-2 weeks)
- [ ] Profile hot paths
- [ ] Tune TLAB/chunk sizes
- [ ] Optimize termination detection
- [ ] Final benchmarks

---

## Implementation Progress

### Session Log

#### 2024-12-27: Initial Implementation Start

**Decision Points:**
1. Starting with Phase 0 (Prerequisites) - atomic mark operations and thread context extensions
2. Will keep existing single-threaded GC working alongside new parallel infrastructure
3. Using `_Atomic` qualifier from C11/C23 for portability (already used in codebase)

**Implementation Status:**

| Component | Status | Notes |
|-----------|--------|-------|
| Phase 0.1 Atomic Mark Bit | DONE | `valk_gc_try_mark()`, `valk_gc_is_marked()`, `valk_gc_clear_mark()` |
| Phase 0.2 Thread Context Extension | DONE | `gc_thread_id`, `gc_registered`, `root_stack` in `valk_thread_context_t` |
| Phase 0.3 Atomic Flags | DONE | Changed `flags` to `_Atomic uint64_t` in `valk_lval_t` and `valk_lenv_t` |
| Phase 0.4 Portable Barrier | DONE | `valk_barrier_t` (pthread_barrier_t unavailable on macOS) |
| Phase 0.5 Chase-Lev Deque | DONE | `valk_gc_mark_queue_t` with push/pop/steal |
| Phase 0.6 GC Coordinator | DONE | `valk_gc_coordinator_t` for multi-threaded coordination |
| Phase 0.7 Thread Registration | DONE | `valk_gc_thread_register()`, `valk_gc_thread_unregister()` |
| Phase 0.8 Safe Point Slow Path | DONE | `valk_gc_safe_point_slow()` |
| Phase 0.9 Global Roots | DONE | `valk_gc_add_global_root()`, `valk_gc_remove_global_root()` |
| Phase 0 Tests | DONE | 16 tests in `test/unit/test_gc_parallel.c` - all passing |
| Existing Tests | DONE | All existing tests pass |
| Phase 1.1 Page Structure | DONE | `valk_gc_page_t` with mark/alloc bitmaps, 64KB pages |
| Phase 1.2 Page Pool | DONE | `valk_gc_page_pool_t` with mutex-protected management |
| Phase 1.3 TLAB | DONE | `valk_gc_tlab_t` with bump-pointer allocation |
| Phase 1.4 TLAB Refill | DONE | Pre-sets alloc bits for thread-safe concurrent access |
| Phase 1 Tests | DONE | 10 new tests (total 26) - all passing |

#### Next Steps

1. **Phase 2**: Safe points in eval loop and AIO loops  
2. **Phase 3**: Root enumeration with VALK_GC_ROOT macros
3. **Phase 4**: Parallel mark with work-stealing

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| Work-stealing bugs | Missed objects, double-free | TSAN, extensive testing, formal verification |
| Safe point placement | Deadlock, long pauses | Audit blocking calls, timeout detection |
| TLAB fragmentation | Memory waste | Tune sizes, add compaction later |
| Cross-thread races | Corruption | TSAN, careful atomics review |
| Performance regression | Slower than single-thread | Benchmark early, optimize critical paths |
| Finalizer ordering | Resource leaks | Document guarantees, careful testing |

---

## References

1. [The Garbage Collection Handbook](https://gchandbook.org/) - Jones, Hosking, Moss
2. [Chase-Lev Deque](https://www.dre.vanderbilt.edu/~schmidt/PDF/work-stealing-dequeue.pdf) - Work-stealing algorithm
3. [V8 Orinoco GC](https://v8.dev/blog/trash-talk) - Parallel GC in practice
4. [Go GC](https://go.dev/blog/ismmkeynote) - Concurrent GC design
5. [JVM G1 GC](https://www.oracle.com/technetwork/tutorials/tutorials-1876574.html) - Parallel + concurrent hybrid
6. [Boehm GC](https://hboehm.info/gc/) - Conservative GC techniques
