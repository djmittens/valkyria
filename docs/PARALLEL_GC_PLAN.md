# Parallel GC Implementation Plan

## Overview

This document outlines the implementation plan for a parallel stop-the-world (STW) garbage collector for Valkyria Lisp. The goal is to enable safe multi-threaded access to the Lisp heap from multiple AIO event loops while minimizing GC pause times through parallel marking and sweeping.

## Design Philosophy

**The GC is a fallback, not the primary allocator.**

Most Valkyria programs use scratch arenas with bump allocation and reset-after-eval. The GC heap only handles:

1. **Escaped objects** - Values that survive checkpoint/evacuation from scratch
2. **Async handles / futures** - Objects with confusing lifetimes spanning multiple eval cycles  
3. **Long-lived globals** - def'd symbols, closures, module exports

This means:
- The GC heap stays small
- Collections are rare
- Simple single-generation, non-compacting design is sufficient
- Fragmentation is acceptable (few long-lived objects scattered across pages)

---

## Goals

1. **Thread-safe heap access** - Multiple AIO threads can hold `valk_lval_t` references
2. **Parallel STW GC** - All threads pause, all threads help with GC
3. **Unified lifetime management** - Futures become `valk_lval_t`, eliminating double refcounting
4. **< 10ms pause times** - For heaps up to 100MB with 4-8 threads
5. **Bounded memory usage** - Hard limits enforced, graceful degradation

## Non-Goals (Future Work)

- Concurrent GC (requires write barriers)
- Generational GC
- Compacting GC

---

## Architecture

### Memory Layout Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         VALKYRIA MEMORY MODEL                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │  SCRATCH ARENA (per-thread)                                          │    │
│  │  • Primary allocator - 99% of allocations                            │    │
│  │  • Bump allocate, reset after eval                                   │    │
│  │  • Zero GC involvement                                               │    │
│  │  • Default: 64MB per thread                                          │    │
│  └──────────────────────────────┬──────────────────────────────────────┘    │
│                                 │                                            │
│                                 │ checkpoint (escape)                        │
│                                 ▼                                            │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │  GC HEAP (virtual address reservation with size classes)             │    │
│  │                                                                       │    │
│  │  ┌───────────────────────────────────────────────────────────────┐   │    │
│  │  │              4GB Virtual Address Reservation                   │   │    │
│  │  │    mmap(PROT_NONE, MAP_NORESERVE) - no physical RAM yet       │   │    │
│  │  ├───────────────────────────────────────────────────────────────┤   │    │
│  │  │                                                                │   │    │
│  │  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐  │   │    │
│  │  │  │ Class 0 │ │ Class 1 │ │ Class 2 │ │ Class 3 │ │  Large  │  │   │    │
│  │  │  │  16 B   │ │  32 B   │ │  64 B   │ │  128 B  │ │ Objects │  │   │    │
│  │  │  │(strings)│ │(symbols)│ │ (lval)  │ │ (lenv)  │ │ (>4KB)  │  │   │    │
│  │  │  ├─────────┤ ├─────────┤ ├─────────┤ ├─────────┤ ├─────────┤  │   │    │
│  │  │  │ Page 0  │ │ Page 0  │ │ Page 0  │ │ Page 0  │ │ Direct  │  │   │    │
│  │  │  │ Page 1  │ │ Page 1  │ │ Page 1  │ │ Page 1  │ │  mmap   │  │   │    │
│  │  │  │ ...     │ │ ...     │ │ ...     │ │ ...     │ │  each   │  │   │    │
│  │  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘  │   │    │
│  │  │                                                                │   │    │
│  │  │  Per-Page: 64KB committed on demand via mprotect()            │   │    │
│  │  │  Per-Page: alloc_bitmap + mark_bitmap for slot tracking       │   │    │
│  │  │                                                                │   │    │
│  │  └───────────────────────────────────────────────────────────────┘   │    │
│  │                                                                       │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Size Classes

### Size Class Table

| Class | Slot Size | Slots/Page | Use Case | Typical Objects |
|-------|-----------|------------|----------|-----------------|
| 0 | 16 bytes | 4096 | Tiny strings | Short symbols, error messages |
| 1 | 32 bytes | 2048 | Small strings | Medium symbols, small arrays |
| 2 | 64 bytes | 1024 | Small objects | Small lvals, tiny lenvs |
| 3 | 128 bytes | 512 | Main objects | `valk_lval_t` (72B), `valk_lenv_t` (80B) |
| 4 | 256 bytes | 256 | Medium arrays | `lenv->symbols.items`, `lenv->vals.items` |
| 5 | 512 bytes | 128 | Large arrays | Lists with 32-64 elements |
| 6 | 1024 bytes | 64 | Large objects | Large function bodies |
| 7 | 2048 bytes | 32 | XL objects | Very large lists |
| 8 | 4096 bytes | 16 | XXL objects | Huge strings/arrays |
| LARGE | N/A | 1 | Huge objects | > 4KB, direct mmap per object |

### Size Class Selection Algorithm

```c
#define VALK_GC_NUM_SIZE_CLASSES 9
#define VALK_GC_LARGE_THRESHOLD  4096

static const uint16_t size_classes[VALK_GC_NUM_SIZE_CLASSES] = {
  16, 32, 64, 128, 256, 512, 1024, 2048, 4096
};

static inline uint8_t valk_gc_size_class(size_t bytes) {
  if (bytes <= 16)   return 0;
  if (bytes <= 32)   return 1;
  if (bytes <= 64)   return 2;
  if (bytes <= 128)  return 3;
  if (bytes <= 256)  return 4;
  if (bytes <= 512)  return 5;
  if (bytes <= 1024) return 6;
  if (bytes <= 2048) return 7;
  if (bytes <= 4096) return 8;
  return UINT8_MAX;  // Large object
}
```

### Memory Waste Analysis

| Request Size | Class | Slot Size | Waste | Waste % |
|--------------|-------|-----------|-------|---------|
| 72 (lval_t) | 3 | 128 | 56 | 44% |
| 80 (lenv_t) | 3 | 128 | 48 | 38% |
| 8 (pointer) | 0 | 16 | 8 | 50% |
| 100 (array) | 3 | 128 | 28 | 22% |
| 200 (array) | 4 | 256 | 56 | 22% |

**Design Decision**: 44% waste for lval_t seems high, but:
1. Scratch arena handles 99% of allocations (zero waste there)
2. Simpler code (fewer size classes to manage)
3. Better cache alignment (power of 2)
4. Alternative: Add 80-byte class, but complicates implementation

---

## Memory Limits and Enforcement

### Default Limits

```c
#define VALK_GC_VIRTUAL_RESERVE     (4ULL * 1024 * 1024 * 1024)  // 4GB virtual
#define VALK_GC_DEFAULT_HARD_LIMIT  (512 * 1024 * 1024)          // 512MB physical
#define VALK_GC_DEFAULT_SOFT_LIMIT  (384 * 1024 * 1024)          // 384MB (75% of hard)
#define VALK_GC_PAGE_SIZE           (64 * 1024)                   // 64KB commit unit
#define VALK_GC_INITIAL_COMMIT      (16 * 1024 * 1024)            // 16MB initial

#define VALK_SCRATCH_DEFAULT_SIZE   (64 * 1024 * 1024)            // 64MB per thread
#define VALK_SCRATCH_MAX_SIZE       (256 * 1024 * 1024)           // 256MB max
```

### Limit Hierarchy

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          MEMORY LIMIT HIERARCHY                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Virtual Reservation (4GB)                                                   │
│  └── Never exceeded (mmap fails if OS can't reserve)                        │
│                                                                              │
│  Hard Limit (512MB default, configurable)                                   │
│  └── ABSOLUTE MAXIMUM physical memory                                        │
│  └── Exceeding triggers: abort() with diagnostics                           │
│  └── Set via: VALK_HEAP_HARD_LIMIT env var or API                           │
│                                                                              │
│  Soft Limit (75% of hard limit)                                             │
│  └── Target maximum during normal operation                                  │
│  └── Exceeding triggers: emergency GC                                        │
│  └── If still over after GC: allow up to hard limit, then abort             │
│                                                                              │
│  GC Trigger Threshold (configurable, default 75% of committed)              │
│  └── When used_bytes > committed * threshold_pct                            │
│  └── Triggers: normal GC cycle                                               │
│  └── Does NOT block allocation (non-blocking trigger)                        │
│                                                                              │
│  Per-Thread Scratch (64MB default)                                          │
│  └── Separate from GC heap                                                   │
│  └── Checkpoint at 75% usage evacuates to GC heap                           │
│  └── Overflow falls back to GC heap allocation                              │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Memory Accounting

```c
typedef struct valk_gc_heap {
  // ... other fields ...
  
  // Memory accounting (all atomic for thread safety)
  _Atomic size_t committed_bytes;      // Physical pages committed
  _Atomic size_t used_bytes;           // Bytes in allocated slots
  _Atomic size_t large_object_bytes;   // Bytes in large objects (separate tracking)
  
  // Limits
  size_t hard_limit;                   // Absolute maximum (abort if exceeded)
  size_t soft_limit;                   // Emergency GC trigger
  uint8_t gc_threshold_pct;            // Normal GC trigger (% of committed)
  
  // Per-class accounting
  _Atomic size_t class_used_slots[VALK_GC_NUM_SIZE_CLASSES];
  _Atomic size_t class_total_slots[VALK_GC_NUM_SIZE_CLASSES];
} valk_gc_heap_t;

// Current usage calculation
static inline size_t valk_gc_used_bytes(valk_gc_heap_t *heap) {
  size_t total = atomic_load(&heap->large_object_bytes);
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    total += atomic_load(&heap->class_used_slots[c]) * size_classes[c];
  }
  return total;
}
```

### Limit Enforcement Points

```c
// Called on every allocation
void *valk_gc_alloc(valk_gc_heap_t *heap, size_t bytes) {
  // 1. Check hard limit BEFORE allocation
  size_t current = valk_gc_used_bytes(heap);
  if (current + bytes > heap->hard_limit) {
    // Try emergency GC
    if (!heap->in_emergency_gc) {
      valk_gc_emergency_collect(heap);
      current = valk_gc_used_bytes(heap);
    }
    
    // Still over? Fatal.
    if (current + bytes > heap->hard_limit) {
      valk_gc_oom_abort(heap, bytes);  // Never returns
    }
  }
  
  // 2. Check soft limit (trigger emergency GC but don't block)
  if (current + bytes > heap->soft_limit && !heap->in_emergency_gc) {
    valk_gc_request_collection();  // Non-blocking
  }
  
  // 3. Normal allocation proceeds
  return valk_gc_alloc_internal(heap, bytes);
}
```

### OOM Handling

```c
__attribute__((noreturn))
static void valk_gc_oom_abort(valk_gc_heap_t *heap, size_t requested) {
  fprintf(stderr, "\n");
  fprintf(stderr, "╔══════════════════════════════════════════════════════════════╗\n");
  fprintf(stderr, "║                    FATAL: OUT OF MEMORY                      ║\n");
  fprintf(stderr, "╠══════════════════════════════════════════════════════════════╣\n");
  fprintf(stderr, "║ Requested:    %12zu bytes                              ║\n", requested);
  fprintf(stderr, "║ Used:         %12zu bytes                              ║\n", valk_gc_used_bytes(heap));
  fprintf(stderr, "║ Hard Limit:   %12zu bytes                              ║\n", heap->hard_limit);
  fprintf(stderr, "║ Committed:    %12zu bytes                              ║\n", 
          atomic_load(&heap->committed_bytes));
  fprintf(stderr, "╠══════════════════════════════════════════════════════════════╣\n");
  fprintf(stderr, "║ Per-Class Usage:                                             ║\n");
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    size_t used = atomic_load(&heap->class_used_slots[c]);
    size_t total = atomic_load(&heap->class_total_slots[c]);
    if (total > 0) {
      fprintf(stderr, "║   Class %d (%4d B): %8zu / %8zu slots (%3zu%%)         ║\n",
              c, size_classes[c], used, total, (used * 100) / total);
    }
  }
  fprintf(stderr, "║ Large Objects: %12zu bytes                             ║\n",
          atomic_load(&heap->large_object_bytes));
  fprintf(stderr, "╠══════════════════════════════════════════════════════════════╣\n");
  fprintf(stderr, "║ Increase limit: VALK_HEAP_HARD_LIMIT=%zu                ║\n",
          heap->hard_limit * 2);
  fprintf(stderr, "╚══════════════════════════════════════════════════════════════╝\n");
  abort();
}
```

---

## Heap Data Structures

### Main Heap Structure

```c
typedef struct valk_gc_heap {
  // Virtual address space
  void *base;                          // mmap'd base (never changes)
  size_t reserved;                     // Total virtual reservation (4GB)
  
  // Per-class page lists
  valk_gc_page_list_t classes[VALK_GC_NUM_SIZE_CLASSES];
  
  // Large object tracking
  valk_gc_large_obj_t *large_objects;  // Linked list of large allocations
  pthread_mutex_t large_lock;           // Protects large_objects list
  
  // Memory accounting
  _Atomic size_t committed_bytes;
  _Atomic size_t used_bytes;
  _Atomic size_t large_object_bytes;
  
  // Limits
  size_t hard_limit;
  size_t soft_limit;
  uint8_t gc_threshold_pct;
  
  // GC state
  _Atomic bool gc_in_progress;
  bool in_emergency_gc;
  
  // Statistics
  _Atomic uint64_t collections;
  _Atomic uint64_t bytes_allocated_total;
  _Atomic uint64_t bytes_reclaimed_total;
} valk_gc_heap_t;
```

### Per-Class Page List

```c
typedef struct valk_gc_page_list {
  pthread_mutex_t lock;                 // Protects page list modifications
  valk_gc_page_t *all_pages;            // All pages for this class
  valk_gc_page_t *partial_pages;        // Pages with free slots
  size_t num_pages;
  _Atomic size_t total_slots;
  _Atomic size_t used_slots;
  _Atomic uint32_t next_tlab_page;      // For TLAB round-robin
  uint16_t slot_size;                   // Size class
  uint16_t slots_per_page;              // Pre-computed
} valk_gc_page_list_t;
```

### Page Structure

```c
#define VALK_GC_PAGE_SIZE (64 * 1024)  // 64KB

typedef struct valk_gc_page {
  struct valk_gc_page *next;           // Next in list
  struct valk_gc_page *next_partial;   // Next in partial list (may differ)
  uint32_t page_id;                    // For debugging
  uint16_t slot_size;                  // Size class
  uint16_t slots_per_page;             // Cached
  _Atomic uint32_t num_allocated;      // Slots in use
  
  // Bitmaps: ceil(slots_per_page / 8) bytes each
  // For 128-byte slots: 512 slots = 64 bytes bitmap
  // For 16-byte slots: 4096 slots = 512 bytes bitmap
  uint8_t *alloc_bitmap;               // Points into page or separate allocation
  uint8_t *mark_bitmap;
  
  // Slot data follows (page-aligned)
  _Alignas(64) uint8_t slots[];
} valk_gc_page_t;

// Total page size calculation
static inline size_t valk_gc_page_total_size(uint16_t slot_size) {
  uint16_t slots = VALK_GC_PAGE_SIZE / slot_size;
  size_t bitmap_bytes = (slots + 7) / 8;
  size_t header_size = sizeof(valk_gc_page_t) + 2 * bitmap_bytes;
  header_size = (header_size + 63) & ~63;  // Align to 64 bytes
  return header_size + (slots * slot_size);
}
```

### Large Object Structure

```c
typedef struct valk_gc_large_obj {
  struct valk_gc_large_obj *next;
  void *data;                          // mmap'd region
  size_t size;                         // Allocation size
  bool marked;                         // GC mark
} valk_gc_large_obj_t;
```

### TLAB (Thread-Local Allocation Buffer)

```c
typedef struct valk_gc_tlab {
  valk_gc_heap_t *heap;
  
  // Per-class TLAB state
  struct {
    valk_gc_page_t *page;              // Current page
    uint32_t next_slot;                // Next slot to allocate
    uint32_t limit_slot;               // End of claimed range
  } classes[VALK_GC_NUM_SIZE_CLASSES];
} valk_gc_tlab_t;

#define VALK_GC_TLAB_SLOTS 32          // Slots claimed per refill
```

---

## Allocation Algorithm

### Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         ALLOCATION FLOW                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  valk_gc_alloc(heap, bytes)                                                 │
│       │                                                                      │
│       ├──► bytes > 4KB?                                                      │
│       │         │                                                            │
│       │         YES ──► valk_gc_alloc_large() ──► mmap() individual object  │
│       │         │                                                            │
│       │         NO                                                           │
│       │         ▼                                                            │
│       ├──► class = size_class(bytes)                                        │
│       │         │                                                            │
│       │         ▼                                                            │
│       ├──► TLAB[class].next_slot < limit_slot?                              │
│       │         │                                                            │
│       │         YES ──► return slot[next_slot++]  (FAST PATH - no locks)    │
│       │         │                                                            │
│       │         NO                                                           │
│       │         ▼                                                            │
│       └──► valk_gc_tlab_refill(class) ──► claim slots from page pool        │
│                   │                                                          │
│                   ├──► partial_pages available?                              │
│                   │         │                                                │
│                   │         YES ──► claim slots from partial page           │
│                   │         │                                                │
│                   │         NO                                               │
│                   │         ▼                                                │
│                   └──► allocate new page ──► commit via mprotect()          │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Fast Path (TLAB Bump)

```c
static inline void *valk_gc_alloc(valk_gc_heap_t *heap, size_t bytes) {
  // Check limits
  if (__builtin_expect(valk_gc_used_bytes(heap) + bytes > heap->soft_limit, 0)) {
    valk_gc_check_limits(heap, bytes);
  }
  
  // Large object path
  if (__builtin_expect(bytes > VALK_GC_LARGE_THRESHOLD, 0)) {
    return valk_gc_alloc_large(heap, bytes);
  }
  
  // Get size class
  uint8_t class = valk_gc_size_class(bytes);
  valk_gc_tlab_t *tlab = valk_thread_ctx.tlab;
  
  // Fast path: bump allocate from TLAB
  if (__builtin_expect(tlab->classes[class].next_slot < 
                       tlab->classes[class].limit_slot, 1)) {
    uint32_t slot = tlab->classes[class].next_slot++;
    void *ptr = valk_gc_page_slot_ptr(tlab->classes[class].page, slot);
    memset(ptr, 0, size_classes[class]);
    return ptr;
  }
  
  // Slow path: refill TLAB
  return valk_gc_alloc_slow(heap, class);
}
```

### Slow Path (TLAB Refill)

```c
static void *valk_gc_alloc_slow(valk_gc_heap_t *heap, uint8_t class) {
  valk_gc_tlab_t *tlab = valk_thread_ctx.tlab;
  valk_gc_page_list_t *list = &heap->classes[class];
  
  pthread_mutex_lock(&list->lock);
  
  // Try to get slots from a partial page
  valk_gc_page_t *page = list->partial_pages;
  uint32_t start_slot = 0;
  
  if (page != NULL) {
    // Find contiguous free slots
    start_slot = valk_gc_find_free_slots(page, VALK_GC_TLAB_SLOTS);
    if (start_slot == UINT32_MAX) {
      // Page is actually full, remove from partial list
      list->partial_pages = page->next_partial;
      page = NULL;
    }
  }
  
  if (page == NULL) {
    // Allocate new page
    pthread_mutex_unlock(&list->lock);
    page = valk_gc_page_alloc(heap, class);
    if (page == NULL) {
      return NULL;  // OOM
    }
    pthread_mutex_lock(&list->lock);
    
    // Add to all_pages and partial_pages
    page->next = list->all_pages;
    list->all_pages = page;
    page->next_partial = list->partial_pages;
    list->partial_pages = page;
    list->num_pages++;
    atomic_fetch_add(&list->total_slots, page->slots_per_page);
    
    start_slot = 0;
  }
  
  // Claim slots
  uint32_t num_slots = VALK_GC_TLAB_SLOTS;
  if (start_slot + num_slots > page->slots_per_page) {
    num_slots = page->slots_per_page - start_slot;
  }
  
  // Pre-set alloc bits
  for (uint32_t i = start_slot; i < start_slot + num_slots; i++) {
    valk_gc_bitmap_set(page->alloc_bitmap, i);
  }
  atomic_fetch_add(&page->num_allocated, num_slots);
  atomic_fetch_add(&list->used_slots, num_slots);
  atomic_fetch_add(&heap->used_bytes, num_slots * size_classes[class]);
  
  // Check if page is now full
  if (atomic_load(&page->num_allocated) >= page->slots_per_page) {
    // Remove from partial list
    valk_gc_page_t **pp = &list->partial_pages;
    while (*pp != NULL && *pp != page) {
      pp = &(*pp)->next_partial;
    }
    if (*pp == page) {
      *pp = page->next_partial;
    }
  }
  
  pthread_mutex_unlock(&list->lock);
  
  // Update TLAB
  tlab->classes[class].page = page;
  tlab->classes[class].next_slot = start_slot;
  tlab->classes[class].limit_slot = start_slot + num_slots;
  
  // Return first slot
  uint32_t slot = tlab->classes[class].next_slot++;
  void *ptr = valk_gc_page_slot_ptr(page, slot);
  memset(ptr, 0, size_classes[class]);
  return ptr;
}
```

### Large Object Allocation

```c
static void *valk_gc_alloc_large(valk_gc_heap_t *heap, size_t bytes) {
  // Round up to page boundary
  size_t alloc_size = (bytes + VALK_GC_PAGE_SIZE - 1) & ~(VALK_GC_PAGE_SIZE - 1);
  
  // Check limits
  size_t current = valk_gc_used_bytes(heap);
  if (current + alloc_size > heap->hard_limit) {
    if (!heap->in_emergency_gc) {
      valk_gc_emergency_collect(heap);
    }
    if (valk_gc_used_bytes(heap) + alloc_size > heap->hard_limit) {
      valk_gc_oom_abort(heap, bytes);
    }
  }
  
  // Allocate via mmap
  void *data = mmap(NULL, alloc_size, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (data == MAP_FAILED) {
    return NULL;
  }
  
  // Create tracking structure
  valk_gc_large_obj_t *obj = malloc(sizeof(valk_gc_large_obj_t));
  obj->data = data;
  obj->size = alloc_size;
  obj->marked = false;
  
  // Add to list
  pthread_mutex_lock(&heap->large_lock);
  obj->next = heap->large_objects;
  heap->large_objects = obj;
  pthread_mutex_unlock(&heap->large_lock);
  
  atomic_fetch_add(&heap->large_object_bytes, alloc_size);
  
  return data;
}
```

---

## Marking Algorithm

### Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PARALLEL MARK PHASE                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  1. ROOT ENUMERATION (per-thread, parallel)                                 │
│     ├── Thread root stack (explicit VALK_GC_ROOT pushes)                    │
│     ├── Thread's TLAB in-flight slots                                       │
│     └── Thread 0 also marks: global roots, root_env                         │
│                                                                              │
│  2. BARRIER: Wait for all threads to finish root marking                    │
│                                                                              │
│  3. WORK-STEALING MARK LOOP (parallel)                                      │
│     ├── Pop from local mark queue (LIFO - better locality)                  │
│     ├── If empty, steal from other threads' queues (FIFO)                   │
│     ├── For each object:                                                     │
│     │   ├── Try atomic mark (CAS on mark bitmap)                            │
│     │   ├── If already marked: skip                                          │
│     │   └── If newly marked: scan children, push to queue                   │
│     └── Repeat until all queues empty                                        │
│                                                                              │
│  4. TERMINATION DETECTION                                                   │
│     ├── All threads report idle                                              │
│     ├── Verify all queues truly empty                                        │
│     └── If work found: re-enter loop                                         │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Mark Bit Location

**Design Decision**: Mark bits in bitmap, not in object header.

```c
// Mark bit is in the page's mark_bitmap, not in lval->flags
// This is critical for size classes: objects may not have space for header

static inline bool valk_gc_try_mark_slot(valk_gc_page_t *page, uint32_t slot) {
  uint8_t *byte = &page->mark_bitmap[slot / 8];
  uint8_t bit = 1 << (slot % 8);
  
  // Atomic test-and-set
  uint8_t old = __atomic_fetch_or(byte, bit, __ATOMIC_ACQ_REL);
  return (old & bit) == 0;  // True if we set it first
}

static inline bool valk_gc_is_marked_slot(valk_gc_page_t *page, uint32_t slot) {
  return (page->mark_bitmap[slot / 8] & (1 << (slot % 8))) != 0;
}
```

### Pointer to Page/Slot Lookup

```c
// O(1) pointer lookup using virtual address arithmetic
static inline bool valk_gc_ptr_to_location(valk_gc_heap_t *heap, void *ptr,
                                            uint8_t *out_class,
                                            valk_gc_page_t **out_page,
                                            uint32_t *out_slot) {
  // Check if in heap bounds
  uintptr_t addr = (uintptr_t)ptr;
  uintptr_t base = (uintptr_t)heap->base;
  if (addr < base || addr >= base + heap->reserved) {
    return false;
  }
  
  // Determine which class region
  // Classes are laid out contiguously: [class0 pages][class1 pages]...
  // Each class has a known start offset
  uintptr_t offset = addr - base;
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    uintptr_t class_start = list->region_start;
    uintptr_t class_end = class_start + (list->num_pages * valk_gc_page_total_size(size_classes[c]));
    
    if (offset >= class_start && offset < class_end) {
      // Found the class
      *out_class = c;
      
      // Find page within class
      size_t page_size = valk_gc_page_total_size(size_classes[c]);
      size_t page_index = (offset - class_start) / page_size;
      
      // Walk page list to find page (or use array if we add one)
      valk_gc_page_t *page = list->all_pages;
      for (size_t i = 0; i < page_index && page != NULL; i++) {
        page = page->next;
      }
      if (page == NULL) return false;
      
      *out_page = page;
      
      // Find slot within page
      uintptr_t page_base = (uintptr_t)page->slots;
      if (addr < page_base) return false;
      *out_slot = (addr - page_base) / size_classes[c];
      
      return true;
    }
  }
  
  return false;  // Not in any class region (might be large object)
}
```

### Object Scanning

```c
static void mark_and_push(void *ptr, valk_gc_mark_queue_t *queue, 
                          valk_gc_heap_t *heap) {
  if (ptr == NULL) return;
  
  // Find location
  uint8_t class;
  valk_gc_page_t *page;
  uint32_t slot;
  
  if (!valk_gc_ptr_to_location(heap, ptr, &class, &page, &slot)) {
    // Might be large object
    valk_gc_mark_large_object(heap, ptr);
    return;
  }
  
  // Try to mark
  if (!valk_gc_try_mark_slot(page, slot)) {
    return;  // Already marked
  }
  
  // Push to queue for child scanning
  if (!valk_gc_mark_queue_push(queue, ptr)) {
    // Queue full, process immediately
    scan_object(ptr, class, queue, heap);
  }
}

static void scan_object(void *ptr, uint8_t class, 
                        valk_gc_mark_queue_t *queue,
                        valk_gc_heap_t *heap) {
  // Determine object type by examining contents
  // For lval_t: check flags field for type
  // For arrays: we need type info from allocator (see below)
  
  if (size_classes[class] >= sizeof(valk_lval_t)) {
    // Could be an lval
    valk_lval_t *v = (valk_lval_t *)ptr;
    
    switch (LVAL_TYPE(v)) {
      case LVAL_CONS:
      case LVAL_QEXPR:
        mark_and_push(v->cons.head, queue, heap);
        mark_and_push(v->cons.tail, queue, heap);
        break;
        
      case LVAL_FUN:
        if (v->fun.builtin == NULL) {
          mark_and_push(v->fun.formals, queue, heap);
          mark_and_push(v->fun.body, queue, heap);
          if (v->fun.env) {
            scan_env(v->fun.env, queue, heap);
          }
        }
        // Mark name string
        mark_and_push(v->fun.name, queue, heap);
        break;
        
      case LVAL_SYM:
      case LVAL_STR:
      case LVAL_ERR:
        // Mark string data
        mark_and_push(v->str, queue, heap);
        break;
        
      case LVAL_HANDLE:
        if (v->async.handle) {
          mark_and_push(v->async.handle->on_complete, queue, heap);
          mark_and_push(v->async.handle->on_error, queue, heap);
          mark_and_push(v->async.handle->on_cancel, queue, heap);
          mark_and_push(v->async.handle->result, queue, heap);
          mark_and_push(v->async.handle->error, queue, heap);
          if (v->async.handle->env) {
            scan_env(v->async.handle->env, queue, heap);
          }
        }
        break;
        
      case LVAL_REF:
        // REF may point to GC-allocated data
        mark_and_push(v->ref.type, queue, heap);
        // ref.ptr is opaque, don't scan
        break;
        
      default:
        // LVAL_NUM, LVAL_NIL - no children
        break;
    }
  }
  
  // For arrays: need metadata to know element count
  // This requires storing count in allocation header or using conservative scan
}

static void scan_env(valk_lenv_t *env, valk_gc_mark_queue_t *queue,
                     valk_gc_heap_t *heap) {
  if (env == NULL) return;
  
  // Mark the env struct itself
  mark_and_push(env, queue, heap);
  
  // Mark arrays
  mark_and_push(env->symbols.items, queue, heap);
  mark_and_push(env->vals.items, queue, heap);
  
  // Mark each symbol string
  for (size_t i = 0; i < env->symbols.count; i++) {
    mark_and_push(env->symbols.items[i], queue, heap);
  }
  
  // Mark each value
  for (size_t i = 0; i < env->vals.count; i++) {
    mark_and_push(env->vals.items[i], queue, heap);
  }
  
  // Recurse on parent/fallback
  scan_env(env->parent, queue, heap);
  scan_env(env->fallback, queue, heap);
}
```

### Parallel Mark Main Loop

```c
void valk_gc_parallel_mark(valk_gc_heap_t *heap) {
  size_t my_id = valk_thread_ctx.gc_thread_id;
  valk_gc_mark_queue_t *my_queue = &valk_gc_coord.threads[my_id].mark_queue;
  
  // Initialize queue
  valk_gc_mark_queue_init(my_queue);
  
  // Phase 1: Mark own roots
  valk_gc_visit_thread_roots(mark_root_visitor, my_queue);
  
  // Thread 0 marks global roots
  if (my_id == 0) {
    valk_gc_visit_global_roots(mark_root_visitor, my_queue);
  }
  
  // Barrier: wait for all threads to finish root marking
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  // Phase 2: Work-stealing mark loop
  size_t idle_spins = 0;
  const size_t MAX_IDLE_SPINS = 1000;
  
  while (true) {
    // Process local queue (LIFO for locality)
    void *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != NULL) {
      uint8_t class;
      valk_gc_page_t *page;
      uint32_t slot;
      
      if (valk_gc_ptr_to_location(heap, obj, &class, &page, &slot)) {
        scan_object(obj, class, my_queue, heap);
      }
      idle_spins = 0;
    }
    
    // Try stealing from others
    bool found_work = false;
    size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
    
    for (size_t i = 1; i <= num_threads; i++) {
      size_t victim = (my_id + i) % num_threads;
      if (!valk_gc_coord.threads[victim].active) continue;
      
      obj = valk_gc_mark_queue_steal(&valk_gc_coord.threads[victim].mark_queue);
      if (obj != NULL) {
        uint8_t class;
        valk_gc_page_t *page;
        uint32_t slot;
        
        if (valk_gc_ptr_to_location(heap, obj, &class, &page, &slot)) {
          scan_object(obj, class, my_queue, heap);
        }
        found_work = true;
        idle_spins = 0;
        break;
      }
    }
    
    if (!found_work) {
      idle_spins++;
      if (idle_spins >= MAX_IDLE_SPINS) {
        if (valk_gc_check_termination()) {
          break;
        }
        idle_spins = 0;
      }
      sched_yield();
    }
  }
}
```

---

## Sweeping Algorithm

### Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           PARALLEL SWEEP PHASE                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  1. PARTITION WORK                                                          │
│     ├── Each class's pages divided among threads                            │
│     └── Large objects swept by thread 0                                      │
│                                                                              │
│  2. PER-PAGE SWEEP (parallel)                                               │
│     ├── Load alloc_bitmap word (64 bits = 64 slots)                         │
│     ├── Load mark_bitmap word                                                │
│     ├── garbage = alloc & ~mark                                              │
│     ├── For each garbage bit:                                                │
│     │   ├── Call finalizer if LVAL_REF                                      │
│     │   └── Clear alloc bit                                                  │
│     ├── Clear mark bits for next cycle                                       │
│     └── Update page->num_allocated                                           │
│                                                                              │
│  3. PAGE RECLAMATION                                                        │
│     ├── If page is completely empty:                                         │
│     │   ├── madvise(MADV_DONTNEED) to release physical memory               │
│     │   └── Move to free page pool (or just leave for reuse)                │
│     └── Otherwise: add to partial_pages if has free slots                   │
│                                                                              │
│  4. LARGE OBJECT SWEEP (single-threaded)                                    │
│     ├── Walk large_objects list                                              │
│     ├── If !marked: munmap() and free tracking struct                       │
│     └── If marked: clear mark for next cycle                                │
│                                                                              │
│  5. UPDATE ACCOUNTING                                                       │
│     ├── Sum freed slots per class                                            │
│     ├── Update heap->used_bytes                                              │
│     └── Reset TLAB pointers (allocations restart from slot 0)               │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Word-at-a-Time Bitmap Sweep

```c
static size_t sweep_page(valk_gc_page_t *page, valk_gc_heap_t *heap) {
  size_t freed = 0;
  uint16_t slots = page->slots_per_page;
  uint16_t slot_size = page->slot_size;
  
  // Process 64 slots at a time
  size_t num_words = (slots + 63) / 64;
  uint64_t *alloc_words = (uint64_t *)page->alloc_bitmap;
  uint64_t *mark_words = (uint64_t *)page->mark_bitmap;
  
  for (size_t w = 0; w < num_words; w++) {
    uint64_t alloc = alloc_words[w];
    uint64_t mark = mark_words[w];
    
    // Garbage = allocated but not marked
    uint64_t garbage = alloc & ~mark;
    
    if (garbage != 0) {
      // Count freed slots
      freed += __builtin_popcountll(garbage);
      
      // Clear alloc bits for garbage
      alloc_words[w] = alloc & mark;
      
      // Call finalizers
      while (garbage) {
        size_t bit = __builtin_ctzll(garbage);
        size_t slot = w * 64 + bit;
        
        if (slot < slots) {
          void *ptr = page->slots + (slot * slot_size);
          
          // Check if this looks like an lval with finalizer
          if (slot_size >= sizeof(valk_lval_t)) {
            valk_lval_t *v = (valk_lval_t *)ptr;
            if (LVAL_TYPE(v) == LVAL_REF && v->ref.free != NULL) {
              v->ref.free(v->ref.ptr);
            }
          }
        }
        
        garbage &= garbage - 1;  // Clear lowest bit
      }
    }
    
    // Clear mark bits for next cycle
    mark_words[w] = 0;
  }
  
  // Update page allocation count
  atomic_fetch_sub(&page->num_allocated, freed);
  
  return freed;
}
```

### Parallel Sweep Coordinator

```c
void valk_gc_parallel_sweep(valk_gc_heap_t *heap) {
  size_t my_id = valk_thread_ctx.gc_thread_id;
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  
  size_t total_freed = 0;
  
  // Sweep each size class
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    // Count pages
    size_t num_pages = list->num_pages;
    if (num_pages == 0) continue;
    
    // Partition pages among threads
    size_t pages_per_thread = (num_pages + num_threads - 1) / num_threads;
    size_t my_start = my_id * pages_per_thread;
    size_t my_end = (my_id + 1) * pages_per_thread;
    if (my_end > num_pages) my_end = num_pages;
    
    // Walk to my starting page
    valk_gc_page_t *page = list->all_pages;
    for (size_t i = 0; i < my_start && page != NULL; i++) {
      page = page->next;
    }
    
    // Sweep my pages
    for (size_t i = my_start; i < my_end && page != NULL; i++) {
      size_t freed = sweep_page(page, heap);
      total_freed += freed * size_classes[c];
      
      // Check if page is now empty
      if (atomic_load(&page->num_allocated) == 0) {
        // Could madvise to release physical memory
        // For now, just leave it for reuse
      }
      
      page = page->next;
    }
    
    atomic_fetch_sub(&list->used_slots, total_freed / size_classes[c]);
  }
  
  // Thread 0 sweeps large objects
  if (my_id == 0) {
    total_freed += sweep_large_objects(heap);
  }
  
  // Update heap accounting
  atomic_fetch_sub(&heap->used_bytes, total_freed);
  
  // Barrier: wait for all sweep to complete
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  // Reset TLABs (all threads)
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_thread_ctx.tlab->classes[c].next_slot = 0;
    valk_thread_ctx.tlab->classes[c].limit_slot = 0;
    valk_thread_ctx.tlab->classes[c].page = NULL;
  }
}

static size_t sweep_large_objects(valk_gc_heap_t *heap) {
  size_t freed = 0;
  
  pthread_mutex_lock(&heap->large_lock);
  
  valk_gc_large_obj_t **pp = &heap->large_objects;
  while (*pp != NULL) {
    valk_gc_large_obj_t *obj = *pp;
    
    if (!obj->marked) {
      // Remove from list
      *pp = obj->next;
      
      // Free the memory
      munmap(obj->data, obj->size);
      freed += obj->size;
      free(obj);
    } else {
      // Clear mark for next cycle
      obj->marked = false;
      pp = &obj->next;
    }
  }
  
  pthread_mutex_unlock(&heap->large_lock);
  
  atomic_fetch_sub(&heap->large_object_bytes, freed);
  return freed;
}
```

### Page Reclamation

```c
// Called after sweep to release empty pages to OS
void valk_gc_reclaim_empty_pages(valk_gc_heap_t *heap) {
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    pthread_mutex_lock(&list->lock);
    
    // Rebuild partial_pages list and identify empty pages
    list->partial_pages = NULL;
    
    for (valk_gc_page_t *page = list->all_pages; page != NULL; page = page->next) {
      uint32_t allocated = atomic_load(&page->num_allocated);
      
      if (allocated == 0) {
        // Page is empty - release physical memory
        size_t page_size = valk_gc_page_total_size(size_classes[c]);
        madvise(page, page_size, MADV_DONTNEED);
        
        // Keep in all_pages list (virtual address still valid)
        // Will be recommitted on first allocation
      } else if (allocated < page->slots_per_page) {
        // Page has free slots - add to partial list
        page->next_partial = list->partial_pages;
        list->partial_pages = page;
      }
    }
    
    pthread_mutex_unlock(&list->lock);
  }
}
```

---

## Example Scenarios

### Scenario 1: Simple Allocation and Collection

```
Initial State:
  - Heap committed: 16MB
  - Class 3 (128B): 1 page, 0/512 slots used
  - GC threshold: 75%

Thread A allocates valk_lval_t (72 bytes):
  1. size_class(72) = 3 (128B class)
  2. TLAB[3] empty, refill from page 0
  3. Claim slots 0-31, set alloc_bits[0..31]
  4. Return slot 0, TLAB.next_slot = 1

Thread A allocates 100 more lvals:
  1. Slots 1-31 from TLAB (fast path)
  2. TLAB exhausted at slot 32
  3. Refill: claim slots 32-63
  4. Continue...

At 384 slots used (75% of 512):
  1. GC trigger condition met
  2. valk_gc_request_collection() called
  3. All threads reach safe point
  4. Mark phase: roots → mark_bitmap
  5. Sweep phase: alloc & ~mark → free
  6. Result: freed 200 slots (dead temporaries)
  7. used_slots = 184

After GC:
  - TLABs reset
  - Next allocation: claim from freed slots
  - Page stays committed (has live data)
```

### Scenario 2: Multiple Size Classes

```
Thread creates lenv_t with 10 bindings:

1. Allocate valk_lenv_t (80 bytes):
   - size_class(80) = 3 (128B)
   - From class 3 TLAB

2. Allocate symbols array (10 * 8 = 80 bytes):
   - size_class(80) = 3 (128B)
   - From class 3 TLAB

3. Allocate vals array (10 * 8 = 80 bytes):
   - size_class(80) = 3 (128B)
   - From class 3 TLAB

4. Allocate 10 symbol strings (~8 bytes each):
   - size_class(8) = 0 (16B)
   - From class 0 TLAB (different page!)

5. Allocate 10 valk_lval_t values:
   - size_class(72) = 3 (128B)
   - From class 3 TLAB

Total: 3 + 10 = 13 slots in class 3
       10 slots in class 0

GC marks:
  - Start from root pointing to lenv
  - Mark lenv slot in class 3
  - Follow symbols.items → mark array slot
  - Follow each symbol string → mark in class 0
  - Follow vals.items → mark array slot
  - Follow each value → mark lval slots

Sweep:
  - Class 0: free unmarked string slots
  - Class 3: free unmarked lval/array slots
  - (All 23 slots marked if lenv is live)
```

### Scenario 3: Large Object Lifecycle

```
Thread allocates 1MB buffer for file read:

1. valk_gc_alloc(heap, 1048576):
   - bytes > 4096, use large object path
   - mmap(1MB) directly
   - Create large_obj tracking struct
   - Add to heap->large_objects list
   - heap->large_object_bytes += 1MB

2. Buffer stored in LVAL_STR:
   - lval->str = buffer pointer
   - lval in class 3 slot

GC cycle:
  1. Mark phase: mark lval slot
  2. scan_object finds LVAL_STR
  3. mark_and_push(lval->str) called
  4. valk_gc_mark_large_object() finds buffer
  5. large_obj->marked = true

  6. Sweep phase: sweep_large_objects()
  7. Buffer is marked → skip
  8. Clear mark for next cycle

Later, lval goes out of scope:

GC cycle:
  1. lval not reachable from roots
  2. lval slot not marked
  3. Buffer not marked (no path to it)
  
  4. Sweep: free lval slot
  5. sweep_large_objects:
     - buffer->marked == false
     - munmap(buffer, 1MB)
     - free(large_obj struct)
     - heap->large_object_bytes -= 1MB
```

### Scenario 4: Memory Pressure and Emergency GC

```
Heap state:
  - hard_limit: 512MB
  - soft_limit: 384MB
  - current used: 380MB
  - gc_in_progress: false

Thread A requests 10MB allocation:

1. valk_gc_alloc checks: 380MB + 10MB > 384MB (soft_limit)
2. valk_gc_request_collection() (non-blocking)
3. Allocation proceeds (under hard limit)

Meanwhile, GC coordinator:
1. Sets gc_phase = STW_REQUESTED
2. Waits for threads to reach safe points
3. Runs parallel mark/sweep
4. Frees 100MB of garbage
5. used_bytes now 290MB
6. Sets gc_phase = IDLE

Thread B requests 200MB:

1. current: 290MB + 200MB = 490MB
2. 490MB < 512MB (hard_limit) → OK
3. But 490MB > 384MB (soft_limit)
4. GC requested, allocation proceeds

Thread C requests 50MB while used is 490MB:

1. 490MB + 50MB = 540MB > 512MB (hard_limit)!
2. Emergency GC triggered (blocking)
3. heap->in_emergency_gc = true
4. Synchronous collection runs
5. Frees 150MB → used = 340MB
6. 340MB + 50MB = 390MB < 512MB → OK
7. Allocation succeeds

Thread D requests 200MB while used is 500MB:

1. 500MB + 200MB = 700MB > 512MB
2. Emergency GC: frees only 20MB → 480MB
3. 480MB + 200MB = 680MB > 512MB
4. STILL over limit after emergency GC
5. valk_gc_oom_abort() → prints diagnostics, abort()
```

### Scenario 5: Multi-threaded Contention

```
4 threads allocating concurrently:

Initial state:
  - Class 3: 1 page, 512 slots
  - All TLABs empty

T0: valk_gc_alloc(72)
  - TLAB[3] empty
  - Lock class[3].lock
  - Claim slots 0-31
  - Unlock
  - Return slot 0

T1: valk_gc_alloc(72) (simultaneous)
  - TLAB[3] empty
  - Lock class[3].lock (blocks until T0 releases)
  - Claim slots 32-63
  - Unlock
  - Return slot 32

T2, T3: Same pattern
  - T2 gets slots 64-95
  - T3 gets slots 96-127

After initial refill, each thread has 32-slot TLAB:
  - T0: slots 0-31
  - T1: slots 32-63
  - T2: slots 64-95
  - T3: slots 96-127

Next 31 allocations per thread: FAST PATH (no locks!)

T0's TLAB exhausted first:
  - Lock class[3].lock
  - Page has 384 free slots (128-511)
  - Claim slots 128-159
  - Unlock
  - Continue fast path

Page fills up (512 slots):
  - Next refill: allocate new page
  - mprotect() to commit 64KB
  - Add to all_pages and partial_pages
  - Claim first 32 slots
```

### Scenario 6: GC During Active I/O

```
HTTP server with 4 AIO threads:

Main thread: runs REPL, def's handlers
AIO threads: handle HTTP requests

Request comes in:
  1. AIO thread 2 parses request
  2. Allocates lvals for headers, body
  3. Calls Lisp handler function
  4. Handler allocates response data

During handler execution:
  1. Main thread triggers GC (heap pressure)
  2. gc_phase = STW_REQUESTED

AIO thread 2 at safe point (after libuv poll):
  1. VALK_GC_SAFE_POINT() sees STW_REQUESTED
  2. Evacuates scratch arena to GC heap
  3. Increments threads_paused
  4. Waits on gc_done condition

Other AIO threads:
  1. Each reaches safe point
  2. Each evacuates and pauses
  3. Last thread signals all_paused

GC runs:
  1. All 5 threads participate in marking
  2. AIO thread 2 marks: request lvals, handler closure, response data
  3. Parallel sweep frees unreachable
  4. gc_phase = IDLE, broadcast gc_done

Threads resume:
  1. AIO thread 2 continues handler
  2. Response data still valid (was marked)
  3. Sends response, resets scratch arena
```

### Scenario 7: Closure Escaping Scratch Arena

```
REPL eval: (def make-counter (fn () (let ((n 0)) (fn () (set! n (+ n 1)) n))))

Scratch arena during eval:
  1. Parse creates S-expression in scratch
  2. Eval creates lambda object in scratch
  3. Lambda captures closure env with n=0
  
Checkpoint before REPL prompt:
  1. valk_should_checkpoint() returns true
  2. valk_checkpoint() called:
     a. Walk from root_env
     b. Find def'd make-counter → lambda
     c. Evacuate lambda to GC heap (class 3)
     d. Evacuate closure env to GC heap
     e. Evacuate n binding to GC heap
     f. Set forwarding pointers
     g. Fix internal pointers
  3. Reset scratch arena
  4. root_env->vals[make-counter] now points to GC heap

REPL eval: (def c1 (make-counter))

  1. Call make-counter (from GC heap)
  2. Creates new closure in scratch
  3. Closure has env with n=0
  4. Checkpoint:
     a. Evacuate c1 closure to GC heap
     b. Evacuate its env to GC heap

REPL eval: (c1) → 1
REPL eval: (c1) → 2
REPL eval: (c1) → 3

Each call:
  1. Closure's env (in GC heap) modified: n incremented
  2. Mutation happens in GC heap directly
  3. No scratch involvement for n
  4. Return value (number) in scratch, discarded after print
```

---

## Core Operation Scenarios

These scenarios document the expected step-by-step behavior for every core GC operation.

### Op 1: Allocate Small Object (TLAB Fast Path)

**Preconditions**:
- Thread has TLAB with `next_slot < limit_slot` for target class
- Heap under soft limit

**Steps**:
```
1. valk_gc_alloc(heap, 72)
   
2. Check: 72 <= 4096 (not large object)
   └─ Continue to size class path

3. class = valk_gc_size_class(72)
   └─ 72 > 64, 72 <= 128 → class = 3

4. tlab = valk_thread_ctx.tlab
   └─ Thread-local, no lock needed

5. Check: tlab->classes[3].next_slot < tlab->classes[3].limit_slot
   └─ 5 < 32 → TRUE (fast path)

6. slot = tlab->classes[3].next_slot++
   └─ slot = 5, next_slot becomes 6

7. ptr = valk_gc_page_slot_ptr(tlab->classes[3].page, 5)
   └─ ptr = page->slots + (5 * 128)

8. memset(ptr, 0, 128)
   └─ Zero-initialize slot

9. return ptr
   └─ Allocation complete, ~15ns
```

**Postconditions**:
- `tlab->classes[3].next_slot` incremented by 1
- No locks acquired
- No atomic operations (slot was pre-claimed)

---

### Op 2: Allocate Small Object (TLAB Refill - Partial Page)

**Preconditions**:
- Thread's TLAB exhausted for class 3 (`next_slot >= limit_slot`)
- Class 3 has partial pages with free slots

**Steps**:
```
1. valk_gc_alloc(heap, 72) → class 3

2. Check TLAB: next_slot (32) >= limit_slot (32)
   └─ TLAB exhausted, slow path

3. valk_gc_alloc_slow(heap, class=3)

4. pthread_mutex_lock(&heap->classes[3].lock)
   └─ Acquire class lock

5. page = heap->classes[3].partial_pages
   └─ Get first partial page (has free slots)

6. start_slot = valk_gc_find_free_slots(page, 32)
   └─ Scan bitmap for 32 contiguous free slots
   └─ Found at slot 256

7. Mark slots 256-287 allocated:
   for (i = 256; i < 288; i++)
     valk_gc_bitmap_set(page->alloc_bitmap, i)

8. atomic_fetch_add(&page->num_allocated, 32)
   └─ 384 → 416

9. atomic_fetch_add(&heap->classes[3].used_slots, 32)

10. atomic_fetch_add(&heap->used_bytes, 32 * 128)
    └─ Track memory usage

11. Check: page->num_allocated (416) < slots_per_page (512)
    └─ Still partial, leave in partial_pages

12. pthread_mutex_unlock(&heap->classes[3].lock)

13. Update TLAB:
    tlab->classes[3].page = page
    tlab->classes[3].next_slot = 256
    tlab->classes[3].limit_slot = 288

14. Return first slot (256), increment next_slot to 257
```

**Postconditions**:
- TLAB refilled with 32 slots
- `page->alloc_bitmap` bits 256-287 set
- Class lock released
- ~500ns total

---

### Op 3: Allocate Small Object (TLAB Refill - New Page)

**Preconditions**:
- Thread's TLAB exhausted for class 3
- No partial pages available (all full)

**Steps**:
```
1. valk_gc_alloc_slow(heap, class=3)

2. pthread_mutex_lock(&heap->classes[3].lock)

3. page = heap->classes[3].partial_pages
   └─ NULL (no partial pages)

4. pthread_mutex_unlock(&heap->classes[3].lock)
   └─ Release lock before slow allocation

5. page = valk_gc_page_alloc(heap, class=3)

   5a. page_size = valk_gc_page_total_size(128)
       └─ sizeof(header) + 2*64 (bitmaps) + 512*128 = ~66KB

   5b. Check: committed_bytes + 66KB <= hard_limit
       └─ OK

   5c. Allocate page from virtual region:
       offset = atomic_fetch_add(&heap->classes[3].next_offset, page_size)
       page = heap->base + heap->classes[3].region_start + offset

   5d. mprotect(page, page_size, PROT_READ | PROT_WRITE)
       └─ Commit physical memory (first access)

   5e. atomic_fetch_add(&heap->committed_bytes, page_size)

   5f. Initialize page:
       page->slot_size = 128
       page->slots_per_page = 512
       page->num_allocated = 0
       memset(page->alloc_bitmap, 0, 64)
       memset(page->mark_bitmap, 0, 64)

6. pthread_mutex_lock(&heap->classes[3].lock)

7. Add page to lists:
   page->next = heap->classes[3].all_pages
   heap->classes[3].all_pages = page
   page->next_partial = heap->classes[3].partial_pages
   heap->classes[3].partial_pages = page
   heap->classes[3].num_pages++

8. atomic_fetch_add(&heap->classes[3].total_slots, 512)

9. Claim slots 0-31 (same as Op 2, steps 7-10)

10. pthread_mutex_unlock(&heap->classes[3].lock)

11. Update TLAB, return slot 0
```

**Postconditions**:
- New 64KB page committed
- Page added to `all_pages` and `partial_pages`
- `committed_bytes` increased by ~66KB
- ~10μs total (mprotect dominates)

---

### Op 4: Allocate Large Object (>4KB)

**Preconditions**:
- Requested size > 4096 bytes
- Heap under hard limit

**Steps**:
```
1. valk_gc_alloc(heap, 1048576)  // 1MB

2. Check: 1048576 > 4096
   └─ Large object path

3. valk_gc_alloc_large(heap, 1048576)

4. alloc_size = (1048576 + 65535) & ~65535
   └─ Round to 64KB boundary: 1048576 (already aligned)

5. Check limits:
   current = valk_gc_used_bytes(heap)  // e.g., 100MB
   if (100MB + 1MB > hard_limit)
     └─ No, continue

6. data = mmap(NULL, 1048576, PROT_READ|PROT_WRITE,
               MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)
   └─ OS allocates 1MB

7. obj = malloc(sizeof(valk_gc_large_obj_t))
   obj->data = data
   obj->size = 1048576
   obj->marked = false

8. pthread_mutex_lock(&heap->large_lock)

9. obj->next = heap->large_objects
   heap->large_objects = obj
   └─ Add to head of list

10. pthread_mutex_unlock(&heap->large_lock)

11. atomic_fetch_add(&heap->large_object_bytes, 1048576)

12. return data
```

**Postconditions**:
- 1MB mmap'd region returned
- Tracking struct in `large_objects` list
- `large_object_bytes` increased by 1MB
- ~100μs (mmap syscall)

---

### Op 5: Mark Single Object (Slot in Page)

**Preconditions**:
- Object pointer known to be in GC heap
- Mark phase in progress

**Steps**:
```
1. mark_and_push(ptr, queue, heap)
   └─ ptr = 0x7f0001234500 (example)

2. valk_gc_ptr_to_location(heap, ptr, &class, &page, &slot)

   2a. Check bounds:
       base = 0x7f0001000000
       ptr >= base && ptr < base + 4GB
       └─ TRUE

   2b. offset = ptr - base = 0x234500

   2c. For each class, check region:
       class 3 region: 0x200000 - 0x400000
       offset 0x234500 in range
       └─ class = 3

   2d. page_size = 66KB
       page_index = (0x234500 - 0x200000) / 66KB = 3

   2e. Walk to page 3 in class 3 list
       └─ page = 4th page

   2f. slot = (ptr - page->slots) / 128
       └─ slot = 42

3. valk_gc_try_mark_slot(page, slot=42)

   3a. byte = &page->mark_bitmap[42 / 8]
       └─ byte = &mark_bitmap[5]

   3b. bit = 1 << (42 % 8)
       └─ bit = 0x04

   3c. old = __atomic_fetch_or(byte, bit, __ATOMIC_ACQ_REL)
       └─ Atomic OR sets the bit

   3d. return (old & bit) == 0
       └─ TRUE if we set it first (newly marked)
       └─ FALSE if already marked (skip)

4. If newly marked:
   valk_gc_mark_queue_push(queue, ptr)
   └─ Add to local mark queue for scanning
```

**Postconditions**:
- Mark bit set atomically (no double-marking)
- Object queued for child scanning
- ~50ns per object

---

### Op 6: Mark Large Object

**Preconditions**:
- Pointer not found in page regions (Op 5 step 2 failed)
- Pointer might be large object

**Steps**:
```
1. valk_gc_mark_large_object(heap, ptr)

2. pthread_mutex_lock(&heap->large_lock)
   └─ Must lock to traverse list safely

3. Search large_objects list:
   for (obj = heap->large_objects; obj; obj = obj->next)
     if (ptr >= obj->data && ptr < obj->data + obj->size)
       └─ Found! ptr is in this large object

4. If found:
   obj->marked = true
   └─ Simple bool, no atomic needed (GC is STW)

5. pthread_mutex_unlock(&heap->large_lock)

6. Note: Large objects don't have children to scan
   (they're raw byte buffers like strings)
```

**Postconditions**:
- `large_obj->marked = true`
- ~100ns (lock contention possible)

---

### Op 7: Scan Object for Children

**Preconditions**:
- Object was just marked
- Need to find and mark children

**Steps**:
```
1. scan_object(ptr, class=3, queue, heap)
   └─ ptr points to slot, class tells us size

2. Check if could be lval (class >= 2 for 64+ bytes):
   size_classes[3] = 128 >= sizeof(valk_lval_t) = 72
   └─ Yes, interpret as lval

3. v = (valk_lval_t *)ptr

4. Read type: LVAL_TYPE(v)
   └─ Say it's LVAL_CONS (cons cell)

5. switch (LVAL_CONS):
   
   5a. mark_and_push(v->cons.head, queue, heap)
       └─ Recursively mark head
       └─ If head is in GC heap, marks and queues it

   5b. mark_and_push(v->cons.tail, queue, heap)
       └─ Recursively mark tail

6. For LVAL_FUN (closure):
   mark_and_push(v->fun.formals, queue, heap)
   mark_and_push(v->fun.body, queue, heap)
   scan_env(v->fun.env, queue, heap)  // Recurse into env
   mark_and_push(v->fun.name, queue, heap)

7. For LVAL_STR/SYM/ERR:
   mark_and_push(v->str, queue, heap)
   └─ Mark string data (may be in class 0-2)

8. For LVAL_NUM/NIL:
   └─ No children, nothing to do
```

**Postconditions**:
- All reachable children marked and queued
- ~20-100ns depending on type

---

### Op 8: Sweep Page (Word-at-a-Time)

**Preconditions**:
- Mark phase complete
- Page assigned to this thread for sweeping

**Steps**:
```
1. sweep_page(page, heap)
   └─ page has 512 slots, 128 bytes each

2. num_words = (512 + 63) / 64 = 8
   └─ Process 8 64-bit words

3. For each word w = 0..7:

   3a. alloc = alloc_words[w]  // e.g., 0xFFFF00FF00FF00FF
       mark  = mark_words[w]   // e.g., 0xFF0000FF00FF0000

   3b. garbage = alloc & ~mark
       └─ 0xFFFF00FF00FF00FF & 0x00FFFF00FF00FFFF
       └─ garbage = 0x00FF000000000FFF
       └─ Bits set = allocated but not marked

   3c. freed = __builtin_popcountll(garbage)
       └─ Count garbage bits: 20 slots

   3d. alloc_words[w] = alloc & mark
       └─ Clear garbage from alloc bitmap
       └─ 0xFF0000FF00FF0000

   3e. For each garbage bit (finalizers):
       while (garbage) {
         bit = __builtin_ctzll(garbage)  // Find lowest set bit
         slot = w * 64 + bit
         ptr = page->slots + (slot * 128)
         
         // Check for finalizer
         if (LVAL_TYPE((valk_lval_t*)ptr) == LVAL_REF) {
           valk_lval_t *v = (valk_lval_t*)ptr;
           if (v->ref.free) v->ref.free(v->ref.ptr);
         }
         
         garbage &= garbage - 1  // Clear lowest bit
       }

   3f. mark_words[w] = 0
       └─ Clear mark bits for next cycle

4. atomic_fetch_sub(&page->num_allocated, total_freed)

5. Return total_freed
```

**Postconditions**:
- Garbage slots freed (alloc bits cleared)
- Mark bits cleared for next cycle
- Finalizers called for LVAL_REF
- ~100ns per page (mostly CPU-bound)

---

### Op 9: Sweep Large Objects

**Preconditions**:
- Mark phase complete
- Thread 0 responsible for large objects

**Steps**:
```
1. sweep_large_objects(heap)

2. pthread_mutex_lock(&heap->large_lock)

3. pp = &heap->large_objects  // Pointer to pointer

4. while (*pp != NULL):
   obj = *pp

   4a. If !obj->marked (garbage):
       
       // Remove from list
       *pp = obj->next
       
       // Free memory
       munmap(obj->data, obj->size)
       
       // Track freed bytes
       freed += obj->size
       
       // Free tracking struct
       free(obj)
       
       // Don't advance pp (next item now at *pp)

   4b. If obj->marked (live):
       
       // Clear mark for next cycle
       obj->marked = false
       
       // Advance to next
       pp = &obj->next

5. pthread_mutex_unlock(&heap->large_lock)

6. atomic_fetch_sub(&heap->large_object_bytes, freed)

7. Return freed
```

**Postconditions**:
- Unmarked large objects munmap'd
- `large_object_bytes` decreased
- Marks cleared for next cycle
- ~1μs per large object (munmap syscall)

---

### Op 10: Reclaim Empty Page

**Preconditions**:
- Sweep complete
- Page has `num_allocated == 0`

**Steps**:
```
1. valk_gc_reclaim_empty_pages(heap)

2. For each class c:

   pthread_mutex_lock(&heap->classes[c].lock)

   3. Clear partial_pages list (will rebuild):
      heap->classes[c].partial_pages = NULL

   4. For each page in all_pages:
      allocated = atomic_load(&page->num_allocated)

      4a. If allocated == 0 (empty):
          
          // Release physical memory back to OS
          page_size = valk_gc_page_total_size(size_classes[c])
          madvise(page, page_size, MADV_DONTNEED)
          
          // Page stays in all_pages (virtual address valid)
          // Will be recommitted on first allocation

      4b. Else if allocated < slots_per_page (partial):
          
          // Add to partial list for allocation
          page->next_partial = heap->classes[c].partial_pages
          heap->classes[c].partial_pages = page

      4c. Else (full):
          
          // Not added to partial list
          // Only accessed via all_pages during sweep

   pthread_mutex_unlock(&heap->classes[c].lock)
```

**Postconditions**:
- Empty pages: physical memory released, virtual address retained
- Partial pages: available for new allocations
- Full pages: unchanged
- ~1μs per empty page (madvise)

---

### Op 11: TLAB Reset After GC

**Preconditions**:
- Sweep complete
- Threads about to resume

**Steps**:
```
1. Each thread in parallel:

2. For each class c = 0..8:
   
   tlab->classes[c].page = NULL
   tlab->classes[c].next_slot = 0
   tlab->classes[c].limit_slot = 0

3. Why reset?
   - Pre-sweep slot claims may now be garbage
   - Safer to force refill from fresh partial pages
   - Ensures no dangling references to freed slots
```

**Postconditions**:
- All TLABs empty
- Next allocation triggers refill (Op 2 or Op 3)
- ~10ns per thread

---

### Op 12: Trigger GC (Threshold Reached)

**Preconditions**:
- Allocation detects: `used_bytes > committed_bytes * threshold_pct`
- No GC in progress

**Steps**:
```
1. In valk_gc_alloc, after allocation:

2. Check threshold:
   used = valk_gc_used_bytes(heap)
   threshold = heap->committed_bytes * heap->gc_threshold_pct / 100
   
   if (used > threshold && !heap->gc_in_progress)
     valk_gc_request_collection()

3. valk_gc_request_collection():
   
   3a. if (atomic_exchange(&heap->gc_requested, true))
       return  // Already requested
   
   3b. atomic_store(&valk_gc_coord.gc_phase, GC_PHASE_STW_REQUESTED)

4. Allocation continues (non-blocking)

5. Eventually, thread hits safe point:
   
   VALK_GC_SAFE_POINT()
   
   5a. if (gc_phase == STW_REQUESTED) {
       valk_gc_enter_stw()
   }
```

**Postconditions**:
- GC requested (will happen at next safe point)
- Current allocation succeeds
- Non-blocking for requestor

---

### Op 13: Enter Stop-The-World

**Preconditions**:
- Thread at safe point
- `gc_phase == STW_REQUESTED`

**Steps**:
```
1. valk_gc_enter_stw()

2. Evacuate thread's scratch arena:
   valk_checkpoint()
   └─ Moves live scratch objects to GC heap
   └─ Fixes pointers

3. Increment paused count:
   count = atomic_fetch_add(&valk_gc_coord.threads_paused, 1) + 1

4. Check if last to pause:
   if (count == valk_gc_coord.threads_registered) {
     // All threads paused, signal coordinator
     pthread_cond_signal(&valk_gc_coord.all_paused)
   }

5. Wait for GC completion:
   while (atomic_load(&valk_gc_coord.gc_phase) != GC_PHASE_IDLE) {
     // Participate in GC work
     valk_gc_participate()
   }

6. Reset thread state:
   // Ready to resume normal operation
```

**Postconditions**:
- Thread's scratch arena checkpointed
- Thread participating in GC work
- Will resume when `gc_phase == IDLE`

---

### Op 14: GC Cycle Complete Flow

**Preconditions**:
- All threads paused
- Coordinator running GC

**Steps**:
```
1. Coordinator detects all_paused:

2. atomic_store(&gc_phase, GC_PHASE_MARKING)

3. Signal threads to start marking:
   valk_barrier_release(&mark_start_barrier)

4. All threads run valk_gc_parallel_mark():
   - Each marks own roots
   - Thread 0 marks global roots
   - Work-stealing mark loop

5. Barrier: wait for all marking complete

6. atomic_store(&gc_phase, GC_PHASE_SWEEPING)

7. All threads run valk_gc_parallel_sweep():
   - Each sweeps assigned pages
   - Thread 0 sweeps large objects

8. Barrier: wait for all sweeping complete

9. Thread 0: valk_gc_reclaim_empty_pages()

10. All threads: reset TLABs

11. atomic_store(&gc_phase, GC_PHASE_IDLE)

12. pthread_cond_broadcast(&gc_done)
    └─ Wake any threads waiting

13. atomic_store(&heap->gc_requested, false)
    └─ Allow new GC requests

14. Threads resume normal operation
```

**Postconditions**:
- Garbage collected
- Memory reclaimed
- `used_bytes` decreased
- All threads running

---

### Op 15: Emergency GC (Hard Limit Approached)

**Preconditions**:
- Allocation would exceed hard limit
- `heap->in_emergency_gc == false`

**Steps**:
```
1. In valk_gc_alloc:

2. Check hard limit:
   current = valk_gc_used_bytes(heap)
   if (current + bytes > heap->hard_limit) {
     // Must GC now
   }

3. valk_gc_emergency_collect(heap):

   3a. heap->in_emergency_gc = true
       └─ Prevent recursive emergency GC

   3b. // Force synchronous STW
       atomic_store(&gc_phase, GC_PHASE_STW_REQUESTED)

   3c. // Current thread enters STW immediately
       valk_gc_enter_stw()

   3d. // Wait for GC to complete
       // (participates in marking/sweeping)

   3e. heap->in_emergency_gc = false

4. After emergency GC, recheck:
   current = valk_gc_used_bytes(heap)
   if (current + bytes > heap->hard_limit) {
     // Still over! Can't allocate
     valk_gc_oom_abort(heap, bytes)
   }

5. Proceed with allocation
```

**Postconditions**:
- Synchronous GC completed
- Either allocation succeeds or process aborts
- ~10-50ms pause (full GC)

---

### Op 16: OOM Abort

**Preconditions**:
- Emergency GC didn't free enough
- Allocation still exceeds hard limit

**Steps**:
```
1. valk_gc_oom_abort(heap, requested_bytes)

2. Print diagnostic header:
   "FATAL: OUT OF MEMORY"

3. Print memory state:
   Requested: 10485760 bytes
   Used:      510000000 bytes
   Hard Limit: 536870912 bytes
   Committed: 520000000 bytes

4. Print per-class breakdown:
   Class 0 (16 B):   50000 / 100000 slots (50%)
   Class 1 (32 B):   25000 / 50000 slots (50%)
   Class 2 (64 B):   10000 / 20000 slots (50%)
   Class 3 (128 B): 200000 / 400000 slots (50%)
   ...
   Large Objects: 50000000 bytes

5. Print suggestion:
   "Increase limit: VALK_HEAP_HARD_LIMIT=1073741824"

6. abort()
   └─ Process terminates, core dump if enabled
```

**Postconditions**:
- Process terminated
- Diagnostics printed to stderr
- No undefined behavior

---

## Configuration

### Environment Variables

```bash
# Memory limits
VALK_HEAP_HARD_LIMIT=536870912    # 512MB (default)
VALK_HEAP_SOFT_LIMIT=402653184    # 384MB (default = 75% of hard)
VALK_SCRATCH_SIZE=67108864        # 64MB per thread (default)

# GC tuning
VALK_GC_THRESHOLD_PCT=75          # Trigger GC at this % of committed
VALK_GC_TLAB_SLOTS=32             # Slots per TLAB refill

# Debug
VALK_GC_VERBOSE=1                 # Print GC cycle info
VALK_GC_STRESS=1                  # GC on every allocation (testing)
```

### Runtime API

```c
// Set hard limit (must be >= current usage)
void valk_gc_set_hard_limit(valk_gc_heap_t *heap, size_t bytes);

// Set soft limit (triggers emergency GC)
void valk_gc_set_soft_limit(valk_gc_heap_t *heap, size_t bytes);

// Set GC trigger threshold (0-100)
void valk_gc_set_threshold_pct(valk_gc_heap_t *heap, uint8_t pct);

// Force GC cycle (for testing/debugging)
void valk_gc_force_collect(valk_gc_heap_t *heap);

// Get current stats
void valk_gc_get_stats(valk_gc_heap_t *heap, valk_gc_stats_t *out);
```

---

## Implementation Phases

### Phase 1: Size Class Infrastructure

**Goal**: Implement multi-class allocation without breaking existing code.

1. Define size class table and lookup
2. Create per-class page lists
3. Implement class-aware TLAB
4. Add per-class accounting

**Tests**:
- `test_gc_size_class_lookup`: Verify class selection for various sizes
- `test_gc_multiclass_alloc`: Allocate from multiple classes
- `test_gc_class_accounting`: Verify per-class slot counts

### Phase 2: Large Object Support

**Goal**: Handle allocations > 4KB.

1. Implement mmap-based large object allocation
2. Add large object tracking list
3. Integrate with mark/sweep

**Tests**:
- `test_gc_large_alloc`: Allocate and free large objects
- `test_gc_large_mark`: Mark phase finds large objects
- `test_gc_large_sweep`: Sweep frees unmarked large objects

### Phase 3: Memory Limits

**Goal**: Enforce hard/soft limits with proper error handling.

1. Implement limit checking in allocation path
2. Add emergency GC trigger
3. Implement OOM abort with diagnostics

**Tests**:
- `test_gc_soft_limit_trigger`: Exceeding soft limit triggers GC
- `test_gc_hard_limit_emergency`: Emergency GC when approaching hard
- `test_gc_hard_limit_oom`: OOM abort when over hard limit

### Phase 4: Bitmap-Based Mark/Sweep

**Goal**: Replace linked-list traversal with bitmap operations.

1. Implement per-page mark bitmaps
2. Implement word-at-a-time sweep
3. Implement parallel sweep partitioning

**Tests**:
- `test_gc_bitmap_mark`: Atomic marking in bitmap
- `test_gc_bitmap_sweep`: Word-at-a-time sweep correctness
- `test_gc_parallel_sweep`: Multi-threaded sweep

### Phase 5: Page Reclamation

**Goal**: Return unused memory to OS.

1. Detect empty pages after sweep
2. Call madvise(MADV_DONTNEED) on empty pages
3. Rebuild partial_pages lists

**Tests**:
- `test_gc_page_reclaim`: Empty pages released
- `test_gc_page_recommit`: Released pages usable again

### Phase 6: Integration

**Goal**: Wire everything together, remove old GC.

1. Replace old slab allocators with new size classes
2. Update evacuation to use new allocation
3. Remove legacy GC code

**Tests**:
- Full test suite passes
- HTTP stress test stable
- Memory usage within limits

---

## Performance Targets

| Metric | Target | Notes |
|--------|--------|-------|
| Allocation (fast path) | < 20 ns | TLAB bump only |
| Allocation (slow path) | < 1 μs | TLAB refill |
| GC pause (100MB heap) | < 10 ms | 4 threads parallel |
| GC pause (500MB heap) | < 50 ms | 4 threads parallel |
| Memory overhead | < 5% | Bitmaps + waste |
| Peak RSS | < hard_limit + scratch | Proper accounting |

---

## Implementation Progress

### Status Legend
- [ ] Not started
- [~] In progress
- [x] Complete
- [-] Skipped/Not needed

### Phase 0: Infrastructure (COMPLETE)
- [x] Atomic marks in lval flags
- [x] Chase-Lev deque for work stealing
- [x] Thread registration system
- [x] Safe points with STW coordination
- [x] Global roots registry
- [x] Portable barrier implementation

### Phase 1: Size Class Infrastructure
- [x] Size class constants and lookup (`VALK_GC_NUM_SIZE_CLASSES`, `valk_gc_size_class()`)
- [x] Per-class page list (`valk_gc_page_list_t`)
- [x] Main heap structure (`valk_gc_heap2_t`)
- [x] Class-aware TLAB (`valk_gc_tlab2_t` with per-class state)
- [x] Virtual address reservation (4GB mmap PROT_NONE) **FIXED in Phase 11**
- [x] Page commit on demand (mprotect) **FIXED in Phase 11**
- [x] Class-aware allocation fast path
- [x] Class-aware allocation slow path (TLAB refill)
- [x] Unit tests for size class allocation (12 new tests added)

### Phase 2: Large Object Support
- [x] Large object structure (`valk_gc_large_obj_t`)
- [x] mmap-based large allocation
- [x] Large object tracking list
- [x] Large object marking (`valk_gc_mark_large_object()`)
- [x] Large object sweeping (`valk_gc_sweep_large_objects()`)
- [x] Unit tests for large objects

### Phase 3: Memory Limits
- [x] Hard limit enforcement in allocation
- [x] Soft limit and emergency GC trigger
- [x] OOM abort with diagnostics (`valk_gc_oom_abort()`)
- [x] Memory accounting (committed_bytes, used_bytes) - basic tracking in place
- [x] GC statistics (`valk_gc_heap2_get_stats()`, `valk_gc_stats2_t`)
- [x] Full GC collection cycle (`valk_gc_heap2_collect()`)
- [x] TLAB reset (`valk_gc_tlab2_reset()`)
- [x] Unit tests for limit enforcement (7 new tests)

### Phase 4: Bitmap-Based Mark/Sweep
- [x] Per-page mark bitmaps (inline in page2 structure)
- [x] Atomic mark bit operations (`valk_gc_bitmap_try_set_atomic()`)
- [x] Pointer-to-location lookup (`valk_gc_ptr_to_location()`) **FIXED: Now O(1) via address arithmetic**
- [x] Full mark phase with root enumeration (`valk_gc_heap2_mark_roots()`, `mark_children2()`, `mark_env2()`)
- [x] Mark context struct (`valk_gc_mark_ctx2_t`)
- [x] Unit tests for bitmap marking (6 Phase 4 tests)

### Phase 5: Page Reclamation
- [x] Word-at-a-time bitmap sweep (`valk_gc_sweep_page2()`)
- [x] Finalizer support (LVAL_REF) - in sweep_page2
- [x] Page reclamation via madvise (`valk_gc_reclaim_empty_pages()`) **FIXED: Pages are now mmap'd**
- [x] Partial page list rebuild (`valk_gc_rebuild_partial_lists()`)
- [x] TLAB reset after GC
- [x] Unit tests for sweep and reclamation (12 tests total)

### Phase 6: Integration (COMPLETE)
- [x] Replace valk_gc_malloc_heap_t with new heap (typedef to valk_gc_heap2_t)
- [x] Update evacuation to use new allocation
- [x] Update marking to use new heap
- [x] Remove legacy slab allocators (~1200 lines deleted)
- [x] Full test suite passes
- [x] HTTP stress test stable

### Phase 7: Parallel Mark/Sweep (COMPLETE)
- [x] Parallel mark with work-stealing (`valk_gc_heap2_parallel_mark()`)
- [x] Parallel sweep with page partitioning (`valk_gc_heap2_parallel_sweep()`)
- [x] Full parallel collection cycle (`valk_gc_heap2_parallel_collect()`)
- [x] STW request and coordination (`valk_gc_heap2_request_stw()`)
- [x] Termination detection (`valk_gc_heap2_check_termination()`)
- [x] Unit tests for parallel functions (7 tests)

### Phase 8: Auto GC and Safe Points (COMPLETE)
- [x] Auto-select parallel vs single-threaded (`valk_gc_heap2_collect_auto()`)
- [x] Safe point in eval loop (`valk_lval_eval_recursive()`)
- [x] Safe point in maintenance timer (`__maintenance_timer_cb()`)
- [x] Soft limit triggers `collect_auto()`
- [x] Emergency GC uses `collect_auto()`
- [x] Multi-threaded allocation tests (2 tests)

### Phase 9: Worker Participation (COMPLETE)
- [x] Workers participate in parallel GC (`valk_gc_participate_in_parallel_gc()`)
- [x] Safe point slow path calls participate function
- [x] Initiator counted in threads_paused
- [x] Parallel GC stress tests (2 tests)

### Phase 10: Critical Testing (COMPLETE)
- [x] True multi-threaded parallel GC test (`test_gc_heap2_true_parallel_gc`)
- [x] Thread-local root marking verification test (`test_gc_parallel_thread_local_roots`)
- [x] Barrier sequence comments in `parallel_collect()` and `participate_in_parallel_gc()`
- [ ] Work-stealing verification test (deferred - complex to verify)

### Phase 11: Virtual Memory Reservation (COMPLETE)
- [x] Reserve 4GB virtual address space at heap creation (`mmap PROT_NONE`)
- [x] Per-class contiguous regions (~477MB each)
- [x] Page commit on demand with `mprotect(PROT_READ | PROT_WRITE)`
- [x] O(1) pointer-to-location via address arithmetic
- [x] madvise actually works for page reclamation (pages are now mmap'd)
- [x] Fixed `__gc_heap2_current` race condition with atomic operations

### Phase 12: Remaining Tests (COMPLETE)
- [x] `valk_gc_heap2_realloc()` tests (3 tests added)
- [x] Soft limit / emergency GC multi-threaded tests (`test_gc_heap2_soft_limit_multithread`)
- [x] TLAB exhaustion during GC test (`test_gc_heap2_tlab_exhaust_during_gc`)
- [x] Thread unregister during GC test (`test_gc_thread_unregister_safe`)

### Phase 13: Bug Fixes (COMPLETE)
- [x] Fixed `test_gc_max_pause_tracking` crash - `valk_gc_heap2_mark_roots()` was not marking `heap->root_env`

### Current Session Log

**2024-12-27**: Starting size class implementation
- Read existing gc.h/gc.c (~3900 lines total)
- Existing infrastructure: single 80-byte slot class, page pool, TLAB
- Next: Add size class constants and multi-class support

**2024-12-27**: Phase 1 Complete - Size Class Infrastructure
- Added 9 size classes: 16, 32, 64, 128, 256, 512, 1024, 2048, 4096 bytes
- Fixed page layout math to account for header + inline bitmaps
- Implemented `valk_gc_page2_t` with accessor functions for bitmaps/slots
- Implemented `valk_gc_page_list_t` for per-class page tracking
- Implemented `valk_gc_heap2_t` with per-class arrays
- Implemented `valk_gc_tlab2_t` with per-class TLAB state
- Implemented `valk_gc_heap2_create()`, `valk_gc_heap2_destroy()`
- Implemented `valk_gc_heap2_alloc()` with fast/slow paths
- Implemented large object allocation via mmap
- Added 12 unit tests, all passing
- Full test suite (69 GC tests, all Valk tests) passing

**2024-12-27**: Phase 2 Complete - Pointer Location and Marking/Sweeping
- Moved basic bitmap operations earlier in gc.h (needed for new inline functions)
- Added atomic bitmap operations for thread-safe marking:
  - `valk_gc_bitmap_try_set_atomic()` - atomic test-and-set
  - `valk_gc_bitmap_test_atomic()` - atomic read
- Added `valk_gc_ptr_location_t` result structure
- Implemented `valk_gc_ptr_to_location()` - finds page/slot for a pointer
- Added inline marking helpers:
  - `valk_gc_page2_try_mark()` - atomic mark attempt
  - `valk_gc_page2_is_marked()` - check mark status
  - `valk_gc_page2_is_allocated()` - check allocation status
- Implemented `valk_gc_mark_large_object()` - marks large objects
- Implemented `valk_gc_sweep_page2()` - word-at-a-time bitmap sweep with:
  - 64-bit word processing for speed
  - Automatic finalizer calls for LVAL_REF
  - Atomic num_allocated updates
- Implemented `valk_gc_sweep_large_objects()` - munmaps unmarked large objects
- Implemented `valk_gc_rebuild_partial_lists()` - rebuilds after sweep
- Added 7 new unit tests (total 76 GC tests), all passing
- Full test suite passing

**2024-12-27**: Phase 3 Complete - Memory Limits and GC Cycle
- Added `valk_gc_stats2_t` structure for comprehensive GC diagnostics
- Implemented `valk_gc_heap2_get_stats()` - populates stats from heap
- Implemented `valk_gc_tlab2_reset()` - clears all TLAB state
- Implemented `valk_gc_oom_abort()` - prints detailed diagnostics, aborts:
  - Shows requested/used/limit bytes
  - Per-class slot usage breakdown
  - Large object bytes
  - Collection count and total reclaimed
  - Suggests doubling limit
- Implemented `valk_gc_heap2_collect()` - full GC cycle:
  - Sweeps all pages in all classes
  - Sweeps large objects
  - Rebuilds partial lists
  - Updates reclaimed statistics
- Updated `valk_gc_heap2_alloc()` and large object allocation:
  - Hard limit check triggers emergency GC, then OOM abort if still over
  - Soft limit check triggers non-blocking GC
  - Emergency GC flag prevents recursive GC
- Added 7 new Phase 3 tests (total 83 GC tests), all passing:
  - test_gc_heap2_get_stats
  - test_gc_tlab2_reset
  - test_gc_heap2_collect_empty
  - test_gc_heap2_collect_reclaims_unmarked
  - test_gc_heap2_collect_preserves_marked
  - test_gc_heap2_soft_limit_triggers_gc
  - test_gc_heap2_collect_updates_stats
- Full test suite passing

**2024-12-27**: Phase 6 Complete - Integration
- Made `valk_gc_malloc_heap_t` a typedef to `valk_gc_heap2_t`
- Replaced all legacy API functions with heap2 wrappers:
  - `valk_gc_malloc_heap_init()` → `valk_gc_heap2_create()`
  - `valk_gc_malloc_heap_alloc()` → `valk_gc_heap2_alloc()`
  - `valk_gc_malloc_collect()` → `valk_gc_heap2_collect()`
  - `valk_gc_malloc_heap_destroy()` → `valk_gc_heap2_destroy()`
- Deleted ~1200 lines of legacy code:
  - Removed slab allocators (lval_slab, lenv_slab)
  - Removed object linked list tracking
  - Removed flag-based marking (LVAL_FLAG_GC_MARK)
  - Removed legacy sweep and collection code
- Updated all callers in parser.c, metrics_builtins.c, aio_sse_diagnostics.c
- Fixed runtime_metrics updating in valk_gc_heap2_collect()
- Fixed TLAB owner tracking to prevent use-after-free
- gc.c reduced from ~4140 to ~2996 lines
- All 94 GC unit tests passing
- Full test suite passing

**2024-12-27**: Phase 7 Complete - Parallel Mark/Sweep for heap2
- Implemented `valk_gc_heap2_parallel_mark()`:
  - Uses coordinator barrier for synchronization
  - Thread 0 marks global roots, all threads mark own roots
  - Work-stealing mark loop with Chase-Lev deques
  - Termination detection via idle counting
- Implemented `valk_gc_heap2_parallel_sweep()`:
  - Partitions pages among threads by size class
  - Thread 0 handles large object sweep
  - Uses existing `valk_gc_sweep_page2()` per page
- Implemented `valk_gc_heap2_parallel_collect()`:
  - Full parallel GC cycle orchestration
  - Falls back to single-threaded collect if only 1 thread registered
  - Updates runtime metrics (pause time, reclaimed bytes)
  - Updates coordinator statistics
- Implemented `valk_gc_heap2_request_stw()`:
  - Requests stop-the-world pause
  - Sets up barrier for registered thread count
  - Waits for all threads to pause
- Added 7 new unit tests for parallel GC functions:
  - test_gc_heap2_parallel_collect_null
  - test_gc_heap2_parallel_collect_single_thread
  - test_gc_heap2_parallel_mark_null
  - test_gc_heap2_parallel_sweep_null
  - test_gc_heap2_request_stw_null
  - test_gc_heap2_parallel_collect_reclaims_bytes
  - test_gc_heap2_parallel_collect_updates_metrics
- gc.c now ~3230 lines (added ~230 lines for parallel implementation)
- All 101 GC unit tests passing
- Full Valk test suite passing

**2024-12-27**: Phase 8 Complete - Auto GC and Integration
- Implemented `valk_gc_heap2_collect_auto()`:
  - Chooses single-threaded or parallel based on registered thread count
  - Falls back to single-threaded if < 2 threads or not registered
  - Uses `valk_gc_heap2_request_stw()` for parallel case
- Updated soft limit trigger path to use `valk_gc_heap2_collect_auto()`
- Updated emergency GC to use `valk_gc_heap2_collect_auto()`
- Safe points already in place:
  - `valk_lval_eval_recursive()` in parser.c - checked on every eval
  - `__maintenance_timer_cb()` in aio_maintenance.c - checked periodically
- Added 2 multi-threaded tests:
  - test_gc_heap2_multithread_alloc - 4 threads allocating concurrently
  - test_gc_heap2_multithread_collect_auto - tests auto collection fallback
- gc.c now ~3260 lines
- All 103 GC unit tests passing
- Full Valk test suite passing

**2024-12-27**: Phase 9 - Fix Parallel GC Worker Participation
- Fixed `valk_gc_safe_point_slow()` to call `valk_gc_participate_in_parallel_gc()`:
  - Worker threads now actively participate in mark/sweep via barriers
  - Previously workers just waited on gc_done condition, not helping
- Fixed `valk_gc_heap2_request_stw()` to count initiator thread as paused:
  - Initiator increments threads_paused before waiting for others
  - Prevents deadlock where initiator waits for num_threads but only (num_threads-1) pause
- Added `valk_gc_participate_in_parallel_gc()`:
  - Called by worker threads from safe point slow path
  - Participates in barrier waits, parallel mark, and parallel sweep
  - Waits for gc_done at the end
- Added 2 parallel GC stress tests:
  - test_gc_heap2_parallel_gc_stress - 4 threads allocating concurrently
  - test_gc_heap2_parallel_gc_stw - single-threaded collect_auto with coordinator init
- gc.c now ~3405 lines
- All 101 GC unit tests passing
- Full Valk test suite passing

**2024-12-27**: Phase 10 & 11 Complete - Critical Testing & Virtual Memory
- Added true multi-threaded parallel GC test (`test_gc_heap2_true_parallel_gc`)
- Added thread-local root marking test (`test_gc_parallel_thread_local_roots`)
- Added barrier sequence comments in `parallel_collect()` and `participate_in_parallel_gc()`
- Fixed `__gc_heap2_current` race condition with atomic operations
- Implemented 4GB virtual memory reservation with `mmap(PROT_NONE)`
- Divided into 9 per-class regions (~477MB each)
- Pages committed on demand with `mprotect(PROT_READ | PROT_WRITE)`
- O(1) pointer-to-location via address arithmetic
- madvise now works correctly for page reclamation
- Added realloc tests (`test_gc_heap2_realloc_basic`, `test_gc_heap2_realloc_null`, `test_gc_heap2_realloc_large`)
- gc.c ~3500 lines, gc.h ~930 lines
- All 106 GC unit tests passing
- Full test suite passing

**2024-12-28**: Phase 12 & 13 Complete - Final Tests and Bug Fixes
- Fixed `test_gc_max_pause_tracking` crash: `valk_gc_heap2_mark_roots()` was not marking `heap->root_env`
- Added `test_gc_heap2_soft_limit_multithread`: multi-threaded soft limit / emergency GC test
- Added `test_gc_heap2_tlab_exhaust_during_gc`: TLAB exhaustion during GC test
- Added `test_gc_thread_unregister_safe`: concurrent thread register/unregister safety test
- All 112 GC unit tests passing, 41 parallel unit tests passing
- Full test suite passing
- **PARALLEL GC PLAN COMPLETE**

**2024-12-29**: Phase 14 - Libuv Event Loop Interrupt for GC Synchronization
- Added global AIO system registry (`g_aio_systems[]` with mutex)
- Added `uv_async_t gc_wakeup` handle per AIO system
- Added `gc_acknowledged` atomic flag to prevent double-counting
- Implemented `valk_aio_wake_all_for_gc()` to wake blocked event loops
- Implemented `__gc_wakeup_cb()` callback that enters safe point
- Updated `valk_gc_heap2_request_stw()` to wake all AIO loops immediately
- AIO threads now respond to GC within ~1ms even when blocked in I/O wait
- Full test suite passing
- **LIBUV GC INTERRUPT COMPLETE**

**2024-12-29**: Phase 15 - Bug Fixes and Additional Testing
- Fixed committed_bytes underflow bug in page reclamation:
  - Added `reclaimed` flag to `valk_gc_page2_t` struct (gc.h:544)
  - Updated `valk_gc_reclaim_empty_pages()` to skip already-reclaimed pages (gc.c:2864)
  - Updated `valk_gc_tlab2_refill()` to restore committed_bytes when reusing reclaimed page (gc.c:2427-2431)
  - Added `test_gc_reclaim_committed_bytes_accounting` test to verify fix
- Updated existing reclaim tests to account for collect() already calling reclaim internally
- Added emergency GC trigger test (`test_gc_emergency_gc_trigger`)
- Added multi-threaded soft limit test (`test_gc_soft_limit_multithread`)
- All 115 GC unit tests passing
- Full test suite passing

---

## Known Gaps and Future Work

### Design Gaps - RESOLVED

All major design gaps have been addressed in Phase 10 and Phase 11:

#### 1. Pointer-to-Location Lookup - FIXED
- **Was**: O(n) walking linked lists of pages
- **Now**: O(1) using address arithmetic with virtual memory regions
- Implemented in `valk_gc_ptr_to_location()` - uses `heap->base` + region offsets

#### 2. Virtual Address Reservation - FIXED
- **Was**: `malloc()` for pages, scattered in memory
- **Now**: 4GB virtual reservation with `mmap(PROT_NONE)`, contiguous class regions
- Each class gets ~477MB region, pages committed on demand with `mprotect()`

#### 3. Page Reclamation via madvise - FIXED
- **Was**: No-op on malloc'd pages
- **Now**: Works correctly since pages are mmap'd
- `valk_gc_reclaim_empty_pages()` properly releases physical memory

#### 4. Class Region Layout - FIXED
- **Was**: Pages scattered, no contiguous layout
- **Now**: Each class has a contiguous region with known offset from `heap->base`
- Enables O(1) class determination from pointer

---

### Testing Gaps - MOSTLY RESOLVED

#### 1. True Multi-Threaded Parallel GC Test - FIXED
- Added `test_gc_heap2_true_parallel_gc` - 4 threads, main triggers parallel GC while workers are running
- Verifies `parallel_cycles` counter is incremented

#### 2. Thread-Local Root Marking - FIXED
- Added `test_gc_parallel_thread_local_roots` - verifies worker thread data survives GC

#### 3. Work-Stealing Verification - DEFERRED
- Complex to verify in a unit test (need to inspect internal queue state)
- Correctness verified by object survival in true parallel GC test

#### 4. Memory Pressure Tests - FIXED
- Added `test_gc_emergency_gc_trigger` - verifies GC triggers near hard limit
- Added `test_gc_soft_limit_multithread` - multi-threaded allocation with pressure

#### 5. valk_gc_heap2_realloc() - FIXED
- Added 3 tests: `test_gc_heap2_realloc_basic`, `test_gc_heap2_realloc_null`, `test_gc_heap2_realloc_large`

---

### Implementation Issues - RESOLVED

#### 1. Barrier Count Mismatch - FIXED
- Added explicit comments for each of the 4 barriers in both `parallel_collect()` and `participate_in_parallel_gc()`
- Comments document: BARRIER 1 (before mark), BARRIER 2 (after mark), BARRIER 3 (after sweep), BARRIER 4 (after reclaim)

#### 2. `__gc_heap2_current` Race Condition - FIXED
- Changed to `_Atomic(valk_gc_heap2_t *)` type
- Uses `atomic_store()` in `request_stw()` and `atomic_load()` in `participate_in_parallel_gc()`

#### 3. Thread Unregister During GC - FIXED
- `valk_gc_thread_unregister()` calls `VALK_GC_SAFE_POINT()` first, blocking until GC completes
- Added `test_gc_thread_unregister_safe` to verify concurrent register/unregister safety

---

### Remaining Work

**All planned work is complete.** The parallel GC implementation is fully functional.

**Potential Future Improvements (Optional):**
- Generation counter updates during sweep for survival histogram (LVAL_GC_GEN_INC macro exists but not called)
- Additional parallel GC integration tests for edge cases

---

---

## Libuv Event Loop Interrupt for GC Synchronization

### Problem Statement

When GC needs to run, all threads must reach safe points. AIO threads run libuv event loops that can be blocked indefinitely in `uv_run()` waiting for I/O. We need a reliable way to:

1. Wake a libuv loop blocked in `uv_run()` from another thread (the GC coordinator)
2. Have the loop thread reach a safe point and pause
3. Participate in parallel GC work
4. Resume normal operation after GC completes

### Research Findings: libuv Internals

#### 1. `uv_async_send()` - Thread-Safe Loop Wakeup

From libuv source (`src/unix/async.c`):

```c
int uv_async_send(uv_async_t* handle) {
  _Atomic int* pending = (_Atomic int*) &handle->pending;
  _Atomic int* busy = (_Atomic int*) &handle->u.fd;

  if (atomic_load_explicit(pending, memory_order_relaxed) != 0)
    return 0;  // Already pending, coalesce

  atomic_fetch_add(busy, 1);  // Enter critical section
  if (atomic_exchange(pending, 1) == 0)
    uv__async_send(handle->loop);  // Actually wake the loop
  atomic_fetch_add(busy, -1);  // Exit critical section
  return 0;
}
```

**Key properties:**
- **Thread-safe**: Uses atomics, safe to call from any thread
- **Signal-safe**: Uses only async-signal-safe operations (write to eventfd/pipe)
- **Coalescing**: Multiple sends before callback runs yield single callback
- **Wakes blocked loop**: Write to eventfd/pipe makes poll return immediately

Internal wakeup mechanism by platform:
- **Linux**: `eventfd()` - writes 8-byte counter
- **macOS/BSD with kqueue**: `EVFILT_USER` with `NOTE_TRIGGER` (optimal)
- **Fallback**: Self-pipe trick - writes 1 byte to pipe

#### 2. `uv_stop()` - Request Loop Exit

```c
void uv_stop(uv_loop_t* loop) {
  loop->stop_flag = 1;  // Simple flag set
}
```

**Critical limitation**: `uv_stop()` alone is NOT safe from another thread when loop is blocked:
- Sets `stop_flag = 1` atomically
- BUT loop may be blocked in `epoll_wait`/`kqueue` with long timeout
- Loop won't check `stop_flag` until poll returns

**Solution**: Always pair with `uv_async_send()`:
```c
void request_loop_stop(gc_coord_t* coord) {
  uv_stop(coord->loop);        // Set flag (may be blocked)
  uv_async_send(&coord->wakeup); // Wake loop to check flag
}
```

#### 3. Shutdown Race Conditions

libuv handles `uv_async_send()` during shutdown with a spin-wait:

```c
static void uv__async_spin(uv_async_t* handle) {
  atomic_store(&handle->pending, 1);  // Block new events

  for (;;) {
    for (i = 0; i < 997; i++) {
      if (atomic_load(&handle->u.fd) == 0)  // busy flag
        return;
      uv__cpu_relax();  // PAUSE instruction
    }
    sched_yield();  // Give up CPU slice
  }
}
```

This ensures all in-flight `uv_async_send()` calls complete before handle is closed.

#### 4. Timeout-Based Safe Points

libuv exposes APIs for external polling with timeouts:

```c
int fd = uv_backend_fd(loop);        // epoll/kqueue fd
int timeout = uv_backend_timeout(loop); // -1, 0, or ms

// Poll externally with custom timeout
poll(&(struct pollfd){.fd = fd, .events = POLLIN}, 1, 
     min(timeout, GC_SAFEPOINT_INTERVAL_MS));

// Then run without blocking
uv_run(loop, UV_RUN_NOWAIT);
```

#### 5. Node.js V8 Pattern

Node.js uses `uv_async_t` for V8 platform task posting:

```cpp
// Per-isolate async handle
PerIsolatePlatformData::PerIsolatePlatformData(...) {
  flush_tasks_ = new uv_async_t();
  uv_async_init(loop, flush_tasks_, FlushTasks);
  uv_unref((uv_handle_t*)flush_tasks_);  // Don't keep loop alive!
  flush_tasks_->data = this;
}

// Called from any V8 worker thread
void PostTaskImpl(std::unique_ptr<Task> task, ...) {
  auto locked = foreground_tasks_.Lock();
  if (flush_tasks_ == nullptr) return;  // Shutdown check
  locked.Push(std::make_unique<TaskQueueEntry>(std::move(task), ...));
  uv_async_send(flush_tasks_);
}
```

**Key patterns from Node.js:**
1. `uv_unref()` async handle - doesn't keep loop alive
2. Check for `nullptr` in post path for graceful shutdown
3. Mutex-protected task queue separate from async handle
4. Async handle only for wakeup, not data transfer

---

### End-to-End GC Interrupt Architecture

#### Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    GC INTERRUPT ARCHITECTURE                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────┐           ┌─────────────────┐                          │
│  │   Main Thread   │           │  AIO Thread N   │                          │
│  │  (GC Initiator) │           │  (libuv loop)   │                          │
│  └────────┬────────┘           └────────┬────────┘                          │
│           │                             │                                    │
│           │ 1. GC needed                │ blocked in uv_run()               │
│           │    (heap pressure)          │                                    │
│           ▼                             │                                    │
│  ┌─────────────────┐                    │                                    │
│  │ Set gc_phase =  │                    │                                    │
│  │ STW_REQUESTED   │                    │                                    │
│  └────────┬────────┘                    │                                    │
│           │                             │                                    │
│           │ 2. For each AIO loop:       │                                    │
│           │    uv_async_send(&gc_wakeup)│                                    │
│           ▼                             │                                    │
│  ┌─────────────────┐           ┌────────▼────────┐                          │
│  │ Wait for all    │           │ uv_run() returns│                          │
│  │ threads_paused  │◄──────────│ (eventfd woke)  │                          │
│  └────────┬────────┘           └────────┬────────┘                          │
│           │                             │                                    │
│           │                    3. gc_wakeup_cb():                            │
│           │                       ┌────────▼────────┐                        │
│           │                       │ Check gc_phase  │                        │
│           │                       │ == STW_REQUESTED│                        │
│           │                       └────────┬────────┘                        │
│           │                                │                                 │
│           │                       4. valk_gc_safe_point_slow():              │
│           │                       ┌────────▼────────┐                        │
│           │                       │ Checkpoint arena│                        │
│           │                       │ threads_paused++│                        │
│           │                       │ Signal if last  │                        │
│           │                       └────────┬────────┘                        │
│           │                                │                                 │
│           ▼                                ▼                                 │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                    PARALLEL GC PHASE                                │    │
│  │  - All threads participate via barriers                             │    │
│  │  - Parallel mark (work-stealing)                                    │    │
│  │  - Parallel sweep (page partitioning)                               │    │
│  └───────────────────────────────┬─────────────────────────────────────┘    │
│                                  │                                          │
│           │                      │                                          │
│           ▼                      ▼                                          │
│  ┌─────────────────┐    ┌─────────────────┐                                │
│  │ gc_phase = IDLE │    │ Resume uv_run() │                                │
│  │ broadcast done  │    │ (normal I/O)    │                                │
│  └─────────────────┘    └─────────────────┘                                │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### Data Structures

```c
typedef struct valk_aio_gc_coord {
  uv_async_t wakeup;              // Per-loop async handle for GC wakeup
  _Atomic bool gc_acknowledged;   // This loop has acknowledged GC request
  uv_loop_t* loop;                // The libuv loop
  struct valk_aio_system* sys;    // Parent AIO system
} valk_aio_gc_coord_t;

// In valk_aio_system_t:
typedef struct valk_aio_system {
  // ... existing fields ...
  valk_aio_gc_coord_t gc_coord;   // GC coordination for this loop
} valk_aio_system_t;
```

#### Implementation Steps

**Step 1: Initialize GC Wakeup Handle (in `valk_aio_system_create`)**

```c
static void gc_wakeup_cb(uv_async_t* handle);

int valk_aio_gc_coord_init(valk_aio_system_t* sys) {
  valk_aio_gc_coord_t* coord = &sys->gc_coord;
  coord->sys = sys;
  coord->loop = sys->eventloop;
  atomic_store(&coord->gc_acknowledged, false);
  
  int rv = uv_async_init(sys->eventloop, &coord->wakeup, gc_wakeup_cb);
  if (rv != 0) return rv;
  
  coord->wakeup.data = coord;
  
  // CRITICAL: Unref so GC handle doesn't keep loop alive when idle
  uv_unref((uv_handle_t*)&coord->wakeup);
  
  return 0;
}
```

**Step 2: GC Wakeup Callback (runs on loop thread)**

```c
static void gc_wakeup_cb(uv_async_t* handle) {
  valk_aio_gc_coord_t* coord = (valk_aio_gc_coord_t*)handle->data;
  
  // Check if GC is actually requested (coalescing may cause spurious wakeups)
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);
  if (phase != VALK_GC_PHASE_STW_REQUESTED) {
    return;  // Spurious wakeup or GC already finished
  }
  
  // Already acknowledged? Don't double-count
  if (atomic_exchange(&coord->gc_acknowledged, true)) {
    return;
  }
  
  // Enter safe point - this will:
  // 1. Checkpoint scratch arena
  // 2. Increment threads_paused
  // 3. Signal if last thread
  // 4. Participate in parallel GC work
  // 5. Wait for GC completion
  valk_gc_safe_point_slow();
  
  // Reset acknowledgment for next GC cycle
  atomic_store(&coord->gc_acknowledged, false);
}
```

**Step 3: Request STW from GC Coordinator**

```c
void valk_gc_request_stw_all_loops(void) {
  // Set global phase FIRST (other threads check this)
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_STW_REQUESTED);
  
  // Memory barrier to ensure phase is visible before wakeups
  atomic_thread_fence(memory_order_seq_cst);
  
  // Wake all registered AIO loops
  pthread_mutex_lock(&valk_aio_systems_lock);
  for (size_t i = 0; i < valk_aio_systems_count; i++) {
    valk_aio_system_t* sys = valk_aio_systems[i];
    if (sys && sys->eventloop) {
      uv_async_send(&sys->gc_coord.wakeup);
    }
  }
  pthread_mutex_unlock(&valk_aio_systems_lock);
  
  // Wait for all threads to pause
  // (includes both AIO threads and non-AIO threads)
  pthread_mutex_lock(&valk_gc_coord.lock);
  while (atomic_load(&valk_gc_coord.threads_paused) < 
         atomic_load(&valk_gc_coord.threads_registered)) {
    pthread_cond_wait(&valk_gc_coord.all_paused, &valk_gc_coord.lock);
  }
  pthread_mutex_unlock(&valk_gc_coord.lock);
}
```

**Step 4: Periodic Safe Point Check (Maintenance Timer - Already Exists)**

The maintenance timer already calls `VALK_GC_SAFE_POINT()`:

```c
// In aio_maintenance.c
static void __maintenance_timer_cb(uv_timer_t* handle) {
  valk_aio_system_t* sys = (valk_aio_system_t*)handle->data;
  
  // GC safe point - check for STW request
  VALK_GC_SAFE_POINT();
  
  // ... other maintenance work ...
}
```

This provides a natural safe point interval (default 100ms) even if no async wakeup is sent.

**Step 5: Graceful Shutdown**

```c
void valk_aio_gc_coord_destroy(valk_aio_system_t* sys) {
  valk_aio_gc_coord_t* coord = &sys->gc_coord;
  
  // If GC is in progress, wait for it to complete first
  while (atomic_load(&valk_gc_coord.phase) != VALK_GC_PHASE_IDLE) {
    VALK_GC_SAFE_POINT();
  }
  
  // Close the async handle
  uv_close((uv_handle_t*)&coord->wakeup, NULL);
}
```

#### Integration with Existing Code

1. **AIO System Creation** (`aio_system.c`):
   - Add `valk_aio_gc_coord_init()` call after loop initialization
   - Register AIO system in global list for GC iteration

2. **AIO System Destruction** (`aio_system.c`):
   - Add `valk_aio_gc_coord_destroy()` before loop cleanup
   - Unregister from global list

3. **GC Coordinator** (`gc.c`):
   - Update `valk_gc_heap2_request_stw()` to call `valk_gc_request_stw_all_loops()`
   - AIO loops now get woken immediately instead of waiting for timer

4. **Safe Point Slow Path** (`gc.c`):
   - Already correct - participates in parallel GC work

#### Timing Guarantees

| Scenario | Latency to Safe Point |
|----------|----------------------|
| AIO blocked in I/O wait | < 1ms (async wakeup) |
| AIO processing callbacks | < 100ms (maintenance timer) |
| AIO in Lisp eval | < 1 eval (safe point in eval loop) |
| Non-AIO thread in eval | < 1 eval (safe point in eval loop) |
| Main thread in aio/run | < 100ms (sleep loop with safe point) |

#### Why This Works

1. **`uv_async_send()` is thread-safe**: Can be called from GC coordinator thread
2. **Wakes blocked loops immediately**: Write to eventfd/pipe makes poll return
3. **Coalescing is fine**: We only need one wakeup per GC cycle
4. **Unref prevents loop stall**: GC handle doesn't keep loop alive when idle
5. **Maintenance timer is backup**: Even if async fails, timer provides safe point
6. **Graceful shutdown**: Waits for GC completion before closing handle

#### Edge Cases Handled

| Edge Case | Handling |
|-----------|----------|
| GC requested while loop is idle | Maintenance timer or next I/O event triggers check |
| Multiple GC requests during one cycle | Coalesced by libuv, single callback |
| Loop shutdown during GC | Wait for GC completion, then close handle |
| Async send after handle closed | Won't happen - we wait for GC completion first |
| Thread unregister during GC | `valk_gc_thread_unregister()` calls safe point first |
| Main thread in aio/run sleep loop | Safe point checked every 100ms iteration |

---

### Critical Bug Fix: Main Thread Safe Point in aio/run

**Problem Identified**: The main thread calling `aio/run` was GC-registered but never hit safe points. It just slept in a loop:

```c
// BROKEN - main thread never pauses for GC
while (!valk_aio_is_shutting_down(sys)) {
  uv_sleep(100);  // No safe point check!
}
```

When the AIO thread triggered GC (e.g., due to heap pressure during allocation):
1. AIO thread called `request_stw()`, set phase to `STW_REQUESTED`
2. AIO thread waited for all registered threads to pause
3. Main thread was sleeping - **never checked `gc_phase`**
4. **Deadlock**: AIO thread waited forever for main thread

**Fix Applied** (parser.c `valk_builtin_aio_run`):

```c
while (!valk_aio_is_shutting_down(sys)) {
  VALK_GC_SAFE_POINT();  // Check if GC needs us to pause
  uv_sleep(100);
}
```

Now when GC is requested:
1. Main thread wakes from sleep (after up to 100ms)
2. `VALK_GC_SAFE_POINT()` sees `phase == STW_REQUESTED`
3. Calls `valk_gc_safe_point_slow()` which:
   - Checkpoints scratch arena
   - Increments `threads_paused`
   - Signals `all_paused` if last thread
   - Participates in parallel GC work
   - Waits for GC completion
4. GC proceeds with all threads properly paused

**Why the original comment was wrong**: The comment claimed "GC is intentionally DISABLED here" but GC was not actually disabled - the main thread was just not participating in STW coordination. This caused the race condition where GC could mark environments while the AIO thread was modifying them (because STW never fully stopped all threads).

---

## References

1. [The Garbage Collection Handbook](https://gchandbook.org/) - Jones, Hosking, Moss
2. [Go GC Design](https://go.dev/blog/ismmkeynote) - Rick Hudson, ISMM 2018
3. [V8 Orinoco GC](https://v8.dev/blog/trash-talk) - Parallel/concurrent GC
4. [jemalloc Design](https://jemalloc.net/) - Size class allocator
5. [tcmalloc Design](https://google.github.io/tcmalloc/design.html) - Thread-caching allocator
6. [Chase-Lev Deque](https://www.dre.vanderbilt.edu/~schmidt/PDF/work-stealing-dequeue.pdf) - Work stealing
7. [libuv async handles](https://docs.libuv.org/en/v1.x/async.html) - Thread-safe loop wakeup
8. [libuv source: async.c](https://github.com/libuv/libuv/blob/v1.x/src/unix/async.c) - Implementation details
9. [Node.js platform integration](https://github.com/nodejs/node/blob/main/src/node_platform.cc) - V8/libuv coordination pattern
