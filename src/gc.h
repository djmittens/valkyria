#pragma once

#include <stdbool.h>
#include <stddef.h>
#include "memory.h"

// Forward declarations
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;

// GC allocation header - prepended to every GC-managed allocation
// This allows arbitrary-sized allocations while maintaining tracking metadata
typedef struct valk_gc_header_t {
  void* origin_allocator;              // Which heap allocated this
  struct valk_gc_header_t* gc_next;    // Linked list for GC tracking
  size_t size;                         // User-requested allocation size
  // User data follows immediately after this header
} valk_gc_header_t;

// GC malloc heap - malloc-based allocator with mark & sweep collection
typedef struct {
  valk_mem_allocator_e type;  // VALK_ALLOC_GC_HEAP
  size_t allocated_bytes;     // Current memory usage
  size_t gc_threshold;        // Trigger GC when allocated exceeds this
  size_t num_collections;     // Number of GC runs performed
  valk_gc_header_t* objects;  // Linked list of all allocated object headers
  valk_lenv_t* root_env;      // Root environment for marking
  valk_gc_header_t* free_list;  // Free-list for fast reuse of swept objects
  size_t free_list_size;      // Number of objects in free list
} valk_gc_malloc_heap_t;

// Initialize GC malloc heap with threshold
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t gc_threshold);

// Allocate from GC malloc heap (uses malloc, triggers GC if needed)
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, size_t bytes);

// Set root environment for marking
void valk_gc_malloc_set_root(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env);

// Perform mark & sweep collection
size_t valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap);

// Check if GC should run
bool valk_gc_malloc_should_collect(valk_gc_malloc_heap_t* heap);

// Print GC statistics
void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap);

// Free all GC heap allocations and the heap itself (for clean shutdown)
void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap);

// Arena-based GC (informational only, for backward compatibility)
size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena);
bool valk_gc_should_collect_arena(valk_mem_arena_t* arena);
