#pragma once

#include <stdbool.h>
#include <stddef.h>
#include "memory.h"

// Forward declarations
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;

// GC malloc heap - malloc-based allocator with mark & sweep collection
typedef struct {
  valk_mem_allocator_e type;  // VALK_ALLOC_GC_HEAP
  size_t allocated_bytes;     // Current memory usage
  size_t gc_threshold;        // Trigger GC when allocated exceeds this
  size_t num_collections;     // Number of GC runs performed
  valk_lval_t* objects;       // Linked list of all allocated objects
  valk_lenv_t* root_env;      // Root environment for marking
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

// Arena-based GC (informational only, for backward compatibility)
size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena);
bool valk_gc_should_collect_arena(valk_mem_arena_t* arena);
