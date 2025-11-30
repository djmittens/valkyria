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

// Forward declare slab allocator
struct valk_slab_t;

// GC heap statistics for telemetry
typedef struct {
  size_t overflow_allocations;      // Allocations received from scratch overflow
  size_t evacuations_from_scratch;  // Values received from scratch evacuation
  size_t evacuation_bytes;          // Bytes received from scratch evacuation
  size_t evacuation_pointer_fixups; // Pointer updates during evacuation
  size_t emergency_collections;     // Emergency GCs triggered at hard limit
  size_t peak_usage;                // Maximum allocated_bytes ever reached
} valk_gc_heap_stats_t;

// GC malloc heap - malloc-based allocator with mark & sweep collection
typedef struct {
  valk_mem_allocator_e type;  // VALK_ALLOC_GC_HEAP
  size_t allocated_bytes;     // Current memory usage
  size_t gc_threshold;        // Trigger GC when allocated exceeds this
  size_t hard_limit;          // Absolute maximum heap size (abort if exceeded)
  size_t num_collections;     // Number of GC runs performed
  bool in_emergency_gc;       // Prevent recursive emergency GC
  valk_gc_header_t* objects;  // Linked list of all allocated object headers
  valk_lenv_t* root_env;      // Root environment for marking
  valk_gc_header_t* free_list;  // Free-list for fast reuse of swept objects
  size_t free_list_size;      // Number of objects in free list
  valk_slab_t* lval_slab;  // Fast slab allocator for valk_lval_t objects
  size_t lval_size;           // Size of valk_lval_t for slab allocation
  valk_gc_heap_stats_t stats; // Telemetry statistics
} valk_gc_malloc_heap_t;

// Initialize GC malloc heap with threshold and hard limit
// If hard_limit is 0, defaults to gc_threshold * 2
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t gc_threshold, size_t hard_limit);

// Set hard limit for GC heap (must be >= current allocated_bytes)
void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, size_t limit);

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

// Print combined memory statistics (scratch arena + GC heap)
void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out);

// Free all GC heap allocations and the heap itself (for clean shutdown)
void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap);

// Explicitly free a single GC heap object (for cleanup when switching allocators)
void valk_gc_free_object(void* heap, void* ptr);

// Arena-based GC (informational only, for backward compatibility)
size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena);
bool valk_gc_should_collect_arena(valk_mem_arena_t* arena);

// ============================================================================
// Forwarding Pointer Helpers (for scratch evacuation)
// ============================================================================

// Set forwarding pointer: mark src as forwarded, point to dst
void valk_lval_set_forward(valk_lval_t* src, valk_lval_t* dst);

// Check if value is a forwarding pointer
bool valk_lval_is_forwarded(valk_lval_t* v);

// Follow forwarding pointer chain to find final destination
valk_lval_t* valk_lval_follow_forward(valk_lval_t* v);

// ============================================================================
// Evacuation Context (for checkpoint-based memory management)
// ============================================================================

// Context for evacuation from scratch arena to GC heap
typedef struct {
  valk_mem_arena_t* scratch;      // Source arena
  valk_gc_malloc_heap_t* heap;    // Destination heap
  valk_lval_t** worklist;         // Stack of values to process children
  size_t worklist_count;          // Current worklist size
  size_t worklist_capacity;       // Allocated capacity
  valk_lval_t** evacuated;        // List of evacuated values (for pointer fixing)
  size_t evacuated_count;         // Number of evacuated values
  size_t evacuated_capacity;      // Allocated capacity for evacuated list
  size_t values_copied;           // Stats for this evacuation
  size_t bytes_copied;            // Stats for this evacuation
  size_t pointers_fixed;          // Stats for this evacuation
} valk_evacuation_ctx_t;

// ============================================================================
// Checkpoint API
// ============================================================================

// Default threshold for triggering checkpoint (75% of scratch capacity)
#define VALK_CHECKPOINT_THRESHOLD_DEFAULT 0.75f

// Check if checkpoint should be triggered based on scratch usage
bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold);

// Perform checkpoint: evacuate reachable values from scratch to heap, then reset
void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap,
                     valk_lenv_t* root_env);

// Add a value to the GC heap's object list (for evacuated values)
void valk_gc_add_to_objects(valk_gc_malloc_heap_t* heap, valk_lval_t* v);
