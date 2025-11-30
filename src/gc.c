#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>

// Forward declarations
static void valk_gc_mark_lval(valk_lval_t* v);
static void valk_gc_mark_env(valk_lenv_t* env);
static void valk_gc_clear_marks_recursive(valk_lval_t* v);
static void valk_gc_scan_stack(valk_gc_malloc_heap_t* heap);

// ============================================================================
// GC Heap - Malloc-based allocator with mark & sweep
// ============================================================================

// Initialize GC heap
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t gc_threshold) {
  valk_gc_malloc_heap_t* heap = malloc(sizeof(valk_gc_malloc_heap_t));
  if (!heap) {
    VALK_ERROR("Failed to allocate GC heap structure");
    return NULL;
  }

  heap->type = VALK_ALLOC_GC_HEAP;
  heap->allocated_bytes = 0;
  heap->gc_threshold = gc_threshold;
  heap->num_collections = 0;
  heap->objects = NULL;
  heap->root_env = NULL;
  heap->free_list = NULL;
  heap->free_list_size = 0;

  // Create fast slab allocator for valk_lval_t objects
  // Fixed large size - simple and fast, no threshold complexity
  extern size_t __valk_lval_size;  // Defined in parser.c
  heap->lval_size = __valk_lval_size;

  // Fixed slab size: 256K objects = ~64MB for 256-byte lval_t+header
  // Large enough for most workloads, avoids exhaustion during heavy copying
  size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
  size_t num_lvals = 256 * 1024;  // 256K objects

  size_t slab_size = valk_slab_size(slab_item_size, num_lvals);
  heap->lval_slab = malloc(slab_size);
  if (heap->lval_slab == NULL) {
    VALK_WARN("Failed to allocate lval slab, will fall back to malloc");
  } else {
    valk_slab_init(heap->lval_slab, slab_item_size, num_lvals);
    VALK_INFO("GC slab allocated: %zu objects, %.1f MB (%zu bytes header + %zu bytes lval per object)",
              num_lvals, slab_size / (1024.0 * 1024.0), sizeof(valk_gc_header_t), heap->lval_size);
  }

  VALK_INFO("GC heap initialized with threshold: %zu bytes (%.1f MB)",
            gc_threshold, gc_threshold / (1024.0 * 1024.0));

  return heap;
}

// Set root environment for GC marking
void valk_gc_malloc_set_root(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env) {
  heap->root_env = root_env;
}

// Check if GC should run
bool valk_gc_malloc_should_collect(valk_gc_malloc_heap_t* heap) {
  return heap->allocated_bytes > heap->gc_threshold;
}

// Allocate from GC heap with header-based tracking
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, size_t bytes) {
  // TODO: Auto-GC disabled - conservative stack scanning doesn't work with ASAN
  // ASAN uses shadow stacks that break pointer scanning. Need explicit root registration.
  #if 0
  if (valk_gc_malloc_should_collect(heap) && heap->root_env != NULL) {
    VALK_INFO("GC triggered before allocation (%zu/%zu bytes)",
              heap->allocated_bytes, heap->gc_threshold);
    valk_gc_malloc_collect(heap);
  }
  #endif

  valk_gc_header_t* header = NULL;
  size_t total_size = sizeof(valk_gc_header_t) + bytes;
  bool from_slab = false;
  bool from_free_list = false;

  // Fastest path: Slab allocator for valk_lval_t objects (most common case)
  if (bytes == heap->lval_size && heap->lval_slab != NULL) {
    header = valk_mem_allocator_alloc((void*)heap->lval_slab, total_size);
    if (header != NULL) {
      from_slab = true;
      VALK_TRACE("GC alloc: %zu bytes from slab at %p", bytes, (void*)(header + 1));
    }
  }

  // Fast path: Pop from free list if exact size match (O(1) stack operation)
  if (header == NULL && heap->free_list != NULL && heap->free_list->size == bytes) {
    header = heap->free_list;
    heap->free_list = header->gc_next;
    heap->free_list_size--;
    from_free_list = true;
    VALK_TRACE("GC alloc: %zu bytes from free list at %p", bytes, (void*)(header + 1));
  }

  // Slow path: malloc if not found in slab or free list
  if (header == NULL) {
    header = malloc(total_size);
    if (header == NULL) {
      VALK_ERROR("GC heap malloc failed for %zu bytes (+ %zu header)",
                 bytes, sizeof(valk_gc_header_t));
      return NULL;
    }
    // Track allocation (header + user data)
    heap->allocated_bytes += total_size;
    VALK_TRACE("GC alloc: %zu bytes via malloc at %p", bytes, (void*)(header + 1));
  }

  // Initialize header
  header->origin_allocator = heap;
  header->gc_next = heap->objects;
  header->size = bytes;

  // Zero out user data only for fresh malloc (slab/free-list objects will be reinitialized by caller)
  if (!from_slab && !from_free_list) {
    void* user_data = (void*)(header + 1);
    memset(user_data, 0, bytes);
  }

  // Add to live objects linked list
  heap->objects = header;

  // Return pointer to user data (NOT header!)
  return (void*)(header + 1);
}

// ============================================================================
// Conservative Stack Scanning - Mark objects referenced from C stack
// ============================================================================

// Helper: Check if a pointer-sized value looks like it points into GC heap
static bool valk_gc_is_heap_pointer(valk_gc_malloc_heap_t* heap, void* ptr) {
  if (ptr == NULL) return false;

  // Conservative scan: check if this pointer matches any object in our heap
  for (valk_gc_header_t* header = heap->objects; header != NULL; header = header->gc_next) {
    void* user_data = (void*)(header + 1);
    // Check if ptr points to this allocation (within user data range)
    if (ptr >= user_data && ptr < (void*)((uint8_t*)user_data + header->size)) {
      return true;
    }
  }
  return false;
}

// Conservative stack scanner - scans C stack for heap pointers
static void valk_gc_scan_stack(valk_gc_malloc_heap_t* heap) {
  // Get current stack pointer
  int stack_var;
  void* stack_current = (void*)&stack_var;

  // Get pthread stack bounds
  pthread_attr_t attr;
  void* pthread_stack_base;
  size_t pthread_stack_size;

  pthread_getattr_np(pthread_self(), &attr);
  pthread_attr_getstack(&attr, &pthread_stack_base, &pthread_stack_size);
  pthread_attr_destroy(&attr);

  void* pthread_stack_end = (void*)((uint8_t*)pthread_stack_base + pthread_stack_size);

  // Validate stack pointer is within pthread bounds
  if (stack_current >= pthread_stack_base && stack_current <= pthread_stack_end) {
    // Normal case - scan from pthread base to current
    void* stack_bottom = pthread_stack_base;
    void* stack_top = stack_current;

    VALK_TRACE("GC: Scanning pthread stack from %p to %p (size: %zu bytes)",
               stack_bottom, stack_top,
               (size_t)((uint8_t*)stack_top - (uint8_t*)stack_bottom));

    // Scan every pointer-sized word
    uintptr_t* ptr = (uintptr_t*)stack_bottom;
    uintptr_t* end = (uintptr_t*)stack_top;

    size_t marked_from_stack = 0;
    for (; ptr < end; ptr++) {
      void* potential_ptr = (void*)(*ptr);
      if (valk_gc_is_heap_pointer(heap, potential_ptr)) {
        valk_lval_t* obj = (valk_lval_t*)potential_ptr;
        if (!(obj->flags & LVAL_FLAG_GC_MARK)) {
          valk_gc_mark_lval(obj);
          marked_from_stack++;
        }
      }
    }
    VALK_TRACE("GC: Marked %zu objects from stack", marked_from_stack);
    return;
  }

  // Fallback: stack pointer not in pthread bounds - might be ASAN shadow stack
  // or custom allocator arena. Scan conservatively around current location.
  VALK_WARN("GC: Stack pointer %p outside pthread range [%p, %p] - using conservative scan",
            stack_current, pthread_stack_base, pthread_stack_end);

  // Scan 2MB below current stack pointer (conservative estimate)
  void* scan_start = (void*)((uintptr_t)stack_current - (2 * 1024 * 1024));
  void* scan_end = stack_current;

  VALK_TRACE("GC: Scanning conservative range from %p to %p", scan_start, scan_end);

  // Don't actually scan in fallback mode - it's too dangerous without proper bounds
  // Instead, disable GC collection when we can't determine stack bounds
  VALK_WARN("GC: Skipping stack scan - cannot determine safe bounds");
}

// ============================================================================
// Mark Phase - Traverse from roots and mark reachable objects
// ============================================================================

static void valk_gc_mark_lval(valk_lval_t* v) {
  if (v == NULL) return;

  // Only mark objects allocated by the GC heap - don't mark scratch/arena objects
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return;

  // Already marked - avoid infinite loops
  if (v->flags & LVAL_FLAG_GC_MARK) return;

  // Mark this value
  v->flags |= LVAL_FLAG_GC_MARK;

  switch (LVAL_TYPE(v)) {
    case LVAL_NUM:
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
    case LVAL_REF:
      // Leaf types - no children
      break;

    case LVAL_FUN:
      // Mark function environment, formals, body
      if (v->fun.env) {
        valk_gc_mark_env(v->fun.env);
      }
      valk_gc_mark_lval(v->fun.formals);
      valk_gc_mark_lval(v->fun.body);
      break;

    case LVAL_CONS:
    case LVAL_QEXPR:
      // Mark cons/qexpr list (both have same structure)
      valk_gc_mark_lval(v->cons.head);
      valk_gc_mark_lval(v->cons.tail);
      break;
    case LVAL_NIL:
      // Nil has no children
      break;

    case LVAL_ENV:
      valk_gc_mark_env(&v->env);
      break;

    case LVAL_UNDEFINED:
    case LVAL_CONT:
      break;
  }
}

static void valk_gc_mark_env(valk_lenv_t* env) {
  if (env == NULL) return;

  // Mark all values in this environment
  for (size_t i = 0; i < env->vals.count; i++) {
    valk_gc_mark_lval(env->vals.items[i]);
  }

  // Mark parent environment (lexical chain)
  valk_gc_mark_env(env->parent);

  // Mark fallback environment (dynamic scoping chain)
  valk_gc_mark_env(env->fallback);
}

// ============================================================================
// Sweep Phase - Free unmarked objects
// ============================================================================

static size_t valk_gc_malloc_sweep(valk_gc_malloc_heap_t* heap) {
  size_t reclaimed = 0;
  size_t freed_count = 0;
  valk_gc_header_t** header_ptr = &heap->objects;

  while (*header_ptr != NULL) {
    valk_gc_header_t* header = *header_ptr;
    void* user_data = (void*)(header + 1);

    // Safety check: verify allocator pointer
    if (header->origin_allocator != heap) {
      VALK_ERROR("GC sweep found header with wrong allocator!");
      VALK_ERROR("  Expected GC heap: %p", heap);
      VALK_ERROR("  Got allocator: %p", header->origin_allocator);
      VALK_ERROR("  Header pointer: %p", header);
      VALK_ERROR("  User data: %p", user_data);
      VALK_ERROR("  Header size: %zu", header->size);

      VALK_ERROR("BREAKING TRAVERSAL to prevent infinite loop");
      // Break the list here to prevent following corrupted pointers
      *header_ptr = NULL;
      break;
    }

    // Cast user data to valk_lval_t and check mark bit
    valk_lval_t* obj = (valk_lval_t*)user_data;

    if (obj->flags & LVAL_FLAG_GC_MARK) {
      // Object is live - keep it
      header_ptr = &header->gc_next;
    } else {
      // Object is garbage - free based on allocation source (slab vs malloc)
      *header_ptr = header->gc_next;  // Remove from live objects list

      size_t total_size = sizeof(valk_gc_header_t) + header->size;
      reclaimed += total_size;
      freed_count++;

      // Check if object is from slab via address range check
      bool from_slab = false;
      if (heap->lval_slab != NULL) {
        uintptr_t slab_start = (uintptr_t)heap->lval_slab;
        size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
        size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
        uintptr_t slab_end = slab_start + slab_total_size;
        uintptr_t obj_addr = (uintptr_t)header;
        from_slab = (obj_addr >= slab_start && obj_addr < slab_end);
      }

      if (from_slab) {
        // Return to slab allocator
        valk_mem_allocator_free((void*)heap->lval_slab, header);
        VALK_TRACE("GC sweep: returned %p to slab", user_data);
      } else {
        // Add to free list for fast reuse (malloc'd objects)
        header->gc_next = heap->free_list;
        heap->free_list = header;
        heap->free_list_size++;
        VALK_TRACE("GC sweep: added %p to free list", user_data);
      }
    }
  }

  heap->allocated_bytes -= reclaimed;

  VALK_INFO("GC sweep: freed %zu objects, reclaimed %zu bytes",
            freed_count, reclaimed);

  return reclaimed;
}

// ============================================================================
// Clear marks for next collection
// ============================================================================

static void valk_gc_clear_marks_recursive(valk_lval_t* v) {
  if (v == NULL) return;

  // Only clear marks on GC heap objects - don't touch scratch/arena objects
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return;

  // Already cleared
  if (!(v->flags & LVAL_FLAG_GC_MARK)) return;

  // Clear mark
  v->flags &= ~LVAL_FLAG_GC_MARK;

  // Clear children - note that children might have been freed if unmarked,
  // so the recursive calls will check marks before accessing
  switch (LVAL_TYPE(v)) {
    case LVAL_FUN:
      if (v->fun.env) {
        for (size_t i = 0; i < v->fun.env->vals.count; i++) {
          valk_gc_clear_marks_recursive(v->fun.env->vals.items[i]);
        }
      }
      valk_gc_clear_marks_recursive(v->fun.formals);
      valk_gc_clear_marks_recursive(v->fun.body);
      break;

    case LVAL_CONS:
    case LVAL_QEXPR:
      valk_gc_clear_marks_recursive(v->cons.head);
      valk_gc_clear_marks_recursive(v->cons.tail);
      break;
    case LVAL_NIL:
      // Nil has no children
      break;

    case LVAL_ENV:
      for (size_t i = 0; i < v->env.vals.count; i++) {
        valk_gc_clear_marks_recursive(v->env.vals.items[i]);
      }
      break;

    default:
      break;
  }
}

// ============================================================================
// Main GC Collection
// ============================================================================

void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap) {
  if (heap == NULL) return;

  // Count live objects by traversing headers
  size_t object_count = 0;
  size_t traversal_limit = 1000000;  // Safety limit
  for (valk_gc_header_t* header = heap->objects;
       header != NULL && object_count < traversal_limit;
       header = header->gc_next) {
    void* user_data = (void*)(header + 1);
    valk_lval_t* obj = (valk_lval_t*)user_data;

    // Skip forwarded values (they're scratch-allocated, not GC heap)
    if (!(obj->flags & LVAL_FLAG_FORWARDED)) {
      object_count++;
    }
  }

  fprintf(stderr, "\n=== GC Heap Statistics ===\n");
  fprintf(stderr, "Allocated bytes: %zu / %zu (%.1f%% full)\n",
          heap->allocated_bytes,
          heap->gc_threshold,
          100.0 * heap->allocated_bytes / heap->gc_threshold);
  fprintf(stderr, "Live objects: %zu\n", object_count);
  fprintf(stderr, "Collections: %zu\n", heap->num_collections);
  fprintf(stderr, "Avg allocation per object: %.1f bytes\n",
          object_count > 0 ? (double)heap->allocated_bytes / object_count : 0.0);
  fprintf(stderr, "=========================\n\n");
}

size_t valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap) {
  if (heap->root_env == NULL) {
    VALK_WARN("GC collect called with no root environment");
    return 0;
  }

  size_t before = heap->allocated_bytes;

  VALK_INFO("GC: Starting collection #%zu (allocated: %zu/%zu bytes, %.1f%% full)",
            heap->num_collections + 1,
            before,
            heap->gc_threshold,
            100.0 * before / heap->gc_threshold);

  // Phase 1: Mark reachable objects from root environment
  // GC only runs at safe points (between expressions) where there are no
  // temporary stack objects - everything live is in the environment!
  valk_gc_mark_env(heap->root_env);

  // Phase 2: Sweep unreachable objects
  size_t reclaimed = valk_gc_malloc_sweep(heap);

  // Phase 3: Clear marks for next collection
  // Walk the object list (which now only contains live objects after sweep)
  for (valk_gc_header_t* header = heap->objects; header != NULL; header = header->gc_next) {
    void* user_data = (void*)(header + 1);
    valk_lval_t* obj = (valk_lval_t*)user_data;
    obj->flags &= ~LVAL_FLAG_GC_MARK;
  }

  size_t after = heap->allocated_bytes;
  heap->num_collections++;

  VALK_INFO("GC: Complete - reclaimed %zu bytes (before: %zu, after: %zu, %.1f%% freed)",
            reclaimed, before, after,
            100.0 * reclaimed / before);

  return reclaimed;
}

// ============================================================================
// GC Heap Object Management
// ============================================================================

// Explicitly free a single GC heap object
// Used when explicitly freeing an object (e.g., when switching allocators)
void valk_gc_free_object(void* heap_ptr, void* user_ptr) {
  if (user_ptr == NULL) return;

  valk_gc_malloc_heap_t* heap = (valk_gc_malloc_heap_t*)heap_ptr;

  // Get header (it's right before the user data)
  valk_gc_header_t* header = ((valk_gc_header_t*)user_ptr) - 1;

  // Remove from objects list
  valk_gc_header_t** current_ptr = &heap->objects;
  while (*current_ptr != NULL) {
    if (*current_ptr == header) {
      *current_ptr = header->gc_next;
      break;
    }
    current_ptr = &(*current_ptr)->gc_next;
  }

  // Determine if from slab or malloc and free accordingly
  bool from_slab = false;
  if (heap->lval_slab != NULL) {
    uintptr_t slab_start = (uintptr_t)heap->lval_slab;
    size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
    size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
    uintptr_t slab_end = slab_start + slab_total_size;
    uintptr_t obj_addr = (uintptr_t)header;
    from_slab = (obj_addr >= slab_start && obj_addr < slab_end);
  }

  size_t total_size = sizeof(valk_gc_header_t) + header->size;

  if (from_slab) {
    // Return to slab allocator
    valk_mem_allocator_free((void*)heap->lval_slab, header);
  } else {
    // Free malloc'd memory
    heap->allocated_bytes -= total_size;
    free(header);
  }
}

// ============================================================================
// GC Heap Cleanup - Free all allocations for clean shutdown
// ============================================================================

void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap) {
  if (heap == NULL) return;

  VALK_INFO("GC: Destroying heap, freeing all %zu remaining objects",
            heap->allocated_bytes);

  // Free all objects in the linked list
  valk_gc_header_t* current = heap->objects;
  size_t freed_count = 0;
  size_t freed_bytes = 0;

  while (current != NULL) {
    valk_gc_header_t* next = current->gc_next;

    // Check if object is from slab via address range check
    bool from_slab = false;
    if (heap->lval_slab != NULL) {
      uintptr_t slab_start = (uintptr_t)heap->lval_slab;
      size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
      size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
      uintptr_t slab_end = slab_start + slab_total_size;
      uintptr_t obj_addr = (uintptr_t)current;
      from_slab = (obj_addr >= slab_start && obj_addr < slab_end);
    }

    if (!from_slab) {
      // Free malloc'd objects (slab objects freed with slab itself)
      size_t total_size = sizeof(valk_gc_header_t) + current->size;
      freed_bytes += total_size;
      freed_count++;
      free(current);
    }
    current = next;
  }

  VALK_INFO("GC: Freed %zu objects (%zu bytes)", freed_count, freed_bytes);

  // Also free the free list (again, skip slab objects)
  current = heap->free_list;
  while (current != NULL) {
    valk_gc_header_t* next = current->gc_next;
    bool from_slab = false;
    if (heap->lval_slab != NULL) {
      uintptr_t slab_start = (uintptr_t)heap->lval_slab;
      size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
      size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
      uintptr_t slab_end = slab_start + slab_total_size;
      uintptr_t obj_addr = (uintptr_t)current;
      from_slab = (obj_addr >= slab_start && obj_addr < slab_end);
    }
    if (!from_slab) {
      free(current);
    }
    current = next;
  }

  // Free the slab allocator directly (don't use valk_slab_free which goes through valk_mem_free)
  if (heap->lval_slab != NULL) {
    free(heap->lval_slab);
  }

  // Free the heap structure itself
  free(heap);
}

// ============================================================================
// Arena-based GC (backward compatibility, informational only)
// ============================================================================

bool valk_gc_should_collect_arena(valk_mem_arena_t* arena) {
  return (arena->offset > (arena->capacity * 9 / 10));
}

size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena) {
  if (root_env == NULL) {
    return 0;
  }

  // Mark from roots
  valk_gc_mark_env(root_env);

  // Count dead objects (can't actually free from arena)
  size_t dead_count = 0;
  size_t live_count = 0;
  uint8_t* ptr = arena->heap;
  uint8_t* end = arena->heap + arena->offset;

  while (ptr < end) {
    valk_lval_t* v = (valk_lval_t*)ptr;
    if ((v->flags & LVAL_TYPE_MASK) <= LVAL_ENV) {
      if (v->flags & LVAL_FLAG_GC_MARK) {
        live_count++;
      } else {
        dead_count++;
      }
    }
    ptr += sizeof(valk_lval_t);
  }

  // Clear marks
  for (size_t i = 0; i < root_env->vals.count; i++) {
    valk_gc_clear_marks_recursive(root_env->vals.items[i]);
  }

  return dead_count * sizeof(valk_lval_t);
}
