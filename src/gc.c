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

// ============================================================================
// Forwarding Pointer Helpers (for scratch evacuation)
// ============================================================================

// Set forwarding pointer: mark src as forwarded, point to dst
void valk_lval_set_forward(valk_lval_t* src, valk_lval_t* dst) {
  // Preserve allocation bits but set type to LVAL_FORWARD
  src->flags = LVAL_FORWARD | (src->flags & ~LVAL_TYPE_MASK);
  src->forward = dst;
}

// Check if value is a forwarding pointer
bool valk_lval_is_forwarded(valk_lval_t* v) {
  return v != NULL && LVAL_TYPE(v) == LVAL_FORWARD;
}

// Follow forwarding pointer chain to find final destination
valk_lval_t* valk_lval_follow_forward(valk_lval_t* v) {
  while (v != NULL && LVAL_TYPE(v) == LVAL_FORWARD) {
    v = v->forward;
  }
  return v;
}

// ============================================================================
// GC Heap - Malloc-based allocator with mark & sweep
// ============================================================================

// Initialize GC heap
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t gc_threshold, size_t hard_limit) {
  valk_gc_malloc_heap_t* heap = malloc(sizeof(valk_gc_malloc_heap_t));
  if (!heap) {
    VALK_ERROR("Failed to allocate GC heap structure");
    return NULL;
  }

  heap->type = VALK_ALLOC_GC_HEAP;
  heap->allocated_bytes = 0;
  heap->gc_threshold = gc_threshold;
  heap->hard_limit = hard_limit > 0 ? hard_limit : gc_threshold * 2;
  heap->num_collections = 0;
  heap->in_emergency_gc = false;
  heap->objects = NULL;
  heap->root_env = NULL;
  heap->free_list = NULL;
  heap->free_list_size = 0;

  // Initialize statistics to zero
  heap->stats.overflow_allocations = 0;
  heap->stats.evacuations_from_scratch = 0;
  heap->stats.evacuation_bytes = 0;
  heap->stats.evacuation_pointer_fixups = 0;
  heap->stats.emergency_collections = 0;
  heap->stats.peak_usage = 0;

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

  VALK_INFO("GC heap: threshold=%zu (%.1f MB), hard_limit=%zu (%.1f MB)",
            gc_threshold, gc_threshold / (1024.0 * 1024.0),
            heap->hard_limit, heap->hard_limit / (1024.0 * 1024.0));

  return heap;
}

// Set hard limit for GC heap
void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, size_t limit) {
  if (limit < heap->allocated_bytes) {
    VALK_WARN("Cannot set hard limit below current usage (%zu < %zu)",
              limit, heap->allocated_bytes);
    return;
  }
  heap->hard_limit = limit;
  VALK_INFO("GC heap hard limit set to %zu bytes (%.1f MB)",
            limit, limit / (1024.0 * 1024.0));
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
  size_t total_size = sizeof(valk_gc_header_t) + bytes;

  // Check hard limit BEFORE allocation - trigger emergency GC if approaching
  if (heap->allocated_bytes + total_size > heap->hard_limit) {
    // Try emergency GC if not already in one
    if (!heap->in_emergency_gc && heap->root_env != NULL) {
      heap->in_emergency_gc = true;
      VALK_WARN("Heap approaching hard limit (%zu/%zu bytes, %.1f%%), "
                "triggering emergency GC",
                heap->allocated_bytes, heap->hard_limit,
                100.0 * heap->allocated_bytes / heap->hard_limit);

      size_t before = heap->allocated_bytes;
      valk_gc_malloc_collect(heap);
      size_t reclaimed = before - heap->allocated_bytes;

      heap->stats.emergency_collections++;
      heap->in_emergency_gc = false;

      VALK_INFO("Emergency GC reclaimed %zu bytes (%.1f%%)",
                reclaimed, before > 0 ? 100.0 * reclaimed / before : 0.0);
    }

    // Re-check after emergency GC
    if (heap->allocated_bytes + total_size > heap->hard_limit) {
      // Still can't allocate - fatal error
      VALK_ERROR("=== FATAL: HEAP EXHAUSTED ===");
      VALK_ERROR("Requested: %zu bytes (+ %zu header = %zu total)",
                 bytes, sizeof(valk_gc_header_t), total_size);
      VALK_ERROR("Current:   %zu bytes", heap->allocated_bytes);
      VALK_ERROR("Hard limit: %zu bytes", heap->hard_limit);
      VALK_ERROR("Shortfall: %zu bytes",
                 (heap->allocated_bytes + total_size) - heap->hard_limit);

      // Dump full diagnostics
      valk_gc_malloc_print_stats(heap);

      VALK_ERROR("Consider increasing VALK_HEAP_HARD_LIMIT environment variable");
      VALK_ERROR("Current: VALK_HEAP_HARD_LIMIT=%zu", heap->hard_limit);

      abort();
    }
  }

  valk_gc_header_t* header = NULL;
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

  // Track peak usage
  if (heap->allocated_bytes > heap->stats.peak_usage) {
    heap->stats.peak_usage = heap->allocated_bytes;
  }

  // Return pointer to user data (NOT header!)
  return (void*)(header + 1);
}

// ============================================================================
// Conservative Stack Scanning - Mark objects referenced from C stack
// ============================================================================

// Helper: Check if a pointer-sized value looks like it points into GC heap
__attribute__((unused))
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
    case LVAL_FORWARD:
      // Forwarding pointers should not exist during GC marking
      // (they only exist transiently during evacuation)
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
        // Return to slab allocator - don't count towards reclaimed bytes
        // since slab allocations aren't tracked in allocated_bytes
        valk_mem_allocator_free((void*)heap->lval_slab, header);
        VALK_TRACE("GC sweep: returned %p to slab", user_data);
      } else {
        // Add to free list for fast reuse (malloc'd objects)
        // Only malloc'd objects count towards reclaimed bytes since
        // slab allocations don't add to allocated_bytes
        reclaimed += total_size;
        header->gc_next = heap->free_list;
        heap->free_list = header;
        heap->free_list_size++;
        VALK_TRACE("GC sweep: added %p to free list", user_data);
      }
    }
  }

  // Only subtract reclaimed bytes (from malloc'd objects) from allocated_bytes
  if (reclaimed <= heap->allocated_bytes) {
    heap->allocated_bytes -= reclaimed;
  } else {
    // Safety: prevent underflow
    VALK_WARN("GC sweep: reclaimed (%zu) > allocated_bytes (%zu), resetting to 0",
              reclaimed, heap->allocated_bytes);
    heap->allocated_bytes = 0;
  }

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
    object_count++;
  }

  fprintf(stderr, "\n=== GC Heap Statistics ===\n");
  fprintf(stderr, "Allocated bytes:  %zu / %zu (%.1f%% of threshold)\n",
          heap->allocated_bytes,
          heap->gc_threshold,
          100.0 * heap->allocated_bytes / heap->gc_threshold);
  fprintf(stderr, "Hard limit:       %zu bytes (%.1f%% used)\n",
          heap->hard_limit,
          100.0 * heap->allocated_bytes / heap->hard_limit);
  fprintf(stderr, "Peak usage:       %zu bytes\n", heap->stats.peak_usage);
  fprintf(stderr, "Live objects:     %zu\n", object_count);
  fprintf(stderr, "Collections:      %zu\n", heap->num_collections);
  fprintf(stderr, "Emergency GCs:    %zu\n", heap->stats.emergency_collections);
  fprintf(stderr, "Avg allocation:   %.1f bytes/object\n",
          object_count > 0 ? (double)heap->allocated_bytes / object_count : 0.0);

  // Evacuation stats (from scratch arena)
  if (heap->stats.evacuations_from_scratch > 0) {
    fprintf(stderr, "--- Evacuation Stats ---\n");
    fprintf(stderr, "Values evacuated: %zu\n", heap->stats.evacuations_from_scratch);
    fprintf(stderr, "Bytes evacuated:  %zu\n", heap->stats.evacuation_bytes);
    fprintf(stderr, "Pointers fixed:   %zu\n", heap->stats.evacuation_pointer_fixups);
  }

  // Overflow stats
  if (heap->stats.overflow_allocations > 0) {
    fprintf(stderr, "--- Overflow Stats ---\n");
    fprintf(stderr, "⚠️  Overflow allocs: %zu\n", heap->stats.overflow_allocations);
  }

  fprintf(stderr, "=========================\n\n");
}

// Print a line with box drawing, auto-padded to width
static void print_boxed_line(FILE* out, const char* content) {
  int len = (int)strlen(content);
  int padding = 64 - len;
  if (padding < 0) padding = 0;
  fprintf(out, "║ %s%*s ║\n", content, padding, "");
}

// Print combined memory statistics (scratch arena + GC heap)
void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out) {
  if (out == NULL) out = stderr;
  char buf[256];

  fprintf(out, "\n╔══════════════════════════════════════════════════════════════════╗\n");
  print_boxed_line(out, "                   MEMORY STATISTICS");
  fprintf(out, "╠══════════════════════════════════════════════════════════════════╣\n");

  if (scratch != NULL) {
    print_boxed_line(out, "SCRATCH ARENA");
    snprintf(buf, sizeof(buf), "  Current usage:     %10zu / %10zu bytes (%5.1f%%)",
            scratch->offset, scratch->capacity,
            100.0 * scratch->offset / scratch->capacity);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  High water mark:   %10zu bytes (%5.1f%%)",
            scratch->stats.high_water_mark,
            100.0 * scratch->stats.high_water_mark / scratch->capacity);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  Total allocations: %10zu", scratch->stats.total_allocations);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  Resets:            %10zu", scratch->stats.num_resets);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  Checkpoints:       %10zu", scratch->stats.num_checkpoints);
    print_boxed_line(out, buf);

    if (scratch->stats.num_checkpoints > 0) {
      snprintf(buf, sizeof(buf), "  Avg values/chkpt:  %10.1f",
              (double)scratch->stats.values_evacuated / scratch->stats.num_checkpoints);
      print_boxed_line(out, buf);
    }

    if (scratch->stats.overflow_fallbacks > 0) {
      snprintf(buf, sizeof(buf), "  [!] Overflow fallbacks: %zu (%zu bytes)",
              scratch->stats.overflow_fallbacks, scratch->stats.overflow_bytes);
      print_boxed_line(out, buf);
    }
    fprintf(out, "╠══════════════════════════════════════════════════════════════════╣\n");
  }

  if (heap != NULL) {
    // Count live objects
    size_t object_count = 0;
    for (valk_gc_header_t* h = heap->objects; h != NULL && object_count < 1000000; h = h->gc_next) {
      object_count++;
    }

    print_boxed_line(out, "GC HEAP");
    snprintf(buf, sizeof(buf), "  Allocated:         %10zu / %10zu bytes (%5.1f%%)",
            heap->allocated_bytes, heap->gc_threshold,
            100.0 * heap->allocated_bytes / heap->gc_threshold);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  Hard limit:        %10zu bytes (%5.1f%% used)",
            heap->hard_limit,
            100.0 * heap->allocated_bytes / heap->hard_limit);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  Peak usage:        %10zu bytes", heap->stats.peak_usage);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  Live objects:      %10zu", object_count);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "  Collections:       %10zu", heap->num_collections);
    print_boxed_line(out, buf);

    if (heap->stats.emergency_collections > 0) {
      snprintf(buf, sizeof(buf), "  [!] Emergency GCs: %zu", heap->stats.emergency_collections);
      print_boxed_line(out, buf);
    }

    if (heap->stats.evacuations_from_scratch > 0) {
      snprintf(buf, sizeof(buf), "  Evacuations recv'd:%10zu (%zu bytes)",
              heap->stats.evacuations_from_scratch, heap->stats.evacuation_bytes);
      print_boxed_line(out, buf);
    }
  }

  fprintf(out, "╚══════════════════════════════════════════════════════════════════╝\n\n");
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
  uint8_t* ptr = arena->heap;
  uint8_t* end = arena->heap + arena->offset;

  while (ptr < end) {
    valk_lval_t* v = (valk_lval_t*)ptr;
    if ((v->flags & LVAL_TYPE_MASK) <= LVAL_ENV) {
      if (!(v->flags & LVAL_FLAG_GC_MARK)) {
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

// ============================================================================
// Checkpoint-based Evacuation (Phase 3)
// ============================================================================

// Initial worklist capacity
#define EVAC_WORKLIST_INITIAL_CAPACITY 256

// Initialize evacuation context lists
static void evac_ctx_init(valk_evacuation_ctx_t* ctx) {
  ctx->worklist = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->worklist_count = 0;
  ctx->worklist_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;

  ctx->evacuated = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;
}

// Free evacuation context lists
static void evac_ctx_free(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist) {
    free(ctx->worklist);
    ctx->worklist = NULL;
  }
  ctx->worklist_count = 0;
  ctx->worklist_capacity = 0;

  if (ctx->evacuated) {
    free(ctx->evacuated);
    ctx->evacuated = NULL;
  }
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = 0;
}

// Add value to evacuated list (for pointer fixing phase)
static void evac_add_evacuated(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  // Grow if at capacity
  if (ctx->evacuated_count >= ctx->evacuated_capacity) {
    size_t new_cap = ctx->evacuated_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->evacuated, new_cap * sizeof(valk_lval_t*));
    if (new_list == NULL) {
      VALK_ERROR("Failed to grow evacuated list");
      return;
    }
    ctx->evacuated = new_list;
    ctx->evacuated_capacity = new_cap;
  }

  ctx->evacuated[ctx->evacuated_count++] = v;
}

// Push value to worklist
static void evac_worklist_push(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  // Grow if at capacity
  if (ctx->worklist_count >= ctx->worklist_capacity) {
    size_t new_cap = ctx->worklist_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->worklist, new_cap * sizeof(valk_lval_t*));
    if (new_list == NULL) {
      VALK_ERROR("Failed to grow evacuation worklist");
      return;
    }
    ctx->worklist = new_list;
    ctx->worklist_capacity = new_cap;
  }

  ctx->worklist[ctx->worklist_count++] = v;
}

// Pop value from worklist
static valk_lval_t* evac_worklist_pop(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist_count == 0) return NULL;
  return ctx->worklist[--ctx->worklist_count];
}

// Add an already-allocated value to GC heap's object tracking list
void valk_gc_add_to_objects(valk_gc_malloc_heap_t* heap, valk_lval_t* v) {
  // Get the header (it's right before the user data)
  valk_gc_header_t* header = ((valk_gc_header_t*)v) - 1;

  // Add to live objects linked list
  header->gc_next = heap->objects;
  heap->objects = header;
}

// Check if checkpoint should be triggered
bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold) {
  if (scratch == NULL) return false;
  return (float)scratch->offset / scratch->capacity > threshold;
}

// Forward declarations for evacuation helpers
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);

// ============================================================================
// Phase 1: Copy Values from Scratch to Heap
// ============================================================================

// Evacuate a single value from scratch to heap
// Returns the new location (or original if not in scratch or already forwarded)
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return NULL;

  // Already forwarded? Return destination
  if (LVAL_TYPE(v) == LVAL_FORWARD) {
    return v->forward;
  }

  // Not in scratch? Return as-is (already in heap or global)
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) {
    return v;
  }

  // Allocate new value in heap
  valk_lval_t* new_val = NULL;
  VALK_WITH_ALLOC((void*)ctx->heap) {
    new_val = valk_mem_alloc(sizeof(valk_lval_t));
  }

  if (new_val == NULL) {
    VALK_ERROR("Failed to allocate value during evacuation");
    return v;
  }

  // Copy the value data
  memcpy(new_val, v, sizeof(valk_lval_t));

  // Update allocation flags: clear scratch, set heap
  new_val->flags = (new_val->flags & ~LVAL_ALLOC_MASK) | LVAL_ALLOC_HEAP;
  new_val->origin_allocator = ctx->heap;

  // Copy strings for string types (they're also in scratch arena)
  switch (LVAL_TYPE(new_val)) {
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      if (new_val->str != NULL && valk_ptr_in_arena(ctx->scratch, new_val->str)) {
        size_t len = strlen(v->str) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->str = valk_mem_alloc(len);
        }
        if (new_val->str) {
          memcpy(new_val->str, v->str, len);
          ctx->bytes_copied += len;
        }
      }
      break;

    case LVAL_FUN:
      // Copy function name if it's a lambda (not builtin) and in scratch
      if (new_val->fun.name != NULL && new_val->fun.builtin == NULL &&
          valk_ptr_in_arena(ctx->scratch, new_val->fun.name)) {
        size_t len = strlen(v->fun.name) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->fun.name = valk_mem_alloc(len);
        }
        if (new_val->fun.name) {
          memcpy(new_val->fun.name, v->fun.name, len);
          ctx->bytes_copied += len;
        }
      }
      break;

    default:
      break;
  }

  // Set forwarding pointer in old location
  valk_lval_set_forward(v, new_val);

  // Add to evacuated list for pointer fixing phase
  evac_add_evacuated(ctx, new_val);

  // Update stats
  ctx->values_copied++;
  ctx->bytes_copied += sizeof(valk_lval_t);

  return new_val;
}

// Evacuate children of a value (push to worklist for processing)
static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      // Evacuate and queue head (only if freshly evacuated, not already processed)
      if (v->cons.head != NULL) {
        valk_lval_t* old_head = v->cons.head;
        valk_lval_t* new_head = valk_evacuate_value(ctx, old_head);
        if (new_head != old_head) {
          v->cons.head = new_head;
          // Only push if pointer changed (freshly evacuated from scratch)
          if (new_head != NULL) {
            evac_worklist_push(ctx, new_head);
          }
        }
      }
      // Evacuate and queue tail (only if freshly evacuated, not already processed)
      if (v->cons.tail != NULL) {
        valk_lval_t* old_tail = v->cons.tail;
        valk_lval_t* new_tail = valk_evacuate_value(ctx, old_tail);
        if (new_tail != old_tail) {
          v->cons.tail = new_tail;
          // Only push if pointer changed (freshly evacuated from scratch)
          if (new_tail != NULL) {
            evac_worklist_push(ctx, new_tail);
          }
        }
      }
      break;

    case LVAL_FUN:
      if (v->fun.builtin == NULL) {
        // Evacuate formals (only if freshly evacuated)
        if (v->fun.formals != NULL) {
          valk_lval_t* old_formals = v->fun.formals;
          valk_lval_t* new_formals = valk_evacuate_value(ctx, old_formals);
          if (new_formals != old_formals) {
            v->fun.formals = new_formals;
            if (new_formals != NULL) {
              evac_worklist_push(ctx, new_formals);
            }
          }
        }
        // Evacuate body (only if freshly evacuated)
        if (v->fun.body != NULL) {
          valk_lval_t* old_body = v->fun.body;
          valk_lval_t* new_body = valk_evacuate_value(ctx, old_body);
          if (new_body != old_body) {
            v->fun.body = new_body;
            if (new_body != NULL) {
              evac_worklist_push(ctx, new_body);
            }
          }
        }
        // Evacuate closure environment
        if (v->fun.env != NULL) {
          valk_evacuate_env(ctx, v->fun.env);
        }
      }
      break;

    case LVAL_ENV:
      valk_evacuate_env(ctx, &v->env);
      break;

    default:
      // Leaf types (NUM, SYM, STR, ERR, REF, NIL) have no children
      break;
  }
}

// Evacuate an environment's arrays and values
static void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == NULL) return;

  // Evacuate symbol strings array if in scratch
  if (env->symbols.items != NULL && valk_ptr_in_arena(ctx->scratch, env->symbols.items)) {
    size_t array_size = env->symbols.capacity * sizeof(char*);
    char** new_items = NULL;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_items = valk_mem_alloc(array_size);
    }
    if (new_items) {
      memcpy(new_items, env->symbols.items, env->symbols.count * sizeof(char*));
      env->symbols.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  // Evacuate individual symbol strings if in scratch
  for (size_t i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items[i] != NULL &&
        valk_ptr_in_arena(ctx->scratch, env->symbols.items[i])) {
      size_t len = strlen(env->symbols.items[i]) + 1;
      char* new_str = NULL;
      VALK_WITH_ALLOC((void*)ctx->heap) {
        new_str = valk_mem_alloc(len);
      }
      if (new_str) {
        memcpy(new_str, env->symbols.items[i], len);
        env->symbols.items[i] = new_str;
        ctx->bytes_copied += len;
      }
    }
  }

  // Evacuate values array if in scratch
  if (env->vals.items != NULL && valk_ptr_in_arena(ctx->scratch, env->vals.items)) {
    size_t array_size = env->vals.capacity * sizeof(valk_lval_t*);
    valk_lval_t** new_items = NULL;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_items = valk_mem_alloc(array_size);
    }
    if (new_items) {
      memcpy(new_items, env->vals.items, env->vals.count * sizeof(valk_lval_t*));
      env->vals.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  // Evacuate each value in the environment (only push if freshly evacuated)
  for (size_t i = 0; i < env->vals.count; i++) {
    valk_lval_t* val = env->vals.items[i];
    if (val != NULL) {
      valk_lval_t* new_val = valk_evacuate_value(ctx, val);
      if (new_val != val) {
        env->vals.items[i] = new_val;
        // Only push to worklist if freshly evacuated (pointer changed)
        if (new_val != NULL) {
          evac_worklist_push(ctx, new_val);
        }
      }
    }
  }

  // Recursively evacuate parent and fallback environments
  valk_evacuate_env(ctx, env->parent);
  valk_evacuate_env(ctx, env->fallback);
}

// ============================================================================
// Phase 2: Fix Pointers to Use New Locations
// ============================================================================

// Helper: Check if pointer is in scratch and handle accordingly
// Returns true if pointer was in scratch (and should be handled), false otherwise
static inline bool fix_scratch_pointer(valk_evacuation_ctx_t* ctx, valk_lval_t** ptr) {
  valk_lval_t* val = *ptr;
  if (val == NULL) return false;

  // If in scratch and forwarded, update to new location
  if (valk_lval_is_forwarded(val)) {
    *ptr = valk_lval_follow_forward(val);
    ctx->pointers_fixed++;
    return true;
  }

  // If in scratch but NOT forwarded, it's unreachable - null it out
  if (valk_ptr_in_arena(ctx->scratch, val)) {
    *ptr = NULL;
    return true;
  }

  return false;
}

// Fix pointers in a value to follow forwarding pointers
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  // Skip if still in scratch (shouldn't happen after proper evacuation)
  if (LVAL_ALLOC(v) == LVAL_ALLOC_SCRATCH) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      fix_scratch_pointer(ctx, &v->cons.head);
      fix_scratch_pointer(ctx, &v->cons.tail);
      break;

    case LVAL_FUN:
      if (v->fun.builtin == NULL) {
        fix_scratch_pointer(ctx, &v->fun.formals);
        fix_scratch_pointer(ctx, &v->fun.body);
        if (v->fun.env != NULL) {
          valk_fix_env_pointers(ctx, v->fun.env);
        }
      }
      break;

    case LVAL_ENV:
      valk_fix_env_pointers(ctx, &v->env);
      break;

    default:
      // Leaf types have no pointer children
      break;
  }
}

// Fix pointers in an environment
static void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == NULL) return;

  // Skip if vals.items array is in scratch (not evacuated, would be garbage after reset)
  if (env->vals.items != NULL && valk_ptr_in_arena(ctx->scratch, env->vals.items)) {
    return;
  }

  // Fix all value pointers using the helper
  for (size_t i = 0; i < env->vals.count; i++) {
    fix_scratch_pointer(ctx, &env->vals.items[i]);
  }

  // Recursively fix parent and fallback environments
  valk_fix_env_pointers(ctx, env->parent);
  valk_fix_env_pointers(ctx, env->fallback);
}

// ============================================================================
// Checkpoint: Evacuate and Reset
// ============================================================================

void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap,
                     valk_lenv_t* root_env) {
  if (scratch == NULL || heap == NULL) {
    VALK_WARN("Checkpoint called with NULL scratch or heap");
    return;
  }

  VALK_INFO("Checkpoint: arena at %zu/%zu bytes (%.1f%%)",
            scratch->offset, scratch->capacity,
            100.0 * scratch->offset / scratch->capacity);

  // Log overflow stats if any occurred
  if (scratch->stats.overflow_fallbacks > 0) {
    VALK_WARN("Checkpoint: %zu allocations (%zu bytes) overflowed to heap",
              scratch->stats.overflow_fallbacks, scratch->stats.overflow_bytes);
  }

  // Initialize evacuation context
  valk_evacuation_ctx_t ctx = {
    .scratch = scratch,
    .heap = heap,
    .worklist = NULL,
    .worklist_count = 0,
    .worklist_capacity = 0,
    .evacuated = NULL,
    .evacuated_count = 0,
    .evacuated_capacity = 0,
    .values_copied = 0,
    .bytes_copied = 0,
    .pointers_fixed = 0,
  };

  evac_ctx_init(&ctx);

  // Phase 1: Evacuate all reachable values from root environment
  VALK_DEBUG("Checkpoint Phase 1: Starting evacuation from scratch arena");
  if (root_env != NULL) {
    valk_evacuate_env(&ctx, root_env);

    // Process worklist until empty (evacuate children)
    while (ctx.worklist_count > 0) {
      valk_lval_t* v = evac_worklist_pop(&ctx);
      valk_evacuate_children(&ctx, v);
    }
  }
  VALK_DEBUG("Checkpoint Phase 1: Evacuated %zu values (%zu bytes)",
             ctx.values_copied, ctx.bytes_copied);

  // Phase 2: Fix all pointers in evacuated values only
  // This avoids iterating heap->objects which may contain non-value allocations
  VALK_DEBUG("Checkpoint Phase 2: Fixing pointers in %zu evacuated values",
             ctx.evacuated_count);
  for (size_t i = 0; i < ctx.evacuated_count; i++) {
    valk_fix_pointers(&ctx, ctx.evacuated[i]);
  }

  // Fix pointers in root environment
  if (root_env != NULL) {
    valk_fix_env_pointers(&ctx, root_env);
  }
  VALK_DEBUG("Checkpoint Phase 2: Fixed %zu pointers", ctx.pointers_fixed);

  // Update scratch arena stats
  scratch->stats.num_checkpoints++;
  scratch->stats.bytes_evacuated += ctx.bytes_copied;
  scratch->stats.values_evacuated += ctx.values_copied;

  // Update heap stats
  heap->stats.evacuations_from_scratch += ctx.values_copied;
  heap->stats.evacuation_bytes += ctx.bytes_copied;
  heap->stats.evacuation_pointer_fixups += ctx.pointers_fixed;

  VALK_INFO("Checkpoint: evacuated %zu values (%zu bytes), fixed %zu pointers",
            ctx.values_copied, ctx.bytes_copied, ctx.pointers_fixed);

  // Reset scratch arena for next round of allocations
  valk_mem_arena_reset(scratch);

  // Cleanup
  evac_ctx_free(&ctx);
}
