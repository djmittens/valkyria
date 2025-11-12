#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>

// Forward declarations
static void valk_gc_mark_lval(valk_lval_t* v);
static void valk_gc_mark_env(valk_lenv_t* env);
static void valk_gc_clear_marks_recursive(valk_lval_t* v);

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

// Allocate from GC heap
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, size_t bytes) {
  // Trigger GC before allocation if needed
  if (valk_gc_malloc_should_collect(heap) && heap->root_env != NULL) {
    VALK_INFO("GC triggered before allocation (%zu/%zu bytes)",
              heap->allocated_bytes, heap->gc_threshold);
    valk_gc_malloc_collect(heap);
  }

  // Allocate using malloc
  valk_lval_t* obj = malloc(bytes);
  if (obj == NULL) {
    VALK_ERROR("GC heap malloc failed for %zu bytes", bytes);
    return NULL;
  }

  // Initialize GC tracking
  obj->origin_allocator = heap;
  obj->gc_next = heap->objects;
  heap->objects = obj;

  // Track allocation
  heap->allocated_bytes += bytes;

  return obj;
}

// ============================================================================
// Mark Phase - Traverse from roots and mark reachable objects
// ============================================================================

static void valk_gc_mark_lval(valk_lval_t* v) {
  if (v == NULL) return;

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

    case LVAL_QEXPR:
    case LVAL_SEXPR:
      // Mark cons list
      valk_gc_mark_lval(v->cons.head);
      valk_gc_mark_lval(v->cons.tail);
      break;

    case LVAL_ENV:
      valk_gc_mark_env(&v->env);
      break;

    case LVAL_UNDEFINED:
    case LVAL_CONS:
    case LVAL_NIL:
      break;
  }
}

static void valk_gc_mark_env(valk_lenv_t* env) {
  if (env == NULL) return;

  // Mark all values in this environment
  for (size_t i = 0; i < env->count; i++) {
    valk_gc_mark_lval(env->vals[i]);
  }

  // Mark parent environment
  valk_gc_mark_env(env->parent);
}

// ============================================================================
// Sweep Phase - Free unmarked objects
// ============================================================================

static size_t valk_gc_malloc_sweep(valk_gc_malloc_heap_t* heap) {
  size_t reclaimed = 0;
  size_t freed_count = 0;
  valk_lval_t** obj_ptr = &heap->objects;

  while (*obj_ptr != NULL) {
    valk_lval_t* obj = *obj_ptr;

    if (obj->flags & LVAL_FLAG_GC_MARK) {
      // Object is live - keep it
      obj_ptr = &obj->gc_next;
    } else {
      // Object is garbage - free it
      *obj_ptr = obj->gc_next;  // Remove from list

      // TODO: For now, only free the lval struct itself, not string data
      // String data might be in scratch arena or shared (frozen aliased values)
      // Need proper ownership tracking to safely free string data

      size_t obj_size = sizeof(valk_lval_t);
      reclaimed += obj_size;
      freed_count++;

      // Free the object itself
      free(obj);
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

  // Already cleared
  if (!(v->flags & LVAL_FLAG_GC_MARK)) return;

  // Clear mark
  v->flags &= ~LVAL_FLAG_GC_MARK;

  // Clear children
  switch (LVAL_TYPE(v)) {
    case LVAL_FUN:
      if (v->fun.env) {
        for (size_t i = 0; i < v->fun.env->count; i++) {
          valk_gc_clear_marks_recursive(v->fun.env->vals[i]);
        }
      }
      valk_gc_clear_marks_recursive(v->fun.formals);
      valk_gc_clear_marks_recursive(v->fun.body);
      break;

    case LVAL_QEXPR:
    case LVAL_SEXPR:
      valk_gc_clear_marks_recursive(v->cons.head);
      valk_gc_clear_marks_recursive(v->cons.tail);
      break;

    case LVAL_ENV:
      for (size_t i = 0; i < v->env.count; i++) {
        valk_gc_clear_marks_recursive(v->env.vals[i]);
      }
      break;

    default:
      break;
  }
}

// ============================================================================
// Main GC Collection
// ============================================================================

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

  // Phase 1: Mark reachable objects
  valk_gc_mark_env(heap->root_env);

  // Phase 2: Sweep unreachable objects
  size_t reclaimed = valk_gc_malloc_sweep(heap);

  // Phase 3: Clear marks for next collection
  for (size_t i = 0; i < heap->root_env->count; i++) {
    valk_gc_clear_marks_recursive(heap->root_env->vals[i]);
  }

  size_t after = heap->allocated_bytes;
  heap->num_collections++;

  VALK_INFO("GC: Complete - reclaimed %zu bytes (before: %zu, after: %zu, %.1f%% freed)",
            reclaimed, before, after,
            100.0 * reclaimed / before);

  return reclaimed;
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
  for (size_t i = 0; i < root_env->count; i++) {
    valk_gc_clear_marks_recursive(root_env->vals[i]);
  }

  return dead_count * sizeof(valk_lval_t);
}
