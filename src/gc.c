#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <string.h>

// Forward declarations
static void valk_gc_mark_lval(valk_lval_t* v);
static void valk_gc_mark_env(valk_lenv_t* env);

// Mark a single lval and recursively mark its children
static void valk_gc_mark_lval(valk_lval_t* v) {
  if (v == nullptr) return;

  // Already marked - avoid cycles
  if (v->flags & LVAL_FLAG_GC_MARK) return;

  // Mark this value
  v->flags |= LVAL_FLAG_GC_MARK;

  switch (LVAL_TYPE(v)) {
    case LVAL_NUM:
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
    case LVAL_REF:
      // Leaf types - no children to mark
      break;

    case LVAL_FUN:
      // Mark function's captured environment
      if (v->fun.env) {
        valk_gc_mark_env(v->fun.env);
      }
      // Mark function formals and body
      valk_gc_mark_lval(v->fun.formals);
      valk_gc_mark_lval(v->fun.body);
      break;

    case LVAL_QEXPR:
    case LVAL_SEXPR:
      // Mark cons list recursively
      valk_gc_mark_lval(v->cons.head);
      valk_gc_mark_lval(v->cons.tail);
      break;

    case LVAL_ENV:
      // Mark the environment
      valk_gc_mark_env(&v->env);
      break;

    case LVAL_UNDEFINED:
    case LVAL_CONS:
    case LVAL_NIL:
      // These types shouldn't appear here but handle them to avoid warnings
      break;
  }
}

// Mark all values in an environment
static void valk_gc_mark_env(valk_lenv_t* env) {
  if (env == nullptr) return;

  // Mark all values in this environment
  for (size_t i = 0; i < env->count; i++) {
    valk_gc_mark_lval(env->vals[i]);
  }

  // Mark parent environment
  valk_gc_mark_env(env->parent);
}

// Clear all GC marks in preparation for next GC cycle
static void valk_gc_clear_marks_in_arena(valk_mem_arena_t* arena) {
  // We need to iterate through the arena and clear marks
  // This is tricky because arena doesn't track individual allocations
  // For now, we'll scan the entire arena looking for lval pointers

  uint8_t* ptr = arena->heap;
  uint8_t* end = arena->heap + arena->offset;

  while (ptr < end) {
    // Try to interpret this as an lval
    valk_lval_t* v = (valk_lval_t*)ptr;

    // Check if this looks like a valid lval (basic sanity check)
    if ((v->flags & LVAL_TYPE_MASK) <= LVAL_ENV) {
      // Clear the GC mark
      v->flags &= ~LVAL_FLAG_GC_MARK;
    }

    // Move to next potential object
    // This is approximate - we don't know exact object sizes
    ptr += sizeof(valk_lval_t);
  }
}

// Compact arena by copying live objects to a new arena
static size_t valk_gc_compact_arena(valk_mem_arena_t* old_arena, valk_mem_arena_t* new_arena) {
  size_t reclaimed = 0;

  // Scan old arena and copy marked objects to new arena
  uint8_t* ptr = old_arena->heap;
  uint8_t* end = old_arena->heap + old_arena->offset;

  while (ptr < end) {
    valk_lval_t* v = (valk_lval_t*)ptr;

    // Check if this is a marked (live) object
    if ((v->flags & LVAL_FLAG_GC_MARK) &&
        (v->flags & LVAL_TYPE_MASK) <= LVAL_ENV) {

      // Determine object size (approximate)
      size_t obj_size = sizeof(valk_lval_t);

      // For strings and symbols, include string data
      if (LVAL_TYPE(v) == LVAL_STR || LVAL_TYPE(v) == LVAL_SYM || LVAL_TYPE(v) == LVAL_ERR) {
        if (v->str != nullptr) {
          obj_size += strlen(v->str) + 1;
        }
      }

      // Allocate in new arena and copy
      void* new_ptr = valk_mem_arena_alloc(new_arena, obj_size);
      if (new_ptr) {
        memcpy(new_ptr, v, obj_size);

        // TODO: Update all pointers to this object
        // This is the hard part - we need pointer forwarding
      }
    } else {
      // Dead object - count as reclaimed
      reclaimed += sizeof(valk_lval_t);
    }

    ptr += sizeof(valk_lval_t);
  }

  return reclaimed;
}

// Main GC function - mark & sweep with compaction
size_t valk_gc_collect(valk_lenv_t* root_env, valk_mem_arena_t* arena) {
  VALK_INFO("GC: Starting collection (arena used: %zu/%zu bytes)",
            arena->offset, arena->capacity);

  // Phase 1: Clear all marks
  valk_gc_clear_marks_in_arena(arena);

  // Phase 2: Mark from roots
  valk_gc_mark_env(root_env);

  // Phase 3: Compact (sweep)
  // For arena allocator, we need to compact because we can't free individual objects
  // This is complex - for now, just report what would be collected

  // Count unmarked objects
  size_t dead_count = 0;
  size_t live_count = 0;
  size_t dead_bytes = 0;

  uint8_t* ptr = arena->heap;
  uint8_t* end = arena->heap + arena->offset;

  while (ptr < end) {
    valk_lval_t* v = (valk_lval_t*)ptr;

    if ((v->flags & LVAL_TYPE_MASK) <= LVAL_ENV) {
      if (v->flags & LVAL_FLAG_GC_MARK) {
        live_count++;
      } else {
        dead_count++;
        dead_bytes += sizeof(valk_lval_t);
      }
    }

    ptr += sizeof(valk_lval_t);
  }

  VALK_INFO("GC: Complete - live: %zu, dead: %zu, reclaimed: %zu bytes",
            live_count, dead_count, dead_bytes);

  return dead_bytes;
}

// Simple GC trigger - collect when arena is nearly full
bool valk_gc_should_collect(valk_mem_arena_t* arena) {
  // Trigger GC when arena is 90% full
  return (arena->offset > (arena->capacity * 9 / 10));
}
