#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <string.h>

// Forward declarations
static void valk_gc_mark_lval(valk_lval_t* v);
static void valk_gc_mark_env(valk_lenv_t* env);

// Check if GC should run (arena nearly full)
bool valk_gc_should_collect_arena(valk_mem_arena_t* arena) {
  // Trigger GC when arena is 90% full
  return (arena->offset > (arena->capacity * 9 / 10));
}

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

// Clear all GC marks recursively
static void valk_gc_clear_marks_recursive(valk_lval_t* v) {
  if (v == nullptr) return;

  // Already cleared - avoid infinite loops
  if (!(v->flags & LVAL_FLAG_GC_MARK)) return;

  // Clear mark
  v->flags &= ~LVAL_FLAG_GC_MARK;

  // Clear marks on children
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

// Main GC function - mark & count dead objects (informational only for now)
size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena) {
  if (root_env == NULL) {
    VALK_WARN("GC collect called with no root environment");
    return 0;
  }

  VALK_INFO("GC: Starting collection (arena used: %zu/%zu bytes)",
            arena->offset, arena->capacity);

  // Phase 1: Mark from roots
  valk_gc_mark_env(root_env);

  // Phase 2: Count unmarked objects in arena (can't actually sweep arena without compaction)
  // This is informational only - actual memory reclamation happens via scratch arena resets
  size_t dead_count = 0;
  size_t live_count = 0;

  // Scan arena to count marked vs unmarked objects
  // Note: This is approximate since we don't track individual allocations in arena
  uint8_t* ptr = arena->heap;
  uint8_t* end = arena->heap + arena->offset;

  while (ptr < end) {
    valk_lval_t* v = (valk_lval_t*)ptr;

    // Basic sanity check - looks like an lval?
    if ((v->flags & LVAL_TYPE_MASK) <= LVAL_ENV) {
      if (v->flags & LVAL_FLAG_GC_MARK) {
        live_count++;
      } else {
        dead_count++;
      }
    }

    ptr += sizeof(valk_lval_t);
  }

  // Phase 3: Clear marks for next collection
  for (size_t i = 0; i < root_env->count; i++) {
    valk_gc_clear_marks_recursive(root_env->vals[i]);
  }

  size_t estimated_dead_bytes = dead_count * sizeof(valk_lval_t);

  VALK_INFO("GC: Complete - live: %zu, dead: %zu (est. %zu bytes reclaimable)",
            live_count, dead_count, estimated_dead_bytes);

  return estimated_dead_bytes;
}
