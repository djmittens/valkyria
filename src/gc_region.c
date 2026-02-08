#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>

// ============================================================================
// Region API Implementation
// ============================================================================

// LCOV_EXCL_BR_START - region API defensive null checks and lifetime switches
#define VALK_REGION_DEFAULT_SIZE (64 * 1024)

void valk_region_init(valk_region_t *region, valk_lifetime_e lifetime,
                      valk_region_t *parent, valk_mem_arena_t *arena) {
  region->type = VALK_ALLOC_REGION;
  region->lifetime = lifetime;
  region->parent = parent;
  region->arena = arena;
  region->owns_arena = false;
  region->gc_heap = nullptr;
  memset(&region->stats, 0, sizeof(region->stats));

  if (lifetime == VALK_LIFETIME_SESSION) {
    region->gc_heap = valk_runtime_get_heap();
  }
}

// LCOV_EXCL_BR_START - region creation switch/OOM branches
valk_region_t *valk_region_create(valk_lifetime_e lifetime, valk_region_t *parent) {
  valk_region_t *region = malloc(sizeof(valk_region_t));
  if (!region) return nullptr;

  region->type = VALK_ALLOC_REGION;
  region->lifetime = lifetime;
  region->parent = parent;
  region->gc_heap = nullptr;
  region->arena = nullptr;
  region->owns_arena = false;
  memset(&region->stats, 0, sizeof(region->stats));

  switch (lifetime) {
    case VALK_LIFETIME_IMMORTAL:
      break;

    case VALK_LIFETIME_SESSION:
      region->gc_heap = valk_runtime_get_heap();
      break;

    case VALK_LIFETIME_REQUEST:
    case VALK_LIFETIME_SCRATCH: {
      sz arena_size = sizeof(valk_mem_arena_t) + VALK_REGION_DEFAULT_SIZE;
      region->arena = malloc(arena_size);
      if (!region->arena) {
        free(region);
        return nullptr;
      }
      valk_mem_arena_init(region->arena, VALK_REGION_DEFAULT_SIZE);
      region->owns_arena = true;
      break;
    }
  }

  return region;
}

valk_region_t *valk_region_create_with_arena(valk_lifetime_e lifetime,
                                              valk_region_t *parent,
                                              valk_mem_arena_t *arena) {
  valk_region_t *region = malloc(sizeof(valk_region_t));
  if (!region) return nullptr;

  region->type = VALK_ALLOC_REGION;
  region->lifetime = lifetime;
  region->parent = parent;
  region->arena = arena;
  region->owns_arena = false;
  region->gc_heap = nullptr;
  memset(&region->stats, 0, sizeof(region->stats));

  if (lifetime == VALK_LIFETIME_SESSION) {
    region->gc_heap = valk_runtime_get_heap();
  }

  return region;
}

void valk_region_destroy(valk_region_t *region) {
  if (!region) return;

  if (region->arena && region->owns_arena) {
    free(region->arena);
    region->arena = nullptr;
  }

  free(region);
}

void valk_region_reset(valk_region_t *region) {
  if (!region) return;

  if (region->arena) {
    valk_mem_arena_reset(region->arena);
  }

  sz limit = region->stats.bytes_limit;
  atomic_store_explicit(&region->stats.bytes_allocated, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.bytes_promoted, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.alloc_count, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.promotion_count, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.overflow_count, 0, memory_order_relaxed);
  region->stats.bytes_limit = limit;
}

void *valk_region_alloc(valk_region_t *region, sz bytes) {
  if (!region) return nullptr;

  sz limit = region->stats.bytes_limit;
  if (limit > 0) {
    sz current = atomic_load_explicit(&region->stats.bytes_allocated, memory_order_relaxed);
    if (current + bytes > limit) {
      if (region->parent) {
        atomic_fetch_add_explicit(&region->stats.overflow_count, 1, memory_order_relaxed);
        return valk_region_alloc(region->parent, bytes);
      }
      return nullptr;
    }
  }

  void *ptr = nullptr;

  switch (region->lifetime) {
    case VALK_LIFETIME_IMMORTAL:
      return nullptr;

    case VALK_LIFETIME_SESSION:
      if (region->gc_heap) {
        ptr = valk_gc_heap2_alloc(region->gc_heap, bytes);
      }
      break;

    case VALK_LIFETIME_REQUEST:
    case VALK_LIFETIME_SCRATCH:
      if (region->arena) {
        ptr = valk_mem_arena_alloc(region->arena, bytes);
      }
      if (!ptr && region->parent) {
        atomic_fetch_add_explicit(&region->stats.overflow_count, 1, memory_order_relaxed);
        return valk_region_alloc(region->parent, bytes);
      }
      break;
  }

  if (ptr) {
    atomic_fetch_add_explicit(&region->stats.bytes_allocated, bytes, memory_order_relaxed);
    atomic_fetch_add_explicit(&region->stats.alloc_count, 1, memory_order_relaxed);
  }

  return ptr;
}

bool valk_region_set_limit(valk_region_t *region, sz limit) {
  if (!region) return false;
  if (limit > 0 && atomic_load_explicit(&region->stats.bytes_allocated, memory_order_relaxed) > limit) {
    return false;
  }
  region->stats.bytes_limit = limit;
  return true;
}

void valk_region_get_stats(valk_region_t *region, valk_region_stats_t *out) {
  if (!region || !out) return;
  atomic_store_explicit(&out->bytes_allocated,
      atomic_load_explicit(&region->stats.bytes_allocated, memory_order_relaxed), memory_order_relaxed);
  out->bytes_limit = region->stats.bytes_limit;
  atomic_store_explicit(&out->bytes_promoted,
      atomic_load_explicit(&region->stats.bytes_promoted, memory_order_relaxed), memory_order_relaxed);
  atomic_store_explicit(&out->alloc_count,
      atomic_load_explicit(&region->stats.alloc_count, memory_order_relaxed), memory_order_relaxed);
  atomic_store_explicit(&out->promotion_count,
      atomic_load_explicit(&region->stats.promotion_count, memory_order_relaxed), memory_order_relaxed);
  atomic_store_explicit(&out->overflow_count,
      atomic_load_explicit(&region->stats.overflow_count, memory_order_relaxed), memory_order_relaxed);
}

// ============================================================================
// Cross-Region Reference Checking
// ============================================================================

valk_lifetime_e valk_allocator_lifetime(void *allocator) {
  if (!allocator) return VALK_LIFETIME_SCRATCH;

  valk_mem_allocator_t *alloc = (valk_mem_allocator_t *)allocator;
  switch (alloc->type) {
    case VALK_ALLOC_REGION: {
      valk_region_t *region = (valk_region_t *)allocator;
      return region->lifetime;
    }
    case VALK_ALLOC_GC_HEAP:
      return VALK_LIFETIME_SESSION;
    case VALK_ALLOC_ARENA:
      return VALK_LIFETIME_SCRATCH;
    case VALK_ALLOC_MALLOC:
      return VALK_LIFETIME_IMMORTAL;
    default:
      return VALK_LIFETIME_SCRATCH;
  }
}

bool valk_region_write_barrier(void *parent_allocator, void *child_allocator,
                                bool promote_on_escape) {
  if (!parent_allocator || !child_allocator) return true;

  valk_lifetime_e parent_lifetime = valk_allocator_lifetime(parent_allocator);
  valk_lifetime_e child_lifetime = valk_allocator_lifetime(child_allocator);

  if (valk_lifetime_can_reference(parent_lifetime, child_lifetime)) {
    return true;
  }

  if (promote_on_escape) {
    return false;
  }

  return false;
}
// LCOV_EXCL_BR_STOP

static valk_lval_t *region_copy_lval_recursive(valk_region_t *target, valk_lval_t *src,
                                                valk_ptr_map_t *copied) {
  if (!src) return nullptr; // LCOV_EXCL_BR_LINE - null elements in recursive copy

  valk_lval_t *existing = valk_ptr_map_get(copied, src);
  if (existing) return existing; // LCOV_EXCL_BR_LINE - shared references in recursive copy

  valk_lifetime_e src_lifetime = valk_allocator_lifetime(src->origin_allocator);
  if (valk_lifetime_can_reference(target->lifetime, src_lifetime)) { // LCOV_EXCL_BR_LINE - mixed-lifetime structures
    return src;
  }

  sz lval_size = sizeof(valk_lval_t);
  valk_lval_t *copy = valk_region_alloc(target, lval_size);
  if (!copy) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  memcpy(copy, src, lval_size);
  copy->origin_allocator = target;
  copy->gc_next = nullptr;

  valk_ptr_map_put(copied, src, copy);

  valk_ltype_e type = LVAL_TYPE(src);
  switch (type) {
    case LVAL_CONS:
      copy->cons.head = region_copy_lval_recursive(target, src->cons.head, copied);
      copy->cons.tail = region_copy_lval_recursive(target, src->cons.tail, copied);
      break;

    case LVAL_FUN:
      if (src->fun.name) {
        sz len = strlen(src->fun.name) + 1;
        copy->fun.name = valk_region_alloc(target, len);
        if (copy->fun.name) memcpy(copy->fun.name, src->fun.name, len); // LCOV_EXCL_BR_LINE - OOM
      }
      copy->fun.formals = region_copy_lval_recursive(target, src->fun.formals, copied);
      copy->fun.body = region_copy_lval_recursive(target, src->fun.body, copied);
      break;

    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      if (src->str) {
        sz len = strlen(src->str) + 1;
        copy->str = valk_region_alloc(target, len);
        if (copy->str) memcpy(copy->str, src->str, len); // LCOV_EXCL_BR_LINE - OOM
      }
      break;

    default:
      break;
  }

  atomic_fetch_add_explicit(&target->stats.bytes_promoted, lval_size, memory_order_relaxed);
  atomic_fetch_add_explicit(&target->stats.promotion_count, 1, memory_order_relaxed);

  return copy;
}

valk_lval_t *valk_region_promote_lval(valk_region_t *target, valk_lval_t *val) {
  if (!target || !val) return val; // LCOV_EXCL_BR_LINE

  valk_lifetime_e val_lifetime = valk_allocator_lifetime(val->origin_allocator);
  if (valk_lifetime_can_reference(target->lifetime, val_lifetime)) { // LCOV_EXCL_BR_LINE
    return val;
  }

  valk_ptr_map_t copied;
  valk_ptr_map_init(&copied);

  valk_lval_t *promoted = region_copy_lval_recursive(target, val, &copied);

  valk_ptr_map_free(&copied);

  return promoted;
}

valk_lval_t *valk_region_ensure_safe_ref(valk_lval_t *parent, valk_lval_t *child) {
  if (!parent || !child) return child; // LCOV_EXCL_BR_LINE

  void *parent_alloc = parent->origin_allocator;
  void *child_alloc = child->origin_allocator;

  if (!parent_alloc || !child_alloc) return child;

  if (valk_region_write_barrier(parent_alloc, child_alloc, false)) {
    return child;
  }

  valk_mem_allocator_t *alloc = (valk_mem_allocator_t *)parent_alloc;
  if (alloc->type == VALK_ALLOC_REGION) { // LCOV_EXCL_BR_LINE
    return valk_region_promote_lval((valk_region_t *)parent_alloc, child);
  }

  return child;
}
