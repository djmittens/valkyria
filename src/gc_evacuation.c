#include "gc.h"
#include "parser.h"
#include "dict.h"
#include "memory.h"
#include "log.h"
#include "aio/aio.h"
#include <stdlib.h>
#include <string.h>

// ============================================================================
// Evacuation Context
// ============================================================================

typedef struct {
  valk_mem_arena_t* scratch;
  valk_gc_heap_t* heap;
  valk_lval_t** worklist;
  sz worklist_count;
  sz worklist_capacity;
  valk_lval_t** evacuated;
  sz evacuated_count;
  sz evacuated_capacity;
  u64 values_copied;
  sz bytes_copied;
  u64 pointers_fixed;
  valk_ptr_map_t ptr_map;
} valk_evacuation_ctx_t;

// LCOV_EXCL_BR_START - evacuation context internal defensive checks
#define EVAC_WORKLIST_INITIAL_CAPACITY 256

static void evac_ctx_init(valk_evacuation_ctx_t* ctx) {
  ctx->worklist = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->worklist_count = 0;
  ctx->worklist_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;

  ctx->evacuated = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;

  valk_ptr_map_init(&ctx->ptr_map);
}

static void evac_ctx_free(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist) {
    free(ctx->worklist);
    ctx->worklist = nullptr;
  }
  ctx->worklist_count = 0;
  ctx->worklist_capacity = 0;

  if (ctx->evacuated) {
    free(ctx->evacuated);
    ctx->evacuated = nullptr;
  }
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = 0;

  valk_ptr_map_free(&ctx->ptr_map);
}

static void evac_add_evacuated(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;

  // LCOV_EXCL_START - evacuation list realloc OOM
  if (ctx->evacuated_count >= ctx->evacuated_capacity) {
    sz new_cap = ctx->evacuated_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->evacuated, new_cap * sizeof(valk_lval_t*));
    if (new_list == nullptr) {
      VALK_ERROR("Failed to grow evacuated list");
      return;
    }
    ctx->evacuated = new_list;
    ctx->evacuated_capacity = new_cap;
  }
  // LCOV_EXCL_STOP

  ctx->evacuated[ctx->evacuated_count++] = v;
}

static void evac_worklist_push(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return; // LCOV_EXCL_BR_LINE

  // LCOV_EXCL_START - worklist realloc OOM
  if (ctx->worklist_count >= ctx->worklist_capacity) {
    sz new_cap = ctx->worklist_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->worklist, new_cap * sizeof(valk_lval_t*));
    if (new_list == nullptr) {
      VALK_ERROR("Failed to grow evacuation worklist");
      return;
    }
    ctx->worklist = new_list;
    ctx->worklist_capacity = new_cap;
  }
  // LCOV_EXCL_STOP

  ctx->worklist[ctx->worklist_count++] = v;
}

static valk_lval_t* evac_worklist_pop(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist_count == 0) return nullptr; // LCOV_EXCL_BR_LINE
  return ctx->worklist[--ctx->worklist_count];
}

// ============================================================================
// Value Evacuation (scratch -> heap)
// ============================================================================

static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static valk_lenv_t* valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v);

// LCOV_EXCL_BR_START - evacuation value copy null checks and type dispatch
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return nullptr;

  if (v->flags & LVAL_FLAG_IMMORTAL) return v;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) return v;

  void *existing = valk_ptr_map_get(&ctx->ptr_map, v);
  if (existing != nullptr) return (valk_lval_t *)existing;

  valk_lval_t* new_val = nullptr;
  VALK_WITH_ALLOC((void*)ctx->heap) {
    new_val = valk_mem_alloc(sizeof(valk_lval_t));
  }

  // LCOV_EXCL_START - OOM during evacuation
  if (new_val == nullptr) {
    VALK_ERROR("Failed to allocate value during evacuation");
    return v;
  }
  // LCOV_EXCL_STOP

  valk_ptr_map_put(&ctx->ptr_map, v, new_val);

  memcpy(new_val, v, sizeof(valk_lval_t));
  new_val->flags = (new_val->flags & ~LVAL_ALLOC_MASK) | LVAL_ALLOC_HEAP;

  bool needs_string_copy = (ctx->scratch == nullptr) ||
                           !valk_ptr_in_arena(ctx->scratch, v);

  switch (LVAL_TYPE(new_val)) {
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      if (new_val->str != nullptr && !(new_val->flags & LVAL_FLAG_INTERNED) &&
          (needs_string_copy || valk_ptr_in_arena(ctx->scratch, new_val->str))) {
        u64 len = strlen(v->str) + 1;
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
      if (new_val->fun.name != nullptr && new_val->fun.builtin == nullptr &&
          (needs_string_copy || valk_ptr_in_arena(ctx->scratch, new_val->fun.name))) {
        u64 len = strlen(v->fun.name) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->fun.name = valk_mem_alloc(len);
        }
        if (new_val->fun.name) {
          memcpy(new_val->fun.name, v->fun.name, len);
          ctx->bytes_copied += len;
        }
      }
      break;

    // LCOV_EXCL_START - REF deep evacuation: REFs use leaf path via valk_evacuate_to_heap
    case LVAL_REF:
      if (new_val->ref.type != nullptr &&
          (needs_string_copy || valk_ptr_in_arena(ctx->scratch, new_val->ref.type))) {
        u64 len = strlen(v->ref.type) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->ref.type = valk_mem_alloc(len);
        }
        if (new_val->ref.type) {
          memcpy(new_val->ref.type, v->ref.type, len);
          ctx->bytes_copied += len;
        }
      }
      if (new_val->ref.evacuate)
        new_val->ref.evacuate(&new_val->ref.ptr, ctx);
      v->ref.ptr = new_val->ref.ptr;
      if (new_val->ref.retain) new_val->ref.retain(new_val->ref.ptr);
      break;
    // LCOV_EXCL_STOP

    case LVAL_DICT:
      if (new_val->dict.data != nullptr &&
          ctx->scratch != nullptr && valk_ptr_in_arena(ctx->scratch, new_val->dict.data)) {
        valk_dict_t *d = new_val->dict.data;
        u64 sz = dict_block_size(d->num_buckets, d->capacity, d->strings_cap);
        valk_dict_t *nd;
        VALK_WITH_ALLOC((void *)ctx->heap) {
          nd = valk_mem_alloc(sz);
        }
        if (nd) {
          memcpy(nd, d, sz);
          new_val->dict.data = nd;
          ctx->bytes_copied += sz;
        }
      }
      break;

    default:
      break;
  }

  evac_add_evacuated(ctx, new_val);
  ctx->values_copied++;
  ctx->bytes_copied += sizeof(valk_lval_t);

  return new_val;
}

// ============================================================================
// Child Evacuation
// ============================================================================

static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
      if (v->cons.head != nullptr) {
        valk_lval_t* old_head = v->cons.head;
        valk_lval_t* new_head = valk_evacuate_value(ctx, old_head);
        // LCOV_EXCL_START - invariant check
        if ((void*)new_head == (void*)ctx->scratch) {
          fprintf(stderr, "BUG in evacuation: new_head == scratch! old_head=%p new_head=%p scratch=%p\n",
                  (void*)old_head, (void*)new_head, (void*)ctx->scratch);
          fprintf(stderr, "  old_head type=%d alloc=%llu\n", LVAL_TYPE(old_head),
                  (unsigned long long)LVAL_ALLOC(old_head));
          abort();
        }
        // LCOV_EXCL_STOP
        if (new_head != old_head) {
          v->cons.head = new_head;
          if (new_head != nullptr) evac_worklist_push(ctx, new_head);
        }
      }
      if (v->cons.tail != nullptr) {
        valk_lval_t* old_tail = v->cons.tail;
        valk_lval_t* new_tail = valk_evacuate_value(ctx, old_tail);
        if (new_tail != old_tail) {
          v->cons.tail = new_tail;
          if (new_tail != nullptr) evac_worklist_push(ctx, new_tail);
        }
      }
      break;

    case LVAL_FUN:
      if (v->fun.name != nullptr && v->fun.builtin == nullptr &&
          !valk_ptr_in_arena(ctx->scratch, v->fun.name)) {
        u64 len = strlen(v->fun.name) + 1;
        char* new_name = nullptr;
        VALK_WITH_ALLOC((void*)ctx->heap) { new_name = valk_mem_alloc(len); }
        if (new_name) {
          memcpy(new_name, v->fun.name, len);
          v->fun.name = new_name;
          ctx->bytes_copied += len;
        }
      }

      if (v->fun.builtin == nullptr) {
        if (v->fun.formals != nullptr) {
          valk_lval_t* old_formals = v->fun.formals;
          valk_lval_t* new_formals = valk_evacuate_value(ctx, old_formals);
          if (new_formals != old_formals) {
            v->fun.formals = new_formals;
            if (new_formals != nullptr) evac_worklist_push(ctx, new_formals);
          }
        }
        if (v->fun.body != nullptr) {
          valk_lval_t* old_body = v->fun.body;
          valk_lval_t* new_body = valk_evacuate_value(ctx, old_body);
          if (new_body != old_body) {
            v->fun.body = new_body;
            if (new_body != nullptr) evac_worklist_push(ctx, new_body);
          }
        }
        if (v->fun.env != nullptr) {
          v->fun.env = valk_evacuate_env(ctx, v->fun.env);
        }
      }
      break;

    // LCOV_EXCL_START - redundant safety net: valk_evacuate_value already copies strings
    case LVAL_STR:
    case LVAL_SYM:
    case LVAL_ERR:
      if (v->str != nullptr && !(v->flags & LVAL_FLAG_INTERNED) &&
          (ctx->scratch == nullptr || valk_ptr_in_arena(ctx->scratch, v->str))) {
        u64 len = strlen(v->str) + 1;
        char* new_str = nullptr;
        VALK_WITH_ALLOC((void*)ctx->heap) { new_str = valk_mem_alloc(len); }
        if (new_str && new_str != v->str) {
          memcpy(new_str, v->str, len);
          v->str = new_str;
          ctx->bytes_copied += len;
        }
      }
      break;
    // LCOV_EXCL_STOP

    case LVAL_REF: // LCOV_EXCL_LINE
      break;

    case LVAL_DICT: {
      valk_dict_t *d = v->dict.data;
      if (d) {
        valk_dict_cell_t *cells = dict_cells(d);
        u32 *buckets = dict_buckets(d);
        for (u32 b = 0; b < d->num_buckets; b++) {
          u32 ci = buckets[b];
          while (ci != DICT_EMPTY) {
            if (cells[ci].value != nullptr) {
              valk_lval_t *old_val = cells[ci].value;
              valk_lval_t *new_val = valk_evacuate_value(ctx, old_val);
              if (new_val != old_val) {
                cells[ci].value = new_val;
                if (new_val != nullptr) evac_worklist_push(ctx, new_val);
              }
            }
            ci = cells[ci].next;
          }
        }
      }
      break;
    }

    default:
      break;
  }
}

// ============================================================================
// Environment Evacuation
// ============================================================================

// LCOV_EXCL_START - envs are always heap-allocated (valk_lenv_empty), never on scratch
static valk_lenv_t* valk_evacuate_env_clone(valk_evacuation_ctx_t* ctx,
                                             valk_lenv_t* src) {
  valk_lenv_t* dst;
  VALK_WITH_ALLOC((void*)ctx->heap) {
    dst = valk_mem_alloc(sizeof(valk_lenv_t));
  }
  if (!dst) return src;
  memset(dst, 0, sizeof(valk_lenv_t));
  dst->allocator = ctx->heap;
  // Concurrent (global) envs are heap-allocated and never evacuated here, but
  // carry the map pointer through defensively so it is never silently dropped.
  dst->cmap = src->cmap;

  if (src->symbols.items != nullptr && src->symbols.count > 0) {
    u64 array_size = src->symbols.capacity * sizeof(char*);
    VALK_WITH_ALLOC((void*)ctx->heap) {
      dst->symbols.items = valk_mem_alloc(array_size);
    }
    if (dst->symbols.items) {
      dst->symbols.count = src->symbols.count;
      dst->symbols.capacity = src->symbols.capacity;
      ctx->bytes_copied += array_size;

      for (u64 i = 0; i < src->symbols.count; i++) {
        char* sym = src->symbols.items[i];
        if (sym == nullptr) { dst->symbols.items[i] = nullptr; continue; }
        u64 len = strlen(sym) + 1;
        char* new_str = nullptr;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_str = valk_mem_alloc(len);
        }
        if (new_str) {
          memcpy(new_str, sym, len);
          dst->symbols.items[i] = new_str;
          ctx->bytes_copied += len;
        } else {
          dst->symbols.items[i] = sym; // LCOV_EXCL_LINE
        }
      }
    }
  }

  if (src->vals.items != nullptr && src->vals.count > 0) {
    u64 array_size = src->vals.capacity * sizeof(valk_lval_t*);
    VALK_WITH_ALLOC((void*)ctx->heap) {
      dst->vals.items = valk_mem_alloc(array_size);
    }
    if (dst->vals.items) {
      dst->vals.count = src->vals.count;
      dst->vals.capacity = src->vals.capacity;
      ctx->bytes_copied += array_size;

      for (u64 i = 0; i < src->vals.count; i++) {
        valk_lval_t* val = src->vals.items[i];
        if (val == nullptr) { dst->vals.items[i] = nullptr; continue; }
        valk_lval_t* new_val = valk_evacuate_value(ctx, val);
        dst->vals.items[i] = new_val;
        if (new_val != val && new_val != nullptr)
          evac_worklist_push(ctx, new_val);
      }
    }
  }

  return dst;
}
// LCOV_EXCL_STOP

static valk_lenv_t* valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == nullptr) return nullptr;

  valk_lenv_t* new_root = nullptr;
  valk_lenv_t* prev_new = nullptr;
  valk_lenv_t* current = env;

  while (current != nullptr) {
    if (current->allocator == ctx->heap) {
      if (prev_new != nullptr) prev_new->parent = current;
      if (new_root == nullptr) new_root = current;
      break;
    }
    // LCOV_EXCL_START - envs always on heap, clone path unreachable
    valk_lenv_t* cloned = valk_evacuate_env_clone(ctx, current);
    if (new_root == nullptr) new_root = cloned;
    if (prev_new != nullptr) prev_new->parent = cloned;
    prev_new = cloned;
    current = current->parent;
    // LCOV_EXCL_STOP
  }

  return new_root ? new_root : env;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Pointer Fixing
// ============================================================================

// LCOV_EXCL_START - pointer fixing requires active evacuation context from checkpoint
static inline bool fix_scratch_pointer(valk_evacuation_ctx_t* ctx, valk_lval_t** ptr) {
  valk_lval_t* val = *ptr;
  if (val == nullptr) return false;

  if (val->flags & LVAL_FLAG_IMMORTAL) return false;

  void *new_loc = valk_ptr_map_get(&ctx->ptr_map, val);
  if (new_loc != nullptr) {
    *ptr = (valk_lval_t *)new_loc;
    ctx->pointers_fixed++;
    return true;
  }

  bool in_scratch = (ctx->scratch != nullptr && valk_ptr_in_arena(ctx->scratch, val)) ||
                    (LVAL_ALLOC(val) == LVAL_ALLOC_SCRATCH);
  if (in_scratch) {
    valk_lval_t* new_val = valk_evacuate_value(ctx, val);
    if (new_val != val) {
      *ptr = new_val;
      ctx->pointers_fixed++;
      return true;
    }
    *ptr = nullptr;
    return true;
  }

  return false;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_BR_START - pointer fixing null checks and type dispatch
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;
  if (LVAL_ALLOC(v) == LVAL_ALLOC_SCRATCH) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
      fix_scratch_pointer(ctx, &v->cons.head);
      fix_scratch_pointer(ctx, &v->cons.tail);
      break;

    case LVAL_FUN:
      if (v->fun.builtin == nullptr) {
        fix_scratch_pointer(ctx, &v->fun.formals); // LCOV_EXCL_LINE
        fix_scratch_pointer(ctx, &v->fun.body);
      }
      break;

    case LVAL_REF:
      break;

    case LVAL_DICT: { // LCOV_EXCL_LINE
      valk_dict_t *d = v->dict.data;
      if (d) {
        valk_dict_cell_t *cells = dict_cells(d);
        u32 *buckets = dict_buckets(d);
        for (u32 b = 0; b < d->num_buckets; b++) {
          u32 ci = buckets[b];
          while (ci != DICT_EMPTY) {
            if (cells[ci].value != nullptr)
              fix_scratch_pointer(ctx, &cells[ci].value);
            ci = cells[ci].next;
          }
        }
      }
      break;
    }

    default:
      break;
  }
}

// LCOV_EXCL_BR_STOP

// ============================================================================
// Single-Value Evacuation (no STW)
// ============================================================================

// LCOV_EXCL_BR_START - evacuation to heap: heap fallback and lambda env dispatch
static valk_lval_t* valk_evacuate_leaf(valk_gc_heap_t* heap, valk_lval_t* v) {
  valk_lval_t* nv;
  VALK_WITH_ALLOC((void*)heap) { nv = valk_mem_alloc(sizeof(valk_lval_t)); }
  if (!nv) return v; // LCOV_EXCL_LINE
  memcpy(nv, v, sizeof(valk_lval_t));
  nv->flags = (nv->flags & ~LVAL_ALLOC_MASK) | LVAL_ALLOC_HEAP;

  valk_ltype_e t = LVAL_TYPE(v);
  if ((t == LVAL_SYM || t == LVAL_STR || t == LVAL_ERR) && nv->str &&
      !(nv->flags & LVAL_FLAG_INTERNED)) {
    u64 len = strlen(v->str) + 1;
    VALK_WITH_ALLOC((void*)heap) { nv->str = valk_mem_alloc(len); }
    if (nv->str) memcpy(nv->str, v->str, len);
  } else if (t == LVAL_REF && nv->ref.type) {
    u64 len = strlen(v->ref.type) + 1;
    VALK_WITH_ALLOC((void*)heap) { nv->ref.type = valk_mem_alloc(len); }
    if (nv->ref.type) memcpy(nv->ref.type, v->ref.type, len);
  }
  return nv;
}

valk_lval_t* valk_evacuate_to_heap(valk_lval_t* v) {
  if (v == nullptr) return nullptr;
  if (LVAL_ALLOC(v) == LVAL_ALLOC_HEAP) return v;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) return v;

  valk_mem_arena_t* scratch = valk_thread_ctx.scratch; // LCOV_EXCL_LINE
  valk_gc_heap_t* heap = valk_thread_ctx.heap;

  if (!heap && valk_sys) heap = valk_sys->heap; // LCOV_EXCL_LINE

  // LCOV_EXCL_START - heap always available in normal operation
  if (!heap) {
    VALK_ERROR("valk_evacuate_to_heap: no heap available (scratch=%p, heap=%p, v alloc=%u)",
               (void*)scratch, (void*)heap, LVAL_ALLOC(v));
    return v;
  }
  // LCOV_EXCL_STOP

  valk_ltype_e t = LVAL_TYPE(v);
  if (t == LVAL_NUM || t == LVAL_NIL || t == LVAL_SYM ||
      t == LVAL_STR || t == LVAL_ERR || t == LVAL_HANDLE ||
      t == LVAL_REF) {
    return valk_evacuate_leaf(heap, v);
  }

  valk_evacuation_ctx_t ctx = {
    .scratch = scratch,
    .heap = heap,
    .values_copied = 0,
    .bytes_copied = 0,
    .pointers_fixed = 0,
  };
  evac_ctx_init(&ctx);

  valk_lval_t* new_val = valk_evacuate_value(&ctx, v);

  if (new_val && LVAL_TYPE(new_val) == LVAL_FUN &&
      new_val->fun.builtin == nullptr && new_val->fun.env != nullptr) {
    new_val->fun.env = valk_evacuate_env(&ctx, new_val->fun.env);
  }

  if (new_val != nullptr && new_val != v)
    evac_worklist_push(&ctx, new_val);

  while (ctx.worklist_count > 0) {
    valk_lval_t* val = evac_worklist_pop(&ctx);
    valk_evacuate_children(&ctx, val);
  }

  for (u64 i = 0; i < ctx.evacuated_count; i++) {
    valk_fix_pointers(&ctx, ctx.evacuated[i]);
  }

  evac_ctx_free(&ctx);

  return new_val;
}
// LCOV_EXCL_BR_STOP
