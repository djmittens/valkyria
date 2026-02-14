#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include "aio/aio.h"
#include <stdlib.h>
#include <string.h>

// ============================================================================
// Environment Worklist (iterative traversal)
// ============================================================================

// LCOV_EXCL_BR_START - worklist internal defensive checks and growth paths
#define ENV_WORKLIST_INITIAL_CAPACITY 64

typedef struct {
  valk_lenv_t** items;
  sz count;
  sz capacity;
} valk_env_worklist_t;

static void env_worklist_init(valk_env_worklist_t* wl) {
  wl->items = malloc(ENV_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lenv_t*));
  wl->count = 0;
  wl->capacity = ENV_WORKLIST_INITIAL_CAPACITY;
}

static void env_worklist_free(valk_env_worklist_t* wl) {
  if (wl->items) {
    free(wl->items);
    wl->items = nullptr;
  }
  wl->count = 0;
  wl->capacity = 0;
}

static void env_worklist_push(valk_env_worklist_t* wl, valk_lenv_t* env) {
  if (env == nullptr) return;
  if (wl->count >= wl->capacity) {
    sz new_cap = wl->capacity * 2;
    valk_lenv_t** new_items = realloc(wl->items, new_cap * sizeof(valk_lenv_t*));
    if (new_items == nullptr) {
      VALK_ERROR("Failed to grow env worklist");
      return;
    }
    wl->items = new_items;
    wl->capacity = new_cap;
  }
  wl->items[wl->count++] = env;
}

static valk_lenv_t* env_worklist_pop(valk_env_worklist_t* wl) {
  if (wl->count == 0) return nullptr;
  return wl->items[--wl->count];
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Evacuation Context Lifecycle
// ============================================================================

// LCOV_EXCL_BR_START - evacuation context internal defensive checks
#define EVAC_WORKLIST_INITIAL_CAPACITY 256

void evac_ctx_init(valk_evacuation_ctx_t* ctx) {
  ctx->worklist = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->worklist_count = 0;
  ctx->worklist_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;

  ctx->evacuated = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;

  valk_ptr_map_init(&ctx->ptr_map);
}

void evac_ctx_free(valk_evacuation_ctx_t* ctx) {
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

  // LCOV_EXCL_BR_START - evacuation list realloc OOM
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
  // LCOV_EXCL_BR_STOP

  ctx->evacuated[ctx->evacuated_count++] = v;
}

static void evac_worklist_push(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return; // LCOV_EXCL_BR_LINE

  // LCOV_EXCL_BR_START - worklist realloc OOM
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
  // LCOV_EXCL_BR_STOP

  ctx->worklist[ctx->worklist_count++] = v;
}

valk_lval_t* evac_worklist_pop(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist_count == 0) return nullptr; // LCOV_EXCL_BR_LINE
  return ctx->worklist[--ctx->worklist_count];
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Checkpoint Threshold Check
// ============================================================================

bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold) {
  if (scratch == nullptr) return false;
  return (float)scratch->offset / scratch->capacity > threshold;
}

// ============================================================================
// Value Evacuation (scratch -> heap)
// ============================================================================

valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);
void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);

// LCOV_EXCL_BR_START - evacuation value copy null checks and type dispatch
valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return nullptr;

  if (v->flags & LVAL_FLAG_IMMORTAL) return v;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) return v;

  void *existing = valk_ptr_map_get(&ctx->ptr_map, v);
  if (existing != nullptr) return (valk_lval_t *)existing;

  valk_lval_t* new_val = nullptr;
  VALK_WITH_ALLOC((void*)ctx->heap) {
    new_val = valk_mem_alloc(sizeof(valk_lval_t));
  }

  if (new_val == nullptr) {
    VALK_ERROR("Failed to allocate value during evacuation");
    return v;
  }

  valk_ptr_map_put(&ctx->ptr_map, v, new_val);

  memcpy(new_val, v, sizeof(valk_lval_t));
  new_val->flags = (new_val->flags & ~LVAL_ALLOC_MASK) | LVAL_ALLOC_HEAP;
  new_val->origin_allocator = ctx->heap;

  bool needs_string_copy = (ctx->scratch == nullptr);

  switch (LVAL_TYPE(new_val)) {
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      if (new_val->str != nullptr &&
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

void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
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
          valk_evacuate_env(ctx, v->fun.env);
        }
      }
      break;

    case LVAL_STR:
    case LVAL_SYM:
    case LVAL_ERR:
      if (v->str != nullptr &&
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

    default:
      break;
  }
}

// ============================================================================
// Environment Evacuation
// ============================================================================

static void valk_evacuate_env_single(valk_evacuation_ctx_t* ctx, valk_lenv_t* env,
                                     valk_env_worklist_t* env_worklist) {
  bool needs_array_copy = (ctx->scratch == nullptr);

  if (env->symbols.items != nullptr &&
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->symbols.items))) {
    u64 array_size = env->symbols.capacity * sizeof(char*);
    char** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_items = valk_mem_alloc(array_size);
    }
    if (new_items) {
      memcpy(new_items, env->symbols.items, env->symbols.count * sizeof(char*));
      env->symbols.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  if (env->symbols.items != nullptr) {
    for (u64 i = 0; i < env->symbols.count; i++) {
      char* sym = env->symbols.items[i];
      if (sym == nullptr) continue;

      u64 len = strlen(sym) + 1;
      char* new_str = nullptr;
      VALK_WITH_ALLOC((void*)ctx->heap) {
        new_str = valk_mem_alloc(len);
      }
      if (new_str && new_str != sym) {
        memcpy(new_str, sym, len);
        env->symbols.items[i] = new_str;
        ctx->bytes_copied += len;
      }
    }
  }

  if (env->vals.items != nullptr &&
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->vals.items))) {
    u64 array_size = env->vals.capacity * sizeof(valk_lval_t*);
    valk_lval_t** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_items = valk_mem_alloc(array_size);
    }
    if (new_items) {
      memcpy(new_items, env->vals.items, env->vals.count * sizeof(valk_lval_t*));
      env->vals.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  if (env->vals.items != nullptr) {
    for (u64 i = 0; i < env->vals.count; i++) {
      valk_lval_t* val = env->vals.items[i];
      if (val != nullptr) {
        valk_lval_t* new_val = valk_evacuate_value(ctx, val);
        if (new_val != val) {
          env->vals.items[i] = new_val;
          if (new_val != nullptr) evac_worklist_push(ctx, new_val);
        } else {
          if (val != nullptr && LVAL_TYPE(val) == LVAL_FUN &&
              val->fun.builtin == nullptr && val->fun.env != nullptr) {
            env_worklist_push(env_worklist, val->fun.env);
          }
        }
      }
    }
  }
}

void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == nullptr) return;

  valk_env_worklist_t worklist;
  env_worklist_init(&worklist);

  valk_env_worklist_t visited;
  env_worklist_init(&visited);

  env_worklist_push(&worklist, env);

  while (worklist.count > 0) {
    valk_lenv_t* current = env_worklist_pop(&worklist);
    if (current == nullptr) continue;

    bool already_visited = false;
    for (u64 i = 0; i < visited.count; i++) {
      if (visited.items[i] == current) {
        already_visited = true;
        break;
      }
    }
    if (already_visited) continue;

    env_worklist_push(&visited, current);
    valk_evacuate_env_single(ctx, current, &worklist);

    if (current->parent != nullptr) {
      env_worklist_push(&worklist, current->parent);
    }
  }

  env_worklist_free(&worklist);
  env_worklist_free(&visited);
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
    VALK_DEBUG("Fixing pointer via hashmap %p -> %p", (void*)val, new_loc);
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
void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;
  if (LVAL_ALLOC(v) == LVAL_ALLOC_SCRATCH) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
      fix_scratch_pointer(ctx, &v->cons.head);
      fix_scratch_pointer(ctx, &v->cons.tail);
      break;

    case LVAL_FUN:
      if (v->fun.builtin == nullptr) {
        fix_scratch_pointer(ctx, &v->fun.formals);
        fix_scratch_pointer(ctx, &v->fun.body);
        if (v->fun.env != nullptr) {
          valk_fix_env_pointers(ctx, v->fun.env);
        }
      }
      break;

    default:
      break;
  }
}

static void valk_fix_env_pointers_single(valk_evacuation_ctx_t* ctx, valk_lenv_t* env,
                                         valk_env_worklist_t* env_worklist) {
  bool needs_array_copy = (ctx->scratch == nullptr);

  if (env->symbols.items != nullptr &&
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->symbols.items))) {
    u64 array_size = env->symbols.capacity * sizeof(char*);
    char** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) { new_items = valk_mem_alloc(array_size); }
    if (new_items) {
      if (env->symbols.count > 0) {
        memcpy(new_items, env->symbols.items, env->symbols.count * sizeof(char*));
      }
      env->symbols.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  if (env->symbols.items != nullptr) {
    for (u64 i = 0; i < env->symbols.count; i++) {
      if (env->symbols.items[i] &&
          (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->symbols.items[i]))) {
        u64 len = strlen(env->symbols.items[i]) + 1;
        char* new_str = nullptr;
        VALK_WITH_ALLOC((void*)ctx->heap) { new_str = valk_mem_alloc(len); }
        if (new_str) {
          memcpy(new_str, env->symbols.items[i], len);
          env->symbols.items[i] = new_str;
          ctx->bytes_copied += len;
        }
      }
    }
  }

  if (env->vals.items != nullptr &&
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->vals.items))) {
    u64 array_size = env->vals.capacity * sizeof(valk_lval_t*);
    valk_lval_t** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) { new_items = valk_mem_alloc(array_size); }
    if (new_items) {
      if (env->vals.count > 0) {
        memcpy(new_items, env->vals.items, env->vals.count * sizeof(valk_lval_t*));
      }
      env->vals.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  if (env->vals.items != nullptr) {
    for (u64 i = 0; i < env->vals.count; i++) {
      fix_scratch_pointer(ctx, &env->vals.items[i]);
      valk_lval_t* val = env->vals.items[i];
      if (val != nullptr && LVAL_TYPE(val) == LVAL_FUN &&
          val->fun.builtin == nullptr && val->fun.env != nullptr) {
        env_worklist_push(env_worklist, val->fun.env);
      }
    }
  }
}

void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == nullptr) return;

  valk_env_worklist_t worklist;
  env_worklist_init(&worklist);

  valk_env_worklist_t visited;
  env_worklist_init(&visited);

  env_worklist_push(&worklist, env);

  while (worklist.count > 0) {
    valk_lenv_t* current = env_worklist_pop(&worklist);
    if (current == nullptr) continue;

    bool already_visited = false;
    for (u64 i = 0; i < visited.count; i++) {
      if (visited.items[i] == current) {
        already_visited = true;
        break;
      }
    }
    if (already_visited) continue;

    env_worklist_push(&visited, current);
    valk_fix_env_pointers_single(ctx, current, &worklist);

    if (current->parent != nullptr) {
      env_worklist_push(&worklist, current->parent);
    }
  }

  env_worklist_free(&worklist);
  env_worklist_free(&visited);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Single-Value Evacuation (no STW)
// ============================================================================

// LCOV_EXCL_BR_START - evacuation to heap: heap fallback and lambda env dispatch
valk_lval_t* valk_evacuate_to_heap(valk_lval_t* v) {
  if (v == nullptr) return nullptr;
  if (LVAL_ALLOC(v) == LVAL_ALLOC_HEAP) return v;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) return v;

  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  valk_gc_heap_t* heap = valk_thread_ctx.heap;

  if (!heap && valk_sys) heap = valk_sys->heap;

  if (!heap) {
    VALK_ERROR("valk_evacuate_to_heap: no heap available (scratch=%p, heap=%p, v alloc=%u)",
               (void*)scratch, (void*)heap, LVAL_ALLOC(v));
    return v;
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
    valk_evacuate_env(&ctx, new_val->fun.env);
  }

  while (ctx.worklist_count > 0) {
    valk_lval_t* val = evac_worklist_pop(&ctx);
    valk_evacuate_children(&ctx, val);
  }

  for (u64 i = 0; i < ctx.evacuated_count; i++) {
    valk_fix_pointers(&ctx, ctx.evacuated[i]);
  }

  if (new_val != nullptr && new_val != v && LVAL_TYPE(new_val) == LVAL_FUN &&
      new_val->fun.builtin == nullptr && new_val->fun.env != nullptr) {
    valk_fix_env_pointers(&ctx, new_val->fun.env);
  }

  evac_ctx_free(&ctx);

  return new_val;
}
// LCOV_EXCL_BR_STOP
