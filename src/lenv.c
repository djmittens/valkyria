#include "parser.h"

#include <string.h>

#include "builtins_internal.h"
#include "common.h"
#include "conc_map.h"
#include "gc.h"
#include "log.h"
#include "memory.h"

extern valk_eval_metrics_t g_eval_metrics;

static void valk_lenv_init(valk_lenv_t* env);

// Promote `env` to use a concurrent hash map for its bindings. Used for the
// shared global/root env, which is read on every symbol resolution and
// mutated concurrently by the LSP's worker threads. Idempotent.
void valk_lenv_make_concurrent(valk_lenv_t* env) {
  if (!env || env->cmap) return;
  void* alloc = env->allocator ? env->allocator : valk_thread_ctx.allocator;
  valk_cmap_t* m = valk_cmap_new(alloc, 1024);
  // Migrate any existing linear bindings into the map.
  for (u64 i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items[i] == nullptr) continue;
    valk_cmap_put(m, env->symbols.items[i], env->vals.items[i]);
  }
  env->cmap = m;
}

valk_lenv_t* valk_lenv_empty(void) {
  valk_lenv_t* res;
  if (valk_thread_ctx.heap != NULL) {
    res = valk_gc_heap_alloc(valk_thread_ctx.heap, sizeof(valk_lenv_t));
  } else {
    res = valk_mem_alloc(sizeof(valk_lenv_t));
  }
  memset(res, 0, sizeof(valk_lenv_t));
  valk_lenv_init(res);

  if (valk_thread_ctx.heap != NULL) {
    res->allocator = valk_thread_ctx.heap;
  }
  return res;
}

static void valk_lenv_init(valk_lenv_t* env) {
  env->parent = nullptr;
  env->symbols.count = 0;
  env->symbols.capacity = 0;
  env->symbols.items = nullptr;
  env->vals.count = 0;
  env->vals.capacity = 0;
  env->vals.items = nullptr;
  env->allocator = valk_thread_ctx.allocator;
  env->cmap = nullptr;
}

// LCOV_EXCL_BR_START - env free/copy have defensive null checks for internal consistency
void valk_lenv_free(valk_lenv_t* env) {
  if (!env) return;
  valk_mem_allocator_t* alloc = (valk_mem_allocator_t*)env->allocator;
  if (alloc && alloc->type != VALK_ALLOC_MALLOC) return;

  for (u64 i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items && env->symbols.items[i]) {
      free(env->symbols.items[i]);
    }
    if (env->vals.items && env->vals.items[i]) {
      valk_lval_t* lval = env->vals.items[i];
      if (!valk_lval_is_immortal(lval)) {
        if (LVAL_TYPE(lval) == LVAL_SYM || LVAL_TYPE(lval) == LVAL_STR ||
            LVAL_TYPE(lval) == LVAL_ERR) {
          if (lval->str && !(lval->flags & LVAL_FLAG_INTERNED)) free(lval->str);
        }
        free(lval);
      }
    }
  }
  if (env->symbols.items) free(env->symbols.items);
  if (env->vals.items) free(env->vals.items);
  free(env);
}

// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - env lookup has defensive null checks for internal consistency
valk_lval_t* valk_lenv_get(valk_lenv_t* env, valk_lval_t* key) {
  atomic_fetch_add(&g_eval_metrics.env_lookups, 1);

  if (env == NULL) {
    return valk_lval_err("LEnv: Cannot lookup `%s` in NULL environment", key->str);
  }

  if (LVAL_TYPE(key) != LVAL_SYM) {
    return valk_lval_err("LEnv: Expected symbol for lookup, got %s", valk_ltype_name(LVAL_TYPE(key)));
  }

  while (env) {
    if (env->cmap) {
      // Concurrent (shared global) env: lock-free hash lookup.
      valk_lval_t* v = valk_cmap_get((valk_cmap_t*)env->cmap, key->str);
      if (v != nullptr) return v;
    } else {
      for (u64 i = 0; i < env->symbols.count; i++) {
        if (strcmp(key->str, env->symbols.items[i]) == 0) {
          if (valk_log_would_log(VALK_LOG_TRACE)) {
            VALK_TRACE("env get idx=%zu key=%s", i, env->symbols.items[i]);
          }
          return env->vals.items[i];
        }
      }
    }
    env = env->parent;
  }

  return valk_lval_err("LEnv: Symbol `%s` is not bound", key->str);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - write barrier logic has many internal branches
static valk_lval_t* __lenv_ensure_safe_val(valk_lenv_t* env, valk_lval_t* val) {
  if (!val) return val;

  void *env_alloc = env->allocator;
  if (!env_alloc && valk_thread_ctx.heap) {
    env_alloc = valk_thread_ctx.heap;
  }
  if (!env_alloc) return val;

  valk_lifetime_e env_lt = valk_allocator_lifetime(env_alloc);
  valk_lifetime_e val_lt = valk_lval_alloc_lifetime(val);

  if (valk_lifetime_can_reference(env_lt, val_lt)) {
    return val;
  }

  if (LVAL_ALLOC(val) == LVAL_ALLOC_SCRATCH) {
    return valk_evacuate_to_heap(val);
  }

  return val;
}
// LCOV_EXCL_BR_STOP

void valk_lenv_put(valk_lenv_t* env, valk_lval_t* key, valk_lval_t* val) {
  if (valk_log_would_log(VALK_LOG_DEBUG)) {
    VALK_DEBUG("env put: %s", key->str);
  }
  valk_lval_t* safe_val = __lenv_ensure_safe_val(env, val);

  // INVARIANT: envs binding GC-heap values must live in GC-managed memory.
  // The marker cannot walk an env block in malloc/foreign memory (mark_env
  // stops there — no mark bit for dedup, unbounded recursion on cyclic
  // closures), so a heap value bound in one is collected while live and
  // corrupts silently at the next collection. Fail loudly at the write
  // instead. Event-loop threads must eval under the scratch discipline
  // (__run_task_in_scratch, pipe read callbacks) to keep this invariant.
  {
    valk_mem_allocator_t *ea = (valk_mem_allocator_t *)env->allocator;
    if (ea && ea->type == VALK_ALLOC_MALLOC && safe_val &&
        LVAL_ALLOC(safe_val) == LVAL_ALLOC_HEAP &&
        !(safe_val->flags & LVAL_FLAG_IMMORTAL) &&
        valk_thread_ctx.heap != NULL) {
      VALK_ASSERT(false,
                  "GC-heap value '%s' bound into malloc-backed env %p — "
                  "unmarkable, will be collected while live",
                  key->str ? key->str : "?", (void *)env);
    }
  }

  if (env->cmap) {
    // Concurrent (shared global) env: striped-lock map handles overwrite,
    // growth, and cross-thread visibility.
    valk_cmap_put((valk_cmap_t*)env->cmap, key->str, safe_val);
    return;
  }

  for (u64 i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items == NULL || env->symbols.items[i] == NULL) {  // LCOV_EXCL_BR_LINE - defensive check
      break;
    }
    if (strcmp(key->str, env->symbols.items[i]) == 0) {
      env->vals.items[i] = safe_val;
      return;
    }
  }

  valk_mem_allocator_t *env_alloc;
  if (valk_thread_ctx.heap != NULL) {
    env_alloc = valk_thread_ctx.heap;
  } else if (env->allocator != NULL) {
    env_alloc = (valk_mem_allocator_t*)env->allocator;
  } else {
    env_alloc = valk_thread_ctx.allocator;
  }

  VALK_WITH_ALLOC(env_alloc) {
    u64 slen = strlen(key->str);
    char* new_symbol = valk_mem_alloc(slen + 1);
    // LCOV_EXCL_START - memory allocation never fails in practice
    if (!new_symbol) {
      VALK_RAISE("valk_lenv_put: failed to allocate symbol string for '%s'", key->str);
      return;
    }
    // LCOV_EXCL_STOP
    memcpy(new_symbol, key->str, slen + 1);

    if (env->symbols.count >= env->symbols.capacity) {
      u64 new_capacity =
          env->symbols.capacity == 0 ? 8 : env->symbols.capacity * 2;
      char** new_items = valk_mem_alloc(sizeof(char*) * new_capacity);
      // LCOV_EXCL_START - memory allocation never fails in practice
      if (!new_items) {
        valk_mem_free(new_symbol);
        VALK_RAISE("valk_lenv_put: failed to allocate symbols array (capacity=%llu)", new_capacity);
        return;
      }
      // LCOV_EXCL_STOP
      if (env->symbols.count > 0) {
        memcpy(new_items, env->symbols.items, sizeof(char*) * env->symbols.count);
      }
      if (env->symbols.items) valk_mem_free(env->symbols.items);
      env->symbols.items = new_items;
      env->symbols.capacity = new_capacity;
    }
    if (env->vals.count >= env->vals.capacity) {
      u64 new_capacity = env->vals.capacity == 0 ? 8 : env->vals.capacity * 2;
      valk_lval_t** new_items =
          valk_mem_alloc(sizeof(valk_lval_t*) * new_capacity);
      // LCOV_EXCL_START - memory allocation never fails in practice
      if (!new_items) {
        valk_mem_free(new_symbol);
        VALK_RAISE("valk_lenv_put: failed to allocate vals array (capacity=%llu)", new_capacity);
        return;
      }
      // LCOV_EXCL_STOP
      if (env->vals.count > 0) {
        memcpy(new_items, env->vals.items,
               sizeof(valk_lval_t*) * env->vals.count);
      }
      if (env->vals.items) valk_mem_free(env->vals.items);
      env->vals.items = new_items;
      env->vals.capacity = new_capacity;
    }

    env->symbols.items[env->symbols.count++] = new_symbol;
    env->vals.items[env->vals.count++] = safe_val;
  }
}

typedef struct {
  char** names;
  valk_lval_t** vals;
  u64 count;
} lenv_snapshot_t;

static void lenv_snapshot_cb(char* key, _Atomic(valk_lval_t*)* slot, void* ctx) {
  lenv_snapshot_t* s = ctx;
  s->names[s->count] = key;
  s->vals[s->count] = atomic_load(slot);
  s->count++;
}

u64 valk_lenv_snapshot(valk_lenv_t* env, char*** out_names,
                       valk_lval_t*** out_vals) {
  if (env->cmap) {
    u64 cap = valk_cmap_count((valk_cmap_t*)env->cmap);
    lenv_snapshot_t s = {0};
    s.names = malloc(sizeof(char*) * (cap ? cap : 1));
    s.vals = malloc(sizeof(valk_lval_t*) * (cap ? cap : 1));
    valk_cmap_foreach((valk_cmap_t*)env->cmap, lenv_snapshot_cb, &s);
    *out_names = s.names;
    *out_vals = s.vals;
    return s.count;
  }
  u64 n = env->symbols.count;
  char** names = malloc(sizeof(char*) * (n ? n : 1));
  valk_lval_t** vals = malloc(sizeof(valk_lval_t*) * (n ? n : 1));
  for (u64 i = 0; i < n; i++) {
    names[i] = env->symbols.items[i];
    vals[i] = env->vals.items[i];
  }
  *out_names = names;
  *out_vals = vals;
  return n;
}

void valk_lenv_def(valk_lenv_t* env, valk_lval_t* key, valk_lval_t* val) {
  // Walk up to the outermost mutable env, stopping before any frozen
  // ancestor (e.g. an image-loaded env).
  while (env->parent) {
    if (atomic_load(&env->parent->flags) & LENV_FLAG_FROZEN) break;
    env = env->parent;
  }
  if (atomic_load(&env->flags) & LENV_FLAG_FROZEN) {
    VALK_RAISE("valk_lenv_def: refused write to frozen env (key='%s')",
               key && key->str ? key->str : "?");
    return;
  }
  if (val && LVAL_ALLOC(val) == LVAL_ALLOC_SCRATCH)
    val = valk_evacuate_to_heap(val);
  valk_lenv_put(env, key, val);
}

static void put_builtin_impl(valk_lenv_t* env, char* key,
                              valk_lval_builtin_t* _fun, u64 extra_flags) {
  VALK_INFO("install builtin: %s (count=%zu)", key, env->symbols.count);
  VALK_WITH_ALLOC(env->allocator) {
    valk_lval_t* lfun = valk_mem_alloc(sizeof(valk_lval_t));
    lfun->flags = LVAL_FUN |
        valk_alloc_flags_from_allocator(valk_thread_ctx.allocator) |
        extra_flags;
    VALK_SET_ORIGIN_ALLOCATOR(lfun);
    lfun->fun.builtin = _fun;
    lfun->fun.env = nullptr;
    lfun->fun.formals = nullptr;
    lfun->fun.body = nullptr;
    lfun->fun.arity = 0;
    lfun->fun.native_fn = nullptr;
    lfun->fun.native_name = nullptr;
    u64 klen = strlen(key) + 1;
    lfun->fun.name = valk_mem_alloc(klen);
    memcpy(lfun->fun.name, key, klen);
    valk_lval_set_immortal(lfun);
    valk_lval_t* sym = valk_lval_sym(key);
    valk_lenv_put(env, sym, lfun);
    valk_mem_free(sym);
  }
}

void valk_lenv_put_builtin(valk_lenv_t* env, char* key,
                           valk_lval_builtin_t* _fun) {
  put_builtin_impl(env, key, _fun, 0);
}

void valk_lenv_put_builtin_err_ok(valk_lenv_t* env, char* key,
                                   valk_lval_builtin_t* _fun) {
  put_builtin_impl(env, key, _fun, LVAL_FLAG_ACCEPTS_ERR);
}
