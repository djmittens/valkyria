#include "parser.h"

#include <string.h>

#include "builtins_internal.h"
#include "common.h"
#include "gc.h"
#include "log.h"
#include "memory.h"

extern valk_eval_metrics_t g_eval_metrics;

static void valk_lenv_init(valk_lenv_t* env);

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
      if (LVAL_TYPE(lval) == LVAL_SYM || LVAL_TYPE(lval) == LVAL_STR ||
          LVAL_TYPE(lval) == LVAL_ERR) {
        if (lval->str) free(lval->str);
      }
      free(lval);
    }
  }
  if (env->symbols.items) free(env->symbols.items);
  if (env->vals.items) free(env->vals.items);
  free(env);
}

valk_lenv_t* valk_lenv_copy(valk_lenv_t* env) {
  if (env == nullptr) {
    return nullptr;
  }
  if (env->symbols.items == nullptr || env->vals.items == nullptr) {
    return nullptr;
  }

  valk_lenv_t* res = valk_mem_alloc(sizeof(valk_lenv_t));
  atomic_store(&res->flags, 0);
  res->parent = nullptr;
  res->allocator = valk_thread_ctx.allocator;
  
  u64 capacity = 16;
  u64 count = 0;
  res->symbols.items = valk_mem_alloc(sizeof(char*) * capacity);
  res->vals.items = valk_mem_alloc(sizeof(valk_lval_t*) * capacity);
  res->symbols.capacity = capacity;
  res->vals.capacity = capacity;

  for (valk_lenv_t* e = env; e != nullptr; e = e->parent) {
    if (e->symbols.items == nullptr || e->vals.items == nullptr) break;
    for (u64 i = 0; i < e->symbols.count; i++) {
      if (e->symbols.items[i] == nullptr) continue;
      
      bool masked = false;
      for (u64 j = 0; j < count; j++) {
        if (res->symbols.items[j] && strcmp(e->symbols.items[i], res->symbols.items[j]) == 0) {
          masked = true;
          break;
        }
      }
      
      if (!masked) {
        if (count >= capacity) {
          u64 new_capacity = capacity * 2;
          char** new_symbols = valk_mem_alloc(sizeof(char*) * new_capacity);
          valk_lval_t** new_vals = valk_mem_alloc(sizeof(valk_lval_t*) * new_capacity);
          memcpy(new_symbols, res->symbols.items, sizeof(char*) * count);
          memcpy(new_vals, res->vals.items, sizeof(valk_lval_t*) * count);
          res->symbols.items = new_symbols;
          res->vals.items = new_vals;
          capacity = new_capacity;
          res->symbols.capacity = capacity;
          res->vals.capacity = capacity;
        }
        
        u64 slen = strlen(e->symbols.items[i]);
        res->symbols.items[count] = valk_mem_alloc(slen + 1);
        memcpy(res->symbols.items[count], e->symbols.items[i], slen + 1);
        res->vals.items[count] = e->vals.items[i];
        count++;
      }
    }
  }

  res->symbols.count = count;
  res->vals.count = count;
  return res;
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
    for (u64 i = 0; i < env->symbols.count; i++) {
      if (strcmp(key->str, env->symbols.items[i]) == 0) {
        if (valk_log_would_log(VALK_LOG_TRACE)) {
          VALK_TRACE("env get idx=%zu key=%s", i, env->symbols.items[i]);
        }
        return env->vals.items[i];
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

  void *val_alloc = val->origin_allocator;
  if (!val_alloc) return val;

  if (valk_region_write_barrier(env_alloc, val_alloc, false)) {
    return val;
  }

  valk_mem_allocator_t *alloc = (valk_mem_allocator_t *)env_alloc;
  if (alloc->type == VALK_ALLOC_REGION) {
    return valk_region_promote_lval((valk_region_t *)env_alloc, val);
  }

  return val;
}
// LCOV_EXCL_BR_STOP

void valk_lenv_put(valk_lenv_t* env, valk_lval_t* key, valk_lval_t* val) {
  if (valk_log_would_log(VALK_LOG_DEBUG)) {
    VALK_DEBUG("env put: %s", key->str);
  }
  valk_lval_t* safe_val = __lenv_ensure_safe_val(env, val);

  for (u64 i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items == NULL || env->symbols.items[i] == NULL) {  // LCOV_EXCL_BR_LINE - defensive check
      break;
    }
    if (strcmp(key->str, env->symbols.items[i]) == 0) {
      env->vals.items[i] = safe_val;
      return;
    }
  }

  // LCOV_EXCL_BR_START - allocator selection logic
  valk_mem_allocator_t *env_alloc;
  if (valk_thread_ctx.heap != NULL) {
    env_alloc = valk_thread_ctx.heap;
  } else if (env->allocator != NULL) {
    env_alloc = (valk_mem_allocator_t*)env->allocator;
  } else {
    env_alloc = valk_thread_ctx.allocator;
  }
  // LCOV_EXCL_BR_STOP
  
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

void valk_lenv_def(valk_lenv_t* env, valk_lval_t* key, valk_lval_t* val) {
  while (env->parent) {
    env = env->parent;
  }
  valk_lenv_put(env, key, val);
}

void valk_lenv_put_builtin(valk_lenv_t* env, char* key,
                           valk_lval_builtin_t* _fun) {
  VALK_INFO("install builtin: %s (count=%zu)", key, env->symbols.count);
  VALK_WITH_ALLOC(env->allocator) {
    valk_lval_t* lfun = valk_mem_alloc(sizeof(valk_lval_t));
    lfun->flags =
        LVAL_FUN | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
    VALK_SET_ORIGIN_ALLOCATOR(lfun);
    lfun->fun.builtin = _fun;
    lfun->fun.env = nullptr;
    valk_lval_set_immortal(lfun);
    valk_lval_t* sym = valk_lval_sym(key);
    valk_lenv_put(env, sym, lfun);
    valk_mem_free(sym->str);
    valk_mem_free(sym);
  }
}
