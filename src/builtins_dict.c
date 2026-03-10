#include "builtins_internal.h"
#include "gc.h"
#include <string.h>

typedef struct {
  char **keys;
  valk_lval_t **values;
  u64 count;
  u64 capacity;
} valk_dict_t;

#define DICT_INITIAL_CAPACITY 16
#define DICT_LOAD_FACTOR_PCT 75

static inline u64 dict_hash(const char *key) {
  u64 h = 0xcbf29ce484222325ULL;
  for (const unsigned char *p = (const unsigned char *)key; *p; p++) {
    h ^= *p;
    h *= 0x100000001b3ULL;
  }
  return h;
}

static valk_dict_t *dict_alloc(u64 capacity) {
  valk_dict_t *d = valk_mem_calloc(1, sizeof(valk_dict_t));
  d->capacity = capacity;
  d->count = 0;
  d->keys = valk_mem_calloc(capacity, sizeof(char *));
  d->values = valk_mem_calloc(capacity, sizeof(valk_lval_t *));
  return d;
}

static void dict_mark_fn(void *ptr, void *gc_ctx) {
  valk_dict_t *d = ptr;
  if (!d) return; // LCOV_EXCL_LINE
  valk_gc_mark_ctx_t *ctx = gc_ctx;
  for (u64 i = 0; i < d->capacity; i++) {
    if (d->values[i] != nullptr)
      valk_gc_heap_mark_object(ctx, d->values[i]);
  }
}

static void dict_evacuate_fn(void **ptr_ref, void *evac_ctx) {
  valk_dict_t *d = *ptr_ref;
  if (!d) return;
  valk_evacuation_ctx_t *ctx = evac_ctx;
  bool in_scratch = ctx->scratch && valk_ptr_in_arena(ctx->scratch, d);

  if (in_scratch) {
    valk_dict_t *nd;
    VALK_WITH_ALLOC((void *)ctx->heap) {
      nd = valk_mem_calloc(1, sizeof(valk_dict_t));
      nd->capacity = d->capacity;
      nd->count = d->count;
      nd->keys = valk_mem_calloc(d->capacity, sizeof(char *));
      nd->values = valk_mem_calloc(d->capacity, sizeof(valk_lval_t *));
      for (u64 i = 0; i < d->capacity; i++) {
        if (d->keys[i]) {
          u64 len = strlen(d->keys[i]) + 1;
          nd->keys[i] = valk_mem_alloc(len);
          memcpy(nd->keys[i], d->keys[i], len);
        }
      }
    }
    memcpy(nd->values, d->values, d->capacity * sizeof(valk_lval_t *));
    *ptr_ref = nd;
    d = nd;
    ctx->bytes_copied += sizeof(valk_dict_t) + d->capacity * (sizeof(char *) + sizeof(valk_lval_t *));
  }

  for (u64 i = 0; i < d->capacity; i++) {
    if (d->values[i] != nullptr) {
      valk_lval_t *old_val = d->values[i];
      valk_lval_t *new_val = valk_evacuate_value(ctx, old_val);
      if (new_val != old_val) {
        d->values[i] = new_val;
        if (new_val != nullptr) valk_evac_worklist_push(ctx, new_val);
      }
    }
  }
}


static void dict_grow(valk_dict_t *d) {
  u64 new_cap = d->capacity * 2;
  char **new_keys = valk_mem_calloc(new_cap, sizeof(char *));
  valk_lval_t **new_values = valk_mem_calloc(new_cap, sizeof(valk_lval_t *));
  u64 mask = new_cap - 1;

  for (u64 i = 0; i < d->capacity; i++) {
    if (d->keys[i] != NULL) {
      u64 idx = dict_hash(d->keys[i]) & mask;
      while (new_keys[idx] != NULL)
        idx = (idx + 1) & mask;
      new_keys[idx] = d->keys[i];
      new_values[idx] = d->values[i];
    }
  }

  valk_mem_free(d->keys);
  valk_mem_free(d->values);
  d->keys = new_keys;
  d->values = new_values;
  d->capacity = new_cap;
}

static bool dict_put(valk_dict_t *d, const char *key) {
  if (d->count * 100 >= d->capacity * DICT_LOAD_FACTOR_PCT)
    dict_grow(d);

  u64 mask = d->capacity - 1;
  u64 idx = dict_hash(key) & mask;

  for (u64 i = 0; i < d->capacity; i++) {
    u64 slot = (idx + i) & mask;
    if (d->keys[slot] == NULL) {
      u64 len = strlen(key);
      d->keys[slot] = valk_mem_alloc(len + 1);
      memcpy(d->keys[slot], key, len + 1);
      d->count++;
      return true;
    }
    if (strcmp(d->keys[slot], key) == 0)
      return false;
  }
  return false;
}

static void dict_set(valk_dict_t *d, const char *key, valk_lval_t *value) {
  if (d->count * 100 >= d->capacity * DICT_LOAD_FACTOR_PCT)
    dict_grow(d);

  u64 mask = d->capacity - 1;
  u64 idx = dict_hash(key) & mask;

  for (u64 i = 0; i < d->capacity; i++) {
    u64 slot = (idx + i) & mask;
    if (d->keys[slot] == NULL) {
      u64 len = strlen(key);
      d->keys[slot] = valk_mem_alloc(len + 1);
      memcpy(d->keys[slot], key, len + 1);
      d->values[slot] = value;
      d->count++;
      return;
    }
    if (strcmp(d->keys[slot], key) == 0) {
      d->values[slot] = value;
      return;
    }
  }
}

static valk_lval_t *dict_get(valk_dict_t *d, const char *key) {
  u64 mask = d->capacity - 1;
  u64 idx = dict_hash(key) & mask;

  for (u64 i = 0; i < d->capacity; i++) {
    u64 slot = (idx + i) & mask;
    if (d->keys[slot] == NULL) return nullptr;
    if (strcmp(d->keys[slot], key) == 0) return d->values[slot];
  }
  return nullptr;
}

static bool dict_has(valk_dict_t *d, const char *key) {
  u64 mask = d->capacity - 1;
  u64 idx = dict_hash(key) & mask;

  for (u64 i = 0; i < d->capacity; i++) {
    u64 slot = (idx + i) & mask;
    if (d->keys[slot] == NULL) return false;
    if (strcmp(d->keys[slot], key) == 0) return true;
  }
  return false;
}

static bool dict_remove(valk_dict_t *d, const char *key) {
  u64 mask = d->capacity - 1;
  u64 idx = dict_hash(key) & mask;

  for (u64 i = 0; i < d->capacity; i++) {
    u64 slot = (idx + i) & mask;
    if (d->keys[slot] == NULL) return false;
    if (strcmp(d->keys[slot], key) == 0) {
      valk_mem_free(d->keys[slot]);
      d->keys[slot] = NULL;
      d->values[slot] = nullptr;
      d->count--;

      u64 j = (slot + 1) & mask;
      while (d->keys[j] != NULL) {
        char *rkey = d->keys[j];
        valk_lval_t *rval = d->values[j];
        d->keys[j] = NULL;
        d->values[j] = nullptr;
        d->count--;

        u64 ridx = dict_hash(rkey) & mask;
        while (d->keys[ridx] != NULL)
          ridx = (ridx + 1) & mask;
        d->keys[ridx] = rkey;
        d->values[ridx] = rval;
        d->count++;

        j = (j + 1) & mask;
      }
      return true;
    }
  }
  return false;
}

static inline const char *dict_key_str(valk_lval_t *v) {
  if (LVAL_TYPE(v) == LVAL_STR) return v->str;
  if (LVAL_TYPE(v) == LVAL_SYM) return v->str;
  return NULL;
}

#define DICT_ASSERT_REF(args, v) \
  LVAL_ASSERT_TYPE(args, v, LVAL_REF); \
  LVAL_ASSERT(args, strcmp(v->ref.type, "dict") == 0, \
              "Expected dict, got ref<%s>", v->ref.type)

static valk_lval_t *dict_make_ref(valk_dict_t *d) {
  valk_lval_t *ref = valk_lval_ref("dict", d, nullptr);
  ref->ref.mark = dict_mark_fn;
  ref->ref.evacuate = dict_evacuate_fn;
  ref->ref.retain = nullptr;
  return ref;
}

static valk_lval_t *valk_builtin_dict_new(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  u64 n = valk_lval_list_count(a);
  LVAL_ASSERT(a, n <= 1, "dict/new takes 0 or 1 arguments, got %zu", n);

  u64 cap = DICT_INITIAL_CAPACITY;
  if (n == 1) {
    valk_lval_t *hint = valk_lval_list_nth(a, 0);
    LVAL_ASSERT_TYPE(a, hint, LVAL_NUM);
    u64 want = (u64)hint->num;
    while (cap * DICT_LOAD_FACTOR_PCT / 100 < want)
      cap *= 2;
  }

  return dict_make_ref(dict_alloc(cap));
}

static valk_lval_t *valk_builtin_dict_put(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT_REF(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/put! key must be String or Symbol");

  dict_put(d->ref.ptr, k);
  return d;
}

static valk_lval_t *valk_builtin_dict_set(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  valk_lval_t *val = valk_lval_list_nth(a, 2);
  DICT_ASSERT_REF(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/set! key must be String or Symbol");

  dict_set(d->ref.ptr, k, val);
  return d;
}

static valk_lval_t *valk_builtin_dict_get(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  u64 n = valk_lval_list_count(a);
  LVAL_ASSERT(a, n == 2 || n == 3,
              "dict/get takes 2 or 3 arguments, got %zu", n);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT_REF(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/get key must be String or Symbol");

  valk_lval_t *result = dict_get(d->ref.ptr, k);
  if (result != nullptr) return result;

  if (n == 3) return valk_lval_list_nth(a, 2);
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_dict_remove(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT_REF(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/remove! key must be String or Symbol");

  dict_remove(d->ref.ptr, k);
  return d;
}

static valk_lval_t *valk_builtin_dict_has(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT_REF(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/has? key must be String or Symbol");

  return valk_lval_num(dict_has(d->ref.ptr, k) ? 1 : 0);
}

static valk_lval_t *valk_builtin_dict_from_keys(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *list = valk_lval_list_nth(a, 0);

  u64 count = valk_lval_list_count(list);
  u64 cap = DICT_INITIAL_CAPACITY;
  while (cap * DICT_LOAD_FACTOR_PCT / 100 < count)
    cap *= 2;

  valk_dict_t *d = dict_alloc(cap);

  valk_lval_t *curr = list;
  while (curr && !valk_lval_list_is_empty(curr)) {
    valk_lval_t *item = curr->cons.head;
    const char *k = item ? dict_key_str(item) : NULL;
    if (k) dict_put(d, k);
    curr = curr->cons.tail;
  }

  return dict_make_ref(d);
}

static valk_lval_t *valk_builtin_dict_count(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  DICT_ASSERT_REF(a, d);

  return valk_lval_num((long)((valk_dict_t *)d->ref.ptr)->count);
}

static valk_lval_t *valk_builtin_dict_keys(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d_ref = valk_lval_list_nth(a, 0);
  DICT_ASSERT_REF(a, d_ref);

  valk_dict_t *d = d_ref->ref.ptr;
  valk_lval_t *result = valk_lval_nil();

  for (u64 i = d->capacity; i > 0; i--) {
    if (d->keys[i - 1] != NULL)
      result = valk_lval_qcons(valk_lval_str(d->keys[i - 1]), result);
  }

  return result;
}

static valk_lval_t *valk_builtin_dict_values(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d_ref = valk_lval_list_nth(a, 0);
  DICT_ASSERT_REF(a, d_ref);

  valk_dict_t *d = d_ref->ref.ptr;
  valk_lval_t *result = valk_lval_nil();

  for (u64 i = d->capacity; i > 0; i--) {
    if (d->keys[i - 1] != NULL) {
      valk_lval_t *v = d->values[i - 1];
      result = valk_lval_qcons(v ? v : valk_lval_nil(), result);
    }
  }

  return result;
}

static valk_lval_t *valk_builtin_dict_entries(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d_ref = valk_lval_list_nth(a, 0);
  DICT_ASSERT_REF(a, d_ref);

  valk_dict_t *d = d_ref->ref.ptr;
  valk_lval_t *result = valk_lval_nil();

  for (u64 i = d->capacity; i > 0; i--) {
    if (d->keys[i - 1] != NULL) {
      valk_lval_t *v = d->values[i - 1];
      valk_lval_t *pair = valk_lval_qcons(
          valk_lval_str(d->keys[i - 1]),
          valk_lval_qcons(v ? v : valk_lval_nil(), valk_lval_nil()));
      result = valk_lval_qcons(pair, result);
    }
  }

  return result;
}

void valk_register_dict_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "dict/new", valk_builtin_dict_new);
  valk_lenv_put_builtin(env, "dict/put!", valk_builtin_dict_put);
  valk_lenv_put_builtin(env, "dict/set!", valk_builtin_dict_set);
  valk_lenv_put_builtin(env, "dict/get", valk_builtin_dict_get);
  valk_lenv_put_builtin(env, "dict/remove!", valk_builtin_dict_remove);
  valk_lenv_put_builtin(env, "dict/has?", valk_builtin_dict_has);
  valk_lenv_put_builtin(env, "dict/from-keys", valk_builtin_dict_from_keys);
  valk_lenv_put_builtin(env, "dict/count", valk_builtin_dict_count);
  valk_lenv_put_builtin(env, "dict/keys", valk_builtin_dict_keys);
  valk_lenv_put_builtin(env, "dict/values", valk_builtin_dict_values);
  valk_lenv_put_builtin(env, "dict/entries", valk_builtin_dict_entries);
}
