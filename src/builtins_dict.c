#include "builtins_internal.h"
#include <string.h>
#include <stdlib.h>

typedef struct {
  char **keys;
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
  valk_dict_t *d = calloc(1, sizeof(valk_dict_t));
  d->capacity = capacity;
  d->count = 0;
  d->keys = calloc(capacity, sizeof(char *));
  return d;
}

static void dict_free_fn(void *ptr) { // LCOV_EXCL_START
  valk_dict_t *d = ptr;
  if (!d) return;
  for (u64 i = 0; i < d->capacity; i++) {
    free(d->keys[i]);
  }
  free(d->keys);
  free(d);
} // LCOV_EXCL_STOP

static void dict_grow(valk_dict_t *d) {
  u64 new_cap = d->capacity * 2;
  char **new_keys = calloc(new_cap, sizeof(char *));
  u64 mask = new_cap - 1;

  for (u64 i = 0; i < d->capacity; i++) {
    if (d->keys[i] != NULL) {
      u64 idx = dict_hash(d->keys[i]) & mask;
      while (new_keys[idx] != NULL)
        idx = (idx + 1) & mask;
      new_keys[idx] = d->keys[i];
    }
  }

  free(d->keys);
  d->keys = new_keys;
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
      d->keys[slot] = malloc(len + 1);
      memcpy(d->keys[slot], key, len + 1);
      d->count++;
      return true;
    }
    if (strcmp(d->keys[slot], key) == 0)
      return false;
  }
  return false;
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

static inline const char *dict_key_str(valk_lval_t *v) {
  if (LVAL_TYPE(v) == LVAL_STR) return v->str;
  if (LVAL_TYPE(v) == LVAL_SYM) return v->str;
  return NULL;
}

#define DICT_ASSERT_REF(args, v) \
  LVAL_ASSERT_TYPE(args, v, LVAL_REF); \
  LVAL_ASSERT(args, strcmp(v->ref.type, "dict") == 0, \
              "Expected dict, got ref<%s>", v->ref.type)

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

  return valk_lval_ref("dict", dict_alloc(cap), dict_free_fn);
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

  return valk_lval_ref("dict", d, dict_free_fn);
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

void valk_register_dict_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "dict/new", valk_builtin_dict_new);
  valk_lenv_put_builtin(env, "dict/put!", valk_builtin_dict_put);
  valk_lenv_put_builtin(env, "dict/has?", valk_builtin_dict_has);
  valk_lenv_put_builtin(env, "dict/from-keys", valk_builtin_dict_from_keys);
  valk_lenv_put_builtin(env, "dict/count", valk_builtin_dict_count);
  valk_lenv_put_builtin(env, "dict/keys", valk_builtin_dict_keys);
}
