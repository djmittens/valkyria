#include "builtins_internal.h"
#include "dict.h"
#include "gc.h"
#include <string.h>

// ==========================================================================
// Flat, single-allocation hash map with separate chaining.
//
// Layout (one contiguous block):
//   valk_dict_t       header
//   u32               buckets[num_buckets]   (index into cells, EMPTY=end)
//   valk_dict_cell_t  cells[capacity]         (entry pool + embedded freelist)
//   char              strings[strings_cap]    (packed key strings)
//
// - Fixed bucket count (set at creation, never rehashed).
// - Cells are a pool: used cells form per-bucket chains via `next`,
//   free cells form a freelist via `next`.
// - When cell pool is exhausted, allocate a new larger block, copy
//   cells + strings, rebuild bucket heads from chains.
// ==========================================================================

#define DICT_DEFAULT_BUCKETS    16
#define DICT_INITIAL_CAPACITY   16
#define DICT_INITIAL_STRINGS    256

// ---------- Allocation ----------

static valk_dict_t *dict_alloc(u32 num_buckets, u32 capacity, u64 strings_cap) {
  u64 sz = dict_block_size(num_buckets, capacity, strings_cap);
  valk_dict_t *d = valk_mem_calloc(1, sz);
  d->num_buckets = num_buckets;
  d->capacity = capacity;
  d->count = 0;
  d->strings_used = 0;
  d->strings_cap = strings_cap;

  u32 *buckets = dict_buckets(d);
  for (u32 i = 0; i < num_buckets; i++)
    buckets[i] = DICT_EMPTY;

  valk_dict_cell_t *cells = dict_cells(d);
  for (u32 i = 0; i < capacity - 1; i++)
    cells[i].next = i + 1;
  cells[capacity - 1].next = DICT_EMPTY;
  d->free_head = 0;

  return d;
}

// ---------- Internal: copy a key into the string pool ----------

static u32 dict_intern_key(valk_dict_t *d, const char *key, u64 len) {
  u32 off = (u32)d->strings_used;
  memcpy(dict_strings(d) + off, key, len + 1);
  d->strings_used += len + 1;
  return off;
}

// ---------- Grow cell pool (and optionally string pool) ----------

static valk_dict_t *dict_grow(valk_dict_t *d, u64 need_str) {
  u32 new_cap = d->capacity * 2;
  u64 new_str = d->strings_cap;
  while (new_str < need_str)
    new_str *= 2;

  bool on_heap = !valk_thread_ctx.scratch ||
                 !valk_ptr_in_arena(valk_thread_ctx.scratch, d);
  valk_dict_t *nd;
  u64 sz = dict_block_size(d->num_buckets, new_cap, new_str);
  if (on_heap) {
    VALK_WITH_ALLOC((void *)valk_thread_ctx.heap) {
      nd = valk_mem_calloc(1, sz);
    }
  } else {
    nd = valk_mem_calloc(1, sz);
  }
  nd->num_buckets = d->num_buckets;
  nd->capacity = new_cap;
  nd->count = d->count;
  nd->strings_used = d->strings_used;
  nd->strings_cap = new_str;

  u32 *new_buckets = dict_buckets(nd);
  for (u32 i = 0; i < nd->num_buckets; i++)
    new_buckets[i] = DICT_EMPTY;

  valk_dict_cell_t *old_cells = dict_cells(d);
  valk_dict_cell_t *new_cells = dict_cells(nd);

  memcpy(dict_strings(nd), dict_strings(d), d->strings_used);

  u32 *old_buckets = dict_buckets(d);
  u32 new_used = 0;
  for (u32 b = 0; b < d->num_buckets; b++) {
    u32 ci = old_buckets[b];
    u32 *chain_tail = &new_buckets[b];
    while (ci != DICT_EMPTY) {
      u32 slot = new_used++;
      new_cells[slot].hash = old_cells[ci].hash;
      new_cells[slot].key_offset = old_cells[ci].key_offset;
      new_cells[slot].value = old_cells[ci].value;
      new_cells[slot].next = DICT_EMPTY;
      *chain_tail = slot;
      chain_tail = &new_cells[slot].next;
      ci = old_cells[ci].next;
    }
  }

  for (u32 i = new_used; i < new_cap - 1; i++)
    new_cells[i].next = i + 1;
  new_cells[new_cap - 1].next = DICT_EMPTY;
  nd->free_head = new_used < new_cap ? new_used : DICT_EMPTY;

  if (on_heap) {
    VALK_WITH_ALLOC((void *)valk_thread_ctx.heap) {
      valk_mem_free(d);
    }
  } else {
    valk_mem_free(d);
  }
  return nd;
}

// ---------- Ensure space for one entry + key bytes ----------

static valk_dict_t *dict_ensure(valk_dict_t *d, u64 key_len) {
  bool need_cell = d->free_head == DICT_EMPTY;
  u64 need_str = d->strings_used + key_len + 1;
  bool need_str_grow = need_str > d->strings_cap;
  if (!need_cell && !need_str_grow) return d;
  return dict_grow(d, need_str_grow ? need_str : d->strings_cap);
}

// ---------- Lookup: returns cell index or DICT_EMPTY ----------

static u32 dict_find(valk_dict_t *d, const char *key, u64 h) {
  u32 bucket = (u32)(h % d->num_buckets);
  valk_dict_cell_t *cells = dict_cells(d);
  u32 ci = dict_buckets(d)[bucket];
  while (ci != DICT_EMPTY) {
    if (cells[ci].hash == h && strcmp(dict_strings(d) + cells[ci].key_offset, key) == 0)
      return ci;
    ci = cells[ci].next;
  }
  return DICT_EMPTY;
}

// ---------- Public operations ----------

static void dict_set(valk_dict_t **dp, const char *key, valk_lval_t *value) {
  bool on_heap = !valk_thread_ctx.scratch ||
                 !valk_ptr_in_arena(valk_thread_ctx.scratch, *dp);
  if (on_heap && value != nullptr && LVAL_ALLOC(value) == LVAL_ALLOC_SCRATCH)
    value = valk_evacuate_to_heap(value);

  u64 h = dict_hash(key);
  u32 ci = dict_find(*dp, key, h);
  if (ci != DICT_EMPTY) {
    dict_cells(*dp)[ci].value = value;
    return;
  }

  u64 len = strlen(key);
  *dp = dict_ensure(*dp, len);
  valk_dict_t *d = *dp;

  u32 slot = d->free_head;
  valk_dict_cell_t *cells = dict_cells(d);
  d->free_head = cells[slot].next;

  u32 bucket = (u32)(h % d->num_buckets);
  cells[slot].hash = h;
  cells[slot].key_offset = dict_intern_key(d, key, len);
  cells[slot].value = value;
  cells[slot].next = dict_buckets(d)[bucket];
  dict_buckets(d)[bucket] = slot;
  d->count++;
}

static bool dict_put(valk_dict_t **dp, const char *key) {
  u64 h = dict_hash(key);
  if (dict_find(*dp, key, h) != DICT_EMPTY) return false;

  u64 len = strlen(key);
  *dp = dict_ensure(*dp, len);
  valk_dict_t *d = *dp;

  u32 slot = d->free_head;
  valk_dict_cell_t *cells = dict_cells(d);
  d->free_head = cells[slot].next;

  u32 bucket = (u32)(h % d->num_buckets);
  cells[slot].hash = h;
  cells[slot].key_offset = dict_intern_key(d, key, len);
  cells[slot].value = nullptr;
  cells[slot].next = dict_buckets(d)[bucket];
  dict_buckets(d)[bucket] = slot;
  d->count++;
  return true;
}

static valk_lval_t *dict_get(valk_dict_t *d, const char *key) {
  u64 h = dict_hash(key);
  u32 ci = dict_find(d, key, h);
  if (ci == DICT_EMPTY) return nullptr;
  return dict_cells(d)[ci].value;
}

static bool dict_has(valk_dict_t *d, const char *key) {
  return dict_find(d, key, dict_hash(key)) != DICT_EMPTY;
}

static bool dict_remove(valk_dict_t *d, const char *key) {
  u64 h = dict_hash(key);
  u32 bucket = (u32)(h % d->num_buckets);
  valk_dict_cell_t *cells = dict_cells(d);
  u32 *prev = &dict_buckets(d)[bucket];
  u32 ci = *prev;

  while (ci != DICT_EMPTY) {
    if (cells[ci].hash == h && strcmp(dict_strings(d) + cells[ci].key_offset, key) == 0) {
      *prev = cells[ci].next;
      cells[ci].value = nullptr;
      cells[ci].next = d->free_head;
      d->free_head = ci;
      d->count--;
      return true;
    }
    prev = &cells[ci].next;
    ci = cells[ci].next;
  }
  return false;
}

// ---------- Builtin glue ----------

static inline const char *dict_key_str(valk_lval_t *v) {
  if (LVAL_TYPE(v) == LVAL_STR) return v->str;
  if (LVAL_TYPE(v) == LVAL_SYM) return v->str;
  return NULL;
}

#define DICT_ASSERT(args, v) \
  LVAL_ASSERT_TYPE(args, v, LVAL_DICT)

static valk_lval_t *valk_builtin_dict_new(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  u64 n = valk_lval_list_count(a);
  LVAL_ASSERT(a, n <= 1, "dict/new takes 0 or 1 arguments, got %zu", n);

  u32 cap = DICT_INITIAL_CAPACITY;
  if (n == 1) {
    valk_lval_t *hint = valk_lval_list_nth(a, 0);
    LVAL_ASSERT_TYPE(a, hint, LVAL_NUM);
    u32 want = (u32)hint->num;
    while (cap < want)
      cap *= 2;
  }

  valk_lval_t *r = valk_lval_dict(dict_alloc(DICT_DEFAULT_BUCKETS, cap, DICT_INITIAL_STRINGS));
  return r;
}

static valk_lval_t *valk_builtin_dict_put(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/put! key must be String or Symbol");

  valk_dict_t *dp = d->dict.data;
  dict_put(&dp, k);
  d->dict.data = dp;
  return d;
}

static valk_lval_t *valk_builtin_dict_set(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  valk_lval_t *val = valk_lval_list_nth(a, 2);
  DICT_ASSERT(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/set! key must be String or Symbol");

  valk_dict_t *dp = d->dict.data;
  dict_set(&dp, k, val);
  d->dict.data = dp;
  return d;
}

static valk_lval_t *valk_builtin_dict_get(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  u64 n = valk_lval_list_count(a);
  LVAL_ASSERT(a, n == 2 || n == 3,
              "dict/get takes 2 or 3 arguments, got %zu", n);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/get key must be String or Symbol");

  valk_lval_t *result = dict_get(d->dict.data, k);
  if (result != nullptr) return result;

  if (n == 3) return valk_lval_list_nth(a, 2);
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_dict_remove(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/remove! key must be String or Symbol");

  dict_remove(d->dict.data, k);
  return d;
}

static valk_lval_t *valk_builtin_dict_has(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/has? key must be String or Symbol");

  return valk_lval_num(dict_has(d->dict.data, k) ? 1 : 0);
}

static valk_lval_t *valk_builtin_dict_from_keys(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *list = valk_lval_list_nth(a, 0);

  u64 count = valk_lval_list_count(list);
  u32 cap = DICT_INITIAL_CAPACITY;
  while (cap < count)
    cap *= 2;

  valk_dict_t *d = dict_alloc(DICT_DEFAULT_BUCKETS, cap, DICT_INITIAL_STRINGS);

  valk_lval_t *curr = list;
  while (curr && !valk_lval_list_is_empty(curr)) {
    valk_lval_t *item = curr->cons.head;
    const char *k = item ? dict_key_str(item) : NULL;
    if (k) dict_put(&d, k);
    curr = curr->cons.tail;
  }

  return valk_lval_dict(d);
}

static valk_lval_t *valk_builtin_dict_count(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  DICT_ASSERT(a, d);

  return valk_lval_num((long)d->dict.data->count);
}

static valk_lval_t *valk_builtin_dict_keys(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d_lval = valk_lval_list_nth(a, 0);
  DICT_ASSERT(a, d_lval);

  valk_dict_t *d = d_lval->dict.data;
  valk_dict_cell_t *cells = dict_cells(d);
  u32 *buckets = dict_buckets(d);
  valk_lval_t *result = valk_lval_nil();

  for (u32 b = d->num_buckets; b > 0; b--) {
    u32 ci = buckets[b - 1];
    while (ci != DICT_EMPTY) {
      result = valk_lval_qcons(valk_lval_str(dict_key_at(d, ci)), result);
      ci = cells[ci].next;
    }
  }

  return result;
}

static valk_lval_t *valk_builtin_dict_values(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d_lval = valk_lval_list_nth(a, 0);
  DICT_ASSERT(a, d_lval);

  valk_dict_t *d = d_lval->dict.data;
  valk_dict_cell_t *cells = dict_cells(d);
  u32 *buckets = dict_buckets(d);
  valk_lval_t *result = valk_lval_nil();

  for (u32 b = d->num_buckets; b > 0; b--) {
    u32 ci = buckets[b - 1];
    while (ci != DICT_EMPTY) {
      valk_lval_t *v = cells[ci].value;
      result = valk_lval_qcons(v ? v : valk_lval_nil(), result);
      ci = cells[ci].next;
    }
  }

  return result;
}

static valk_lval_t *valk_builtin_dict_entries(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d_lval = valk_lval_list_nth(a, 0);
  DICT_ASSERT(a, d_lval);

  valk_dict_t *d = d_lval->dict.data;
  valk_dict_cell_t *cells = dict_cells(d);
  u32 *buckets = dict_buckets(d);
  valk_lval_t *result = valk_lval_nil();

  for (u32 b = d->num_buckets; b > 0; b--) {
    u32 ci = buckets[b - 1];
    while (ci != DICT_EMPTY) {
      valk_lval_t *v = cells[ci].value;
      valk_lval_t *pair = valk_lval_qcons(
          valk_lval_str(dict_key_at(d, ci)),
          valk_lval_qcons(v ? v : valk_lval_nil(), valk_lval_nil()));
      result = valk_lval_qcons(pair, result);
      ci = cells[ci].next;
    }
  }

  return result;
}

static valk_lval_t *valk_builtin_dict_p(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *v = valk_lval_list_nth(a, 0);
  return valk_lval_num(LVAL_TYPE(v) == LVAL_DICT ? 1 : 0);
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
  valk_lenv_put_builtin(env, "dict?", valk_builtin_dict_p);
}
