#include "builtins_internal.h"
#include "gc.h"
#include <string.h>

// ==========================================================================
// Flat, single-allocation open-addressing hash map.
//
// Layout (one contiguous block):
//   valk_dict_t header
//   u64           hashes[capacity]
//   u32           key_offsets[capacity]   (byte offset into string pool)
//   valk_lval_t*  values[capacity]
//   char          strings[strings_cap]
//
// - hash == 0 means empty slot.  We set bit 63 on every stored hash so
//   a real hash can never be 0.
// - Grow / string-pool exhaustion: allocate a whole new block, rehash.
// - Evacuation: single memcpy of the block, then fixup value pointers.
// ==========================================================================

#define DICT_INITIAL_CAPACITY 16
#define DICT_INITIAL_STRINGS  256
#define DICT_LOAD_FACTOR_PCT  75
#define DICT_OCCUPIED_BIT     (1ULL << 63)

typedef struct {
  u64 capacity;
  u64 count;
  u64 strings_used;
  u64 strings_cap;
  // Flexible-array members are laid out immediately after this header
  // via the accessor macros below.
} valk_dict_t;

static inline u64 *dict_hashes(valk_dict_t *d) {
  return (u64 *)((u8 *)d + sizeof(valk_dict_t));
}

static inline u32 *dict_key_offsets(valk_dict_t *d) {
  return (u32 *)((u8 *)d + sizeof(valk_dict_t) + d->capacity * sizeof(u64));
}

static inline valk_lval_t **dict_values(valk_dict_t *d) {
  return (valk_lval_t **)((u8 *)d + sizeof(valk_dict_t)
         + d->capacity * sizeof(u64)
         + d->capacity * sizeof(u32));
}

static inline char *dict_strings(valk_dict_t *d) {
  return (char *)((u8 *)d + sizeof(valk_dict_t)
         + d->capacity * sizeof(u64)
         + d->capacity * sizeof(u32)
         + d->capacity * sizeof(valk_lval_t *));
}

static inline u64 dict_block_size(u64 capacity, u64 strings_cap) {
  return sizeof(valk_dict_t)
       + capacity * sizeof(u64)
       + capacity * sizeof(u32)
       + capacity * sizeof(valk_lval_t *)
       + strings_cap;
}

static inline const char *dict_key_at(valk_dict_t *d, u64 slot) {
  return dict_strings(d) + dict_key_offsets(d)[slot];
}

// ---------- FNV-1a hash ----------

static inline u64 dict_hash(const char *key) {
  u64 h = 0xcbf29ce484222325ULL;
  for (const unsigned char *p = (const unsigned char *)key; *p; p++) {
    h ^= *p;
    h *= 0x100000001b3ULL;
  }
  return h | DICT_OCCUPIED_BIT;
}

// ---------- Allocation ----------

static valk_dict_t *dict_alloc(u64 capacity, u64 strings_cap) {
  u64 sz = dict_block_size(capacity, strings_cap);
  valk_dict_t *d = valk_mem_calloc(1, sz);
  d->capacity = capacity;
  d->count = 0;
  d->strings_used = 0;
  d->strings_cap = strings_cap;
  return d;
}

// ---------- Free ----------

static void dict_free_fn(void *ptr) {
  (void)ptr;
}

// ---------- GC mark ----------

static void dict_mark_fn(void *ptr, void *gc_ctx) {
  valk_dict_t *d = ptr;
  if (!d) return; // LCOV_EXCL_LINE
  valk_gc_mark_ctx_t *ctx = gc_ctx;
  valk_gc_heap_mark_raw(ctx, d);
  u64 *hashes = dict_hashes(d);
  valk_lval_t **vals = dict_values(d);
  for (u64 i = 0; i < d->capacity; i++) {
    if (hashes[i] && vals[i] != nullptr)
      valk_gc_heap_mark_object(ctx, vals[i]);
  }
}

// ---------- GC evacuation ----------

static void dict_evacuate_fn(void **ptr_ref, void *evac_ctx) {
  valk_dict_t *d = *ptr_ref;
  if (!d) return;
  valk_evacuation_ctx_t *ctx = evac_ctx;

  if (ctx->scratch && valk_ptr_in_arena(ctx->scratch, d)) {
    u64 sz = dict_block_size(d->capacity, d->strings_cap);
    valk_dict_t *nd;
    VALK_WITH_ALLOC((void *)ctx->heap) {
      nd = valk_mem_alloc(sz);
    }
    memcpy(nd, d, sz);
    *ptr_ref = nd;
    d = nd;
    ctx->bytes_copied += sz;
  }

  valk_lval_t **vals = dict_values(d);
  u64 *hashes = dict_hashes(d);
  for (u64 i = 0; i < d->capacity; i++) {
    if (hashes[i] && vals[i] != nullptr) {
      valk_lval_t *old_val = vals[i];
      valk_lval_t *new_val = valk_evacuate_value(ctx, old_val);
      if (new_val != old_val) {
        vals[i] = new_val;
        if (new_val != nullptr) valk_evac_worklist_push(ctx, new_val);
      }
    }
  }
}

// ---------- Internal: copy a key into the string pool ----------

static u32 dict_intern_key(valk_dict_t *d, const char *key, u64 len) {
  u32 off = (u32)d->strings_used;
  memcpy(dict_strings(d) + off, key, len + 1);
  d->strings_used += len + 1;
  return off;
}

// ---------- Rehash into a new block (grow or string-pool full) ----------

static valk_dict_t *dict_rehash(valk_dict_t *d, u64 new_cap, u64 new_str_cap) {
  valk_dict_t *nd = dict_alloc(new_cap, new_str_cap);

  u64 *old_h = dict_hashes(d);
  u32 *old_ko = dict_key_offsets(d);
  valk_lval_t **old_v = dict_values(d);
  char *old_s = dict_strings(d);

  u64 mask = new_cap - 1;
  u64 *new_h = dict_hashes(nd);
  u32 *new_ko = dict_key_offsets(nd);
  valk_lval_t **new_v = dict_values(nd);

  for (u64 i = 0; i < d->capacity; i++) {
    if (old_h[i] == 0) continue;
    const char *key = old_s + old_ko[i];
    u64 len = strlen(key);
    u64 idx = old_h[i] & mask;
    while (new_h[idx]) idx = (idx + 1) & mask;
    new_h[idx] = old_h[i];
    new_ko[idx] = dict_intern_key(nd, key, len);
    new_v[idx] = old_v[i];
    nd->count++;
  }

  valk_mem_free(d);
  return nd;
}

// ---------- Ensure capacity for one more entry + key bytes ----------

static valk_dict_t *dict_ensure(valk_dict_t *d, u64 key_len) {
  bool need_grow = d->count * 100 >= d->capacity * DICT_LOAD_FACTOR_PCT;
  bool need_str = d->strings_used + key_len + 1 > d->strings_cap;
  if (!need_grow && !need_str) return d;

  u64 new_cap = need_grow ? d->capacity * 2 : d->capacity;
  u64 new_str = d->strings_cap;
  if (need_str) {
    while (new_str < d->strings_used + key_len + 1)
      new_str *= 2;
  }
  return dict_rehash(d, new_cap, new_str);
}

// ---------- Lookup helpers ----------

static inline u64 dict_find_slot(valk_dict_t *d, const char *key, u64 h) {
  u64 mask = d->capacity - 1;
  u64 *hashes = dict_hashes(d);
  u64 idx = h & mask;
  for (u64 i = 0; i < d->capacity; i++) {
    u64 slot = (idx + i) & mask;
    if (hashes[slot] == 0) return slot;
    if (hashes[slot] == h && strcmp(dict_key_at(d, slot), key) == 0)
      return slot;
  }
  return (u64)-1;
}

// ---------- Public operations ----------

static void dict_set(valk_dict_t **dp, const char *key, valk_lval_t *value) {
  u64 len = strlen(key);
  *dp = dict_ensure(*dp, len);
  valk_dict_t *d = *dp;
  u64 h = dict_hash(key);
  u64 slot = dict_find_slot(d, key, h);
  u64 *hashes = dict_hashes(d);
  if (hashes[slot] == 0) {
    hashes[slot] = h;
    dict_key_offsets(d)[slot] = dict_intern_key(d, key, len);
    d->count++;
  }
  dict_values(d)[slot] = value;
}

static bool dict_put(valk_dict_t **dp, const char *key) {
  u64 len = strlen(key);
  *dp = dict_ensure(*dp, len);
  valk_dict_t *d = *dp;
  u64 h = dict_hash(key);
  u64 slot = dict_find_slot(d, key, h);
  u64 *hashes = dict_hashes(d);
  if (hashes[slot] != 0) return false;
  hashes[slot] = h;
  dict_key_offsets(d)[slot] = dict_intern_key(d, key, len);
  d->count++;
  return true;
}

static valk_lval_t *dict_get(valk_dict_t *d, const char *key) {
  u64 h = dict_hash(key);
  u64 slot = dict_find_slot(d, key, h);
  if (dict_hashes(d)[slot] == 0) return nullptr;
  return dict_values(d)[slot];
}

static bool dict_has(valk_dict_t *d, const char *key) {
  u64 h = dict_hash(key);
  u64 slot = dict_find_slot(d, key, h);
  return dict_hashes(d)[slot] != 0;
}

static bool dict_remove(valk_dict_t *d, const char *key) {
  u64 h = dict_hash(key);
  u64 mask = d->capacity - 1;
  u64 *hashes = dict_hashes(d);
  u64 slot = dict_find_slot(d, key, h);
  if (hashes[slot] == 0) return false;

  hashes[slot] = 0;
  dict_values(d)[slot] = nullptr;
  d->count--;

  // Robin Hood backward-shift deletion
  u64 j = (slot + 1) & mask;
  while (hashes[j] != 0) {
    u64 natural = hashes[j] & mask;
    // Check if j is displaced past slot
    bool displaced = (j >= slot)
      ? (natural <= slot || natural > j)
      : (natural <= slot && natural > j);
    if (displaced) {
      hashes[slot] = hashes[j];
      dict_key_offsets(d)[slot] = dict_key_offsets(d)[j];
      dict_values(d)[slot] = dict_values(d)[j];
      hashes[j] = 0;
      dict_values(d)[j] = nullptr;
      slot = j;
    }
    j = (j + 1) & mask;
  }
  return true;
}

// ---------- Builtin glue ----------

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
  valk_lval_t *ref = valk_lval_ref("dict", d, dict_free_fn);
  ref->ref.mark = dict_mark_fn;
  ref->ref.evacuate = dict_evacuate_fn;
  ref->ref.retain = nullptr;
  return ref;
}

// Mutating operations may rehash, so they need to update ref.ptr.
static inline void dict_update_ref(valk_lval_t *ref, valk_dict_t *d) {
  ref->ref.ptr = d;
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

  return dict_make_ref(dict_alloc(cap, DICT_INITIAL_STRINGS));
}

static valk_lval_t *valk_builtin_dict_put(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *d = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  DICT_ASSERT_REF(a, d);

  const char *k = dict_key_str(key);
  LVAL_ASSERT(a, k != NULL, "dict/put! key must be String or Symbol");

  valk_dict_t *dp = d->ref.ptr;
  dict_put(&dp, k);
  dict_update_ref(d, dp);
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

  valk_dict_t *dp = d->ref.ptr;
  dict_set(&dp, k, val);
  dict_update_ref(d, dp);
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

  valk_dict_t *d = dict_alloc(cap, DICT_INITIAL_STRINGS);

  valk_lval_t *curr = list;
  while (curr && !valk_lval_list_is_empty(curr)) {
    valk_lval_t *item = curr->cons.head;
    const char *k = item ? dict_key_str(item) : NULL;
    if (k) dict_put(&d, k);
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
  u64 *hashes = dict_hashes(d);
  valk_lval_t *result = valk_lval_nil();

  for (u64 i = d->capacity; i > 0; i--) {
    if (hashes[i - 1])
      result = valk_lval_qcons(valk_lval_str(dict_key_at(d, i - 1)), result);
  }

  return result;
}

static valk_lval_t *valk_builtin_dict_values(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *d_ref = valk_lval_list_nth(a, 0);
  DICT_ASSERT_REF(a, d_ref);

  valk_dict_t *d = d_ref->ref.ptr;
  u64 *hashes = dict_hashes(d);
  valk_lval_t **vals = dict_values(d);
  valk_lval_t *result = valk_lval_nil();

  for (u64 i = d->capacity; i > 0; i--) {
    if (hashes[i - 1]) {
      valk_lval_t *v = vals[i - 1];
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
  u64 *hashes = dict_hashes(d);
  valk_lval_t **vals = dict_values(d);
  valk_lval_t *result = valk_lval_nil();

  for (u64 i = d->capacity; i > 0; i--) {
    if (hashes[i - 1]) {
      valk_lval_t *v = vals[i - 1];
      valk_lval_t *pair = valk_lval_qcons(
          valk_lval_str(dict_key_at(d, i - 1)),
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
