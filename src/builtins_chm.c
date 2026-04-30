// Concurrent Hash Map (chm) - thread-safe dict for cross-thread shared state.
//
// Existing `dict` (LVAL_DICT in builtins_dict.c) is a chained hash table in a
// single contiguous block, fast for single-threaded access but unsafe to share
// across threads (no locking; resize moves the entire allocation, so concurrent
// readers see freed memory).
//
// `chm` is the multi-threaded sibling: separate per-CHM mutex protecting a
// classic chained hash table with malloc'd entries (so resizing doesn't move
// existing entries — readers walking a bucket-chain see stable pointers).
// One mutex per CHM is the v1 lock granularity. Bucket-level or rwlock-based
// finer-grained locking is possible later but adds complexity to GC marking.
//
// Used in valk for state shared across worker threads dispatched via
// aio/dispatch — typically LSP caches (lsp/ast-cache, lsp/last-good-tokens-cache,
// etc.) that are read+written from multiple worker loops. Plain `dict` from
// those contexts races and corrupts.
//
// The user-visible builtins:
//   (chm/new) (chm/new num-buckets)
//   (chm/get chm key)             ; returns value or nil
//   (chm/get chm key default)     ; returns default if missing
//   (chm/has? chm key)            ; 1 or 0
//   (chm/put! chm key value)      ; returns chm
//   (chm/del! chm key)            ; returns chm
//   (chm/cas! chm key old new)    ; returns 1 if swapped, 0 if old didn't match
//                                 ; pointer-equal compare for old (use eq? semantics)
//   (chm/size chm)                ; current number of entries
//   (chm/keys chm)                ; list of keys (snapshot; held lock briefly)
//   (chm/clear! chm)              ; remove all entries

#include "builtins_internal.h"
#include "valk_thread.h"
#include "gc.h"
#include <string.h>
#include <stdlib.h>

#define CHM_REF_TYPE "chm"
#define CHM_DEFAULT_BUCKETS 64

typedef struct chm_entry_t {
  char *key;                 // owned; malloc'd
  valk_lval_t *value;        // GC-managed
  struct chm_entry_t *next;
} chm_entry_t;

typedef struct valk_chm_t {
  valk_mutex_t lock;
  u32 num_buckets;
  u32 size;
  chm_entry_t **buckets;
} valk_chm_t;

static u64 chm_hash(const char *key) {
  // FNV-1a, same constants as dict.h's dict_hash for consistency.
  u64 h = 0xcbf29ce484222325ULL;
  for (const unsigned char *p = (const unsigned char *)key; *p; p++) {
    h ^= *p;
    h *= 0x100000001b3ULL;
  }
  return h;
}

static chm_entry_t *chm_find(valk_chm_t *chm, const char *key) {
  u32 b = (u32)(chm_hash(key) % chm->num_buckets);
  for (chm_entry_t *e = chm->buckets[b]; e; e = e->next) {
    if (strcmp(e->key, key) == 0) return e;
  }
  return NULL;
}

static void chm_remove_entry(valk_chm_t *chm, const char *key) {
  u32 b = (u32)(chm_hash(key) % chm->num_buckets);
  chm_entry_t **slot = &chm->buckets[b];
  while (*slot) {
    if (strcmp((*slot)->key, key) == 0) {
      chm_entry_t *e = *slot;
      *slot = e->next;
      free(e->key);
      free(e);
      chm->size--;
      return;
    }
    slot = &(*slot)->next;
  }
}

static void chm_free(void *ptr) {
  valk_chm_t *chm = ptr;
  if (!chm) return;
  for (u32 b = 0; b < chm->num_buckets; b++) {
    chm_entry_t *e = chm->buckets[b];
    while (e) {
      chm_entry_t *next = e->next;
      free(e->key);
      free(e);
      e = next;
    }
  }
  free(chm->buckets);
  valk_mutex_destroy(&chm->lock);
  free(chm);
}

// GC mark hook. Called during STW marking. Walks every entry's value
// and visits it via valk_gc_mark_visit. The CHM's own struct lives in
// malloc heap (not GC heap) so we don't mark it; we only need to mark
// the GC-allocated values it holds reachable.
//
// We don't take the lock here — STW pauses all mutator threads, so
// nothing else is touching the CHM's structure. Taking the lock would
// be unnecessary and could deadlock if a thread held the lock when it
// hit the GC barrier.
static void chm_mark(void *ptr, void *ctx) {
  valk_chm_t *chm = ptr;
  if (!chm) return;
  for (u32 b = 0; b < chm->num_buckets; b++) {
    for (chm_entry_t *e = chm->buckets[b]; e; e = e->next) {
      if (e->value) valk_gc_mark_visit(e->value, ctx);
    }
  }
}

#define LVAL_ASSERT_CHM(args, val)                                          \
  do {                                                                       \
    LVAL_ASSERT_TYPE(args, val, LVAL_REF);                                  \
    LVAL_ASSERT(args, strcmp((val)->ref.type, CHM_REF_TYPE) == 0,           \
                "expected chm, got ref:%s", (val)->ref.type);              \
  } while (0)

static valk_chm_t *chm_alloc(u32 num_buckets) {
  valk_chm_t *chm = calloc(1, sizeof(valk_chm_t));
  if (!chm) return NULL;
  chm->num_buckets = num_buckets;
  chm->buckets = calloc(num_buckets, sizeof(chm_entry_t *));
  if (!chm->buckets) { free(chm); return NULL; }
  if (valk_mutex_init(&chm->lock) != 0) {
    free(chm->buckets);
    free(chm);
    return NULL;
  }
  return chm;
}

static const char *lval_key_str(valk_lval_t *key) {
  // Accept Sym or Str.
  if (LVAL_TYPE(key) == LVAL_SYM || LVAL_TYPE(key) == LVAL_STR) return key->str;
  return NULL;
}

static valk_lval_t *valk_builtin_chm_new(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  u32 nb = CHM_DEFAULT_BUCKETS;
  u64 n = valk_lval_list_count(a);
  if (n >= 1) {
    valk_lval_t *arg0 = valk_lval_list_nth(a, 0);
    LVAL_ASSERT_TYPE(a, arg0, LVAL_NUM);
    if (arg0->num > 0 && arg0->num < (1 << 20)) nb = (u32)arg0->num;
  }
  valk_chm_t *chm = chm_alloc(nb);
  if (!chm) return valk_lval_err("chm/new: allocation failed");
  valk_lval_t *ref = valk_lval_ref(CHM_REF_TYPE, chm, chm_free);
  ref->ref.mark = chm_mark;
  return ref;
}

static valk_lval_t *valk_builtin_chm_get(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  u64 n = valk_lval_list_count(a);
  LVAL_ASSERT(a, n == 2 || n == 3, "chm/get takes 2 or 3 args, got %zu", n);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_CHM(a, ref);
  const char *k = lval_key_str(key);
  LVAL_ASSERT(a, k != NULL, "chm/get key must be Sym or Str");

  valk_chm_t *chm = ref->ref.ptr;
  valk_mutex_lock(&chm->lock);
  chm_entry_t *ent = chm_find(chm, k);
  valk_lval_t *result = ent ? ent->value : NULL;
  valk_mutex_unlock(&chm->lock);

  if (result) return result;
  if (n == 3) return valk_lval_list_nth(a, 2);
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_chm_has(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_CHM(a, ref);
  const char *k = lval_key_str(key);
  LVAL_ASSERT(a, k != NULL, "chm/has? key must be Sym or Str");

  valk_chm_t *chm = ref->ref.ptr;
  valk_mutex_lock(&chm->lock);
  bool found = chm_find(chm, k) != NULL;
  valk_mutex_unlock(&chm->lock);
  return valk_lval_num(found ? 1 : 0);
}

static valk_lval_t *valk_builtin_chm_put(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 3);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  valk_lval_t *val = valk_lval_list_nth(a, 2);
  LVAL_ASSERT_CHM(a, ref);
  const char *k = lval_key_str(key);
  LVAL_ASSERT(a, k != NULL, "chm/put! key must be Sym or Str");

  valk_chm_t *chm = ref->ref.ptr;
  valk_mutex_lock(&chm->lock);
  chm_entry_t *ent = chm_find(chm, k);
  if (ent) {
    ent->value = val;
  } else {
    chm_entry_t *e_new = malloc(sizeof(chm_entry_t));
    if (!e_new) {
      valk_mutex_unlock(&chm->lock);
      return valk_lval_err("chm/put!: allocation failed");
    }
    u64 klen = strlen(k);
    e_new->key = malloc(klen + 1);
    if (!e_new->key) {
      free(e_new);
      valk_mutex_unlock(&chm->lock);
      return valk_lval_err("chm/put!: allocation failed");
    }
    memcpy(e_new->key, k, klen + 1);
    e_new->value = val;
    u32 b = (u32)(chm_hash(k) % chm->num_buckets);
    e_new->next = chm->buckets[b];
    chm->buckets[b] = e_new;
    chm->size++;
  }
  valk_mutex_unlock(&chm->lock);
  return ref;
}

static valk_lval_t *valk_builtin_chm_del(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  LVAL_ASSERT_CHM(a, ref);
  const char *k = lval_key_str(key);
  LVAL_ASSERT(a, k != NULL, "chm/del! key must be Sym or Str");

  valk_chm_t *chm = ref->ref.ptr;
  valk_mutex_lock(&chm->lock);
  chm_remove_entry(chm, k);
  valk_mutex_unlock(&chm->lock);
  return ref;
}

// chm/cas! — atomic compare-and-swap by pointer-equality on the value.
// If current[key] is pointer-equal to `old`, replace with `new` and return 1.
// Otherwise return 0 (no change). Pointer equality means the SAME lval object,
// not value-equal. For atomic increment of e.g. a counter held in chm, callers
// pair this with a retry loop:
//   (= {curr} (chm/get chm "k"))
//   (= {next} (compute curr))
//   (if (chm/cas! chm "k" curr next) ...success... ...retry...)
// The empty-cell case: passing nil for old matches when key is absent;
// the new value is then inserted. Passing nil for new with non-nil old
// is equivalent to chm/del! conditional on match.
static valk_lval_t *valk_builtin_chm_cas(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 4);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  valk_lval_t *key = valk_lval_list_nth(a, 1);
  valk_lval_t *old = valk_lval_list_nth(a, 2);
  valk_lval_t *new_val = valk_lval_list_nth(a, 3);
  LVAL_ASSERT_CHM(a, ref);
  const char *k = lval_key_str(key);
  LVAL_ASSERT(a, k != NULL, "chm/cas! key must be Sym or Str");

  // Treat LVAL_NIL singleton as "absent" for old-match purposes.
  bool old_is_nil = (LVAL_TYPE(old) == LVAL_NIL);
  bool new_is_nil = (LVAL_TYPE(new_val) == LVAL_NIL);

  valk_chm_t *chm = ref->ref.ptr;
  valk_mutex_lock(&chm->lock);

  chm_entry_t *ent = chm_find(chm, k);
  bool matched;
  if (ent == NULL) {
    matched = old_is_nil;
  } else {
    matched = (ent->value == old);
  }

  if (!matched) {
    valk_mutex_unlock(&chm->lock);
    return valk_lval_num(0);
  }

  if (ent == NULL) {
    if (!new_is_nil) {
      chm_entry_t *e_new = malloc(sizeof(chm_entry_t));
      if (!e_new) {
        valk_mutex_unlock(&chm->lock);
        return valk_lval_err("chm/cas!: allocation failed");
      }
      u64 klen = strlen(k);
      e_new->key = malloc(klen + 1);
      if (!e_new->key) {
        free(e_new);
        valk_mutex_unlock(&chm->lock);
        return valk_lval_err("chm/cas!: allocation failed");
      }
      memcpy(e_new->key, k, klen + 1);
      e_new->value = new_val;
      u32 b = (u32)(chm_hash(k) % chm->num_buckets);
      e_new->next = chm->buckets[b];
      chm->buckets[b] = e_new;
      chm->size++;
    }
  } else {
    if (new_is_nil) {
      chm_remove_entry(chm, k);
    } else {
      ent->value = new_val;
    }
  }

  valk_mutex_unlock(&chm->lock);
  return valk_lval_num(1);
}

static valk_lval_t *valk_builtin_chm_size(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_CHM(a, ref);
  valk_chm_t *chm = ref->ref.ptr;
  valk_mutex_lock(&chm->lock);
  long sz = (long)chm->size;
  valk_mutex_unlock(&chm->lock);
  return valk_lval_num(sz);
}

static valk_lval_t *valk_builtin_chm_keys(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_CHM(a, ref);
  valk_chm_t *chm = ref->ref.ptr;

  // Snapshot keys under lock, then build the cons list outside the lock
  // (allocating GC objects while holding a non-GC mutex is an inversion
  // hazard — if the alloc triggers GC, the GC needs all threads at safe
  // points but we're holding a mutex no one else can release).
  u32 cap = 0, count = 0;
  char **snapshot = NULL;
  valk_mutex_lock(&chm->lock);
  for (u32 b = 0; b < chm->num_buckets; b++) {
    for (chm_entry_t *ent = chm->buckets[b]; ent; ent = ent->next) {
      if (count >= cap) {
        cap = cap == 0 ? 16 : cap * 2;
        snapshot = realloc(snapshot, cap * sizeof(char *));
      }
      // Duplicate the string so we can safely use it after releasing the lock.
      u64 klen = strlen(ent->key);
      char *kc = malloc(klen + 1);
      memcpy(kc, ent->key, klen + 1);
      snapshot[count++] = kc;
    }
  }
  valk_mutex_unlock(&chm->lock);

  valk_lval_t *out = valk_lval_nil();
  for (u32 i = count; i > 0; i--) {
    valk_lval_t *s = valk_lval_str(snapshot[i - 1]);
    out = valk_lval_cons(s, out);
    free(snapshot[i - 1]);
  }
  free(snapshot);
  return out;
}

static valk_lval_t *valk_builtin_chm_clear(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_CHM(a, ref);
  valk_chm_t *chm = ref->ref.ptr;
  valk_mutex_lock(&chm->lock);
  for (u32 b = 0; b < chm->num_buckets; b++) {
    chm_entry_t *ent = chm->buckets[b];
    while (ent) {
      chm_entry_t *next = ent->next;
      free(ent->key);
      free(ent);
      ent = next;
    }
    chm->buckets[b] = NULL;
  }
  chm->size = 0;
  valk_mutex_unlock(&chm->lock);
  return ref;
}

void valk_register_chm_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "chm/new", valk_builtin_chm_new);
  valk_lenv_put_builtin(env, "chm/get", valk_builtin_chm_get);
  valk_lenv_put_builtin(env, "chm/has?", valk_builtin_chm_has);
  valk_lenv_put_builtin(env, "chm/put!", valk_builtin_chm_put);
  valk_lenv_put_builtin(env, "chm/del!", valk_builtin_chm_del);
  valk_lenv_put_builtin(env, "chm/cas!", valk_builtin_chm_cas);
  valk_lenv_put_builtin(env, "chm/size", valk_builtin_chm_size);
  valk_lenv_put_builtin(env, "chm/keys", valk_builtin_chm_keys);
  valk_lenv_put_builtin(env, "chm/clear!", valk_builtin_chm_clear);
}
