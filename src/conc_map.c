#include "conc_map.h"

#include <string.h>

#include "memory.h"
#include "parser.h"  // valk_sym_intern

// Keys are canonical pointers into the global symbol intern table (see
// valk_sym_intern), enforced by valk_cmap_put. That makes symbol identity
// pointer identity, so this map never hashes or compares string BYTES:
//
//   - hash mixes the pointer, not the characters, so lookup cost is
//     independent of symbol length;
//   - a probe compares pointers, so a hit is one integer compare and a miss
//     costs nothing extra.
//
// Before this, every global/builtin resolution hashed the name and strcmp'd it.
// Measured on one LSP document validation: 339,548 strcmps, all of them
// avoidable — interning was already in place, but both the env arrays and this
// map copied the key string and threw the canonical pointer away.
//
// splitmix64 finalizer: malloc'd pointers are 16-byte aligned, so the low bits
// are near-constant and must be mixed up into the index bits.
static u64 cmap_hash(const char *key) {
  u64 h = (u64)(uintptr_t)key;
  h ^= h >> 30; h *= 0xbf58476d1ce4e5b9ULL;
  h ^= h >> 27; h *= 0x94d049bb133111ebULL;
  h ^= h >> 31;
  return h;
}

static u64 round_pow2(u64 n) {
  if (n < 16) return 16;
  n--;
  n |= n >> 1;
  n |= n >> 2;
  n |= n >> 4;
  n |= n >> 8;
  n |= n >> 16;
  n |= n >> 32;
  return n + 1;
}

static valk_cmap_table_t *cmap_table_new(void *allocator, u64 capacity) {
  u64 bytes = sizeof(valk_cmap_table_t) + capacity * sizeof(valk_cmap_slot_t);
  valk_cmap_table_t *t;
  VALK_WITH_ALLOC(allocator) { t = valk_mem_alloc(bytes); }
  if (!t) return nullptr; // LCOV_EXCL_LINE - OOM
  memset(t, 0, bytes);
  t->capacity = capacity;
  atomic_store_explicit(&t->count, 0, memory_order_relaxed);
  t->retired = nullptr;
  return t;
}

valk_cmap_t *valk_cmap_new(void *allocator, u64 initial_capacity) {
  valk_cmap_t *m;
  VALK_WITH_ALLOC(allocator) { m = valk_mem_alloc(sizeof(valk_cmap_t)); }
  if (!m) return nullptr; // LCOV_EXCL_LINE - OOM
  memset(m, 0, sizeof(*m));
  m->allocator = allocator;
  for (u32 i = 0; i < VALK_CMAP_SEGMENTS; i++) {
    valk_mutex_init(&m->seg_locks[i]);
  }
  valk_cmap_table_t *t = cmap_table_new(allocator, round_pow2(initial_capacity));
  atomic_store_explicit(&m->table, t, memory_order_release);
  return m;
}

// Lock-free probe of a published table snapshot.
// Fast path. PRECONDITION: `key` is already a canonical intern-table pointer.
// Keys are hashed BY POINTER, so a non-interned key hashes into a different
// bucket and would silently miss — hence the separate safe wrapper below
// rather than a "best effort" single entry point.
valk_lval_t *valk_cmap_get_interned(valk_cmap_t *m, const char *key) {
  if (!m || !key) return nullptr;
  valk_cmap_table_t *t = atomic_load_explicit(&m->table, memory_order_acquire);
  u64 mask = t->capacity - 1;
  u64 h = cmap_hash(key);
  for (u64 i = 0; i < t->capacity; i++) {
    u64 idx = (h + i) & mask;
    char *k = atomic_load_explicit(&t->slots[idx].key, memory_order_acquire);
    if (k == nullptr) {
      return nullptr; // empty slot => key absent (open addressing)
    }
    if (k == key) {
      return atomic_load_explicit(&t->slots[idx].val, memory_order_acquire);
    }
  }
  return nullptr; // LCOV_EXCL_LINE - full table without match (resize prevents)
}

// Safe entry point for callers holding an arbitrary string. Canonicalizes
// first, so correctness never depends on where the caller's bytes came from.
valk_lval_t *valk_cmap_get(valk_cmap_t *m, const char *key) {
  if (!m || !key) return nullptr;
  return valk_cmap_get_interned(m, valk_sym_intern(key));
}

static u32 seg_for(u64 hash) { return (u32)(hash & (VALK_CMAP_SEGMENTS - 1)); }

static void cmap_lock_all(valk_cmap_t *m) {
  for (u32 i = 0; i < VALK_CMAP_SEGMENTS; i++) valk_mutex_lock(&m->seg_locks[i]);
}
static void cmap_unlock_all(valk_cmap_t *m) {
  for (i32 i = VALK_CMAP_SEGMENTS - 1; i >= 0; i--)
    valk_mutex_unlock(&m->seg_locks[(u32)i]);
}

// Insert into a specific table without locking or growth checks. Used by both
// the live put (under segment lock) and by resize rehashing (under all locks).
// Returns true if a NEW key slot was occupied (caller bumps count).
static bool cmap_table_put(valk_cmap_table_t *t, char *key, valk_lval_t *val) {
  u64 mask = t->capacity - 1;
  u64 h = cmap_hash(key);
  for (u64 i = 0; i < t->capacity; i++) {
    u64 idx = (h + i) & mask;
    char *k = atomic_load_explicit(&t->slots[idx].key, memory_order_acquire);
    if (k == nullptr) {
      // Publish value BEFORE key so a lock-free reader that observes the key
      // is guaranteed to also observe the value.
      atomic_store_explicit(&t->slots[idx].val, val, memory_order_release);
      atomic_store_explicit(&t->slots[idx].key, key, memory_order_release);
      return true;
    }
    if (k == key) {
      atomic_store_explicit(&t->slots[idx].val, val, memory_order_release);
      return false;
    }
  }
  return false; // LCOV_EXCL_LINE - unreachable: resize keeps room
}

// Grow to a larger table. Caller must hold ALL segment locks. Old table is
// retired (chained off the new one) so concurrent lock-free readers that still
// hold the old pointer keep working; the stop-the-world GC reclaims it.
static void cmap_resize(valk_cmap_t *m, valk_cmap_table_t *old) {
  valk_cmap_table_t *nt = cmap_table_new(m->allocator, old->capacity * 2);
  if (!nt) return; // LCOV_EXCL_LINE - OOM: leave old table in place
  u64 live = 0;
  for (u64 i = 0; i < old->capacity; i++) {
    char *k = atomic_load_explicit(&old->slots[i].key, memory_order_relaxed);
    if (k == nullptr) continue;
    valk_lval_t *v =
        atomic_load_explicit(&old->slots[i].val, memory_order_relaxed);
    if (cmap_table_put(nt, k, v)) live++;
  }
  atomic_store_explicit(&nt->count, live, memory_order_relaxed);
  nt->retired = old;
  atomic_store_explicit(&m->table, nt, memory_order_release);
}

void valk_cmap_put(valk_cmap_t *m, const char *key, valk_lval_t *val) {
  if (!m || !key) return;
  // Canonicalize once, here. Every other operation on this map then relies on
  // "same symbol == same pointer". valk_sym_intern is a pass-through before
  // singleton init, but the global env is only populated after it.
  key = valk_sym_intern(key);
  u64 h = cmap_hash(key);
  u32 seg = seg_for(h);

  valk_mutex_lock(&m->seg_locks[seg]);
  valk_cmap_table_t *t = atomic_load_explicit(&m->table, memory_order_acquire);

  // Fast path: key already present -> overwrite value in place.
  u64 mask = t->capacity - 1;
  for (u64 i = 0; i < t->capacity; i++) {
    u64 idx = (h + i) & mask;
    char *k = atomic_load_explicit(&t->slots[idx].key, memory_order_acquire);
    if (k == nullptr) break;
    if (k == key) {
      atomic_store_explicit(&t->slots[idx].val, val, memory_order_release);
      valk_mutex_unlock(&m->seg_locks[seg]);
      return;
    }
  }
  valk_mutex_unlock(&m->seg_locks[seg]);

  // No copy: the interned string is permanent and shared, so the map stores
  // the canonical pointer directly.
  char *owned = (char *)key;

  // Inserting a new key (and possibly resizing) requires exclusivity across
  // the whole table, so take all segment locks. Re-check presence under the
  // full lock in case a racing writer inserted the same key meanwhile.
  cmap_lock_all(m);
  t = atomic_load_explicit(&m->table, memory_order_acquire);

  mask = t->capacity - 1;
  bool found = false;
  for (u64 i = 0; i < t->capacity; i++) {
    u64 idx = (h + i) & mask;
    char *k = atomic_load_explicit(&t->slots[idx].key, memory_order_acquire);
    if (k == nullptr) break;
    if (k == key) {
      atomic_store_explicit(&t->slots[idx].val, val, memory_order_release);
      found = true;
      break;
    }
  }

  if (!found) {
    u64 cnt = atomic_load_explicit(&t->count, memory_order_relaxed);
    // Grow at 70% load factor to keep probe chains short.
    if ((cnt + 1) * 10 >= t->capacity * 7) {
      cmap_resize(m, t);
      t = atomic_load_explicit(&m->table, memory_order_acquire);
    }
    if (cmap_table_put(t, owned, val)) {
      atomic_fetch_add_explicit(&t->count, 1, memory_order_relaxed);
    }
  }
  cmap_unlock_all(m);
}

u64 valk_cmap_count(valk_cmap_t *m) {
  if (!m) return 0;
  valk_cmap_table_t *t = atomic_load_explicit(&m->table, memory_order_acquire);
  return atomic_load_explicit(&t->count, memory_order_relaxed);
}

void valk_cmap_foreach(valk_cmap_t *m,
                       void (*fn)(char *key, _Atomic(valk_lval_t *) *val_slot,
                                  void *ctx),
                       void *ctx) {
  if (!m || !fn) return;
  valk_cmap_table_t *t = atomic_load_explicit(&m->table, memory_order_acquire);
  for (u64 i = 0; i < t->capacity; i++) {
    char *k = atomic_load_explicit(&t->slots[i].key, memory_order_relaxed);
    if (k == nullptr) continue;
    fn(k, &t->slots[i].val, ctx);
  }
}

void valk_cmap_gc_mark(valk_cmap_t *m,
                       void (*mark_block)(void *ptr, void *ctx),
                       void (*mark_value)(valk_lval_t *val, void *ctx),
                       void *ctx) {
  if (!m) return;
  mark_block(m, ctx);
  // Mark the current table and the whole retired chain, plus every key/value.
  valk_cmap_table_t *t = atomic_load_explicit(&m->table, memory_order_acquire);
  while (t != nullptr) {
    mark_block(t, ctx);
    for (u64 i = 0; i < t->capacity; i++) {
      char *k = atomic_load_explicit(&t->slots[i].key, memory_order_relaxed);
      if (k == nullptr) continue;
      // Keys are intern-table allocations, not GC blocks — marking them would
      // walk the large-object list under a lock for every key, every mark.
      mark_value(atomic_load_explicit(&t->slots[i].val, memory_order_relaxed),
                 ctx);
    }
    t = t->retired;
  }
}
