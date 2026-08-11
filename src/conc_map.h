#pragma once

// Concurrent string-keyed map for the shared/global environment.
//
// Design (Java ConcurrentHashMap / Clojure-namespace inspired):
//   - Open-addressed (linear probing) table of {key, value} entry slots.
//   - Lock-free reads: a lookup hashes, probes, and loads each slot's key
//     pointer and value pointer with acquire ordering. No lock on the read
//     path (the global env is read on essentially every symbol resolution).
//   - Striped write locks: the table is partitioned into N segments; an
//     insert locks only the segment its bucket falls in, so concurrent
//     writers to different regions don't contend.
//   - Value update on an existing key is a single atomic release store into
//     the slot (no structural change, no lock needed for correctness, but we
//     still take the segment lock to serialize against a concurrent insert of
//     the same key).
//   - Resize: when load factor is exceeded, a writer (holding all segment
//     locks) allocates a larger table, rehashes, atomically publishes the new
//     table pointer (release), and RETIRES the old table rather than freeing
//     it, so a lock-free reader still walking the old table never touches
//     freed memory. Retired tables are reclaimed by the stop-the-world GC.
//
// Memory model: the map and its tables/keys are allocated from the GC heap
// (the env's allocator). The GC is stop-the-world, so the collector can mark
// and relocate map contents with no mutator running. Therefore this structure
// only needs to be correct for concurrent MUTATOR access between collections.

#include <stdatomic.h>

#include "types.h"
#include "valk_thread.h"

typedef struct valk_lval_t valk_lval_t;

typedef struct {
  _Atomic(char *) key;        // interned/owned key string; nullptr = empty
  _Atomic(valk_lval_t *) val; // value pointer
} valk_cmap_slot_t;

typedef struct valk_cmap_table {
  u64 capacity;                       // number of slots (power of two)
  _Atomic u64 count;                  // live entries (approximate under race)
  struct valk_cmap_table *retired;    // previous table kept alive for readers
  valk_cmap_slot_t slots[];           // flexible array
} valk_cmap_table_t;

#define VALK_CMAP_SEGMENTS 16

typedef struct valk_cmap {
  _Atomic(valk_cmap_table_t *) table; // current table (published with release)
  valk_mutex_t seg_locks[VALK_CMAP_SEGMENTS];
  void *allocator;                    // GC heap the tables/keys live in
} valk_cmap_t;

// Create an empty concurrent map with the given initial slot capacity
// (rounded up to a power of two, min 16). Allocated from `allocator` (a
// valk_mem_allocator_t*, typically the GC heap).
valk_cmap_t *valk_cmap_new(void *allocator, u64 initial_capacity);

// Lock-free lookup. Returns the value for `key`, or nullptr if absent.
// Lookup. Keys are hashed and compared BY POINTER (see conc_map.c), so:
//   valk_cmap_get_interned - caller guarantees `key` is a canonical
//                            valk_sym_intern pointer. One integer compare.
//   valk_cmap_get          - any string; interns first, then delegates.
valk_lval_t *valk_cmap_get_interned(valk_cmap_t *m, const char *key);
valk_lval_t *valk_cmap_get(valk_cmap_t *m, const char *key);

// Insert or overwrite `key` -> `val`. The key is copied into the map's
// allocator on first insert. Grows the table if the load factor is exceeded.
void valk_cmap_put(valk_cmap_t *m, const char *key, valk_lval_t *val);

// Number of live entries (snapshot; may be stale under concurrent writers).
u64 valk_cmap_count(valk_cmap_t *m);

// Iterate all live {key, val} pairs, invoking fn for each. NOT safe to call
// concurrently with writers (intended for GC marking / image dump, both of
// which run stop-the-world). `val` is passed by address so callers (GC) can
// update the slot in place during evacuation.
void valk_cmap_foreach(valk_cmap_t *m,
                       void (*fn)(char *key, _Atomic(valk_lval_t *) *val_slot,
                                  void *ctx),
                       void *ctx);

// GC support (stop-the-world only). Visit every heap allocation owned by the
// map so the collector can mark them and keep them alive:
//   - mark_block(ptr, ctx): the map struct, each table (incl. retired chain),
//     and each key string. These are opaque blocks with no further children.
//   - mark_value(lval, ctx): each live value (a valk_lval_t* with children).
// Both callbacks tolerate nullptr.
void valk_cmap_gc_mark(valk_cmap_t *m,
                       void (*mark_block)(void *ptr, void *ctx),
                       void (*mark_value)(valk_lval_t *val, void *ctx),
                       void *ctx);
