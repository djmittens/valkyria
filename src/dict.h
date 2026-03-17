#pragma once
#include "types.h"
#include <stdint.h>

struct valk_lval_t;

#define DICT_EMPTY UINT32_MAX

#define DICT_ALIGN_UP(x, a) (((x) + (a) - 1) & ~((a) - 1))

typedef struct valk_dict_cell_t {
  u64 hash;
  u32 key_offset;
  u32 next;
  struct valk_lval_t *value;
} valk_dict_cell_t;

typedef struct valk_dict_t {
  u32 num_buckets;
  u32 capacity;
  u32 count;
  u32 free_head;
  u64 strings_used;
  u64 strings_cap;
} valk_dict_t;

static inline u32 *dict_buckets(valk_dict_t *d) {
  return (u32 *)((u8 *)d + sizeof(valk_dict_t));
}

static inline u64 dict_cells_offset(u32 num_buckets) {
  return DICT_ALIGN_UP(sizeof(valk_dict_t) + num_buckets * sizeof(u32),
                       alignof(valk_dict_cell_t));
}

static inline valk_dict_cell_t *dict_cells(valk_dict_t *d) {
  return (valk_dict_cell_t *)((u8 *)d + dict_cells_offset(d->num_buckets));
}

static inline char *dict_strings(valk_dict_t *d) {
  return (char *)((u8 *)d + dict_cells_offset(d->num_buckets)
         + d->capacity * sizeof(valk_dict_cell_t));
}

static inline u64 dict_block_size(u32 num_buckets, u32 capacity, u64 strings_cap) {
  return dict_cells_offset(num_buckets)
       + capacity * sizeof(valk_dict_cell_t)
       + strings_cap;
}

static inline const char *dict_key_at(valk_dict_t *d, u32 cell_idx) {
  return dict_strings(d) + dict_cells(d)[cell_idx].key_offset;
}

static inline u64 dict_hash(const char *key) {
  u64 h = 0xcbf29ce484222325ULL;
  for (const unsigned char *p = (const unsigned char *)key; *p; p++) {
    h ^= *p;
    h *= 0x100000001b3ULL;
  }
  return h;
}
