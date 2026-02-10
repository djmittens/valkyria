#include "memory.h"

#include <errno.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#include "common.h"
#include "log.h"

#define VALK_SLAB_TREIBER_STACK
#define VALK_SLAB_VERSIONS

static inline sz __valk_mem_align_up(sz x, sz A) {
  return (x + A - 1) & ~(A - 1);
}

static inline valk_slab_item_t *valk_slab_item_at(valk_slab_t *self,
                                                  sz offset) {
#ifdef VALK_SLAB_TREIBER_STACK
  const sz freeLen = 0;
#else
  const sz freeLen = (sizeof(u64) * self->numItems);
#endif
  const sz itemsLen = valk_slab_item_stride(self->itemSize) * offset;

  // LCOV_EXCL_BR_START - assertion failure branch
  VALK_ASSERT(offset < self->numItems,
              "Offset passed in is out of bounds offset: %zu  numItems %zu",
              offset, self->numItems);
  // LCOV_EXCL_BR_STOP
  return (void *)&((char *)self->heap)[freeLen + itemsLen];
}

static void valk_slab_init(valk_slab_t *self, sz itemSize, sz numItems);

valk_slab_t *valk_slab_new(sz itemSize, sz numItems) {
  sz slabSize = valk_slab_size(itemSize, numItems);
  sz pageSize = 4096;
  sz mmapSize = (slabSize + pageSize - 1) & ~(pageSize - 1);
  
  void *mem = mmap(nullptr, mmapSize, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mem == MAP_FAILED) { // LCOV_EXCL_BR_LINE
    VALK_ERROR("mmap failed for slab of %zu bytes: %s", mmapSize, strerror(errno)); // LCOV_EXCL_LINE
    return nullptr; // LCOV_EXCL_LINE
  }
  
  valk_slab_t *res = mem;
  res->mmap_size = mmapSize;
  valk_slab_init(res, itemSize, numItems);
  return res;
}

static void valk_slab_init(valk_slab_t *self, sz itemSize, sz numItems) {
  self->type = VALK_ALLOC_SLAB;

  self->itemSize = itemSize;
  self->numItems = numItems;

  for (sz i = 0; i < numItems; i++) {
    valk_slab_item_t *item = valk_slab_item_at(self, i);
    item->handle = i;
#ifdef VALK_SLAB_TREIBER_STACK
    __atomic_store_n(&item->next, (i < numItems - 1) ? i + 1 : SIZE_MAX,
                     __ATOMIC_RELAXED);
#else
    ((u64 *)self->heap)[i] = i;
#endif
  }
  __atomic_store_n(&self->head, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&self->numFree, numItems, __ATOMIC_RELAXED);
  __atomic_store_n(&self->overflowCount, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&self->peakUsed, 0, __ATOMIC_RELAXED);
  atomic_store_explicit(&self->total_acquires, 0, memory_order_relaxed);
  atomic_store_explicit(&self->total_releases, 0, memory_order_relaxed);

  sz bitmap_bytes = (numItems + 7) / 8;
  // NOLINTNEXTLINE(clang-analyzer-optin.portability.UnixAPI) - 0-size calloc is valid edge case
  self->usage_bitmap = calloc(bitmap_bytes, 1);
  __atomic_store_n(&self->bitmap_version, 0, __ATOMIC_RELAXED);
}

void valk_slab_free(valk_slab_t *self) {
  if (!self) return;
  
  if (self->usage_bitmap) { // LCOV_EXCL_BR_LINE
    free(self->usage_bitmap);
    self->usage_bitmap = nullptr;
  }

  if (self->mmap_size > 0) { // LCOV_EXCL_BR_LINE
    munmap(self, self->mmap_size);
  } else {
    valk_mem_free(self);
  }
}

sz valk_slab_item_stride(sz itemSize) {
  return __valk_mem_align_up(sizeof(valk_slab_item_t) + itemSize, 64);
}

sz valk_slab_size(sz itemSize, sz numItems) {
  sz stride = valk_slab_item_stride(itemSize);
  const sz freelen = sizeof(u64) * numItems;

  return sizeof(valk_slab_t) + freelen + (stride * numItems);
}

static inline u64 __valk_slab_offset_unpack(u64 tag, u64 *version) {
#ifdef VALK_SLAB_VERSIONS
  *version = tag >> 32;
#else
  *version = 0;
#endif
  return tag & (u64)UINT32_MAX;
}

static inline u64 __valk_slab_offset_pack(u64 offset, u64 version) {
#ifdef VALK_SLAB_VERSIONS
  return ((u64)version << 32) | (offset & (u64)UINT32_MAX);
#else
  return (offset & (u64)UINT32_MAX);
#endif
}

valk_slab_item_t *valk_slab_aquire(valk_slab_t *self) {
  valk_slab_item_t *res;
#ifdef VALK_SLAB_TREIBER_STACK
  sz expected, desired;
  do {
    expected = __atomic_load_n(&self->numFree, __ATOMIC_ACQUIRE);
    if (expected == 0) {
      __atomic_fetch_add(&self->overflowCount, 1, __ATOMIC_RELAXED);
      return nullptr;
    }
    desired = expected - 1;
  } while (!__atomic_compare_exchange_n(&self->numFree, &expected, desired,
                                        false, __ATOMIC_ACQ_REL,
                                        __ATOMIC_RELAXED));

  sz oldTag, newTag;
  sz head, next;
  u64 version;
  do {
    oldTag = __atomic_load_n(&self->head, __ATOMIC_ACQUIRE);
    head = __valk_slab_offset_unpack(oldTag, &version);
    if (head == SIZE_MAX) { // LCOV_EXCL_BR_LINE
      __atomic_fetch_add(&self->numFree, 1, __ATOMIC_RELAXED);
      return nullptr;
    }
    next =
        __atomic_load_n(&valk_slab_item_at(self, head)->next, __ATOMIC_ACQUIRE);
    newTag = __valk_slab_offset_pack(next, version + 1);
  } while (!__atomic_compare_exchange_n(&self->head, &oldTag, newTag, false,
                                        __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));
  res = valk_slab_item_at(self, head);

  if (self->usage_bitmap) {
    u64 byte_idx = head / 8;
    u8 bit_mask = 1 << (head % 8);
    __atomic_fetch_or(&self->usage_bitmap[byte_idx], bit_mask, __ATOMIC_RELAXED);
    __atomic_fetch_add(&self->bitmap_version, 1, __ATOMIC_RELAXED);
  }

  sz used = self->numItems - __atomic_load_n(&self->numFree, __ATOMIC_RELAXED);
  sz current_peak;
  do {
    current_peak = __atomic_load_n(&self->peakUsed, __ATOMIC_RELAXED);
    if (used <= current_peak) break;
  } while (!__atomic_compare_exchange_n(&self->peakUsed, &current_peak, used, // LCOV_EXCL_BR_LINE
                                         false, __ATOMIC_RELAXED, __ATOMIC_RELAXED));

  atomic_fetch_add_explicit(&self->total_acquires, 1, memory_order_relaxed);

  return res;

#else
  if (self->numFree == 0) {
    __atomic_fetch_add(&self->overflowCount, 1, __ATOMIC_RELAXED);
    return nullptr;
  }
  u64 offset = ((u64 *)self->heap)[0];
  ((u64 *)self->heap)[0] = ((u64 *)self->heap)[self->numFree - 1];
  ((u64 *)self->heap)[self->numFree - 1] = offset;
  --self->numFree;

  const u64 freeLen = (sizeof(u64) * self->numItems);
  const u64 itemsLen = valk_slab_item_stride(self->itemSize) * offset;

  res = (void *)&((char *)self->heap)[freeLen + itemsLen];
  const u64 swapTo = ((u64 *)self->heap)[0];
  VALK_TRACE("Acquiring slab: handle=%ld idx=%ld swap=%ld", res->handle, offset,
         swapTo);

  u64 used = self->numItems - self->numFree;
  if (used > self->peakUsed) {
    self->peakUsed = used;
  }
#endif
  return res;
}

void valk_slab_release(valk_slab_t *self, valk_slab_item_t *item) {
#ifdef VALK_SLAB_TREIBER_STACK
  sz slot_idx = item->handle;

  if (self->usage_bitmap && slot_idx < self->numItems) {
    sz byte_idx = slot_idx / 8;
    u8 bit_mask = 1 << (slot_idx % 8);
    __atomic_fetch_and(&self->usage_bitmap[byte_idx], ~bit_mask, __ATOMIC_RELAXED);
    __atomic_fetch_add(&self->bitmap_version, 1, __ATOMIC_RELAXED);
  }

  sz oldTag, newTag;
  sz head;
  u64 version;
  do {
    oldTag = __atomic_load_n(&self->head, __ATOMIC_ACQUIRE);
    head = __valk_slab_offset_unpack(oldTag, &version);
    __atomic_store_n(&item->next, head, __ATOMIC_RELEASE);
    newTag = __valk_slab_offset_pack(item->handle, version + 1);
  } while (!__atomic_compare_exchange_n(&self->head, &oldTag, newTag, false,
                                        __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));

  __atomic_fetch_add(&self->numFree, 1, __ATOMIC_RELAXED);

  atomic_fetch_add_explicit(&self->total_releases, 1, memory_order_relaxed);

#else
  for (u64 i = 0; i < self->numItems; ++i) {
    const u64 handle = ((u64 *)self->heap)[i];

    if (handle == item->handle) {
      const u64 target = self->numFree;
      VALK_TRACE("Releasing slab: handle=%ld idx=%ld swap=%ld", item->handle, i, ((u64 *)self->heap)[target]);
      ((u64 *)self->heap)[i] = ((u64 *)self->heap)[target];
      ((u64 *)self->heap)[target] = handle;
      ++self->numFree;
      return;
    }
  }
  VALK_RAISE("Hey man, the slab item you tried to release was bullshit %ld",
             item->handle);
#endif
}

void valk_slab_release_ptr(valk_slab_t *self, void *data) {
  u64 v;
  __valk_slab_offset_unpack(
      valk_container_of(data, valk_slab_item_t, data)->handle, &v);
  valk_slab_release(self, valk_container_of(data, valk_slab_item_t, data));
}

void valk_slab_bitmap_snapshot(valk_slab_t *slab, valk_slab_bitmap_t *out) {
  if (!slab || !out) return;  // LCOV_EXCL_BR_LINE - null check
  out->data = nullptr;
  out->bytes = 0;
  out->version = 0;

  if (!slab->usage_bitmap) return;  // LCOV_EXCL_BR_LINE - tested by test_slab_bitmap_snapshot_no_bitmap

  sz bitmap_bytes = (slab->numItems + 7) / 8;
  out->data = malloc(bitmap_bytes);
  if (!out->data) return;  // LCOV_EXCL_BR_LINE - malloc failure

  out->version = __atomic_load_n(&slab->bitmap_version, __ATOMIC_ACQUIRE);
  memcpy(out->data, slab->usage_bitmap, bitmap_bytes);
  out->bytes = bitmap_bytes;
}

void valk_slab_bitmap_free(valk_slab_bitmap_t *bmp) {
  if (bmp && bmp->data) {
    free(bmp->data);
    bmp->data = nullptr;
    bmp->bytes = 0;
  }
}

void valk_bitmap_delta_init(valk_bitmap_delta_t *delta) {
  if (!delta) return;
  delta->runs = nullptr;
  delta->run_count = 0;
  delta->run_capacity = 0;
  delta->from_version = 0;
  delta->to_version = 0;
}

void valk_bitmap_delta_free(valk_bitmap_delta_t *delta) {
  if (delta && delta->runs) {
    free(delta->runs);
    delta->runs = nullptr;
    delta->run_count = 0;
    delta->run_capacity = 0;
  }
}

static bool delta_add_run(valk_bitmap_delta_t *delta, sz offset, sz count, u8 byte) {
  if (delta->run_count >= delta->run_capacity) {
    sz new_cap = delta->run_capacity ? delta->run_capacity * 2 : 64;
    valk_bitmap_delta_run_t *new_runs = realloc(delta->runs, new_cap * sizeof(valk_bitmap_delta_run_t));
    if (!new_runs) return false; // LCOV_EXCL_BR_LINE - realloc OOM
    delta->runs = new_runs;
    delta->run_capacity = new_cap;
  }
  delta->runs[delta->run_count].offset = offset;
  delta->runs[delta->run_count].count = count;
  delta->runs[delta->run_count].byte = byte;
  delta->run_count++;
  return true;
}

bool valk_bitmap_delta_compute(const valk_slab_bitmap_t *curr,
                                const valk_slab_bitmap_t *prev,
                                valk_bitmap_delta_t *out) {
  if (!curr || !prev || !out) return false;
  if (!curr->data || !prev->data) return false; // LCOV_EXCL_BR_LINE
  if (curr->bytes != prev->bytes) return false;

  valk_bitmap_delta_init(out);
  out->from_version = prev->version;
  out->to_version = curr->version;

  sz i = 0;
  while (i < curr->bytes) {
    if (curr->data[i] == prev->data[i]) {
      i++;
      continue;
    }

    u8 xor_byte = curr->data[i] ^ prev->data[i];
    sz run_start = i;
    sz run_len = 1;

    while (i + run_len < curr->bytes &&
           (curr->data[i + run_len] ^ prev->data[i + run_len]) == xor_byte) {
      run_len++;
    }

    if (!delta_add_run(out, run_start, run_len, xor_byte)) { // LCOV_EXCL_BR_LINE - OOM in delta_add_run
      valk_bitmap_delta_free(out); // LCOV_EXCL_LINE
      return false; // LCOV_EXCL_LINE
    }
    i += run_len;
  }

  return true;
}

// LCOV_EXCL_BR_START - RLE serialization buffer overflow guards
sz valk_bitmap_delta_to_rle(const valk_bitmap_delta_t *delta,
                                 char *buf, sz buf_size) {
  if (!delta || !buf || buf_size < 4) {
    if (buf && buf_size > 0) buf[0] = '\0';
    return 0;
  }

  static const char hex_chars[] = "0123456789abcdef";
  char *p = buf;
  char *end = buf + buf_size - 1;

  for (sz i = 0; i < delta->run_count && p < end - 16; i++) {
    valk_bitmap_delta_run_t *run = &delta->runs[i];

    if (i > 0 && p < end) *p++ = ',';

    int n = snprintf(p, end - p, "%llu:", (unsigned long long)run->offset);
    if (n < 0 || p + n >= end) break;
    p += n;

    if (p + 2 >= end) break;
    *p++ = hex_chars[(run->byte >> 4) & 0x0F];
    *p++ = hex_chars[run->byte & 0x0F];

    if (run->count > 1) {
      n = snprintf(p, end - p, "*%llu", (unsigned long long)run->count);
      if (n < 0 || p + n >= end) break;
      p += n;
    }
  }

  *p = '\0';
  return p - buf;
}
// LCOV_EXCL_BR_STOP

sz valk_slab_bitmap_buckets(valk_slab_t *slab,
                                 sz start_slot, sz end_slot,
                                 sz num_buckets,
                                 valk_bitmap_bucket_t *out_buckets) {
  if (!slab || !out_buckets || num_buckets == 0) return 0; // LCOV_EXCL_BR_LINE
  if (!slab->usage_bitmap) return 0; // LCOV_EXCL_BR_LINE

  if (end_slot > slab->numItems) end_slot = slab->numItems;
  if (start_slot >= end_slot) return 0;

  sz total_slots = end_slot - start_slot;
  sz slots_per_bucket = (total_slots + num_buckets - 1) / num_buckets;
  if (slots_per_bucket == 0) slots_per_bucket = 1; // LCOV_EXCL_BR_LINE

  for (sz b = 0; b < num_buckets; b++) {
    out_buckets[b].used = 0;
    out_buckets[b].free = 0;
  }

  for (sz slot = start_slot; slot < end_slot; slot++) {
    sz byte_idx = slot / 8;
    u8 bit_mask = 1 << (slot % 8);
    bool is_used = (slab->usage_bitmap[byte_idx] & bit_mask) != 0;

    sz bucket_idx = (slot - start_slot) / slots_per_bucket;
    if (bucket_idx >= num_buckets) bucket_idx = num_buckets - 1; // LCOV_EXCL_BR_LINE

    if (is_used) {
      out_buckets[bucket_idx].used++;
    } else {
      out_buckets[bucket_idx].free++;
    }
  }

  return num_buckets;
}
