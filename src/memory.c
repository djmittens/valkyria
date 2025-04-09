#include "memory.h"
#include "common.h"
#include <stdlib.h>
#include <string.h>

__thread valk_thread_context_t valk_thread_ctx = {0};

static void *__valk_mem_malloc(void *heap, size_t bytes) {
  UNUSED(heap);
  return malloc(bytes);
}

static void __valk_mem_malloc_free(void *heap, void *ptr) {
  UNUSED(heap);
  free(ptr);
}

void valk_mem_init_malloc() {
  valk_thread_ctx.allocType = VALK_ALLOC_MALLOC;
  valk_thread_ctx.heap = NULL;
  valk_thread_ctx.alloc = __valk_mem_malloc;
  valk_thread_ctx.free = __valk_mem_malloc_free;
}

void valk_buffer_alloc(valk_buffer_t *buf, size_t capacity) {
  buf->capacity = capacity;
  buf->count = 0;
  // TODO(networking): use mmap with page aligned shit for this instead
  buf->items = valk_mem_alloc(capacity);
}

void valk_buffer_append(valk_buffer_t *buf, void *bytes, size_t len) {
  VALK_ASSERT(
      buf->capacity > (buf->count + len),
      "Buffer too small !!!  capacity [%ld] :: count [%ld] :: new bytes [%ld]",
      buf->capacity, buf->count, len);
  memcpy(&((char *)buf->items)[buf->count], bytes, len);
  buf->count += len;
}

int valk_buffer_is_full(valk_buffer_t *buf) {
  return (buf->capacity - buf->count) < 1;
}

static inline size_t __valk_slab_alloc_item_size(valk_slab_t *self) {
  return sizeof(valk_slab_item_t) + self->itemSize;
}

void valk_slab_alloc_init(valk_slab_t *self, size_t itemSize, size_t numItems) {
  // TODO(networking): do like mmap and some platform specific slab code
  self->heap = valk_mem_alloc(
      (sizeof(size_t) + sizeof(valk_slab_item_t) + itemSize) * numItems);

  self->itemSize = itemSize;
  self->numItems = numItems;
  self->numFree = numItems;

  const size_t itemlen = sizeof(valk_slab_item_t) + itemSize;
  const size_t freelen = sizeof(size_t) * numItems;

  for (size_t i = 0; i < numItems; i++) {
    ((size_t *)self->heap)[i] = i;
    valk_slab_item_t *item =
        (valk_slab_item_t *)&(((char *)self->heap)[(freelen) + (itemlen * i)]);
    item->handle = i;
  }
}

valk_slab_item_t *valk_slab_alloc_aquire(valk_slab_t *self) {
  if (self->numFree <= 0) {
    return NULL;
  }

  // pop  free item
  size_t offset = ((size_t *)self->heap)[0];
  ((size_t *)self->heap)[0] = ((size_t *)self->heap)[self->numFree - 1];
  ((size_t *)self->heap)[self->numFree - 1] = offset;
  --self->numFree;

  // Lookup this item in the slab and return
  const size_t freeLen = (sizeof(size_t) * self->numItems);
  const size_t itemsLen = __valk_slab_alloc_item_size(self) * offset;
  valk_slab_item_t *res = (void *)&((char *)self->heap)[freeLen + itemsLen];
  printf("Aquiring slab: %ld :: idx : %ld : swap %ld\n", res->handle, offset,
         ((size_t *)self->heap)[0]);
  return res;
}

void valk_slab_alloc_release(valk_slab_t *self, valk_slab_item_t *item) {
  // find the slab handle
  for (size_t i = 0; i < self->numItems; ++i) {
    if (((size_t *)self->heap)[i] == item->handle) {
      // Swap it out with a stale one
      size_t offset = ((size_t *)self->heap)[i];
      ((size_t *)self->heap)[i] = ((size_t *)self->heap)[self->numFree - 1];
      ((size_t *)self->heap)[self->numFree - 1] = offset;
      ++self->numFree;
      printf("Releasing slab: %ld : idx: %ld\n", item->handle, i);
      return;
    }
  }

  VALK_RAISE("Hey man, the slab item you tried to release was bullshit %ld",
             item->handle);
  // Swap it in as free
}

void valk_slab_alloc_release_ptr(valk_slab_t *self, void *data) {
  // This function will look back item size bytes in the array, to figure out
  // the handle and then free that shit
  valk_slab_alloc_release(
      self, (valk_slab_item_t *)(&((char *)data)[-sizeof(valk_slab_item_t)]));
}

void valk_mem_arena_reset(valk_mem_arena_t *self) {
  __atomic_store_n(&self->offset, 0, __ATOMIC_SEQ_CST);
}
void *valk_mem_arena_alloc(valk_mem_arena_t *self, size_t bytes) {
  size_t oldVal = __atomic_load_n(&self->offset, __ATOMIC_RELAXED);
  do {

    size_t newVal = oldVal + bytes + sizeof(size_t);
    VALK_ASSERT(newVal < self->capacity,
                "Arena ran out of memory during alloc, %ld + %ld > %ld", oldVal,
                bytes, self->capacity);
    if (__atomic_compare_exchange_n(&self->offset, &oldVal, newVal, 1,
                                    __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
      (self->heap)[newVal - bytes - sizeof(size_t)] = bytes;
      return &(self->heap)[newVal - bytes];
    }
  } while (1);
}
