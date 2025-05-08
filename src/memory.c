#include "memory.h"
#include "common.h"
#include <stdatomic.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

// #define VALK_SLAB_TRIBER

__thread valk_thread_context_t valk_thread_ctx = {nullptr};

char *valk_mem_allocator_e_to_string(valk_mem_allocator_e self) {
  switch (self) {
  case VALK_ALLOC_NULL:
    return "NULL Alloc";
  case VALK_ALLOC_MALLOC:
    return "Malloc Alloc";
  case VALK_ALLOC_ARENA:
    return "Arena Alloc";
  case VALK_ALLOC_SLAB:
    return "Slab Alloc";
  }
}

static valk_mem_allocator_t __allocator_malloc = {.type = VALK_ALLOC_MALLOC};

void valk_mem_init_malloc() { valk_thread_ctx.allocator = &__allocator_malloc; }

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
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memcpy(&((char *)buf->items)[buf->count], bytes, len);
  buf->count += len;
}

int valk_buffer_is_full(valk_buffer_t *buf) {
  return (buf->capacity - buf->count) == 0;
}

/// helper: round x up to next multiple of A (A must be a power of two)
/// return multiple of A
static inline size_t __valk_mem_align_up(size_t x, size_t A) {
  return (x + A - 1) & ~(A - 1);
}
static inline valk_slab_item_t *valk_slab_item_at(valk_slab_t *self,
                                                  size_t offset) {
#ifdef VALK_SLAB_TRIBER
  // No free list in concurrency
  const size_t freeLen = 0;
#else
  const size_t freeLen = (sizeof(size_t) * self->numItems);
#endif
  const size_t itemsLen = valk_slab_item_stride(self->itemSize) * offset;

  VALK_ASSERT(offset < self->numItems,
              "Offset passed in is out of bounds offset: %ld  numItems %ld",
              offset, self->numItems);
  return (void *)&((char *)self->heap)[freeLen + itemsLen];
}

valk_slab_t *valk_slab_new(size_t itemSize, size_t numItems) {
  size_t slabSize = valk_slab_size(itemSize, numItems);
  printf("Calculating slab size to be %ld\n", slabSize);
  valk_slab_t *res = valk_mem_alloc(slabSize);
  valk_slab_init(res, itemSize, numItems);
  return res;
}

void valk_slab_init(valk_slab_t *self, size_t itemSize, size_t numItems) {
  // TODO(networking): do like mmap and some platform specific slab code
  self->type = VALK_ALLOC_SLAB;

  self->itemSize = itemSize;
  self->numItems = numItems;

  for (size_t i = 0; i < numItems; i++) {

    valk_slab_item_t *item = valk_slab_item_at(self, i);
    item->handle = i;
#ifdef VALK_SLAB_TRIBER // Treiber list
    __atomic_store_n(&item->next, (i < numItems - 1) ? i + 1 : SIZE_MAX,
                     __ATOMIC_RELAXED);
#else
    ((size_t *)self->heap)[i] = i;
#endif
  }
  __atomic_store_n(&self->head, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&self->numFree, numItems, __ATOMIC_RELAXED);
}

// TODO(networking): do we even need this? might be useful for debugging
void valk_slab_free(valk_slab_t *self) { valk_mem_free(self); }

size_t valk_slab_item_stride(size_t itemSize) {
  // TODO(networking): when implementing AVX or other instruciton sets might
  // need to expand alignment parameters
  // alignof(max_align_t)  <<- is the minimal required
  // 64 according to chatgpt is the cacheline alignment, which is better for
  // slabs
  return __valk_mem_align_up(sizeof(valk_slab_item_t) + itemSize, 64);
}

size_t valk_slab_size(size_t itemSize, size_t numItems) {
  size_t stride = valk_slab_item_stride(itemSize);
  printf("Calculated stride %ld\n", stride);
  const size_t freelen = sizeof(size_t) * numItems; // guranteed alignment

  return sizeof(valk_slab_t) + freelen + (stride * numItems);
}

static inline size_t __valk_slab_offset_unpack(uint64_t tag, size_t *version) {
  *version = tag >> 32;
  return tag & (size_t)UINT32_MAX;
}

static inline uint64_t __valk_slab_offset_pack(size_t offset, size_t version) {
  return ((uint64_t)version << 32) | (offset & (size_t)UINT32_MAX);
}

valk_slab_item_t *valk_slab_aquire(valk_slab_t *self) {
  VALK_ASSERT(self->numFree > 0,
              "Attempted to aquire, when the slab is already full",
              self->numFree);
  valk_slab_item_t *res;
#ifdef VALK_SLAB_TRIBER // Threadsafe
  uint64_t oldTag, newTag;
  size_t head, next, version;
  do {
    oldTag = __atomic_load_n(&self->head, __ATOMIC_ACQUIRE);
    head = __valk_slab_offset_unpack(oldTag, &version);
    VALK_ASSERT(head != SIZE_MAX, "Shits fully busy");
    next =
        __atomic_load_n(&valk_slab_item_at(self, head)->next, __ATOMIC_ACQUIRE);
    newTag = __valk_slab_offset_pack(next, version + 1);
  } while (!__atomic_compare_exchange_n(&self->head, &oldTag, newTag, false,
                                        __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));

  __atomic_fetch_sub(&self->numFree, 1, __ATOMIC_RELAXED);

  return valk_slab_item_at(self, head);

#else // Not threadsafe
  // pop  free item
  size_t offset = ((size_t *)self->heap)[0];
  ((size_t *)self->heap)[0] = ((size_t *)self->heap)[self->numFree - 1];
  ((size_t *)self->heap)[self->numFree - 1] = offset;
  --self->numFree;

  // Lookup this item in the slab and return
  const size_t freeLen = (sizeof(size_t) * self->numItems);
  const size_t itemsLen = valk_slab_item_stride(self->itemSize) * offset;

  res = (void *)&((char *)self->heap)[freeLen + itemsLen];
  const size_t swapTo = ((size_t *)self->heap)[0];
  printf("Aquiring slab: %ld :: idx : %ld : swap %ld\n", res->handle, offset,
         swapTo);
#endif
  return res;
}

void valk_slab_release(valk_slab_t *self, valk_slab_item_t *item) {
#ifdef VALK_SLAB_TRIBER
  uint64_t oldTag, newTag;
  size_t head, version;
  do {
    oldTag = __atomic_load_n(&self->head, __ATOMIC_ACQUIRE);
    head = __valk_slab_offset_unpack(oldTag, &version);
    __atomic_store_n(&item->next, head, __ATOMIC_RELEASE);
    newTag = __valk_slab_offset_pack(item->handle, version + 1);
  } while (!__atomic_compare_exchange_n(&self->head, &oldTag, newTag, false,
                                        __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));

  __atomic_fetch_add(&self->numFree, 1, __ATOMIC_RELAXED);

#else
  // find the slab handle
  for (size_t i = 0; i < self->numItems; ++i) {
    const size_t handle = ((size_t *)self->heap)[i];

    if (handle == item->handle) {
      const size_t target = self->numFree;
      // Swap it out with a stale one
      printf("Releasing slab: %ld [idx: %ld]: swaping with %ld[idx: %ld]\n",
             item->handle, i, ((size_t *)self->heap)[target], target);
      ((size_t *)self->heap)[i] = ((size_t *)self->heap)[target];
      ((size_t *)self->heap)[target] = handle;
      ++self->numFree;
      return;
    }
  }
  VALK_RAISE("Hey man, the slab item you tried to release was bullshit %ld",
             item->handle);
#endif

  // Swap it in as free
}

void valk_slab_release_ptr(valk_slab_t *self, void *data) {
  // This function will look back item size bytes in the array, to figure out
  // the handle and then free that shit
  valk_slab_release(self, valk_container_of(data, valk_slab_item_t, data));
}

//
/* alignment = power‑of‑two */
static inline size_t __alignment_adjustment(void *ptr, size_t alignment) {
  uintptr_t addr = (uintptr_t)ptr;
  uintptr_t mask = alignment - 1;               /* 0b…111 */
  uintptr_t misalign = addr & mask;             /* how far we’re off */
  return misalign ? (alignment - misalign) : 0; /* bytes to *add* forward */
}

void valk_mem_arena_init(valk_mem_arena_t *self, size_t capacity) {
  self->type = VALK_ALLOC_ARENA;
  self->capacity = capacity;
  self->offset = __alignment_adjustment(&self->heap, alignof(max_align_t));
}

void valk_mem_arena_reset(valk_mem_arena_t *self) {
  __atomic_store_n(&self->offset, 0, __ATOMIC_SEQ_CST);
}

// TODO(networking): should probably write some unit tests for all this math
void *valk_mem_arena_alloc(valk_mem_arena_t *self, size_t bytes) {
  size_t oldVal = __atomic_load_n(&self->offset, __ATOMIC_RELAXED);
  do {
    size_t newVal = oldVal + bytes;
    newVal += __alignment_adjustment(&self->heap[newVal], alignof(max_align_t));
    VALK_ASSERT((newVal) < self->capacity,
                "Arena ran out of memory during alloc, %ld + %ld > %ld", oldVal,
                bytes, self->capacity);
    if (__atomic_compare_exchange_n(&self->offset, &oldVal, newVal, 1,
                                    __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
      return &(self->heap)[oldVal];
    }
  } while (1);
}

void *valk_mem_allocator_alloc(valk_mem_allocator_t *self, size_t bytes) {
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to alloc %ld",
              bytes);
  // Order by performance.
  switch (self->type) {
  case VALK_ALLOC_NULL:
    VALK_RAISE("Alloc on NULL allocator %ld", bytes);
    return NULL;
  case VALK_ALLOC_ARENA:
    return valk_mem_arena_alloc((void *)self, bytes);
  case VALK_ALLOC_SLAB:
    return (void *)valk_slab_aquire((void *)self)->data;
  case VALK_ALLOC_MALLOC:
    return malloc(bytes);
  }
}

void *valk_mem_allocator_calloc(valk_mem_allocator_t *self, size_t num,
                                size_t size) {
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %ld :: size: %ld",
              num, size);
  void *res;
  // Order by performance.
  switch (self->type) {
  case VALK_ALLOC_NULL:
    VALK_RAISE("Calloc on NULL allocator num: %ld :: size: %ld", num, size);
    res = NULL;
    break;
  case VALK_ALLOC_ARENA:
    res = valk_mem_arena_alloc((void *)self, num * size);
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memset(res, 0, num * size);
    break;
  case VALK_ALLOC_SLAB:
    res = valk_slab_aquire((void *)self);
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memset(res, 0, num * size);
    break;
  case VALK_ALLOC_MALLOC:
    res = calloc(num, size);
    break;
  }
  return res;
}

void *valk_mem_allocator_realloc(valk_mem_allocator_t *self, void *ptr,
                                 size_t new_size) {
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %p :: size: %ld",
              ptr, new_size);

  // Order by performance.
  switch (self->type) {
  case VALK_ALLOC_NULL:
    VALK_RAISE("Realloc on NULL allocator ptr: %p :: size: %ld", ptr, new_size);
    return NULL;
  case VALK_ALLOC_ARENA:
    // cant really free in arenas soo... just make a new one i guess
    return valk_mem_arena_alloc((void *)self, new_size);
  case VALK_ALLOC_SLAB:
    // slabs are all of the same size, make sure we dont try to resize it to
    // something bigger than the slab
    size_t slabSize = ((valk_slab_t *)self)->itemSize;
    VALK_ASSERT(
        new_size <= slabSize,
        "Realloc with slab allocator is unsafe,\n  tried to allocate more "
        "memory than fits in a slab\n %ld wanted, but %ld is the size",
        new_size, slabSize);
    return ptr;
  case VALK_ALLOC_MALLOC:
    return realloc(ptr, new_size);
  }
}

void valk_mem_allocator_free(valk_mem_allocator_t *self, void *ptr) {
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %p",
              ptr);

  // printf("Freeing %p\n", ptr);
  switch (self->type) {
  case VALK_ALLOC_NULL:
    VALK_RAISE("Free on NULL allocator %p", ptr);
  case VALK_ALLOC_ARENA:
    return;
  case VALK_ALLOC_SLAB:
    valk_slab_release_ptr((void *)self, ptr);
    return;
  case VALK_ALLOC_MALLOC:
    free(ptr);
    return;
  }
}
