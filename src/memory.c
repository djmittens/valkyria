#include "memory.h"

#include <stdatomic.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "collections.h"
#include "common.h"

#define VALK_SLAB_TREIBER_STACK
#define VALK_SLAB_VERSIONS

__thread valk_thread_context_t valk_thread_ctx = {nullptr};

#ifdef VALK_ARC_DEBUG
#include "debug.h"
void __valk_arc_trace_report_print(valk_arc_trace_info *traces, size_t num) {
  for (size_t i = 0; i < num; i++) {
    const char *shit;
    switch (traces->kind) {
      case VALK_TRACE_ACQUIRE:
        shit = "ACQUIRE";
        break;
      case VALK_TRACE_RELEASE:
        shit = "RELEASE";
        break;
      case VALK_TRACE_NEW:
        shit = "NEW";
        break;
      case VALK_TRACE_FREE:
        shit = "FREE";
        break;
    }
    fprintf(stderr, "[%s] refcount[%ld] %s()|%s:%d \n", shit, traces->refcount,
            traces->function, traces->file, traces->line);
    valk_trace_print(traces->stack, traces->size);
    traces++;
  }
}
#endif

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

static inline bool is_pow2(size_t x) { return x && ((x & (x - 1)) == 0); }

void valk_ring_init(valk_ring_t *self, size_t capacity) {
  VALK_ASSERT(is_pow2(capacity),
              "Ring buffer capacity must be pow of 2, to reduce branching, %ld",
              capacity);
  self->offset = 0;
  self->capacity = capacity;
  memset(self->items, 0, capacity);
}

void valk_ring_write(valk_ring_t *self, uint8_t *data, size_t len) {
  size_t offset = self->offset;
  uint8_t *buf = (void *)self->items;

  // printf("Offset: %ld\n", offset);
  /// 0 1 2 3 4 5 6
  ///     ^           7

  while (len) {
    size_t dt = self->capacity - offset;

    if (len < dt) {
      // printf("copying offset %ld: dt: %ld, end: %c\n", offset, len, data[len
      // - 1]);
      memcpy(buf + offset, data, len);
      offset = offset + len;
      break;
    } else {
      // printf("copying offset %ld: dt: %ld, end: %c\n", offset, dt, data[dt -
      // 1]);
      memcpy(buf + offset, data, dt);
      offset = 0;
    }

    data += dt;
    len -= dt;
  }

  self->offset = offset % self->capacity;
}

void valk_ring_rewind(valk_ring_t *self, size_t n) {
  size_t mask = self->capacity - 1;         /* 0111… pattern */
  self->offset = (self->offset - n) & mask; /* subtract, then wrap by masking */
}

void valk_ring_read(valk_ring_t *self, size_t n, void *dst) {
  /* --- normalise inputs ------------------------------------------ */
  size_t cap = self->capacity;
  size_t head = self->offset % cap; /* in case callers misbehave  */
  n %= cap;                         /* ignore full extra laps     */

  /* --- split request into contiguous chunks ---------------------- */
  size_t first = cap - head; /* bytes until physical end   */
  if (first > n) first = n;  /* clamp to what we need      */
  size_t second = n - first; /* 0 if we stayed in-range    */

  const uint8_t *buf = (const uint8_t *)self->items;
  uint8_t *out = (uint8_t *)dst;

  memcpy(out, buf + head, first);
  if (second) memcpy(out + first, buf, second);

  /* ── advance head (optional: keep the ring consistent) ─────────── */
  self->offset = (head + n) & (cap - 1); /* cap is power-of-2 – cheap */
}

void valk_ring_fread(valk_ring_t *self, size_t n, FILE *f) {
  const uint8_t *base = (const uint8_t *)self->items;
  size_t cap = self->capacity;
  size_t head = self->offset; /* local copy for speed   */

  while (n) {
    /* contiguous bytes left in this lap */
    size_t chunk = cap - head;
    if (chunk > n) chunk = n;

    fwrite(base + head, 1, chunk, f);

    /* advance */
    head = (head + chunk) & (cap - 1); /* ring wrap (use % if cap not pow-2) */
    n -= chunk;
  }
  self->offset = head; /* commit the consumer cursor */
}

void valk_ring_print(valk_ring_t *self, FILE *f) {
  fwrite(&((uint8_t *)self->items)[self->offset], 1,
         self->capacity - self->offset, f);
  fwrite(&((uint8_t *)self->items)[0], 1, self->offset, f);
}

/// helper: round x up to next multiple of A (A must be a power of two)
/// return multiple of A
static inline size_t __valk_mem_align_up(size_t x, size_t A) {
  return (x + A - 1) & ~(A - 1);
}
static inline valk_slab_item_t *valk_slab_item_at(valk_slab_t *self,
                                                  size_t offset) {
#ifdef VALK_SLAB_TREIBER_STACK
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
  VALK_DEBUG("Slab size = %ld", slabSize);
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
#ifdef VALK_SLAB_TREIBER_STACK  // Treiber list
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
  VALK_DEBUG("Slab stride = %ld", stride);
  const size_t freelen = sizeof(size_t) * numItems;  // guranteed alignment

  return sizeof(valk_slab_t) + freelen + (stride * numItems);
}

static inline size_t __valk_slab_offset_unpack(uint64_t tag, size_t *version) {
#ifdef VALK_SLAB_VERSIONS
  *version = tag >> 32;
#else
  *version = 0;
#endif
  return tag & (size_t)UINT32_MAX;
}

static inline uint64_t __valk_slab_offset_pack(size_t offset, size_t version) {
#ifdef VALK_SLAB_VERSIONS
  return ((uint64_t)version << 32) | (offset & (size_t)UINT32_MAX);
#else
  return (offset & (size_t)UINT32_MAX);
#endif
}

valk_slab_item_t *valk_slab_aquire(valk_slab_t *self) {
  VALK_ASSERT(self->numFree > 0,
              "Attempted to aquire, when the slab is already full");
  valk_slab_item_t *res;
#ifdef VALK_SLAB_TREIBER_STACK  // Threadsafe
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
  res = valk_slab_item_at(self, head);
  // printf("Slab Aquired %ld %p\n", head, res->data);

  return res;

#else  // Not threadsafe
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
  VALK_TRACE("Acquiring slab: handle=%ld idx=%ld swap=%ld", res->handle, offset,
         swapTo);
#endif
  return res;
}

void valk_slab_release(valk_slab_t *self, valk_slab_item_t *item) {
#ifdef VALK_SLAB_TREIBER_STACK
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
      VALK_TRACE("Releasing slab: handle=%ld idx=%ld swap=%ld", item->handle, i, ((size_t *)self->heap)[target]);
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
  uint64_t v;
  __valk_slab_offset_unpack(
      valk_container_of(data, valk_slab_item_t, data)->handle, &v);
  // printf("Slab Releasing %ld %p\n", offset, data);
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
  // Layout: [optional padding][size_t size][padding to align payload][payload]
  size_t old = __atomic_load_n(&self->offset, __ATOMIC_RELAXED);
  for (;;) {
    size_t hdr = old + sizeof(size_t);
    // Align payload after header to max_align_t
    size_t adj = __alignment_adjustment(&self->heap[hdr], alignof(max_align_t));
    size_t payload = hdr + adj;
    size_t end = payload + bytes;
    VALK_ASSERT(end < self->capacity,
                "Arena OOM: %ld + sizeof(size) + %ld + %ld > %ld", old, adj,
                bytes, self->capacity);
    if (__atomic_compare_exchange_n(&self->offset, &old, end, 1,
                                    __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
      // Store payload size right before payload pointer
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      *((size_t *)&self->heap[payload] - 1) = bytes;
      return &self->heap[payload];
    }
  }
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
      VALK_RAISE("Realloc on NULL allocator ptr: %p :: size: %ld", ptr,
                 new_size);
      return NULL;
    case VALK_ALLOC_ARENA: {
      // Copy-alloc semantics for arena realloc
      size_t old_size = 0;
      if (ptr) {
        old_size = *(((size_t *)ptr) - 1);
      }
      void *np = valk_mem_arena_alloc((void *)self, new_size);
      if (ptr && np) {
        size_t n = old_size < new_size ? old_size : new_size;
        // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
        memcpy(np, ptr, n);
      }
      return np;
    }
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

void valk_gc_init(valk_gc_heap_t *self, size_t capacity) {
  self->free = capacity;
  self->capacity = capacity;
  self->allocator = valk_thread_ctx.allocator;
  self->sentinel.next = &self->sentinel;
  self->sentinel.prev = &self->sentinel;
  self->sentinel.marked = 1;
}

void valk_gc_mark(valk_gc_heap_t *self, void *ptr) {
  valk_gc_chunk_t *chunk = (valk_gc_chunk_t *)ptr - 1;
  if (self->mark) {
    self->mark(chunk);
  } else {
    chunk->marked = 1;
  }
}

void *valk_gc_alloc(valk_gc_heap_t *heap, size_t size) {
  if ((heap->free - size) == 0) {
    // Try to free some memory to allocate this thing.
    valk_gc_sweep(heap);
    VALK_ASSERT(
        (heap->free - size) == 0,
        "Failed free enough memory to allocate %ld bytes on heap with %ld size",
        size, heap->capacity);
  }

  valk_gc_chunk_t *res =
      valk_mem_allocator_alloc(heap->allocator, size + sizeof(valk_gc_chunk_t));
  heap->free -= size;

  res->marked = 1;
  valk_dll_insert_node(&heap->sentinel, res);
  return res + 1;  // skip over to the good stuff
}

void *valk_gc_realloc(valk_gc_heap_t *heap, void *ptr, size_t size) {
  valk_gc_chunk_t *self = ptr;
  --self;  // get ourselves the header
  self = valk_mem_allocator_realloc(heap->allocator, self,
                                    size + sizeof(valk_gc_heap_t));
  self->prev->next = self;
  self->next->prev = self;
  return self + 1;  // uhhh yeah the good shit
}

void valk_gc_sweep(valk_gc_heap_t *self) {
  valk_gc_chunk_t *node = self->sentinel.next;
  while (node != &self->sentinel) {
    if (!node->marked) {
      if (self->finalize) {
        self->finalize(node);
      } else {
        // Eject this shit
        valk_dll_pop(node);
        valk_mem_allocator_free(self->allocator, node);
      }
    } else {
      // reset this bad boii for the next time
      node->marked = 0;
    }
  }
}
