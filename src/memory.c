#include "memory.h"

#include <stdatomic.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "gc.h"
#include "log.h"

__thread valk_thread_context_t valk_thread_ctx = {.allocator = nullptr, .heap = nullptr};

// Global malloc allocator for use with VALK_WITH_ALLOC when malloc is needed
valk_mem_allocator_t valk_malloc_allocator = {.type = VALK_ALLOC_MALLOC};

char *valk_mem_allocator_e_to_string(valk_mem_allocator_e self) {
  switch (self) {
    case VALK_ALLOC_NULL:
      return "nullptr Alloc";
    case VALK_ALLOC_MALLOC:
      return "Malloc Alloc";
    case VALK_ALLOC_ARENA:
      return "Arena Alloc";
    case VALK_ALLOC_SLAB:
      return "Slab Alloc";
    case VALK_ALLOC_GC_HEAP:
      return "GC Heap Alloc";
    case VALK_ALLOC_REGION:
      return "Region Alloc";
  }
}

static valk_mem_allocator_t __allocator_malloc = {.type = VALK_ALLOC_MALLOC};

void valk_mem_init_malloc() { valk_thread_ctx.allocator = &__allocator_malloc; }

void valk_buffer_alloc(valk_buffer_t *buf, sz capacity) {
  buf->capacity = capacity;
  buf->count = 0;
  // TODO(networking): use mmap with page-aligned memory for this instead
  buf->items = valk_mem_alloc(capacity);
}

void valk_buffer_append(valk_buffer_t *buf, void *bytes, sz len) {
  // LCOV_EXCL_BR_START - assertion failure branch
  VALK_ASSERT(
      buf->capacity > (buf->count + len),
      "Buffer too small !!!  capacity [%zu] :: count [%zu] :: new bytes [%zu]",
      buf->capacity, buf->count, len);
  // LCOV_EXCL_BR_STOP
  memcpy(&((char *)buf->items)[buf->count], bytes, len);
  buf->count += len;
}

int valk_buffer_is_full(valk_buffer_t *buf) {
  return (buf->capacity - buf->count) == 0;
}

// LCOV_EXCL_BR_START - internal helper, x=0 case not used in practice
static inline bool is_pow2(u64 x) { return x && ((x & (x - 1)) == 0); }
// LCOV_EXCL_BR_STOP

void valk_ring_init(valk_ring_t *self, sz capacity) {
  // LCOV_EXCL_BR_START - assertion failure branch
  VALK_ASSERT(is_pow2(capacity),
              "Ring buffer capacity must be pow of 2, to reduce branching, %zu",
              capacity);
  // LCOV_EXCL_BR_STOP
  self->offset = 0;
  self->capacity = capacity;
  memset(self->items, 0, capacity);
}

void valk_ring_write(valk_ring_t *self, u8 *data, sz len) {
  sz offset = self->offset;
  u8 *buf = (void *)self->items;

  // printf("Offset: %ld\n", offset);
  /// 0 1 2 3 4 5 6
  ///     ^           7

  while (len) {
    sz dt = self->capacity - offset;

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

void valk_ring_rewind(valk_ring_t *self, sz n) {
  sz mask = self->capacity - 1;         /* 0111… pattern */
  self->offset = (self->offset - n) & mask; /* subtract, then wrap by masking */
}

void valk_ring_read(valk_ring_t *self, sz n, void *dst) {
  /* --- normalise inputs ------------------------------------------ */
  sz cap = self->capacity;
  sz head = self->offset % cap; /* in case callers misbehave  */
  n %= cap;                         /* ignore full extra laps     */

  // LCOV_EXCL_BR_START - ring buffer wrap optimization branches
  sz first = cap - head;
  if (first > n) first = n;
  sz second = n - first;

  const u8 *buf = (const u8 *)self->items;
  u8 *out = (u8 *)dst;

  memcpy(out, buf + head, first);
  if (second) memcpy(out + first, buf, second);
  // LCOV_EXCL_BR_STOP

  /* ── advance head (optional: keep the ring consistent) ─────────── */
  self->offset = (head + n) & (cap - 1); /* cap is power-of-2 – cheap */
}

void valk_ring_fread(valk_ring_t *self, sz n, FILE *f) {
  const u8 *base = (const u8 *)self->items;
  sz cap = self->capacity;
  sz head = self->offset; /* local copy for speed   */

  while (n) {
    /* contiguous bytes left in this lap */
    sz chunk = cap - head;
    if (chunk > n) chunk = n;

    fwrite(base + head, 1, chunk, f);

    /* advance */
    head = (head + chunk) & (cap - 1); /* ring wrap (use % if cap not pow-2) */
    n -= chunk;
  }
  self->offset = head; /* commit the consumer cursor */
}

void valk_ring_print(valk_ring_t *self, FILE *f) {
  fwrite(&((u8 *)self->items)[self->offset], 1,
         self->capacity - self->offset, f);
  fwrite(&((u8 *)self->items)[0], 1, self->offset, f);
}

/* alignment = power‑of‑two */
static inline sz __alignment_adjustment(void *ptr, sz alignment) {
  uptr addr = (uptr)ptr;
  uptr mask = alignment - 1;               /* 0b…111 */
  uptr misalign = addr & mask;             /* how far we're off */
  return misalign ? (alignment - misalign) : 0; /* bytes to *add* forward */
}

void valk_mem_arena_init(valk_mem_arena_t *self, sz capacity) {
  self->type = VALK_ALLOC_ARENA;
  self->capacity = capacity;
  self->offset = __alignment_adjustment(&self->heap, alignof(max_align_t));
  self->warned_overflow = false;

  // Initialize statistics to zero
  atomic_store_explicit(&self->stats.total_allocations, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.total_bytes_allocated, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.high_water_mark, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.num_resets, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.num_checkpoints, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.bytes_evacuated, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.values_evacuated, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.overflow_fallbacks, 0, memory_order_relaxed);
  atomic_store_explicit(&self->stats.overflow_bytes, 0, memory_order_relaxed);
}

void valk_mem_arena_reset(valk_mem_arena_t *self) {
  __atomic_store_n(&self->offset, 0, __ATOMIC_SEQ_CST);
  self->warned_overflow = false;
  atomic_fetch_add_explicit(&self->stats.num_resets, 1, memory_order_relaxed);
}

valk_arena_checkpoint_t valk_arena_checkpoint_save(valk_mem_arena_t *arena) {
  return (valk_arena_checkpoint_t){ .offset = arena->offset };
}

void valk_arena_checkpoint_restore(valk_mem_arena_t *arena, valk_arena_checkpoint_t cp) {
  arena->offset = cp.offset;
  atomic_fetch_add_explicit(&arena->stats.num_checkpoints, 1, memory_order_relaxed);
}

// TODO(networking): should probably write some unit tests for all this math
void *valk_mem_arena_alloc(valk_mem_arena_t *self, sz bytes) {
  // Layout: [optional padding][u64 size][padding to align payload][payload]
  sz old = __atomic_load_n(&self->offset, __ATOMIC_RELAXED);
  for (;;) {
    sz hdr = old + sizeof(u64);
    // Align payload after header to max_align_t
    sz adj = __alignment_adjustment(&self->heap[hdr], alignof(max_align_t));
    sz payload = hdr + adj;
    sz end = payload + bytes;

    // Check if allocation would exceed capacity - fall back to heap
    if (end >= self->capacity) {
      // OVERFLOW: Fall back to heap allocation
      atomic_fetch_add_explicit(&self->stats.overflow_fallbacks, 1, memory_order_relaxed);
      atomic_fetch_add_explicit(&self->stats.overflow_bytes, bytes, memory_order_relaxed);

      // Track that overflow occurred (logged at checkpoint)
      self->warned_overflow = true;

      // Allocate from heap instead - value will have LVAL_ALLOC_HEAP flag
      // and will be in GC object list, so no evacuation needed
      valk_gc_malloc_heap_t *heap = (valk_gc_malloc_heap_t *)valk_thread_ctx.heap;
      if (heap == nullptr) { // LCOV_EXCL_BR_LINE
        VALK_ERROR("Scratch overflow but no heap available!");
        abort();
      }
      return valk_gc_malloc_heap_alloc(heap, bytes);
    }

    // LCOV_EXCL_BR_START - CAS retry loop
    if (__atomic_compare_exchange_n(&self->offset, &old, end, 1,
                                    __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
    // LCOV_EXCL_BR_STOP
      // Store payload size right before payload pointer
      *((u64 *)&self->heap[payload] - 1) = bytes;

      // Update statistics (relaxed atomics - telemetry doesn't need precision)
      atomic_fetch_add_explicit(&self->stats.total_allocations, 1, memory_order_relaxed);
      atomic_fetch_add_explicit(&self->stats.total_bytes_allocated, bytes, memory_order_relaxed);
      sz cur_hwm = atomic_load_explicit(&self->stats.high_water_mark, memory_order_relaxed);
      while (end > cur_hwm) {
        if (atomic_compare_exchange_weak_explicit(&self->stats.high_water_mark, &cur_hwm, end,
                                                   memory_order_relaxed, memory_order_relaxed))
          break;
      }

      // Zero the allocated memory to prevent uninitialized data bugs
      memset(&self->heap[payload], 0, bytes);
      return &self->heap[payload];
    }
  }
}

// Print arena statistics to a file stream
void valk_mem_arena_print_stats(valk_mem_arena_t *arena, FILE *out) {
  if (arena == nullptr || out == nullptr) return;

  sz hwm = atomic_load_explicit(&arena->stats.high_water_mark, memory_order_relaxed);
  u64 overflow_fallbacks = atomic_load_explicit(&arena->stats.overflow_fallbacks, memory_order_relaxed);

  fprintf(out, "\n=== Scratch Arena Statistics ===\n");
  fprintf(out, "Current usage:     %zu / %zu bytes (%.1f%%)\n",
          arena->offset, arena->capacity,
          100.0 * arena->offset / arena->capacity);
  fprintf(out, "High water mark:   %zu bytes (%.1f%%)\n",
          hwm, 100.0 * hwm / arena->capacity);
  fprintf(out, "Total allocations: %llu\n",
          (unsigned long long)atomic_load_explicit(&arena->stats.total_allocations, memory_order_relaxed));
  fprintf(out, "Total bytes:       %zu\n",
          atomic_load_explicit(&arena->stats.total_bytes_allocated, memory_order_relaxed));
  fprintf(out, "Reset count:       %llu\n",
          (unsigned long long)atomic_load_explicit(&arena->stats.num_resets, memory_order_relaxed));
  fprintf(out, "Checkpoints:       %llu\n",
          (unsigned long long)atomic_load_explicit(&arena->stats.num_checkpoints, memory_order_relaxed));
  fprintf(out, "Values evacuated:  %llu\n",
          (unsigned long long)atomic_load_explicit(&arena->stats.values_evacuated, memory_order_relaxed));
  fprintf(out, "Bytes evacuated:   %zu\n",
          atomic_load_explicit(&arena->stats.bytes_evacuated, memory_order_relaxed));

  if (overflow_fallbacks > 0) { // LCOV_EXCL_BR_LINE
    fprintf(out, "⚠️  Overflow fallbacks: %llu (%zu bytes)\n",
            (unsigned long long)overflow_fallbacks,
            atomic_load_explicit(&arena->stats.overflow_bytes, memory_order_relaxed));
  }
  fprintf(out, "================================\n\n");
}

// Reset arena statistics (except high_water_mark which tracks lifetime max)
void valk_mem_arena_reset_stats(valk_mem_arena_t *arena) {
  if (arena == nullptr) return;

  atomic_store_explicit(&arena->stats.total_allocations, 0, memory_order_relaxed);
  atomic_store_explicit(&arena->stats.total_bytes_allocated, 0, memory_order_relaxed);
  // Note: high_water_mark is intentionally NOT reset
  atomic_store_explicit(&arena->stats.num_resets, 0, memory_order_relaxed);
  atomic_store_explicit(&arena->stats.num_checkpoints, 0, memory_order_relaxed);
  atomic_store_explicit(&arena->stats.bytes_evacuated, 0, memory_order_relaxed);
  atomic_store_explicit(&arena->stats.values_evacuated, 0, memory_order_relaxed);
  atomic_store_explicit(&arena->stats.overflow_fallbacks, 0, memory_order_relaxed);
  atomic_store_explicit(&arena->stats.overflow_bytes, 0, memory_order_relaxed);
}

// Check if a pointer is within the arena's address range
bool valk_ptr_in_arena(valk_mem_arena_t *arena, void *ptr) {
  if (arena == nullptr || ptr == nullptr) return false;

  u8 *start = arena->heap;
  u8 *end = arena->heap + arena->capacity;
  u8 *p = (u8 *)ptr;

  return p >= start && p < end;
}

void *valk_mem_allocator_alloc(valk_mem_allocator_t *self, sz bytes) {
  // LCOV_EXCL_BR_START - assertion failure branch
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to alloc %zu",
              bytes);
  // LCOV_EXCL_BR_STOP
  // Order by performance.
  switch (self->type) {  // LCOV_EXCL_BR_LINE - switch coverage
    case VALK_ALLOC_NULL:  // LCOV_EXCL_LINE - error path
      VALK_RAISE("Alloc on nullptr allocator %zu", bytes);  // LCOV_EXCL_LINE
      return nullptr;  // LCOV_EXCL_LINE
    case VALK_ALLOC_ARENA:
      return valk_mem_arena_alloc((void *)self, bytes);
    case VALK_ALLOC_SLAB: {
      valk_slab_item_t *item = valk_slab_aquire((void *)self);
      return item ? (void *)item->data : nullptr;  // LCOV_EXCL_BR_LINE - slab exhaustion
    }
    case VALK_ALLOC_MALLOC:
      return malloc(bytes);
    case VALK_ALLOC_GC_HEAP: {
      return valk_gc_malloc_heap_alloc((valk_gc_malloc_heap_t *)self, bytes);
    }
    case VALK_ALLOC_REGION: {
      return valk_region_alloc((valk_region_t *)self, bytes);
    }
  }
  return nullptr;
}

void *valk_mem_allocator_calloc(valk_mem_allocator_t *self, sz num,
                                sz size) {
  // LCOV_EXCL_BR_START - assertion failure branch
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %zu :: size: %zu",
              num, size);
  // LCOV_EXCL_BR_STOP
  void *res;
  // Order by performance.
  switch (self->type) {  // LCOV_EXCL_BR_LINE - switch coverage
    case VALK_ALLOC_NULL:  // LCOV_EXCL_LINE - error path
      VALK_RAISE("Calloc on nullptr allocator num: %zu :: size: %zu", num, size);  // LCOV_EXCL_LINE
      res = nullptr;  // LCOV_EXCL_LINE
      break;  // LCOV_EXCL_LINE
    case VALK_ALLOC_ARENA:
      res = valk_mem_arena_alloc((void *)self, num * size);
      memset(res, 0, num * size);
      break;
    case VALK_ALLOC_SLAB:
      res = valk_slab_aquire((void *)self);
      memset(res, 0, num * size);
      break;
    case VALK_ALLOC_MALLOC:
      res = calloc(num, size);
      break;
    case VALK_ALLOC_GC_HEAP:
      res = valk_gc_malloc_heap_alloc((valk_gc_malloc_heap_t *)self, num * size);
      memset(res, 0, num * size);
      break;
    case VALK_ALLOC_REGION:
      res = valk_region_alloc((valk_region_t *)self, num * size);
      if (res) memset(res, 0, num * size);  // LCOV_EXCL_BR_LINE - alloc failure
      break;
  }
  return res;
}

void *valk_mem_allocator_realloc(valk_mem_allocator_t *self, void *ptr,
                                 sz new_size) {
  // LCOV_EXCL_BR_START - assertion failure branch
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %p :: size: %zu",
              ptr, new_size);
  // LCOV_EXCL_BR_STOP

  // Order by performance.
  switch (self->type) {  // LCOV_EXCL_BR_LINE - switch coverage
    case VALK_ALLOC_NULL:  // LCOV_EXCL_LINE - error path
      VALK_RAISE("Realloc on nullptr allocator ptr: %p :: size: %zu", ptr,  // LCOV_EXCL_LINE
                 new_size);  // LCOV_EXCL_LINE
      return nullptr;  // LCOV_EXCL_LINE
    case VALK_ALLOC_ARENA: {
      // Copy-alloc semantics for arena realloc
      sz old_size = 0;
      if (ptr) {  // LCOV_EXCL_BR_LINE - ptr null case
        old_size = *(((u64 *)ptr) - 1);
      }
      void *np = valk_mem_arena_alloc((void *)self, new_size);
      if (ptr && np) {  // LCOV_EXCL_BR_LINE - alloc failure
        sz n = old_size < new_size ? old_size : new_size;
        memcpy(np, ptr, n);
      }
      return np;
    }
    case VALK_ALLOC_SLAB: {
      sz slabSize = ((valk_slab_t *)self)->itemSize;
      // LCOV_EXCL_BR_START - assertion failure branch
      VALK_ASSERT(
          new_size <= slabSize,
          "Realloc with slab allocator is unsafe,\n  tried to allocate more "
          "memory than fits in a slab\n %zu wanted, but %zu is the size",
          new_size, slabSize);
      // LCOV_EXCL_BR_STOP
      return ptr;
    }
    case VALK_ALLOC_GC_HEAP: {
      return valk_gc_heap2_realloc((valk_gc_heap2_t *)self, ptr, new_size);
    }
    case VALK_ALLOC_MALLOC:
      return realloc(ptr, new_size);
    case VALK_ALLOC_REGION: {
      valk_region_t *region = (valk_region_t *)self;
      if (region->arena) {
        sz old_size = 0;
        if (ptr) {  // LCOV_EXCL_BR_LINE - ptr null case
          old_size = *(((u64 *)ptr) - 1);
        }
        void *np = valk_region_alloc(region, new_size);
        if (ptr && np) {  // LCOV_EXCL_BR_LINE - alloc failure
          sz n = old_size < new_size ? old_size : new_size;
          memcpy(np, ptr, n);
        }
        return np;
      }
      if (region->gc_heap) {
        return valk_gc_heap2_realloc(region->gc_heap, ptr, new_size);
      }
      return nullptr;  // LCOV_EXCL_LINE - region with no backing
    }
  }
  return nullptr;
}

void valk_mem_allocator_free(valk_mem_allocator_t *self, void *ptr) {
  // LCOV_EXCL_BR_START - assertion failure branch
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %p",
              ptr);
  // LCOV_EXCL_BR_STOP

  // printf("Freeing %p\n", ptr);
  switch (self->type) {  // LCOV_EXCL_BR_LINE - switch coverage
    case VALK_ALLOC_NULL:  // LCOV_EXCL_LINE - error path
      VALK_RAISE("Free on nullptr allocator %p", ptr);  // LCOV_EXCL_LINE
      return;  // LCOV_EXCL_LINE
    case VALK_ALLOC_ARENA:
      return;
    case VALK_ALLOC_SLAB:
      valk_slab_release_ptr((void *)self, ptr);
      return;
    case VALK_ALLOC_MALLOC:
      free(ptr);
      return;
    case VALK_ALLOC_GC_HEAP:
      return;
    case VALK_ALLOC_REGION:
      return;
  }
}

void valk_chunked_ptrs_init(valk_chunked_ptrs_t *self) {
  self->head = nullptr;
  self->tail = nullptr;
  self->count = 0;
  self->tail_count = 0;
  self->malloc_chunks = false;
}

bool valk_chunked_ptrs_push(valk_chunked_ptrs_t *self, void *ptr, void *alloc_ctx) {
  if (!self->tail || self->tail_count >= VALK_CHUNK_SIZE) {
    valk_ptr_chunk_t *chunk;
    if (alloc_ctx) {
      chunk = valk_region_alloc((valk_region_t *)alloc_ctx, sizeof(valk_ptr_chunk_t));
    } else {
      chunk = malloc(sizeof(valk_ptr_chunk_t));
      self->malloc_chunks = true;
    }
    if (!chunk) return false;
    chunk->next = nullptr;
    
    if (self->tail) {
      self->tail->next = chunk;
    } else {
      self->head = chunk;
    }
    self->tail = chunk;
    self->tail_count = 0;
  }
  
  self->tail->items[self->tail_count++] = ptr;
  self->count++;
  return true;
}

void *valk_chunked_ptrs_get(valk_chunked_ptrs_t *self, u32 index) {
  if (index >= self->count) return nullptr;
  
  u32 chunk_idx = index / VALK_CHUNK_SIZE;
  u32 item_idx = index % VALK_CHUNK_SIZE;
  
  valk_ptr_chunk_t *chunk = self->head;
  for (u32 i = 0; i < chunk_idx && chunk; i++) {
    chunk = chunk->next;
  }
  
  return chunk ? chunk->items[item_idx] : nullptr;
}

void valk_chunked_ptrs_free(valk_chunked_ptrs_t *self) {
  if (!self->malloc_chunks) return;
  valk_ptr_chunk_t *chunk = self->head;
  while (chunk) {
    valk_ptr_chunk_t *next = chunk->next;
    free(chunk);
    chunk = next;
  }
  self->head = nullptr;
  self->tail = nullptr;
  self->count = 0;
  self->tail_count = 0;
  self->malloc_chunks = false;
}
