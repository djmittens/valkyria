#include "memory.h"

#include <stdatomic.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "collections.h"
#include "common.h"
#include "gc.h"
#include "log.h"

#define VALK_SLAB_TREIBER_STACK
#define VALK_SLAB_VERSIONS

__thread valk_thread_context_t valk_thread_ctx = {.allocator = nullptr, .heap = nullptr};

// Global malloc allocator for use with VALK_WITH_ALLOC when malloc is needed
valk_mem_allocator_t valk_malloc_allocator = {.type = VALK_ALLOC_MALLOC};

#ifdef VALK_ARC_DEBUG
#include "debug.h"
void __valk_arc_trace_report_print(valk_arc_trace_info *traces, size_t num) {
  for (size_t i = 0; i < num; i++) {
    const char *kind_str;
    switch (traces->kind) {
      case VALK_TRACE_ACQUIRE:
        kind_str = "ACQUIRE";
        break;
      case VALK_TRACE_RELEASE:
        kind_str = "RELEASE";
        break;
      case VALK_TRACE_NEW:
        kind_str = "NEW";
        break;
      case VALK_TRACE_FREE:
        kind_str = "FREE";
        break;
    }
    fprintf(stderr, "[%s] refcount[%ld] %s()|%s:%d \n", kind_str, traces->refcount,
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
    case VALK_ALLOC_GC_HEAP:
      return "GC Heap Alloc";
    case VALK_ALLOC_TLAB:
      return "TLAB Alloc";
  }
}

static valk_mem_allocator_t __allocator_malloc = {.type = VALK_ALLOC_MALLOC};

void valk_mem_init_malloc() { valk_thread_ctx.allocator = &__allocator_malloc; }

void valk_buffer_alloc(valk_buffer_t *buf, size_t capacity) {
  buf->capacity = capacity;
  buf->count = 0;
  // TODO(networking): use mmap with page-aligned memory for this instead
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
  __atomic_store_n(&self->overflowCount, 0, __ATOMIC_RELAXED);
  __atomic_store_n(&self->peakUsed, 0, __ATOMIC_RELAXED);

#ifdef VALK_METRICS_ENABLED
  size_t bitmap_bytes = (numItems + 7) / 8;
  self->usage_bitmap = calloc(bitmap_bytes, 1);
  __atomic_store_n(&self->bitmap_version, 0, __ATOMIC_RELAXED);
#endif
}

// TODO(networking): do we even need this? might be useful for debugging
void valk_slab_free(valk_slab_t *self) {
#ifdef VALK_METRICS_ENABLED
  if (self->usage_bitmap) {
    free(self->usage_bitmap);
    self->usage_bitmap = NULL;
  }
#endif
  valk_mem_free(self);
}

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
  valk_slab_item_t *res;
#ifdef VALK_SLAB_TREIBER_STACK  // Threadsafe
  // Atomically check and decrement numFree to avoid TOCTOU race
  size_t expected, desired;
  do {
    expected = __atomic_load_n(&self->numFree, __ATOMIC_ACQUIRE);
    if (expected == 0) {
      __atomic_fetch_add(&self->overflowCount, 1, __ATOMIC_RELAXED);
      return NULL;  // Slab exhausted - caller should fall back to malloc
    }
    desired = expected - 1;
  } while (!__atomic_compare_exchange_n(&self->numFree, &expected, desired,
                                        false, __ATOMIC_ACQ_REL,
                                        __ATOMIC_RELAXED));

  uint64_t oldTag, newTag;
  size_t head, next, version;
  do {
    oldTag = __atomic_load_n(&self->head, __ATOMIC_ACQUIRE);
    head = __valk_slab_offset_unpack(oldTag, &version);
    if (head == SIZE_MAX) {
      // Shouldn't happen - we reserved a slot but free list is empty
      // Restore numFree and return NULL
      __atomic_fetch_add(&self->numFree, 1, __ATOMIC_RELAXED);
      return NULL;
    }
    next =
        __atomic_load_n(&valk_slab_item_at(self, head)->next, __ATOMIC_ACQUIRE);
    newTag = __valk_slab_offset_pack(next, version + 1);
  } while (!__atomic_compare_exchange_n(&self->head, &oldTag, newTag, false,
                                        __ATOMIC_ACQ_REL, __ATOMIC_RELAXED));
  res = valk_slab_item_at(self, head);
  // printf("Slab Aquired %ld %p\n", head, res->data);

#ifdef VALK_METRICS_ENABLED
  if (self->usage_bitmap) {
    size_t byte_idx = head / 8;
    uint8_t bit_mask = 1 << (head % 8);
    __atomic_fetch_or(&self->usage_bitmap[byte_idx], bit_mask, __ATOMIC_RELAXED);
    __atomic_fetch_add(&self->bitmap_version, 1, __ATOMIC_RELAXED);
  }
#endif

  // Update peak usage (high water mark) tracking
  size_t used = self->numItems - __atomic_load_n(&self->numFree, __ATOMIC_RELAXED);
  size_t current_peak;
  do {
    current_peak = __atomic_load_n(&self->peakUsed, __ATOMIC_RELAXED);
    if (used <= current_peak) break;
  } while (!__atomic_compare_exchange_n(&self->peakUsed, &current_peak, used,
                                        false, __ATOMIC_RELAXED, __ATOMIC_RELAXED));

  return res;

#else  // Not threadsafe
  // Return NULL when slab is exhausted
  if (self->numFree == 0) {
    __atomic_fetch_add(&self->overflowCount, 1, __ATOMIC_RELAXED);
    return NULL;
  }
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

  // Update peak usage (high water mark) tracking
  size_t used = self->numItems - self->numFree;
  if (used > self->peakUsed) {
    self->peakUsed = used;
  }
#endif
  return res;
}

void valk_slab_release(valk_slab_t *self, valk_slab_item_t *item) {
#ifdef VALK_SLAB_TREIBER_STACK
  size_t slot_idx = item->handle;

#ifdef VALK_METRICS_ENABLED
  if (self->usage_bitmap && slot_idx < self->numItems) {
    size_t byte_idx = slot_idx / 8;
    uint8_t bit_mask = 1 << (slot_idx % 8);
    __atomic_fetch_and(&self->usage_bitmap[byte_idx], ~bit_mask, __ATOMIC_RELAXED);
    __atomic_fetch_add(&self->bitmap_version, 1, __ATOMIC_RELAXED);
  }
#endif

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
  // the handle and then free it
  size_t v;
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
  self->warned_overflow = false;

  // Initialize statistics to zero
  self->stats.total_allocations = 0;
  self->stats.total_bytes_allocated = 0;
  self->stats.high_water_mark = 0;
  self->stats.num_resets = 0;
  self->stats.num_checkpoints = 0;
  self->stats.bytes_evacuated = 0;
  self->stats.values_evacuated = 0;
  self->stats.overflow_fallbacks = 0;
  self->stats.overflow_bytes = 0;
}

void valk_mem_arena_reset(valk_mem_arena_t *self) {
  __atomic_store_n(&self->offset, 0, __ATOMIC_SEQ_CST);
  self->warned_overflow = false;
  self->stats.num_resets++;
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

    // Check if allocation would exceed capacity - fall back to heap
    if (end >= self->capacity) {
      // OVERFLOW: Fall back to heap allocation
      self->stats.overflow_fallbacks++;
      self->stats.overflow_bytes += bytes;

      // Track that overflow occurred (logged at checkpoint)
      self->warned_overflow = true;

      // Allocate from heap instead - value will have LVAL_ALLOC_HEAP flag
      // and will be in GC object list, so no evacuation needed
      valk_gc_malloc_heap_t *heap = (valk_gc_malloc_heap_t *)valk_thread_ctx.heap;
      if (heap == NULL) {
        VALK_ERROR("Scratch overflow but no heap available!");
        abort();
      }
      return valk_gc_malloc_heap_alloc(heap, bytes);
    }

    if (__atomic_compare_exchange_n(&self->offset, &old, end, 1,
                                    __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {
      // Store payload size right before payload pointer
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      *((size_t *)&self->heap[payload] - 1) = bytes;

      // Update statistics
      self->stats.total_allocations++;
      self->stats.total_bytes_allocated += bytes;
      if (end > self->stats.high_water_mark) {
        self->stats.high_water_mark = end;
      }

      return &self->heap[payload];
    }
  }
}

// Print arena statistics to a file stream
void valk_mem_arena_print_stats(valk_mem_arena_t *arena, FILE *out) {
  if (arena == NULL || out == NULL) return;

  fprintf(out, "\n=== Scratch Arena Statistics ===\n");
  fprintf(out, "Current usage:     %zu / %zu bytes (%.1f%%)\n",
          arena->offset, arena->capacity,
          100.0 * arena->offset / arena->capacity);
  fprintf(out, "High water mark:   %zu bytes (%.1f%%)\n",
          arena->stats.high_water_mark,
          100.0 * arena->stats.high_water_mark / arena->capacity);
  fprintf(out, "Total allocations: %zu\n", arena->stats.total_allocations);
  fprintf(out, "Total bytes:       %zu\n", arena->stats.total_bytes_allocated);
  fprintf(out, "Reset count:       %zu\n", arena->stats.num_resets);
  fprintf(out, "Checkpoints:       %zu\n", arena->stats.num_checkpoints);
  fprintf(out, "Values evacuated:  %zu\n", arena->stats.values_evacuated);
  fprintf(out, "Bytes evacuated:   %zu\n", arena->stats.bytes_evacuated);

  if (arena->stats.overflow_fallbacks > 0) {
    fprintf(out, "⚠️  Overflow fallbacks: %zu (%zu bytes)\n",
            arena->stats.overflow_fallbacks, arena->stats.overflow_bytes);
  }
  fprintf(out, "================================\n\n");
}

// Reset arena statistics (except high_water_mark which tracks lifetime max)
void valk_mem_arena_reset_stats(valk_mem_arena_t *arena) {
  if (arena == NULL) return;

  arena->stats.total_allocations = 0;
  arena->stats.total_bytes_allocated = 0;
  // Note: high_water_mark is intentionally NOT reset
  arena->stats.num_resets = 0;
  arena->stats.num_checkpoints = 0;
  arena->stats.bytes_evacuated = 0;
  arena->stats.values_evacuated = 0;
  arena->stats.overflow_fallbacks = 0;
  arena->stats.overflow_bytes = 0;
}

// Check if a pointer is within the arena's address range
bool valk_ptr_in_arena(valk_mem_arena_t *arena, void *ptr) {
  if (arena == NULL || ptr == NULL) return false;

  uint8_t *start = arena->heap;
  uint8_t *end = arena->heap + arena->capacity;
  uint8_t *p = (uint8_t *)ptr;

  return p >= start && p < end;
}

// Collect process-level memory stats from the OS
#if defined(__linux__)
#include <sys/resource.h>
#include <unistd.h>

void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == NULL) return;
  memset(pm, 0, sizeof(*pm));

  long page_size = sysconf(_SC_PAGESIZE);

  // System total RAM
  long phys_pages = sysconf(_SC_PHYS_PAGES);
  if (phys_pages > 0 && page_size > 0) {
    pm->system_total_bytes = (size_t)phys_pages * page_size;
  }

  // Read from /proc/self/statm (fast, minimal parsing)
  // Format: size resident shared text lib data dirty (all in pages)
  FILE *f = fopen("/proc/self/statm", "r");
  if (f) {
    unsigned long size, resident, shared, text, lib, data, dirty;
    if (fscanf(f, "%lu %lu %lu %lu %lu %lu %lu",
               &size, &resident, &shared, &text, &lib, &data, &dirty) >= 4) {
      pm->vms_bytes = size * page_size;
      pm->rss_bytes = resident * page_size;
      pm->shared_bytes = shared * page_size;
      pm->data_bytes = data * page_size;
    }
    fclose(f);
  }

  // Page faults from getrusage
  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) == 0) {
    pm->page_faults_minor = ru.ru_minflt;
    pm->page_faults_major = ru.ru_majflt;
  }
}

#elif defined(__APPLE__)
#include <mach/mach.h>
#include <sys/resource.h>
#include <sys/sysctl.h>

void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == NULL) return;
  memset(pm, 0, sizeof(*pm));

  // System total RAM via sysctl
  int mib[2] = {CTL_HW, HW_MEMSIZE};
  uint64_t memsize = 0;
  size_t len = sizeof(memsize);
  if (sysctl(mib, 2, &memsize, &len, NULL, 0) == 0) {
    pm->system_total_bytes = (size_t)memsize;
  }

  mach_task_basic_info_data_t info;
  mach_msg_type_number_t count = MACH_TASK_BASIC_INFO_COUNT;

  if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO,
                (task_info_t)&info, &count) == KERN_SUCCESS) {
    pm->rss_bytes = info.resident_size;
    pm->vms_bytes = info.virtual_size;
  }

  struct rusage ru;
  if (getrusage(RUSAGE_SELF, &ru) == 0) {
    pm->page_faults_minor = ru.ru_minflt;
    pm->page_faults_major = ru.ru_majflt;
  }
}

#else
// Fallback for other platforms
void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == NULL) return;
  memset(pm, 0, sizeof(*pm));
}
#endif

// =============================================================================
// Detailed smaps breakdown (Linux only)
// Parses /proc/self/smaps to categorize RSS by region type
// =============================================================================

#if defined(__linux__)

void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == NULL) return;
  memset(smaps, 0, sizeof(*smaps));

  FILE *f = fopen("/proc/self/smaps", "r");
  if (!f) return;

  char line[512];
  char current_name[256] = {0};
  bool is_heap = false;
  bool is_stack = false;
  bool is_anon = false;
  bool is_file = false;
  bool is_uring = false;
  bool is_special = false;

  while (fgets(line, sizeof(line), f)) {
    // Region header line: "addr-addr perms offset dev inode pathname"
    // Example: "7f560a600000-7f560a624000 r--p 00000000 00:1b 844871  /usr/lib/libc.so.6"
    if (line[0] != ' ' && strchr(line, '-')) {
      // Reset flags for new region
      is_heap = false;
      is_stack = false;
      is_anon = false;
      is_file = false;
      is_uring = false;
      is_special = false;
      current_name[0] = '\0';

      // Find the pathname (after the inode)
      // Format: addr-addr perms offset dev inode [pathname]
      char *name_start = NULL;
      int spaces = 0;
      for (char *p = line; *p; p++) {
        if (*p == ' ') {
          spaces++;
          // After 5 spaces, we're at the pathname
          if (spaces == 5) {
            // Skip leading spaces
            while (*p == ' ') p++;
            name_start = p;
            break;
          }
        }
      }

      if (name_start) {
        // Remove trailing newline
        char *nl = strchr(name_start, '\n');
        if (nl) *nl = '\0';
        strncpy(current_name, name_start, sizeof(current_name) - 1);
      }

      // Categorize the region
      if (strstr(current_name, "[heap]")) {
        is_heap = true;
      } else if (strstr(current_name, "[stack]") || strstr(current_name, "stack:")) {
        is_stack = true;
      } else if (strstr(current_name, "[vdso]") || strstr(current_name, "[vvar]") ||
                 strstr(current_name, "[vsyscall]")) {
        is_special = true;
      } else if (strstr(current_name, "io_uring")) {
        is_uring = true;
      } else if (current_name[0] == '\0') {
        // Anonymous mapping (no pathname)
        is_anon = true;
        smaps->anon_regions++;
      } else if (current_name[0] == '/') {
        // File-backed mapping
        is_file = true;
        smaps->file_regions++;
      } else {
        is_special = true;
      }
    }

    // Look for Rss line within a region
    // Format: "Rss:               1234 kB"
    if (strncmp(line, "Rss:", 4) == 0) {
      size_t rss_kb = 0;
      if (sscanf(line, "Rss: %zu kB", &rss_kb) == 1) {
        size_t rss_bytes = rss_kb * 1024;

        if (is_heap) {
          smaps->heap_rss += rss_bytes;
        } else if (is_stack) {
          smaps->stack_rss += rss_bytes;
        } else if (is_uring) {
          smaps->uring_rss += rss_bytes;
        } else if (is_anon) {
          smaps->anon_rss += rss_bytes;
        } else if (is_file) {
          smaps->file_rss += rss_bytes;
        } else if (is_special) {
          smaps->other_rss += rss_bytes;
        }

        smaps->total_rss += rss_bytes;
      }
    }

    // Also check for Shmem (shared memory)
    if (strncmp(line, "Shmem:", 6) == 0) {
      size_t shmem_kb = 0;
      if (sscanf(line, "Shmem: %zu kB", &shmem_kb) == 1) {
        smaps->shmem_rss += shmem_kb * 1024;
      }
    }
  }

  fclose(f);
}

#elif defined(__APPLE__)
#include <mach/mach.h>
#include <mach/mach_vm.h>

void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == NULL) return;
  memset(smaps, 0, sizeof(*smaps));

  task_t task = mach_task_self();
  mach_vm_address_t address = 0;
  mach_vm_size_t size = 0;
  vm_region_basic_info_data_64_t info;
  mach_msg_type_number_t info_count;
  mach_port_t object_name;

  while (1) {
    info_count = VM_REGION_BASIC_INFO_COUNT_64;
    kern_return_t kr = mach_vm_region(task, &address, &size,
                                       VM_REGION_BASIC_INFO_64,
                                       (vm_region_info_t)&info,
                                       &info_count, &object_name);
    if (kr != KERN_SUCCESS) break;

    // Only count resident memory (similar to RSS)
    // We can't get exact RSS per region easily, so use full size for mapped regions
    // that have read/write permissions (likely resident)
    size_t region_size = (size_t)size;

    if (info.shared) {
      smaps->shmem_rss += region_size;
    } else {
      smaps->anon_rss += region_size;
      smaps->anon_regions++;
    }

    smaps->total_rss += region_size;
    address += size;
  }

  // On macOS, we can't easily distinguish heap vs stack vs other anon
  // Put a portion in heap as estimate (malloc typically uses ~10% overhead)
  // This is approximate - macOS doesn't expose this granularity
  if (smaps->anon_rss > 0) {
    // Heuristic: attribute small portion to heap metadata
    smaps->heap_rss = smaps->anon_rss / 20;  // ~5% as heap overhead estimate
    smaps->anon_rss -= smaps->heap_rss;
  }

  // Stack estimate: typical 8MB per thread, but we don't know thread count
  // Leave as 0 since we can't reliably detect it
}

#else
// Other platforms: no-op
void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == NULL) return;
  memset(smaps, 0, sizeof(*smaps));
}
#endif

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
    case VALK_ALLOC_SLAB: {
      valk_slab_item_t *item = valk_slab_aquire((void *)self);
      return item ? (void *)item->data : NULL;
    }
    case VALK_ALLOC_MALLOC:
      return malloc(bytes);
    case VALK_ALLOC_GC_HEAP: {
      // GC heap allocates ALL structures (lval_t + auxiliary data like arrays/strings)
      // Slab is used for lval_t, malloc fallback for other sizes
      // Everything goes through unified GC interface for proper tracking
      return valk_gc_malloc_heap_alloc((valk_gc_malloc_heap_t *)self, bytes);
    }
    case VALK_ALLOC_TLAB: {
      // TLAB uses the parallel GC page pool for lval-sized allocations
      return valk_gc_tlab_alloc_slow(bytes);
    }
  }
  return NULL;
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
    case VALK_ALLOC_GC_HEAP:
      res = valk_gc_malloc_heap_alloc((valk_gc_malloc_heap_t *)self, num * size);
      memset(res, 0, num * size);
      break;
    case VALK_ALLOC_TLAB:
      res = valk_gc_tlab_alloc_slow(num * size);
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
    case VALK_ALLOC_GC_HEAP: {
      return valk_gc_heap2_realloc((valk_gc_heap2_t *)self, ptr, new_size);
    }
    case VALK_ALLOC_MALLOC:
      return realloc(ptr, new_size);
    case VALK_ALLOC_TLAB:
      VALK_RAISE("Realloc on TLAB allocator not supported: %p -> %zu", ptr, new_size);
      return NULL;
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
    case VALK_ALLOC_GC_HEAP: {
      // For GC heap objects, we need to properly free them by removing from tracking
      // and returning memory to the appropriate source (slab or malloc)
      if (ptr == NULL) return;

      // Get header (it's right before the user data)
      extern void valk_gc_free_object(void* heap, void* ptr);
      valk_gc_free_object((void*)self, ptr);
      return;
    }
    case VALK_ALLOC_TLAB:
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
  return self + 1;  // return pointer to data after header
}

void valk_gc_sweep(valk_gc_heap_t *self) {
  valk_gc_chunk_t *node = self->sentinel.next;
  while (node != &self->sentinel) {
    if (!node->marked) {
      if (self->finalize) {
        self->finalize(node);
      } else {
        // Remove from list and free
        valk_dll_pop(node);
        valk_mem_allocator_free(self->allocator, node);
      }
    } else {
      // reset this bad boii for the next time
      node->marked = 0;
    }
  }
}

#ifdef VALK_METRICS_ENABLED
void valk_slab_bitmap_snapshot(valk_slab_t *slab, valk_slab_bitmap_t *out) {
  if (!slab || !out) return;
  out->data = NULL;
  out->bytes = 0;
  out->version = 0;

  if (!slab->usage_bitmap) return;

  size_t bitmap_bytes = (slab->numItems + 7) / 8;
  out->data = malloc(bitmap_bytes);
  if (!out->data) return;

  out->version = __atomic_load_n(&slab->bitmap_version, __ATOMIC_ACQUIRE);
  memcpy(out->data, slab->usage_bitmap, bitmap_bytes);
  out->bytes = bitmap_bytes;
}

void valk_slab_bitmap_free(valk_slab_bitmap_t *bmp) {
  if (bmp && bmp->data) {
    free(bmp->data);
    bmp->data = NULL;
    bmp->bytes = 0;
  }
}

void valk_bitmap_delta_init(valk_bitmap_delta_t *delta) {
  if (!delta) return;
  delta->runs = NULL;
  delta->run_count = 0;
  delta->run_capacity = 0;
  delta->from_version = 0;
  delta->to_version = 0;
}

void valk_bitmap_delta_free(valk_bitmap_delta_t *delta) {
  if (delta && delta->runs) {
    free(delta->runs);
    delta->runs = NULL;
    delta->run_count = 0;
    delta->run_capacity = 0;
  }
}

static bool delta_add_run(valk_bitmap_delta_t *delta, size_t offset, size_t count, uint8_t byte) {
  if (delta->run_count >= delta->run_capacity) {
    size_t new_cap = delta->run_capacity ? delta->run_capacity * 2 : 64;
    valk_bitmap_delta_run_t *new_runs = realloc(delta->runs, new_cap * sizeof(valk_bitmap_delta_run_t));
    if (!new_runs) return false;
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
  if (!curr->data || !prev->data) return false;
  if (curr->bytes != prev->bytes) return false;

  valk_bitmap_delta_init(out);
  out->from_version = prev->version;
  out->to_version = curr->version;

  size_t i = 0;
  while (i < curr->bytes) {
    if (curr->data[i] == prev->data[i]) {
      i++;
      continue;
    }

    uint8_t xor_byte = curr->data[i] ^ prev->data[i];
    size_t run_start = i;
    size_t run_len = 1;

    while (i + run_len < curr->bytes &&
           (curr->data[i + run_len] ^ prev->data[i + run_len]) == xor_byte) {
      run_len++;
    }

    if (!delta_add_run(out, run_start, run_len, xor_byte)) {
      valk_bitmap_delta_free(out);
      return false;
    }
    i += run_len;
  }

  return true;
}

size_t valk_bitmap_delta_to_rle(const valk_bitmap_delta_t *delta,
                                 char *buf, size_t buf_size) {
  if (!delta || !buf || buf_size < 4) {
    if (buf && buf_size > 0) buf[0] = '\0';
    return 0;
  }

  static const char hex_chars[] = "0123456789abcdef";
  char *p = buf;
  char *end = buf + buf_size - 1;

  for (size_t i = 0; i < delta->run_count && p < end - 16; i++) {
    valk_bitmap_delta_run_t *run = &delta->runs[i];

    if (i > 0 && p < end) *p++ = ',';

    int n = snprintf(p, end - p, "%zu:", run->offset);
    if (n < 0 || p + n >= end) break;
    p += n;

    if (p + 2 >= end) break;
    *p++ = hex_chars[(run->byte >> 4) & 0x0F];
    *p++ = hex_chars[run->byte & 0x0F];

    if (run->count > 1) {
      n = snprintf(p, end - p, "*%zu", run->count);
      if (n < 0 || p + n >= end) break;
      p += n;
    }
  }

  *p = '\0';
  return p - buf;
}

size_t valk_slab_bitmap_buckets(valk_slab_t *slab,
                                 size_t start_slot, size_t end_slot,
                                 size_t num_buckets,
                                 valk_bitmap_bucket_t *out_buckets) {
  if (!slab || !out_buckets || num_buckets == 0) return 0;
  if (!slab->usage_bitmap) return 0;

  if (end_slot > slab->numItems) end_slot = slab->numItems;
  if (start_slot >= end_slot) return 0;

  size_t total_slots = end_slot - start_slot;
  size_t slots_per_bucket = (total_slots + num_buckets - 1) / num_buckets;
  if (slots_per_bucket == 0) slots_per_bucket = 1;

  for (size_t b = 0; b < num_buckets; b++) {
    out_buckets[b].used = 0;
    out_buckets[b].free = 0;
  }

  for (size_t slot = start_slot; slot < end_slot; slot++) {
    size_t byte_idx = slot / 8;
    uint8_t bit_mask = 1 << (slot % 8);
    bool is_used = (slab->usage_bitmap[byte_idx] & bit_mask) != 0;

    size_t bucket_idx = (slot - start_slot) / slots_per_bucket;
    if (bucket_idx >= num_buckets) bucket_idx = num_buckets - 1;

    if (is_used) {
      out_buckets[bucket_idx].used++;
    } else {
      out_buckets[bucket_idx].free++;
    }
  }

  return num_buckets;
}
#endif
