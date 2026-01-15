#include "memory.h"

#include <stdatomic.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#include "collections.h"
#include "common.h"
#include "gc.h"
#include "log.h"

#define VALK_SLAB_TREIBER_STACK
#define VALK_SLAB_VERSIONS

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
    case VALK_ALLOC_TLAB:
      return "TLAB Alloc";
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
  VALK_ASSERT(
      buf->capacity > (buf->count + len),
      "Buffer too small !!!  capacity [%zu] :: count [%zu] :: new bytes [%zu]",
      buf->capacity, buf->count, len);
  memcpy(&((char *)buf->items)[buf->count], bytes, len);
  buf->count += len;
}

int valk_buffer_is_full(valk_buffer_t *buf) {
  return (buf->capacity - buf->count) == 0;
}

static inline bool is_pow2(u64 x) { return x && ((x & (x - 1)) == 0); }

void valk_ring_init(valk_ring_t *self, sz capacity) {
  VALK_ASSERT(is_pow2(capacity),
              "Ring buffer capacity must be pow of 2, to reduce branching, %zu",
              capacity);
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

/// helper: round x up to next multiple of A (A must be a power of two)
/// return multiple of A
static inline sz __valk_mem_align_up(sz x, sz A) {
  return (x + A - 1) & ~(A - 1);
}
static inline valk_slab_item_t *valk_slab_item_at(valk_slab_t *self,
                                                  sz offset) {
#ifdef VALK_SLAB_TREIBER_STACK
  // No free list in concurrency
  const sz freeLen = 0;
#else
  const sz freeLen = (sizeof(u64) * self->numItems);
#endif
  const sz itemsLen = valk_slab_item_stride(self->itemSize) * offset;

  VALK_ASSERT(offset < self->numItems,
              "Offset passed in is out of bounds offset: %zu  numItems %zu",
              offset, self->numItems);
  return (void *)&((char *)self->heap)[freeLen + itemsLen];
}

valk_slab_t *valk_slab_new(sz itemSize, sz numItems) {
  sz slabSize = valk_slab_size(itemSize, numItems);
  VALK_DEBUG("Slab size = %zu (%.2f MB)", slabSize, (double)slabSize / 1024 / 1024);
  
  sz pageSize = 4096;
  sz mmapSize = (slabSize + pageSize - 1) & ~(pageSize - 1);
  
  void *mem = mmap(nullptr, mmapSize, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mem == MAP_FAILED) { // LCOV_EXCL_BR_LINE
    VALK_ERROR("mmap failed for slab of %zu bytes", mmapSize);
    return nullptr;
  }
  
  valk_slab_t *res = mem;
  res->mmap_size = mmapSize;
  valk_slab_init(res, itemSize, numItems);
  return res;
}

void valk_slab_init(valk_slab_t *self, sz itemSize, sz numItems) {
  // TODO(networking): do like mmap and some platform specific slab code
  self->type = VALK_ALLOC_SLAB;

  self->itemSize = itemSize;
  self->numItems = numItems;

  for (sz i = 0; i < numItems; i++) {
    valk_slab_item_t *item = valk_slab_item_at(self, i);
    item->handle = i;
#ifdef VALK_SLAB_TREIBER_STACK  // Treiber list
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
  // TODO(networking): when implementing AVX or other instruciton sets might
  // need to expand alignment parameters
  // alignof(max_align_t)  <<- is the minimal required
  // 64 according to chatgpt is the cacheline alignment, which is better for
  // slabs
  return __valk_mem_align_up(sizeof(valk_slab_item_t) + itemSize, 64);
}

sz valk_slab_size(sz itemSize, sz numItems) {
  sz stride = valk_slab_item_stride(itemSize);
  VALK_DEBUG("Slab stride = %zu", stride);
  const sz freelen = sizeof(u64) * numItems;  // guranteed alignment

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
#ifdef VALK_SLAB_TREIBER_STACK  // Threadsafe
  // Atomically check and decrement numFree to avoid TOCTOU race
  sz expected, desired;
  do {
    expected = __atomic_load_n(&self->numFree, __ATOMIC_ACQUIRE);
    if (expected == 0) {
      __atomic_fetch_add(&self->overflowCount, 1, __ATOMIC_RELAXED);
      return nullptr;  // Slab exhausted - caller should fall back to malloc
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
  // printf("Slab Aquired %ld %p\n", head, res->data);

  if (self->usage_bitmap) {
    u64 byte_idx = head / 8;
    u8 bit_mask = 1 << (head % 8);
    __atomic_fetch_or(&self->usage_bitmap[byte_idx], bit_mask, __ATOMIC_RELAXED);
    __atomic_fetch_add(&self->bitmap_version, 1, __ATOMIC_RELAXED);
  }

  // Update peak usage (high water mark) tracking
  sz used = self->numItems - __atomic_load_n(&self->numFree, __ATOMIC_RELAXED);
  sz current_peak;
  do {
    current_peak = __atomic_load_n(&self->peakUsed, __ATOMIC_RELAXED);
    if (used <= current_peak) break;
  } while (!__atomic_compare_exchange_n(&self->peakUsed, &current_peak, used, // LCOV_EXCL_BR_LINE
                                         false, __ATOMIC_RELAXED, __ATOMIC_RELAXED));

  return res;

#else  // Not threadsafe
  // Return nullptr when slab is exhausted
  if (self->numFree == 0) {
    __atomic_fetch_add(&self->overflowCount, 1, __ATOMIC_RELAXED);
    return nullptr;
  }
  // pop  free item
  u64 offset = ((u64 *)self->heap)[0];
  ((u64 *)self->heap)[0] = ((u64 *)self->heap)[self->numFree - 1];
  ((u64 *)self->heap)[self->numFree - 1] = offset;
  --self->numFree;

  // Lookup this item in the slab and return
  const u64 freeLen = (sizeof(u64) * self->numItems);
  const u64 itemsLen = valk_slab_item_stride(self->itemSize) * offset;

  res = (void *)&((char *)self->heap)[freeLen + itemsLen];
  const u64 swapTo = ((u64 *)self->heap)[0];
  VALK_TRACE("Acquiring slab: handle=%ld idx=%ld swap=%ld", res->handle, offset,
         swapTo);

  // Update peak usage (high water mark) tracking
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

#else
  // find the slab handle
  for (u64 i = 0; i < self->numItems; ++i) {
    const u64 handle = ((u64 *)self->heap)[i];

    if (handle == item->handle) {
      const u64 target = self->numFree;
      // Swap it out with a stale one
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

  // Swap it in as free
}

void valk_slab_release_ptr(valk_slab_t *self, void *data) {
  // This function will look back item size bytes in the array, to figure out
  // the handle and then free it
  u64 v;
  __valk_slab_offset_unpack(
      valk_container_of(data, valk_slab_item_t, data)->handle, &v);
  // printf("Slab Releasing %ld %p\n", offset, data);
  valk_slab_release(self, valk_container_of(data, valk_slab_item_t, data));
}

//
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

valk_arena_checkpoint_t valk_arena_checkpoint_save(valk_mem_arena_t *arena) {
  return (valk_arena_checkpoint_t){ .offset = arena->offset };
}

void valk_arena_checkpoint_restore(valk_mem_arena_t *arena, valk_arena_checkpoint_t cp) {
  arena->offset = cp.offset;
  arena->stats.num_checkpoints++;
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
      self->stats.overflow_fallbacks++;
      self->stats.overflow_bytes += bytes;

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

      // Update statistics
      self->stats.total_allocations++;
      self->stats.total_bytes_allocated += bytes;
      if (end > self->stats.high_water_mark) {
        self->stats.high_water_mark = end;
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

  fprintf(out, "\n=== Scratch Arena Statistics ===\n");
  fprintf(out, "Current usage:     %zu / %zu bytes (%.1f%%)\n",
          arena->offset, arena->capacity,
          100.0 * arena->offset / arena->capacity);
  fprintf(out, "High water mark:   %zu bytes (%.1f%%)\n",
          arena->stats.high_water_mark,
          100.0 * arena->stats.high_water_mark / arena->capacity);
  fprintf(out, "Total allocations: %llu\n", arena->stats.total_allocations);
  fprintf(out, "Total bytes:       %zu\n", arena->stats.total_bytes_allocated);
  fprintf(out, "Reset count:       %llu\n", arena->stats.num_resets);
  fprintf(out, "Checkpoints:       %llu\n", arena->stats.num_checkpoints);
  fprintf(out, "Values evacuated:  %llu\n", arena->stats.values_evacuated);
  fprintf(out, "Bytes evacuated:   %zu\n", arena->stats.bytes_evacuated);

  if (arena->stats.overflow_fallbacks > 0) { // LCOV_EXCL_BR_LINE
    fprintf(out, "⚠️  Overflow fallbacks: %llu (%zu bytes)\n",
            arena->stats.overflow_fallbacks, arena->stats.overflow_bytes);
  }
  fprintf(out, "================================\n\n");
}

// Reset arena statistics (except high_water_mark which tracks lifetime max)
void valk_mem_arena_reset_stats(valk_mem_arena_t *arena) {
  if (arena == nullptr) return;

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
  if (arena == nullptr || ptr == nullptr) return false;

  u8 *start = arena->heap;
  u8 *end = arena->heap + arena->capacity;
  u8 *p = (u8 *)ptr;

  return p >= start && p < end;
}

// Collect process-level memory stats from the OS
#if defined(__linux__)
#include <sys/resource.h>
#include <unistd.h>

void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == nullptr) return;
  memset(pm, 0, sizeof(*pm));

  long page_size = sysconf(_SC_PAGESIZE);

  // System total RAM
  long phys_pages = sysconf(_SC_PHYS_PAGES);
  if (phys_pages > 0 && page_size > 0) {
    pm->system_total_bytes = (u64)phys_pages * page_size;
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
  if (pm == nullptr) return;
  memset(pm, 0, sizeof(*pm));

  // LCOV_EXCL_BR_START - OS syscall success checks
  int mib[2] = {CTL_HW, HW_MEMSIZE};
  u64 memsize = 0;
  size_t len = sizeof(memsize);
  if (sysctl(mib, 2, &memsize, &len, nullptr, 0) == 0) {
    pm->system_total_bytes = (u64)memsize;
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
  // LCOV_EXCL_BR_STOP
}

#else
// Fallback for other platforms
void valk_process_memory_collect(valk_process_memory_t *pm) {
  if (pm == nullptr) return;
  memset(pm, 0, sizeof(*pm));
}
#endif

// =============================================================================
// Detailed smaps breakdown (Linux only)
// Parses /proc/self/smaps to categorize RSS by region type
// =============================================================================

#if defined(__linux__)

typedef enum {
  SMAPS_REGION_HEAP,
  SMAPS_REGION_STACK,
  SMAPS_REGION_ANON,
  SMAPS_REGION_FILE,
  SMAPS_REGION_URING,
  SMAPS_REGION_SPECIAL,
} smaps_region_type_e;

static smaps_region_type_e categorize_smaps_region(const char *name) {
  if (strstr(name, "[heap]")) {
    return SMAPS_REGION_HEAP;
  }
  if (strstr(name, "[stack]") || strstr(name, "stack:")) {
    return SMAPS_REGION_STACK;
  }
  if (strstr(name, "[vdso]") || strstr(name, "[vvar]") || strstr(name, "[vsyscall]")) {
    return SMAPS_REGION_SPECIAL;
  }
  if (strstr(name, "io_uring")) {
    return SMAPS_REGION_URING;
  }
  if (name[0] == '\0') {
    return SMAPS_REGION_ANON;
  }
  if (name[0] == '/') {
    return SMAPS_REGION_FILE;
  }
  return SMAPS_REGION_SPECIAL;
}

static const char *extract_smaps_pathname(const char *line, char *out_name, sz out_size) {
  out_name[0] = '\0';
  int spaces = 0;
  const char *name_start = nullptr;
  for (const char *p = line; *p; p++) {
    if (*p == ' ') {
      spaces++;
      if (spaces == 5) {
        while (*p == ' ') p++;
        name_start = p;
        break;
      }
    }
  }
  if (name_start) {
    sz len = strlen(name_start);
    if (len > 0 && name_start[len - 1] == '\n') len--;
    if (len >= out_size) len = out_size - 1;
    memcpy(out_name, name_start, len);
    out_name[len] = '\0';
  }
  return out_name;
}

void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == nullptr) return;
  memset(smaps, 0, sizeof(*smaps));

  FILE *f = fopen("/proc/self/smaps", "r");
  if (!f) return;

  char line[512];
  char current_name[256] = {0};
  smaps_region_type_e region_type = SMAPS_REGION_SPECIAL;

  while (fgets(line, sizeof(line), f)) {
    if (line[0] != ' ' && strchr(line, '-')) {
      extract_smaps_pathname(line, current_name, sizeof(current_name));
      region_type = categorize_smaps_region(current_name);

      if (region_type == SMAPS_REGION_ANON) {
        smaps->anon_regions++;
      } else if (region_type == SMAPS_REGION_FILE) {
        smaps->file_regions++;
      }
    }

    if (strncmp(line, "Rss:", 4) == 0) {
      u64 rss_kb = 0;
      if (sscanf(line, "Rss: %llu kB", &rss_kb) == 1) {
        u64 rss_bytes = rss_kb * 1024;
        switch (region_type) {
          case SMAPS_REGION_HEAP:   smaps->heap_rss += rss_bytes; break;
          case SMAPS_REGION_STACK:  smaps->stack_rss += rss_bytes; break;
          case SMAPS_REGION_URING:  smaps->uring_rss += rss_bytes; break;
          case SMAPS_REGION_ANON:   smaps->anon_rss += rss_bytes; break;
          case SMAPS_REGION_FILE:   smaps->file_rss += rss_bytes; break;
          case SMAPS_REGION_SPECIAL: smaps->other_rss += rss_bytes; break;
        }
        smaps->total_rss += rss_bytes;
      }
    }

    if (strncmp(line, "Shmem:", 6) == 0) {
      u64 shmem_kb = 0;
      if (sscanf(line, "Shmem: %llu kB", &shmem_kb) == 1) {
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
  if (smaps == nullptr) return;
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
    u64 region_size = (u64)size;

    if (info.shared) {
      smaps->shmem_rss += region_size;
    } else {
      smaps->anon_rss += region_size;
      smaps->anon_regions++;
    }

    smaps->total_rss += region_size;
    address += size;
  }

  // LCOV_EXCL_BR_START - macOS memory region heuristics
  if (smaps->anon_rss > 0) {
    smaps->heap_rss = smaps->anon_rss / 20;
    smaps->anon_rss -= smaps->heap_rss;
  }
  // LCOV_EXCL_BR_STOP

  // Stack estimate: typical 8MB per thread, but we don't know thread count
  // Leave as 0 since we can't reliably detect it
}

#else
// Other platforms: no-op
void valk_smaps_collect(valk_smaps_breakdown_t *smaps) {
  if (smaps == nullptr) return;
  memset(smaps, 0, sizeof(*smaps));
}
#endif

void *valk_mem_allocator_alloc(valk_mem_allocator_t *self, sz bytes) {
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to alloc %zu",
              bytes);
  // Order by performance.
  switch (self->type) {
    case VALK_ALLOC_NULL:
      VALK_RAISE("Alloc on nullptr allocator %zu", bytes);
      return nullptr;
    case VALK_ALLOC_ARENA:
      return valk_mem_arena_alloc((void *)self, bytes);
    case VALK_ALLOC_SLAB: {
      valk_slab_item_t *item = valk_slab_aquire((void *)self);
      return item ? (void *)item->data : nullptr;
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
  return nullptr;
}

void *valk_mem_allocator_calloc(valk_mem_allocator_t *self, sz num,
                                sz size) {
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %zu :: size: %zu",
              num, size);
  void *res;
  // Order by performance.
  switch (self->type) {
    case VALK_ALLOC_NULL:
      VALK_RAISE("Calloc on nullptr allocator num: %zu :: size: %zu", num, size);
      res = nullptr;
      break;
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
    case VALK_ALLOC_TLAB:
      res = valk_gc_tlab_alloc_slow(num * size);
      break;
  }
  return res;
}

void *valk_mem_allocator_realloc(valk_mem_allocator_t *self, void *ptr,
                                 sz new_size) {
  VALK_ASSERT(self,
              "Thread Local ALLOCATOR has not been initialized, please "
              "initialize it with something like valk_mem_init_malloc()\n "
              "Failed while trying to calloc %p :: size: %zu",
              ptr, new_size);

  // Order by performance.
  switch (self->type) {
    case VALK_ALLOC_NULL:
      VALK_RAISE("Realloc on nullptr allocator ptr: %p :: size: %zu", ptr,
                 new_size);
      return nullptr;
    case VALK_ALLOC_ARENA: {
      // Copy-alloc semantics for arena realloc
      sz old_size = 0;
      if (ptr) {
        old_size = *(((u64 *)ptr) - 1);
      }
      void *np = valk_mem_arena_alloc((void *)self, new_size);
      if (ptr && np) {
        sz n = old_size < new_size ? old_size : new_size;
        memcpy(np, ptr, n);
      }
      return np;
    }
    case VALK_ALLOC_SLAB: {
      sz slabSize = ((valk_slab_t *)self)->itemSize;
      VALK_ASSERT(
          new_size <= slabSize,
          "Realloc with slab allocator is unsafe,\n  tried to allocate more "
          "memory than fits in a slab\n %zu wanted, but %zu is the size",
          new_size, slabSize);
      return ptr;
    }
    case VALK_ALLOC_GC_HEAP: {
      return valk_gc_heap2_realloc((valk_gc_heap2_t *)self, ptr, new_size);
    }
    case VALK_ALLOC_MALLOC:
      return realloc(ptr, new_size);
    case VALK_ALLOC_TLAB:
      VALK_RAISE("Realloc on TLAB allocator not supported: %p -> %zu", ptr, new_size);
      return nullptr;
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
      VALK_RAISE("Free on nullptr allocator %p", ptr);
      return;
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
    case VALK_ALLOC_TLAB:
      return;
  }
}



void valk_slab_bitmap_snapshot(valk_slab_t *slab, valk_slab_bitmap_t *out) {
  if (!slab || !out) return;
  out->data = nullptr;
  out->bytes = 0;
  out->version = 0;

  if (!slab->usage_bitmap) return;

  sz bitmap_bytes = (slab->numItems + 7) / 8;
  out->data = malloc(bitmap_bytes);
  if (!out->data) return;

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

    if (!delta_add_run(out, run_start, run_len, xor_byte)) {
      valk_bitmap_delta_free(out);
      return false;
    }
    i += run_len;
  }

  return true;
}

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

sz valk_slab_bitmap_buckets(valk_slab_t *slab,
                                 sz start_slot, sz end_slot,
                                 sz num_buckets,
                                 valk_bitmap_bucket_t *out_buckets) {
  if (!slab || !out_buckets || num_buckets == 0) return 0;
  if (!slab->usage_bitmap) return 0;

  if (end_slot > slab->numItems) end_slot = slab->numItems;
  if (start_slot >= end_slot) return 0;

  sz total_slots = end_slot - start_slot;
  sz slots_per_bucket = (total_slots + num_buckets - 1) / num_buckets;
  if (slots_per_bucket == 0) slots_per_bucket = 1;

  for (sz b = 0; b < num_buckets; b++) {
    out_buckets[b].used = 0;
    out_buckets[b].free = 0;
  }

  for (sz slot = start_slot; slot < end_slot; slot++) {
    sz byte_idx = slot / 8;
    u8 bit_mask = 1 << (slot % 8);
    bool is_used = (slab->usage_bitmap[byte_idx] & bit_mask) != 0;

    sz bucket_idx = (slot - start_slot) / slots_per_bucket;
    if (bucket_idx >= num_buckets) bucket_idx = num_buckets - 1;

    if (is_used) {
      out_buckets[bucket_idx].used++;
    } else {
      out_buckets[bucket_idx].free++;
    }
  }

  return num_buckets;
}
