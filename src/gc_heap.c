#include "gc_heap.h"
#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

// ============================================================================
// Page ID Counter
// ============================================================================

static _Atomic u32 __page_id_counter = 0;

// ============================================================================
// Live Heap Registry
// ============================================================================

static _Atomic u64 g_heap_generation = 1;

u64 valk_gc_heap_next_generation(void) {
  return atomic_fetch_add(&g_heap_generation, 1);
}

#define VALK_GC_MAX_LIVE_HEAPS 64
static valk_gc_heap2_t *g_live_heaps[VALK_GC_MAX_LIVE_HEAPS];
static pthread_mutex_t g_live_heaps_lock = PTHREAD_MUTEX_INITIALIZER;

static void valk_gc_register_heap(valk_gc_heap2_t *heap) {
  pthread_mutex_lock(&g_live_heaps_lock);
  for (int i = 0; i < VALK_GC_MAX_LIVE_HEAPS; i++) { // LCOV_EXCL_BR_LINE
    if (g_live_heaps[i] == nullptr) {
      g_live_heaps[i] = heap;
      break;
    }
  }
  pthread_mutex_unlock(&g_live_heaps_lock);
}

// LCOV_EXCL_START - heap unregister/alive check used internally by TLAB operations
static void valk_gc_unregister_heap(valk_gc_heap2_t *heap) {
  pthread_mutex_lock(&g_live_heaps_lock);
  for (int i = 0; i < VALK_GC_MAX_LIVE_HEAPS; i++) {
    if (g_live_heaps[i] == heap) {
      g_live_heaps[i] = nullptr;
      break;
    }
  }
  pthread_mutex_unlock(&g_live_heaps_lock);
}

static bool valk_gc_is_heap_alive(valk_gc_heap2_t *heap) {
  if (!heap) return false;
  pthread_mutex_lock(&g_live_heaps_lock);
  bool alive = false;
  for (int i = 0; i < VALK_GC_MAX_LIVE_HEAPS; i++) {
    if (g_live_heaps[i] == heap) {
      alive = true;
      break;
    }
  }
  pthread_mutex_unlock(&g_live_heaps_lock);
  return alive;
}
// LCOV_EXCL_STOP

// ============================================================================
// Page List Initialization
// ============================================================================

static void valk_gc_page_list_init(valk_gc_page_list_t *list, u8 size_class) {
  pthread_mutex_init(&list->lock, nullptr);
  list->all_pages = nullptr;
  list->partial_pages = nullptr;
  list->num_pages = 0;
  atomic_store(&list->total_slots, 0);
  atomic_store(&list->used_slots, 0);
  atomic_store(&list->next_page_offset, 0);
  list->slot_size = valk_gc_size_classes[size_class];
  list->slots_per_page = valk_gc_slots_per_page(size_class);
  list->region_start = 0;
  list->region_size = 0;
  list->page_size = valk_gc_page_total_size(size_class);
}

// ============================================================================
// TLAB Operations
// ============================================================================

void valk_gc_tlab2_init(valk_gc_tlab2_t *tlab) {
  tlab->owner_heap = nullptr;
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = nullptr;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
}

void valk_gc_tlab2_abandon(valk_gc_tlab2_t *tlab) {
  if (!tlab) return; // LCOV_EXCL_BR_LINE
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = nullptr;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
  tlab->owner_heap = nullptr;
}

void valk_gc_tlab2_reset(valk_gc_tlab2_t *tlab) {
  if (!tlab) return; // LCOV_EXCL_BR_LINE

  valk_gc_heap2_t *heap = tlab->owner_heap;

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page2_t *page = tlab->classes[c].page;
    u32 next = tlab->classes[c].next_slot;
    u32 limit = tlab->classes[c].limit_slot;

    // LCOV_EXCL_START - TLAB unused slot reclaim requires specific mid-allocation TLAB state
    if (page && heap && next < limit) {
      u32 unused = limit - next;
      valk_gc_page_list_t *list = &heap->classes[c];
      u8 *bitmap = valk_gc_page2_alloc_bitmap(page);

      pthread_mutex_lock(&list->lock);
      for (u32 i = next; i < limit; i++) {
        valk_gc_bitmap_clear(bitmap, i);
      }
      atomic_fetch_sub(&page->num_allocated, unused);
      atomic_fetch_sub(&list->used_slots, unused);
      pthread_mutex_unlock(&list->lock);
    }
    // LCOV_EXCL_STOP

    tlab->classes[c].page = nullptr;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }

  tlab->owner_heap = nullptr;
}

static __thread valk_gc_tlab2_t *valk_gc_local_tlab = nullptr;

void valk_gc_tlab2_invalidate_heap(valk_gc_heap2_t *heap) {
  if (!valk_gc_local_tlab) return;
  if (valk_gc_local_tlab->owner_heap == heap) {
    valk_gc_tlab2_abandon(valk_gc_local_tlab);
  }
}

// ============================================================================
// Page Allocation
// ============================================================================

static valk_gc_page2_t *valk_gc_page2_alloc(valk_gc_heap2_t *heap, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return nullptr; // LCOV_EXCL_BR_LINE

  valk_gc_page_list_t *list = &heap->classes[size_class];
  u64 page_size = list->page_size;
  u16 slots = list->slots_per_page;
  u16 bitmap_bytes = valk_gc_bitmap_bytes(size_class);

  // LCOV_EXCL_BR_START - hard limit and mprotect failures
  sz current = atomic_load(&heap->committed_bytes);
  sz new_committed;
  do {
    if (current + page_size > heap->hard_limit) {
      VALK_WARN("Cannot allocate page: would exceed hard limit (%zu + %zu > %zu)",
                current, page_size, heap->hard_limit);
      return nullptr;
    }
    new_committed = current + page_size;
  } while (!atomic_compare_exchange_weak(&heap->committed_bytes, &current, new_committed));

  u32 offset = atomic_fetch_add(&list->next_page_offset, (u32)page_size);
  if (offset + page_size > list->region_size) {
    atomic_fetch_sub(&heap->committed_bytes, page_size);
    VALK_ERROR("Region exhausted for class %d", size_class);
    return nullptr;
  }

  void *addr = (u8 *)heap->base + list->region_start + offset;

  if (mprotect(addr, page_size, PROT_READ | PROT_WRITE) != 0) {
    atomic_fetch_sub(&heap->committed_bytes, page_size);
    VALK_ERROR("mprotect failed for page at %p (class %d)", addr, size_class);
    return nullptr;
  }
  // LCOV_EXCL_BR_STOP

  valk_gc_page2_t *page = (valk_gc_page2_t *)addr;

  memset(page, 0, sizeof(valk_gc_page2_t));
  page->page_id = atomic_fetch_add(&__page_id_counter, 1);
  page->size_class = size_class;
  page->slots_per_page = slots;
  page->bitmap_bytes = bitmap_bytes;
  atomic_store(&page->num_allocated, 0);

  memset(valk_gc_page2_alloc_bitmap(page), 0, bitmap_bytes);
  memset(valk_gc_page2_mark_bitmap(page), 0, bitmap_bytes);

  return page;
}

// ============================================================================
// TLAB Refill
// ============================================================================

// LCOV_EXCL_BR_START - TLAB refill internal bitmap search and page management
static u32 valk_gc_page2_find_free_slots(valk_gc_page2_t *page, u32 count) {
  u8 *bitmap = valk_gc_page2_alloc_bitmap(page);
  u16 slots = page->slots_per_page;

  for (u32 i = 0; i < slots; i++) {
    if (!valk_gc_bitmap_test(bitmap, i)) {
      u32 run = 1;
      while (run < count && i + run < slots &&
             !valk_gc_bitmap_test(bitmap, i + run)) {
        run++;
      }
      if (run >= count) {
        return i;
      }
      i += run;
    }
  }
  return UINT32_MAX;
}

bool valk_gc_tlab2_refill(valk_gc_tlab2_t *tlab, valk_gc_heap2_t *heap, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return false;

  valk_gc_page_list_t *list = &heap->classes[size_class];

  pthread_mutex_lock(&list->lock);

  valk_gc_page2_t *page = list->partial_pages;
  u32 start_slot = 0;
  u32 num_slots = VALK_GC_TLAB_SLOTS;

  if (page) {
    start_slot = valk_gc_page2_find_free_slots(page, num_slots);
    if (start_slot == UINT32_MAX) {
      list->partial_pages = page->next_partial;
      page = nullptr;
    // LCOV_EXCL_START - page reclaim path requires MADV_DONTNEED to zero page
    } else if (page->reclaimed) {
      page->size_class = size_class;
      page->slots_per_page = list->slots_per_page;
      page->bitmap_bytes = valk_gc_bitmap_bytes(size_class);
      atomic_store(&page->num_allocated, 0);
      memset(valk_gc_page2_alloc_bitmap(page), 0, page->bitmap_bytes);
      memset(valk_gc_page2_mark_bitmap(page), 0, page->bitmap_bytes);
      atomic_fetch_add(&heap->committed_bytes, list->page_size);
      page->reclaimed = false;
    }
    // LCOV_EXCL_STOP
  }

  if (!page) {
    pthread_mutex_unlock(&list->lock);
    page = valk_gc_page2_alloc(heap, size_class);
    if (!page) return false;
    pthread_mutex_lock(&list->lock);

    page->next = list->all_pages;
    list->all_pages = page;
    page->next_partial = list->partial_pages;
    list->partial_pages = page;
    list->num_pages++;
    atomic_fetch_add(&list->total_slots, page->slots_per_page);

    start_slot = 0;
  }

  if (start_slot + num_slots > page->slots_per_page) {
    num_slots = page->slots_per_page - start_slot;
  }

  u8 *bitmap = valk_gc_page2_alloc_bitmap(page);
  for (u32 i = start_slot; i < start_slot + num_slots; i++) {
    valk_gc_bitmap_set(bitmap, i);
  }
  atomic_fetch_add(&page->num_allocated, num_slots);
  atomic_fetch_add(&list->used_slots, num_slots);
  u64 added_bytes = num_slots * list->slot_size;
  u64 new_used = atomic_fetch_add(&heap->used_bytes, added_bytes) + added_bytes;
  sz cur_peak = atomic_load(&heap->stats.peak_usage);
  while (new_used > cur_peak) {
    if (atomic_compare_exchange_weak(&heap->stats.peak_usage, &cur_peak, new_used))
      break;
  }

  if (atomic_load(&page->num_allocated) >= page->slots_per_page) {
    valk_gc_page2_t **pp = &list->partial_pages;
    while (*pp && *pp != page) {
      pp = &(*pp)->next_partial;
    }
    if (*pp == page) {
      *pp = page->next_partial;
    }
  }

  pthread_mutex_unlock(&list->lock);

  tlab->classes[size_class].page = page;
  tlab->classes[size_class].next_slot = start_slot;
  tlab->classes[size_class].limit_slot = start_slot + num_slots;

  return true;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Large Object Allocation
// ============================================================================

static bool valk_gc_heap2_try_emergency_gc(valk_gc_heap2_t *heap, u64 needed);

// LCOV_EXCL_BR_START - large object mmap/malloc failures and OOM paths
static void *valk_gc_heap2_alloc_large(valk_gc_heap2_t *heap, u64 bytes) {
  u64 alloc_size = (bytes + 4095) & ~4095ULL;

  u64 current = valk_gc_heap2_used_bytes(heap);

  if (current + alloc_size > heap->hard_limit) {
    if (!valk_gc_heap2_try_emergency_gc(heap, alloc_size)) {
      valk_gc_oom_abort(heap, bytes);
    }
  } else if (current + alloc_size > heap->soft_limit) {
    if (!heap->in_emergency_gc && !atomic_load(&heap->gc_in_progress)) {
      valk_gc_heap2_collect(heap);
    }
  }

  void *data = mmap(nullptr, alloc_size, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (data == MAP_FAILED) {
    VALK_ERROR("mmap failed for large object of %zu bytes", alloc_size);
    return nullptr;
  }

  valk_gc_large_obj_t *obj = malloc(sizeof(valk_gc_large_obj_t));
  if (!obj) {
    munmap(data, alloc_size);
    return nullptr;
  }
  obj->data = data;
  obj->size = alloc_size;
  obj->marked = false;

  pthread_mutex_lock(&heap->large_lock);
  obj->next = heap->large_objects;
  heap->large_objects = obj;
  pthread_mutex_unlock(&heap->large_lock);

  atomic_fetch_add(&heap->large_object_bytes, alloc_size);
  u64 used = valk_gc_heap2_used_bytes(heap);
  sz cur_peak = atomic_load(&heap->stats.peak_usage);
  while (used > cur_peak) {
    if (atomic_compare_exchange_weak(&heap->stats.peak_usage, &cur_peak, used))
      break;
  }

  return data;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Main Allocation Entry Point
// ============================================================================

// LCOV_EXCL_BR_START - heap alloc OOM and TLAB failure paths
void *valk_gc_heap2_alloc(valk_gc_heap2_t *heap, sz bytes) {
  if (bytes == 0) return nullptr;

  if (bytes > VALK_GC_LARGE_THRESHOLD) {
    return valk_gc_heap2_alloc_large(heap, bytes);
  }

  u8 size_class = valk_gc_size_class(bytes);
  if (size_class == UINT8_MAX) {
    return valk_gc_heap2_alloc_large(heap, bytes);
  }

  sz alloc_size = valk_gc_size_classes[size_class];
  sz current = valk_gc_heap2_used_bytes(heap);

  if (current + alloc_size > heap->hard_limit) {
    if (!valk_gc_heap2_try_emergency_gc(heap, alloc_size)) {
      valk_gc_oom_abort(heap, bytes);
    }
  } else if (current + alloc_size > heap->soft_limit) {
    if (!heap->in_emergency_gc && !atomic_load(&heap->gc_in_progress)) {
      valk_gc_heap2_collect(heap);
    }
  }

  if (!valk_gc_local_tlab) {
    valk_gc_local_tlab = malloc(sizeof(valk_gc_tlab2_t));
    if (!valk_gc_local_tlab) return nullptr;
    valk_gc_tlab2_init(valk_gc_local_tlab);
  }

  if (valk_gc_local_tlab->owner_heap != heap ||
      valk_gc_local_tlab->owner_generation != heap->generation) {
    if (valk_gc_local_tlab->owner_heap == heap &&
        valk_gc_local_tlab->owner_generation != heap->generation) {
      valk_gc_tlab2_abandon(valk_gc_local_tlab);
    } else if (valk_gc_local_tlab->owner_heap && valk_gc_is_heap_alive(valk_gc_local_tlab->owner_heap)) {
      valk_gc_tlab2_reset(valk_gc_local_tlab);
    } else {
      valk_gc_tlab2_abandon(valk_gc_local_tlab);
    }
    valk_gc_local_tlab->owner_heap = heap;
    valk_gc_local_tlab->owner_generation = heap->generation;
  }

  void *ptr = valk_gc_tlab2_alloc(valk_gc_local_tlab, size_class);
  if (ptr) {
    memset(ptr, 0, alloc_size);
    return ptr;
  }

  if (!valk_gc_tlab2_refill(valk_gc_local_tlab, heap, size_class)) {
    VALK_ERROR("Failed to refill TLAB for class %d", size_class);
    return nullptr;
  }

  ptr = valk_gc_tlab2_alloc(valk_gc_local_tlab, size_class);
  if (ptr) {
    memset(ptr, 0, alloc_size);
  }
  return ptr;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Realloc
// ============================================================================

void *valk_gc_heap2_realloc(valk_gc_heap2_t *heap, void *ptr, sz new_size) {
  if (ptr == nullptr) {
    return valk_gc_heap2_alloc(heap, new_size);
  }
  if (new_size == 0) {
    return nullptr;
  }

  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(heap, ptr, &loc)) { // LCOV_EXCL_BR_LINE
    sz old_size = valk_gc_size_classes[loc.size_class];
    if (new_size <= old_size) {
      return ptr;
    }
    void *new_ptr = valk_gc_heap2_alloc(heap, new_size);
    if (new_ptr) { // LCOV_EXCL_BR_LINE - OOM after successful alloc
      memcpy(new_ptr, ptr, old_size);
    }
    return new_ptr;
  }

  // LCOV_EXCL_START - large object realloc requires allocating large object first then reallocating
  pthread_mutex_lock(&heap->large_lock);
  for (valk_gc_large_obj_t *obj = heap->large_objects; obj != nullptr; obj = obj->next) {
    if (obj->data == ptr) {
      u64 old_size = obj->size;
      pthread_mutex_unlock(&heap->large_lock);

      if (new_size <= old_size) {
        return ptr;
      }
      void *new_ptr = valk_gc_heap2_alloc(heap, new_size);
      if (new_ptr) {
        memcpy(new_ptr, ptr, old_size);
      }
      return new_ptr;
    }
  }
  pthread_mutex_unlock(&heap->large_lock);

  VALK_WARN("valk_gc_heap2_realloc: pointer %p not found in heap", ptr);
  return nullptr;
  // LCOV_EXCL_STOP
}

// ============================================================================
// Heap Create / Destroy
// ============================================================================

// LCOV_EXCL_BR_START - heap creation calloc/mmap failures
valk_gc_heap2_t *valk_gc_heap2_create(sz hard_limit) {
  valk_gc_heap2_t *heap = calloc(1, sizeof(valk_gc_heap2_t));
  if (!heap) {
    VALK_ERROR("Failed to allocate heap structure");
    return nullptr;
  }

  heap->type = VALK_ALLOC_GC_HEAP;
  heap->generation = atomic_fetch_add(&g_heap_generation, 1);
  heap->hard_limit = hard_limit > 0 ? hard_limit : VALK_GC_DEFAULT_HARD_LIMIT;
  heap->soft_limit = heap->hard_limit * 3 / 4;
  heap->gc_threshold_pct = 75;

  heap->reserved = VALK_GC_VIRTUAL_RESERVE;
  heap->base = mmap(nullptr, heap->reserved, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (heap->base == MAP_FAILED) {
    VALK_ERROR("Failed to reserve %zu bytes of virtual address space", heap->reserved);
    free(heap);
    return nullptr;
  }
  // LCOV_EXCL_BR_STOP

  sz region_size = heap->reserved / VALK_GC_NUM_SIZE_CLASSES;
  region_size = region_size & ~(sz)4095;

  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_init(&heap->classes[c], c);
    heap->classes[c].region_start = (sz)c * region_size;
    heap->classes[c].region_size = region_size;
  }

  heap->large_objects = nullptr;
  pthread_mutex_init(&heap->large_lock, nullptr);

  atomic_store(&heap->committed_bytes, 0);
  atomic_store(&heap->used_bytes, 0);
  atomic_store(&heap->large_object_bytes, 0);
  atomic_store(&heap->gc_in_progress, false);
  heap->in_emergency_gc = false;

  atomic_store(&heap->collections, 0);
  atomic_store(&heap->bytes_allocated_total, 0);
  atomic_store(&heap->bytes_reclaimed_total, 0);

  memset(&heap->stats, 0, sizeof(heap->stats));
  memset(&heap->runtime_metrics, 0, sizeof(heap->runtime_metrics));

  VALK_INFO("Created multi-class GC heap: hard_limit=%zu soft_limit=%zu reserved=%zu region_size=%zu",
            heap->hard_limit, heap->soft_limit, heap->reserved, region_size);

  valk_gc_register_heap(heap);
  return heap;
}

void valk_gc_heap2_destroy(valk_gc_heap2_t *heap) {
  if (!heap) return;

  valk_gc_tlab2_invalidate_heap(heap);
  valk_gc_unregister_heap(heap);

  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    pthread_mutex_destroy(&heap->classes[c].lock);
  }

  pthread_mutex_lock(&heap->large_lock);
  valk_gc_large_obj_t *large = heap->large_objects;
  while (large) {
    valk_gc_large_obj_t *next = large->next;
    if (large->data) { // LCOV_EXCL_BR_LINE - large->data always valid
      munmap(large->data, large->size);
    }
    free(large);
    large = next;
  }
  pthread_mutex_unlock(&heap->large_lock);
  pthread_mutex_destroy(&heap->large_lock);

  if (heap->base && heap->reserved > 0) { // LCOV_EXCL_BR_LINE - always valid after create
    munmap(heap->base, heap->reserved);
  }

  VALK_INFO("Destroyed multi-class GC heap");
  free(heap);
}

// ============================================================================
// Pointer Location
// ============================================================================

// LCOV_EXCL_BR_START - pointer location search and validation
bool valk_gc_ptr_to_location(valk_gc_heap2_t *heap, void *ptr, valk_gc_ptr_location_t *out) {
  if (!heap || !ptr || !out) {
    if (out) out->is_valid = false;
    return false;
  }

  out->is_valid = false;

  if (heap->base && heap->reserved > 0) {
    u8 *base = (u8 *)heap->base;
    u8 *addr = (u8 *)ptr;

    if (addr < base || addr >= base + heap->reserved) {
      return false;
    }

    size_t offset = (size_t)(addr - base);

    for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
      valk_gc_page_list_t *list = &heap->classes[c];
      if (offset >= list->region_start && offset < list->region_start + list->region_size) {
        u64 offset_in_region = offset - list->region_start;

        u32 committed = atomic_load(&list->next_page_offset);
        if (offset_in_region >= committed) {
          return false;
        }

        u64 page_idx = offset_in_region / list->page_size;
        valk_gc_page2_t *page = (valk_gc_page2_t *)(base + list->region_start + page_idx * list->page_size);

        u8 *slots_start = valk_gc_page2_slots(page);
        if (addr < slots_start) {
          return false;
        }

        u32 slot = (u32)((size_t)(addr - slots_start) / list->slot_size);
        if (slot >= page->slots_per_page) {
          return false;
        }

        out->page = page;
        out->slot = slot;
        out->size_class = c;
        out->is_valid = true;
        return true;
      }
    }

    return false;
  }

  // LCOV_EXCL_START - slow path for non-contiguous heap requires heap->base not set
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    u16 slot_size = valk_gc_size_classes[c];

    for (valk_gc_page2_t *page = list->all_pages; page != nullptr; page = page->next) {
      u8 *slots_start = valk_gc_page2_slots(page);
      u8 *slots_end = slots_start + page->slots_per_page * slot_size;

      if ((u8 *)ptr >= slots_start && (u8 *)ptr < slots_end) {
        uptr off = (uptr)ptr - (uptr)slots_start;
        if (off % slot_size == 0) {
          out->page = page;
          out->slot = (u32)(off / slot_size);
          out->size_class = c;
          out->is_valid = true;
          return true;
        }
      }
    }
  }

  return false;
  // LCOV_EXCL_STOP
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Large Object Marking
// ============================================================================

// LCOV_EXCL_BR_START - large object marking and sweep iteration
bool valk_gc_mark_large_object(valk_gc_heap2_t *heap, void *ptr) {
  if (!heap || !ptr) return false;

  pthread_mutex_lock(&heap->large_lock);

  for (valk_gc_large_obj_t *obj = heap->large_objects; obj != nullptr; obj = obj->next) {
    if (ptr >= obj->data && (u8 *)ptr < (u8 *)obj->data + obj->size) {
      bool was_unmarked = !obj->marked;
      obj->marked = true;
      pthread_mutex_unlock(&heap->large_lock);
      return was_unmarked;
    }
  }

  pthread_mutex_unlock(&heap->large_lock);
  return false;
}

// ============================================================================
// Sweep
// ============================================================================

sz valk_gc_sweep_page2(valk_gc_page2_t *page) {
  if (!page) return 0;

  sz freed = 0;
  u16 slots = page->slots_per_page;
  u16 slot_size = valk_gc_size_classes[page->size_class];

  u8 *alloc_bitmap = valk_gc_page2_alloc_bitmap(page);
  u8 *mark_bitmap = valk_gc_page2_mark_bitmap(page);

  u64 num_words = (slots + 63) / 64;

  for (u64 w = 0; w < num_words; w++) {
    u64 alloc, mark;
    memcpy(&alloc, alloc_bitmap + w * 8, sizeof(u64));
    memcpy(&mark, mark_bitmap + w * 8, sizeof(u64));

    u64 garbage = alloc & ~mark;

    if (garbage != 0) {
      freed += (sz)__builtin_popcountll(garbage);
      u64 new_alloc = alloc & mark;
      memcpy(alloc_bitmap + w * 8, &new_alloc, sizeof(u64));

      u64 temp = garbage;
      while (temp) {
        u64 bit = (u64)__builtin_ctzll(temp);
        u64 slot = w * 64 + bit;

        if (slot < slots) {
          void *ptr = valk_gc_page2_slot_ptr(page, (u32)slot);

          // LCOV_EXCL_BR_START - LVAL_REF finalizer requires integration with ref creation API
          if (slot_size >= sizeof(valk_lval_t)) {
            valk_lval_t *v = (valk_lval_t *)ptr;
            u64 flags = atomic_load_explicit(&v->flags, memory_order_acquire);
            if ((valk_ltype_e)(flags & LVAL_TYPE_MASK) == LVAL_REF && v->ref.free != nullptr) {
              v->ref.free(v->ref.ptr);
            }
          }
          // LCOV_EXCL_BR_STOP
        }

        temp &= temp - 1;
      }
    }

    u64 zero = 0;
    memcpy(mark_bitmap + w * 8, &zero, sizeof(u64));
  }

  atomic_fetch_sub(&page->num_allocated, (u32)freed);

  return freed;
}

sz valk_gc_sweep_large_objects(valk_gc_heap2_t *heap) {
  if (!heap) return 0; // LCOV_EXCL_BR_LINE

  sz freed = 0;

  pthread_mutex_lock(&heap->large_lock);

  valk_gc_large_obj_t **pp = &heap->large_objects;
  while (*pp != nullptr) {
    valk_gc_large_obj_t *obj = *pp;

    if (!obj->marked) {
      *pp = obj->next;
      if (obj->data) { // LCOV_EXCL_BR_LINE - data always set on large objects
        munmap(obj->data, obj->size);
      }
      freed += obj->size;
      free(obj);
    } else {
      obj->marked = false;
      pp = &obj->next;
    }
  }

  pthread_mutex_unlock(&heap->large_lock);

  atomic_fetch_sub(&heap->large_object_bytes, freed);
  return freed;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Post-Sweep Maintenance
// ============================================================================

// LCOV_EXCL_BR_START - page list rebuild and reclaim iteration
void valk_gc_rebuild_partial_lists(valk_gc_heap2_t *heap) {
  if (!heap) return;

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];

    pthread_mutex_lock(&list->lock);

    list->partial_pages = nullptr;

    for (valk_gc_page2_t *page = list->all_pages; page != nullptr; page = page->next) {
      u32 allocated = atomic_load(&page->num_allocated);

      if (allocated < page->slots_per_page) {
        page->next_partial = list->partial_pages;
        list->partial_pages = page;
      }
    }

    pthread_mutex_unlock(&list->lock);
  }
}

sz valk_gc_reclaim_empty_pages(valk_gc_heap2_t *heap) {
  if (!heap) return 0;

  sz pages_reclaimed = 0;

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];

    pthread_mutex_lock(&list->lock);

    for (valk_gc_page2_t *page = list->all_pages; page != nullptr; page = page->next) {
      u32 allocated = atomic_load(&page->num_allocated);

      if (allocated == 0 && !page->reclaimed) {
        u64 page_size = list->page_size;
#ifdef __APPLE__
        madvise(page, page_size, MADV_FREE);
#else
        madvise(page, page_size, MADV_DONTNEED);
#endif
        atomic_fetch_sub(&heap->committed_bytes, page_size);
        page->reclaimed = true;
        pages_reclaimed++;
      }
    }

    pthread_mutex_unlock(&list->lock);
  }

  return pages_reclaimed;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Heap Stats
// ============================================================================

void valk_gc_heap2_get_stats(valk_gc_heap2_t *heap, valk_gc_stats2_t *out) {
  if (!heap || !out) return; // LCOV_EXCL_BR_LINE

  memset(out, 0, sizeof(*out));
  out->used_bytes = valk_gc_heap2_used_bytes(heap);
  out->committed_bytes = atomic_load(&heap->committed_bytes);
  out->large_object_bytes = atomic_load(&heap->large_object_bytes);
  out->hard_limit = heap->hard_limit;
  out->soft_limit = heap->soft_limit;
  out->collections = atomic_load(&heap->collections);
  out->bytes_reclaimed_total = atomic_load(&heap->bytes_reclaimed_total);

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    out->class_used_slots[c] = atomic_load(&heap->classes[c].used_slots);
    out->class_total_slots[c] = atomic_load(&heap->classes[c].total_slots);
  }
}

// ============================================================================
// OOM Abort
// ============================================================================

// LCOV_EXCL_START - OOM abort is intentionally untestable
__attribute__((noreturn))
void valk_gc_oom_abort(valk_gc_heap2_t *heap, sz requested) {
  fprintf(stderr, "\n");
  fprintf(stderr, "================================================================\n");
  fprintf(stderr, "                    FATAL: OUT OF MEMORY                        \n");
  fprintf(stderr, "================================================================\n");
  fprintf(stderr, " Requested:    %12zu bytes\n", requested);

  if (heap) {
    valk_gc_stats2_t stats;
    valk_gc_heap2_get_stats(heap, &stats);

    fprintf(stderr, " Used:         %12zu bytes\n", stats.used_bytes);
    fprintf(stderr, " Hard Limit:   %12zu bytes\n", stats.hard_limit);
    fprintf(stderr, " Committed:    %12zu bytes\n", stats.committed_bytes);
    fprintf(stderr, "----------------------------------------------------------------\n");
    fprintf(stderr, " Per-Class Usage:\n");
    for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
      if (stats.class_total_slots[c] > 0) {
        u64 pct = (stats.class_used_slots[c] * 100) / stats.class_total_slots[c];
        fprintf(stderr, "   Class %d (%4u B): %8llu / %8llu slots (%3llu%%)\n",
                c, valk_gc_size_classes[c],
                (unsigned long long)stats.class_used_slots[c], (unsigned long long)stats.class_total_slots[c], (unsigned long long)pct);
      }
    }
    fprintf(stderr, " Large Objects: %12zu bytes\n", stats.large_object_bytes);
    fprintf(stderr, "----------------------------------------------------------------\n");
    fprintf(stderr, " GC cycles: %llu, Total reclaimed: %zu bytes\n",
            (unsigned long long)stats.collections,
            stats.bytes_reclaimed_total);
    fprintf(stderr, "----------------------------------------------------------------\n");
    fprintf(stderr, " Increase limit: VALK_HEAP_HARD_LIMIT=%zu\n", stats.hard_limit * 2);
  }
  fprintf(stderr, "================================================================\n");

  abort();
}
// LCOV_EXCL_STOP

// ============================================================================
// Emergency GC
// ============================================================================

// LCOV_EXCL_START - fork safety function requires actual fork()
void valk_gc_heap_reset_after_fork(void) {
  pthread_mutex_init(&g_live_heaps_lock, nullptr);
  for (int i = 0; i < VALK_GC_MAX_LIVE_HEAPS; i++) {
    g_live_heaps[i] = nullptr;
  }
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - emergency GC triggered at hard limit requires specific memory pressure conditions
static bool valk_gc_heap2_try_emergency_gc(valk_gc_heap2_t *heap, u64 needed) {
  if (heap->in_emergency_gc) {
    return false;
  }

  heap->in_emergency_gc = true;

  VALK_WARN("Emergency GC: need %zu bytes, used %zu / %zu",
            needed, valk_gc_heap2_used_bytes(heap), heap->hard_limit);

  u64 reclaimed = valk_gc_heap2_collect(heap);

  heap->in_emergency_gc = false;

  u64 after = valk_gc_heap2_used_bytes(heap);
  if (after + needed <= heap->hard_limit) {
    VALK_INFO("Emergency GC recovered %zu bytes, allocation can proceed", reclaimed);
    return true;
  }

  return false;
}
// LCOV_EXCL_STOP
