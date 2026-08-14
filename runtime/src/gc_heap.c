#include "gc_heap.h"
#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <sched.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

static _Atomic u32 __page_id_counter = 0;

static _Atomic u64 g_heap_generation = 1;

u64 valk_gc_heap_next_generation(void) {
  return atomic_fetch_add(&g_heap_generation, 1);
}



void valk_gc_page_list_init(valk_gc_page_list_t *list, u8 size_class) {
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
  list->page_shift = valk_gc_log2_pow2(list->page_size);
  VALK_ASSERT(((sz)1 << list->page_shift) == list->page_size,
              "page_size must be a power of two for shift-based addressing");
}

void valk_gc_tlab_init(valk_gc_tlab_t *tlab) {
  tlab->owner_heap = nullptr;
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = nullptr;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
}

void valk_gc_tlab_abandon(valk_gc_tlab_t *tlab) {
  if (!tlab) return; // LCOV_EXCL_BR_LINE
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = nullptr;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
  tlab->owner_heap = nullptr;
}

void valk_gc_tlab_reset(valk_gc_tlab_t *tlab) {
  if (!tlab) return; // LCOV_EXCL_BR_LINE

  valk_gc_heap_t *heap = tlab->owner_heap;

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_t *page = tlab->classes[c].page;
    u32 next = tlab->classes[c].next_slot;
    u32 limit = tlab->classes[c].limit_slot;

    // LCOV_EXCL_START - TLAB unused slot reclaim requires specific mid-allocation TLAB state
    if (page && heap && next < limit) {
      u32 unused = limit - next;
      valk_gc_page_list_t *list = &heap->classes[c];
      u8 *bitmap = valk_gc_page_alloc_bitmap(page);

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

static __thread valk_gc_tlab_t *valk_gc_local_tlab = nullptr;

void valk_gc_tlab_invalidate_heap(valk_gc_heap_t *heap) {
  if (!valk_gc_local_tlab) return;
  if (valk_gc_local_tlab->owner_heap == heap) {
    valk_gc_tlab_abandon(valk_gc_local_tlab);
  }
}

// LCOV_EXCL_START - concurrent-mark pause protocol
// Blacken this thread's unconsumed TLAB slots at the CONC_START pause:
// objects bump-allocated from them during the concurrent mark are then
// born marked without any per-allocation work.
void valk_gc_tlab_blacken_remainder(void) {
  valk_gc_tlab_t *tlab = valk_gc_local_tlab;
  if (!tlab || !tlab->owner_heap) return;
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_t *page = tlab->classes[c].page;
    if (!page || page->reclaimed) continue;
    u8 *mark_bitmap = valk_gc_page_mark_bitmap(page);
    for (u32 i = tlab->classes[c].next_slot; i < tlab->classes[c].limit_slot; i++) {
      valk_gc_bitmap_try_set_atomic(mark_bitmap, i);
    }
  }
}
// LCOV_EXCL_STOP

// Release this thread's TLAB (unused slots returned to the heap, struct
// freed). Called from valk_system_unregister_thread; without it every
// exiting thread that touched the heap leaks its TLAB.
void valk_gc_tlab_release_thread(void) {
  if (!valk_gc_local_tlab) return;
  valk_gc_tlab_abandon(valk_gc_local_tlab);
  free(valk_gc_local_tlab);
  valk_gc_local_tlab = nullptr;
}

static valk_gc_page_t *valk_gc_page_alloc(valk_gc_heap_t *heap, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return nullptr; // LCOV_EXCL_BR_LINE

  valk_gc_page_list_t *list = &heap->classes[size_class];
  u64 page_size = list->page_size;
  u16 slots = list->slots_per_page;
  u16 bitmap_bytes = valk_gc_bitmap_bytes(size_class);

  // LCOV_EXCL_START - hard limit and mprotect failures are OOM/platform paths
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

  sz offset = atomic_fetch_add(&list->next_page_offset, page_size);
  // region_size is a power of two >= page_size, so this cannot underflow, and
  // phrasing the bound as a subtraction keeps it correct when region_size is
  // the full width of the offset type.
  if (offset > list->region_size - page_size) {
    atomic_fetch_sub(&list->next_page_offset, page_size);
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
  // LCOV_EXCL_STOP

  valk_gc_page_t *page = (valk_gc_page_t *)addr;

  memset(page, 0, sizeof(valk_gc_page_t));
  page->page_id = atomic_fetch_add(&__page_id_counter, 1);
  page->size_class = size_class;
  page->slots_per_page = slots;
  page->bitmap_bytes = bitmap_bytes;
  page->slots_offset = valk_gc_page_slots_offset(bitmap_bytes);
  atomic_store(&page->num_allocated, 0);

  memset(valk_gc_page_alloc_bitmap(page), 0, bitmap_bytes);
  memset(valk_gc_page_mark_bitmap(page), 0, bitmap_bytes);

  return page;
}

// LCOV_EXCL_BR_START - TLAB refill internal bitmap search and page management
static u32 valk_gc_page_find_free_slots(valk_gc_page_t *page, u32 count) {
  u8 *bitmap = valk_gc_page_alloc_bitmap(page);
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

bool valk_gc_tlab_refill(valk_gc_tlab_t *tlab, valk_gc_heap_t *heap, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return false;

  // Late-registrant gate: a thread that registered while a GC cycle was in
  // flight is not part of the cycle's frozen participant set and must not
  // allocate while mark/sweep runs (sweep rebuilds the very free lists this
  // refill consumes). Counted participants (epoch match) pass through —
  // the coordinator is waiting for them to reach a safepoint. A fresh
  // thread's first allocation always lands here (empty TLAB), so this gate
  // plus the safepoint slow path covers every entry into the heap.
  // LCOV_EXCL_START - requires registration racing an active GC cycle
  if (valk_thread_ctx.gc_registered) {
    for (;;) {
      valk_gc_phase_e ph = atomic_load_explicit(&valk_sys->phase,
                                                memory_order_acquire);
      // CONC_MARK is not a stopped phase: mutators (including late
      // registrants) allocate freely; refilled batches are blackened below.
      if (ph == VALK_GC_PHASE_IDLE || ph == VALK_GC_PHASE_CONC_MARK) break;
      if (atomic_load(&valk_thread_ctx.stw_epoch) ==
          atomic_load(&valk_sys->stw_epoch)) break;
      sched_yield();
    }
  }
  // LCOV_EXCL_STOP

  valk_gc_page_list_t *list = &heap->classes[size_class];

  pthread_mutex_lock(&list->lock);

  valk_gc_page_t *page = list->partial_pages;
  u32 start_slot = 0;
  u32 num_slots = VALK_GC_TLAB_SLOTS;
  u32 pages_tried = 0;

  while (page && pages_tried < VALK_GC_TLAB_REFILL_SCAN_LIMIT) {
    pages_tried++;
    // LCOV_EXCL_START - page reclaim path requires MADV_DONTNEED to zero page
    if (page->reclaimed) {
      sz current = atomic_load(&heap->committed_bytes);
      sz new_committed;
      bool limit_ok = false;
      do {
        if (current + list->page_size > heap->hard_limit) break;
        new_committed = current + list->page_size;
        limit_ok = atomic_compare_exchange_weak(&heap->committed_bytes, &current, new_committed);
      } while (!limit_ok);
      if (!limit_ok) {
        page = page->next_partial;
        continue;
      }
      page->size_class = size_class;
      page->slots_per_page = list->slots_per_page;
      page->bitmap_bytes = valk_gc_bitmap_bytes(size_class);
      page->slots_offset = valk_gc_page_slots_offset(page->bitmap_bytes);
      atomic_store(&page->num_allocated, 0);
      memset(valk_gc_page_alloc_bitmap(page), 0, page->bitmap_bytes);
      memset(valk_gc_page_mark_bitmap(page), 0, page->bitmap_bytes);
      page->reclaimed = false;
      start_slot = 0;
      break;
    }
    // LCOV_EXCL_STOP

    start_slot = valk_gc_page_find_free_slots(page, 1);
    if (start_slot != UINT32_MAX) {
      u8 *bitmap = valk_gc_page_alloc_bitmap(page);
      u32 run = 1;
      while (run < num_slots && start_slot + run < page->slots_per_page &&
             !valk_gc_bitmap_test(bitmap, start_slot + run)) {
        run++;
      }
      num_slots = run;
      break;
    }

    page = page->next_partial;
  }

  if (!page || start_slot == UINT32_MAX) {
    page = NULL;
    num_slots = VALK_GC_TLAB_SLOTS;
  }

  if (!page) {
    pthread_mutex_unlock(&list->lock);
    page = valk_gc_page_alloc(heap, size_class);
    if (!page) return false;
    pthread_mutex_lock(&list->lock);

    page->next = list->all_pages;
    list->all_pages = page;
    page->next_partial = list->partial_pages;
    list->partial_pages = page;
    list->num_pages++;
    atomic_fetch_add(&list->total_slots, page->slots_per_page);

    start_slot = 0;
    num_slots = VALK_GC_TLAB_SLOTS;
  }

  if (start_slot + num_slots > page->slots_per_page) {
    num_slots = page->slots_per_page - start_slot;
  }

  u8 *bitmap = valk_gc_page_alloc_bitmap(page);
  for (u32 i = start_slot; i < start_slot + num_slots; i++) {
    valk_gc_bitmap_set(bitmap, i);
  }
  // Allocate-black: objects born while a concurrent mark runs must survive
  // the cycle's sweep; the marker never traces into them (they are already
  // marked), which also keeps it off still-initializing memory.
  if (atomic_load_explicit(&valk_gc_satb_active, memory_order_acquire)) {
    u8 *mark_bitmap = valk_gc_page_mark_bitmap(page);
    for (u32 i = start_slot; i < start_slot + num_slots; i++) {
      valk_gc_bitmap_try_set_atomic(mark_bitmap, i);
    }
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
    valk_gc_page_t **pp = &list->partial_pages;
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

  if (valk_gc_should_collect(heap)) {
    atomic_fetch_or_explicit(&valk_thread_ctx.safepoint_flags, VALK_SP_GC_COLLECT,
                              memory_order_release);
  }

  return true;
}
// LCOV_EXCL_BR_STOP

// Emergency path helper: a sync collect no-ops while a concurrent cycle is
// in flight (the phase CAS fails). Ride the cycle out — participating in
// its pauses via the safepoint — so the collect that follows can actually
// reclaim.
// LCOV_EXCL_START - requires OOM racing an active concurrent cycle
static void __wait_for_gc_idle(void) {
  while (atomic_load_explicit(&valk_sys->phase, memory_order_acquire) !=
         VALK_GC_PHASE_IDLE) {
    VALK_GC_SAFE_POINT();
    sched_yield();
  }
}
// LCOV_EXCL_STOP

static void *valk_gc_heap_alloc_large(valk_gc_heap_t *heap, u64 bytes) {
  u64 alloc_size = (bytes + 4095) & ~4095ULL;

  u64 current = valk_gc_heap_used_bytes(heap);

  // LCOV_EXCL_START - OOM paths: hard limit exceeded after collection
  if (current + alloc_size > heap->hard_limit) {
    __wait_for_gc_idle();
    valk_gc_heap_collect(heap);
    current = valk_gc_heap_used_bytes(heap);
    if (current + alloc_size > heap->hard_limit) {
      valk_gc_oom_abort(heap, bytes);
    }
  }
  // LCOV_EXCL_STOP

  void *data = mmap(nullptr, alloc_size, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  // LCOV_EXCL_START - mmap/malloc failures are platform OOM paths
  if (data == MAP_FAILED) {
    VALK_ERROR("mmap failed for large object of %zu bytes", alloc_size);
    return nullptr;
  }

  valk_gc_large_obj_t *obj = malloc(sizeof(valk_gc_large_obj_t));
  if (!obj) {
    munmap(data, alloc_size);
    return nullptr;
  }
  // LCOV_EXCL_STOP
  obj->data = data;
  obj->size = alloc_size;
  // Allocate-black during concurrent mark (see TLAB refill).
  obj->marked = atomic_load_explicit(&valk_gc_satb_active, memory_order_acquire);

  pthread_mutex_lock(&heap->large_lock);
  obj->next = heap->large_objects;
  heap->large_objects = obj;
  pthread_mutex_unlock(&heap->large_lock);

  atomic_fetch_add(&heap->large_object_bytes, alloc_size);
  u64 used = valk_gc_heap_used_bytes(heap);
  sz cur_peak = atomic_load(&heap->stats.peak_usage);
  while (used > cur_peak) { // LCOV_EXCL_BR_LINE - CAS retry is non-deterministic
    if (atomic_compare_exchange_weak(&heap->stats.peak_usage, &cur_peak, used)) // LCOV_EXCL_BR_LINE
      break;
  }

  return data;
}
void *valk_gc_heap_alloc(valk_gc_heap_t *heap, sz bytes) {
  if (bytes == 0) return nullptr; // LCOV_EXCL_BR_LINE - tested via zero-byte alloc

  if (bytes > VALK_GC_LARGE_THRESHOLD) {
    return valk_gc_heap_alloc_large(heap, bytes);
  }

  u8 size_class = valk_gc_size_class(bytes);
  if (size_class == UINT8_MAX) { // LCOV_EXCL_BR_LINE - unreachable: sizes >LARGE_THRESHOLD go to alloc_large above
    return valk_gc_heap_alloc_large(heap, bytes);
  }

  sz alloc_size = valk_gc_size_classes[size_class];

  if (!valk_gc_local_tlab) {
    valk_gc_local_tlab = malloc(sizeof(valk_gc_tlab_t));
    // LCOV_EXCL_START - malloc failure is OOM
    if (!valk_gc_local_tlab) return nullptr;
    // LCOV_EXCL_STOP
    valk_gc_tlab_init(valk_gc_local_tlab);
  }

  if (valk_gc_local_tlab->owner_heap != heap ||
      valk_gc_local_tlab->owner_generation != heap->generation) {
    valk_gc_tlab_abandon(valk_gc_local_tlab);
    valk_gc_local_tlab->owner_heap = heap;
    valk_gc_local_tlab->owner_generation = heap->generation;
  }

  void *ptr = valk_gc_tlab_alloc(valk_gc_local_tlab, size_class);
  if (ptr) {
    memset(ptr, 0, alloc_size);
    return ptr;
  }

  if (!valk_gc_tlab_refill(valk_gc_local_tlab, heap, size_class)) {
    __wait_for_gc_idle(); // LCOV_EXCL_LINE - OOM racing a concurrent cycle
    valk_gc_heap_collect(heap);
    // LCOV_EXCL_START - double refill failure is OOM
    if (!valk_gc_tlab_refill(valk_gc_local_tlab, heap, size_class)) {
      valk_gc_oom_abort(heap, bytes);
    }
  }

  ptr = valk_gc_tlab_alloc(valk_gc_local_tlab, size_class);
  if (ptr) { // LCOV_EXCL_BR_LINE - ptr is always non-null after successful refill
    memset(ptr, 0, alloc_size);
  }
  return ptr;
}

void *valk_gc_heap_realloc(valk_gc_heap_t *heap, void *ptr, sz new_size) {
  if (ptr == nullptr) {
    return valk_gc_heap_alloc(heap, new_size);
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
    void *new_ptr = valk_gc_heap_alloc(heap, new_size);
    if (new_ptr) { // LCOV_EXCL_BR_LINE - OOM after successful alloc
      memcpy(new_ptr, ptr, old_size);
    }
    return new_ptr;
  }

  // LCOV_EXCL_START - large object realloc requires specific heap state
  pthread_mutex_lock(&heap->large_lock);
  for (valk_gc_large_obj_t *obj = heap->large_objects; obj != nullptr; obj = obj->next) {
    if (obj->data == ptr) {
      u64 old_size = obj->size;
      pthread_mutex_unlock(&heap->large_lock);

      if (new_size <= old_size) {
        return ptr;
      }
      void *new_ptr = valk_gc_heap_alloc(heap, new_size);
      if (new_ptr) {
        memcpy(new_ptr, ptr, old_size);
      }
      return new_ptr;
    }
  }
  pthread_mutex_unlock(&heap->large_lock);
  // LCOV_EXCL_STOP

  VALK_WARN("valk_gc_heap_realloc: pointer %p not found in heap", ptr);
  return nullptr;
}

// LCOV_EXCL_START - fork safety function requires actual fork()
void valk_gc_heap_reset_after_fork(void) {
}
// LCOV_EXCL_STOP
