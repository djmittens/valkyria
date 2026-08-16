#include "gc_heap.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

// LCOV_EXCL_BR_START - pointer location search and validation
// Non-contiguous fallback only. The contiguous-reserve fast path is inlined
// in gc_heap.h because the marker calls it once per pointer.
bool valk_gc_ptr_to_location_slow(valk_gc_heap_t *heap, void *ptr, valk_gc_ptr_location_t *out) {
  // LCOV_EXCL_START - slow path for non-contiguous heap requires heap->base not set
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    u16 slot_size = valk_gc_size_classes[c];

    for (valk_gc_page_t *page = list->all_pages; page != nullptr; page = page->next) {
      u8 *slots_start = valk_gc_page_slots(page);
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

// LCOV_EXCL_BR_START - large object marking and sweep iteration
bool valk_gc_mark_large_object(valk_gc_heap_t *heap, void *ptr) {
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

sz valk_gc_sweep_page(valk_gc_page_t *page) {
  if (!page) return 0;

  sz freed = 0;
  u16 slots = page->slots_per_page;
  u16 slot_size = valk_gc_size_classes[page->size_class];

  u8 *alloc_bitmap = valk_gc_page_alloc_bitmap(page);
  u8 *mark_bitmap = valk_gc_page_mark_bitmap(page);
  u16 bm_bytes = page->bitmap_bytes;

  // Fast path: no finalizable object has ever been allocated in this page, so
  // sweeping is pure bitmap arithmetic. The slow path below loads v->flags for
  // every dead slot purely to test for LVAL_REF, which costs a cache miss per
  // garbage object and dominated collection time on allocation-heavy loads.
  if (!page->has_refs) {
    for (u16 byte_offset = 0; byte_offset < bm_bytes; byte_offset++) {
      u8 garbage_byte = (u8)(alloc_bitmap[byte_offset] & ~mark_bitmap[byte_offset]);
      if (garbage_byte) {
        // The trailing byte can cover slot indices past slots_per_page. The
        // slow path skips those via `slot < slots`; counting them here would
        // over-report and underflow num_allocated.
        u32 first_slot = (u32)byte_offset * 8;
        if (first_slot + 8 > slots) {
          u8 valid = (u8)((slots > first_slot) ? ((1u << (slots - first_slot)) - 1u) : 0u);
          garbage_byte = (u8)(garbage_byte & valid);
        }
        freed += (sz)__builtin_popcount((unsigned)garbage_byte);
        alloc_bitmap[byte_offset] = (u8)(alloc_bitmap[byte_offset] & mark_bitmap[byte_offset]);
      }
      mark_bitmap[byte_offset] = 0;
    }
    atomic_fetch_sub(&page->num_allocated, (u32)freed);
    return freed;
  }

  for (u16 byte_offset = 0; byte_offset < bm_bytes; byte_offset++) {
    u8 alloc_byte = alloc_bitmap[byte_offset];
    u8 mark_byte = mark_bitmap[byte_offset];

    u8 garbage_byte = alloc_byte & ~mark_byte;
    if (garbage_byte) {
      u8 new_alloc_byte = alloc_byte & mark_byte;
      alloc_bitmap[byte_offset] = new_alloc_byte;

      u8 temp = garbage_byte;
      while (temp) {
        u32 bit = (u32)__builtin_ctz(temp);
        u32 slot = (u32)byte_offset * 8 + bit;

        if (slot < slots) {
          freed++;
          void *ptr = valk_gc_page_slot_ptr(page, slot);

          // LCOV_EXCL_BR_START - LVAL_REF finalizer requires integration with ref creation API
          if (slot_size >= sizeof(valk_lval_t)) {
            valk_lval_t *v = (valk_lval_t *)ptr;
            u64 flags = v->flags;
            if ((valk_ltype_e)(flags & LVAL_TYPE_MASK) == LVAL_REF && v->ref.free != nullptr) {
                v->ref.free(v->ref.ptr);
            }
          }
          // LCOV_EXCL_BR_STOP
        }

        temp &= (u8)(temp - 1);
      }
    }

    mark_bitmap[byte_offset] = 0;
  }

  atomic_fetch_sub(&page->num_allocated, (u32)freed);

  return freed;
}

sz valk_gc_sweep_large_objects(valk_gc_heap_t *heap) {
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

// LCOV_EXCL_BR_START - page list rebuild and reclaim iteration
void valk_gc_rebuild_partial_lists(valk_gc_heap_t *heap) {
  if (!heap) return;

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];

    pthread_mutex_lock(&list->lock);

    list->partial_pages = nullptr;

    for (valk_gc_page_t *page = list->all_pages; page != nullptr; page = page->next) {
      u32 allocated = atomic_load(&page->num_allocated);

      if (allocated < page->slots_per_page || page->reclaimed) {
        page->next_partial = list->partial_pages;
        list->partial_pages = page;
      }
    }

    pthread_mutex_unlock(&list->lock);
  }
}

sz valk_gc_reclaim_empty_pages(valk_gc_heap_t *heap) {
  if (!heap) return 0;

  sz pages_reclaimed = 0;

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];

    pthread_mutex_lock(&list->lock);

    for (valk_gc_page_t *page = list->all_pages; page != nullptr; ) {
      valk_gc_page_t *next_page = page->next;
      u32 allocated = atomic_load(&page->num_allocated);

      if (allocated == 0 && !page->reclaimed) {
        u64 page_size = list->page_size;
        // Decommit the slot array only. The page header lives at the page base
        // and carries the all_pages/partial_pages links; MADV_DONTNEED zeroes
        // whatever it covers, so covering the header unlinks the page from the
        // partial list and the allocator can never hand it back out.
        static uptr os_page = 0;
        if (os_page == 0) os_page = (uptr)sysconf(_SC_PAGESIZE);
        uptr decommit_start =
            ((uptr)valk_gc_page_slots(page) + os_page - 1) & ~(os_page - 1);
        uptr decommit_end = (uptr)page + page_size;
        if (decommit_end > decommit_start) {
#ifdef __APPLE__
          madvise((void *)decommit_start, decommit_end - decommit_start, MADV_FREE);
#else
          madvise((void *)decommit_start, decommit_end - decommit_start, MADV_DONTNEED);
#endif
        }
        page->reclaimed = true;
        atomic_fetch_sub(&heap->committed_bytes, page_size);
        pages_reclaimed++;
      }
      page = next_page;
    }

    pthread_mutex_unlock(&list->lock);
  }

  return pages_reclaimed;
}
// LCOV_EXCL_BR_STOP
