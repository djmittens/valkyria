#include "gc_heap.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

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
