#include "gc_heap.h"
#include "gc.h"
#include "memory.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

// LCOV_EXCL_BR_START - heap creation calloc/mmap failures
valk_gc_heap2_t *valk_gc_heap2_create(sz hard_limit) {
  valk_gc_heap2_t *heap = calloc(1, sizeof(valk_gc_heap2_t));
  if (!heap) {
    VALK_ERROR("Failed to allocate heap structure");
    return nullptr;
  }

  heap->type = VALK_ALLOC_GC_HEAP;
  heap->generation = valk_gc_heap_next_generation();
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
