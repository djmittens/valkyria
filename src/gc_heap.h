#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <pthread.h>
#include "common.h"
#include "memory.h"

typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;

// ============================================================================
// Size Class System
// ============================================================================

#define VALK_GC_NUM_SIZE_CLASSES 9
#define VALK_GC_LARGE_THRESHOLD  4096

static const u16 valk_gc_size_classes[VALK_GC_NUM_SIZE_CLASSES] = {
  16, 32, 64, 128, 256, 512, 1024, 2048, 4096
};

static inline u8 valk_gc_size_class(sz bytes) {
  if (bytes <= 16)   return 0;
  if (bytes <= 32)   return 1;
  if (bytes <= 64)   return 2;
  if (bytes <= 128)  return 3;
  if (bytes <= 256)  return 4;
  if (bytes <= 512)  return 5;
  if (bytes <= 1024) return 6;
  if (bytes <= 2048) return 7;
  if (bytes <= 4096) return 8;
  return UINT8_MAX;
}

// ============================================================================
// Page Layout Constants
// ============================================================================

#define VALK_GC_PAGE_SIZE   (64 * 1024)
#define VALK_GC_PAGE_ALIGN  64
#define VALK_GC_TLAB_SLOTS  32
#define VALK_GC_SLOT_SIZE   80
#define VALK_GC_SLOTS_PER_PAGE  819
#define VALK_GC_BITMAP_SIZE  ((VALK_GC_SLOTS_PER_PAGE + 7) / 8)
#define VALK_GC_PAGE_HEADER_SIZE 64

static inline u16 valk_gc_slots_per_page(u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return 0;
  u16 slot_size = valk_gc_size_classes[size_class];
  sz usable = VALK_GC_PAGE_SIZE - VALK_GC_PAGE_HEADER_SIZE;
  u16 slots = (u16)((usable * 8) / (8 * slot_size + 2));
  return slots;
}

static inline u16 valk_gc_bitmap_bytes(u8 size_class) {
  u16 slots = valk_gc_slots_per_page(size_class);
  return (u16)((slots + 7) / 8);
}

static inline sz valk_gc_page_total_size(u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return 0;
  u16 slots = valk_gc_slots_per_page(size_class);
  u16 bitmap_bytes = valk_gc_bitmap_bytes(size_class);
  u16 slot_size = valk_gc_size_classes[size_class];
  sz total = VALK_GC_PAGE_HEADER_SIZE + 2 * bitmap_bytes + slots * slot_size;
  total = (total + (VALK_GC_PAGE_SIZE - 1)) & ~(VALK_GC_PAGE_SIZE - 1);
  return total;
}

// ============================================================================
// Bitmap Operations
// ============================================================================

static inline bool valk_gc_bitmap_test(const u8 *bitmap, u32 idx) {
  VALK_ASSERT(bitmap != nullptr, "bitmap must not be null");
  return (bitmap[idx / 8] & (1 << (idx % 8))) != 0;
}

static inline void valk_gc_bitmap_set(u8 *bitmap, u32 idx) {
  VALK_ASSERT(bitmap != nullptr, "bitmap must not be null");
  bitmap[idx / 8] |= (u8)(1 << (idx % 8));
}

static inline void valk_gc_bitmap_clear(u8 *bitmap, u32 idx) {
  VALK_ASSERT(bitmap != nullptr, "bitmap must not be null");
  bitmap[idx / 8] &= (u8)~(1 << (idx % 8));
}

static inline bool valk_gc_bitmap_try_set_atomic(u8 *bitmap, u32 idx) {
  u8 *byte = &bitmap[idx / 8];
  u8 bit = (u8)(1 << (idx % 8));
  u8 old = __atomic_fetch_or(byte, bit, __ATOMIC_ACQ_REL);
  return (old & bit) == 0;
}

static inline bool valk_gc_bitmap_test_atomic(const u8 *bitmap, u32 idx) {
  u8 byte = __atomic_load_n(&bitmap[idx / 8], __ATOMIC_ACQUIRE);
  return (byte & (1 << (idx % 8))) != 0;
}

// ============================================================================
// Page Structure
// ============================================================================

typedef struct valk_gc_page2 {
  struct valk_gc_page2 *next;
  struct valk_gc_page2 *next_partial;
  u32 page_id;
  u8 size_class;
  bool reclaimed;
  u8 _pad[2];
  _Atomic u32 num_allocated;
  u16 slots_per_page;
  u16 bitmap_bytes;
} valk_gc_page2_t;

static inline u8 *valk_gc_page2_alloc_bitmap(valk_gc_page2_t *page) {
  return (u8 *)(page + 1);
}

static inline u8 *valk_gc_page2_mark_bitmap(valk_gc_page2_t *page) {
  return (u8 *)(page + 1) + page->bitmap_bytes;
}

static inline u8 *valk_gc_page2_slots(valk_gc_page2_t *page) {
  u8 *after_bitmaps = (u8 *)(page + 1) + 2 * page->bitmap_bytes;
  uptr addr = (uptr)after_bitmaps;
  addr = (addr + 63) & ~63ULL;
  return (u8 *)addr;
}

static inline void *valk_gc_page2_slot_ptr(valk_gc_page2_t *page, u32 slot_idx) {
  u16 slot_size = valk_gc_size_classes[page->size_class];
  return valk_gc_page2_slots(page) + slot_idx * slot_size;
}

static inline bool valk_gc_page2_try_mark(valk_gc_page2_t *page, u32 slot) {
  return valk_gc_bitmap_try_set_atomic(valk_gc_page2_mark_bitmap(page), slot);
}

static inline bool valk_gc_page2_is_marked(valk_gc_page2_t *page, u32 slot) {
  return valk_gc_bitmap_test_atomic(valk_gc_page2_mark_bitmap(page), slot);
}

static inline bool valk_gc_page2_is_allocated(valk_gc_page2_t *page, u32 slot) {
  return valk_gc_bitmap_test(valk_gc_page2_alloc_bitmap(page), slot);
}

// ============================================================================
// Per-Class Page List
// ============================================================================

typedef struct valk_gc_page_list {
  pthread_mutex_t lock;
  valk_gc_page2_t *all_pages;
  valk_gc_page2_t *partial_pages;
  sz num_pages;
  _Atomic sz total_slots;
  _Atomic sz used_slots;
  _Atomic u32 next_page_offset;
  u16 slot_size;
  u16 slots_per_page;
  sz region_start;
  sz region_size;
  sz page_size;
} valk_gc_page_list_t;

// ============================================================================
// Large Object Tracking
// ============================================================================

typedef struct valk_gc_large_obj {
  struct valk_gc_large_obj *next;
  void *data;
  sz size;
  bool marked;
} valk_gc_large_obj_t;

// ============================================================================
// TLAB (Thread-Local Allocation Buffer)
// ============================================================================

typedef struct valk_gc_tlab2 {
  struct valk_gc_heap2 *owner_heap;
  u64 owner_generation;
  struct {
    valk_gc_page2_t *page;
    u32 next_slot;
    u32 limit_slot;
  } classes[VALK_GC_NUM_SIZE_CLASSES];
} valk_gc_tlab2_t;

// ============================================================================
// GC Heap Statistics
// ============================================================================

typedef struct {
  u64 overflow_allocations;
  u64 evacuations_from_scratch;
  sz evacuation_bytes;
  u64 evacuation_pointer_fixups;
  u64 emergency_collections;
  _Atomic sz peak_usage;
} valk_gc_heap_stats_t;

typedef struct {
  _Atomic u64 cycles_total;
  _Atomic u64 pause_us_total;
  _Atomic u64 pause_us_max;
  _Atomic sz reclaimed_bytes_total;
  _Atomic sz allocated_bytes_total;
  _Atomic u64 objects_marked;
  _Atomic u64 objects_swept;
  _Atomic sz last_heap_before_gc;
  _Atomic sz last_reclaimed;
  u64 last_cycle_start_us;
  _Atomic u64 survival_gen_0;
  _Atomic u64 survival_gen_1_5;
  _Atomic u64 survival_gen_6_20;
  _Atomic u64 survival_gen_21_plus;
  _Atomic u64 pause_0_1ms;
  _Atomic u64 pause_1_5ms;
  _Atomic u64 pause_5_10ms;
  _Atomic u64 pause_10_16ms;
  _Atomic u64 pause_16ms_plus;
} valk_gc_runtime_metrics_t;

// ============================================================================
// Virtual Memory Constants
// ============================================================================

#define VALK_GC_VIRTUAL_RESERVE_PER_CLASS  (4ULL * 1024 * 1024 * 1024)
#define VALK_GC_VIRTUAL_RESERVE     (VALK_GC_VIRTUAL_RESERVE_PER_CLASS * VALK_GC_NUM_SIZE_CLASSES)
#define VALK_GC_DEFAULT_HARD_LIMIT  (512 * 1024 * 1024)
#define VALK_GC_DEFAULT_SOFT_LIMIT  (384 * 1024 * 1024)
#define VALK_GC_INITIAL_COMMIT      (16 * 1024 * 1024)

// ============================================================================
// Main Heap Structure
// ============================================================================

struct valk_gc_heap2 {
  valk_mem_allocator_e type;
  _Atomic u64 generation;
  void *base;
  sz reserved;

  valk_gc_page_list_t classes[VALK_GC_NUM_SIZE_CLASSES];

  valk_gc_large_obj_t *large_objects;
  pthread_mutex_t large_lock;

  _Atomic sz committed_bytes;
  _Atomic sz used_bytes;
  _Atomic sz large_object_bytes;

  sz hard_limit;
  sz soft_limit;
  u8 gc_threshold_pct;
  u8 gc_target_pct;
  u32 min_gc_interval_ms;
  u64 last_gc_time_us;

  _Atomic bool gc_in_progress;
  bool in_emergency_gc;

  _Atomic u64 collections;
  _Atomic sz bytes_allocated_total;
  _Atomic sz bytes_reclaimed_total;

  valk_lenv_t *root_env;
  valk_gc_heap_stats_t stats;
  valk_gc_runtime_metrics_t runtime_metrics;
};

typedef struct valk_gc_heap2 valk_gc_heap2_t;
typedef valk_gc_heap2_t valk_gc_malloc_heap_t;

static inline sz valk_gc_heap2_used_bytes(valk_gc_heap2_t *heap) {
  sz total = atomic_load(&heap->large_object_bytes);
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    total += atomic_load(&heap->classes[c].used_slots) * valk_gc_size_classes[c];
  }
  return total;
}

// ============================================================================
// Pointer Location Result
// ============================================================================

typedef struct valk_gc_ptr_location {
  valk_gc_page2_t *page;
  u32 slot;
  u8 size_class;
  bool is_valid;
} valk_gc_ptr_location_t;

// ============================================================================
// GC Statistics Snapshot
// ============================================================================

typedef struct valk_gc_stats2 {
  sz used_bytes;
  sz committed_bytes;
  sz large_object_bytes;
  sz hard_limit;
  sz soft_limit;
  sz class_used_slots[VALK_GC_NUM_SIZE_CLASSES];
  sz class_total_slots[VALK_GC_NUM_SIZE_CLASSES];
  u64 collections;
  sz bytes_reclaimed_total;
} valk_gc_stats2_t;

// ============================================================================
// Heap API
// ============================================================================

valk_gc_heap2_t *valk_gc_heap2_create(sz hard_limit);
void valk_gc_heap2_destroy(valk_gc_heap2_t *heap);
void *valk_gc_heap2_alloc(valk_gc_heap2_t *heap, sz bytes);
void *valk_gc_heap2_realloc(valk_gc_heap2_t *heap, void *ptr, sz new_size);

void valk_gc_tlab2_init(valk_gc_tlab2_t *tlab);
void valk_gc_tlab2_reset(valk_gc_tlab2_t *tlab);
void valk_gc_tlab2_abandon(valk_gc_tlab2_t *tlab);
void valk_gc_tlab2_invalidate_heap(valk_gc_heap2_t *heap);

static inline void *valk_gc_tlab2_alloc(valk_gc_tlab2_t *tlab, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return nullptr;
  valk_gc_page2_t *page = tlab->classes[size_class].page;
  if (__builtin_expect(page != nullptr &&
                       !page->reclaimed &&
                       tlab->classes[size_class].next_slot <
                       tlab->classes[size_class].limit_slot, 1)) {
    u32 slot = tlab->classes[size_class].next_slot++;
    return valk_gc_page2_slot_ptr(page, slot);
  }
  return nullptr;
}

bool valk_gc_tlab2_refill(valk_gc_tlab2_t *tlab, valk_gc_heap2_t *heap, u8 size_class);

bool valk_gc_ptr_to_location(valk_gc_heap2_t *heap, void *ptr, valk_gc_ptr_location_t *out);
bool valk_gc_mark_large_object(valk_gc_heap2_t *heap, void *ptr);
sz valk_gc_sweep_page2(valk_gc_page2_t *page);
sz valk_gc_sweep_large_objects(valk_gc_heap2_t *heap);
void valk_gc_rebuild_partial_lists(valk_gc_heap2_t *heap);
sz valk_gc_reclaim_empty_pages(valk_gc_heap2_t *heap);

void valk_gc_heap2_get_stats(valk_gc_heap2_t *heap, valk_gc_stats2_t *out);
sz valk_gc_heap2_collect(valk_gc_heap2_t *heap);

__attribute__((noreturn))
void valk_gc_oom_abort(valk_gc_heap2_t *heap, sz requested);

u64 valk_gc_heap_next_generation(void);
void valk_gc_heap_reset_after_fork(void);

void valk_gc_register_heap(valk_gc_heap2_t *heap);
void valk_gc_unregister_heap(valk_gc_heap2_t *heap);
void valk_gc_page_list_init(valk_gc_page_list_t *list, u8 size_class);
