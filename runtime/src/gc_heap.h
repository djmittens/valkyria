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

// log2 of a power of two. __builtin_clzll(0) is undefined behaviour, so zero
// is handled explicitly instead of trapping: callers derive shift amounts from
// sizes that are only non-zero by invariant, and a silent bad shift would
// corrupt every pointer-to-page mapping.
static inline u8 valk_gc_log2_pow2(sz v) {
  if (v == 0) return 0;
  return (u8)(63 - __builtin_clzll((unsigned long long)v));
}

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
#define VALK_GC_TLAB_REFILL_SCAN_LIMIT 4
#define VALK_GC_PAGE_HEADER_SIZE 64

static inline u16 valk_gc_slots_per_page(u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return 0;
  u16 slot_size = valk_gc_size_classes[size_class];
  sz usable = VALK_GC_PAGE_SIZE - VALK_GC_PAGE_HEADER_SIZE;
  u16 slots = (u16)((usable * 8) / (8 * slot_size + 2));
  while (slots > 0) {
    u16 bm = (u16)((slots + 7) / 8);
    sz after_bitmaps = VALK_GC_PAGE_HEADER_SIZE + 2 * bm;
    sz slots_start = (after_bitmaps + 63) & ~(sz)63;
    if (slots_start + (sz)slots * slot_size <= VALK_GC_PAGE_SIZE) break;
    slots--;
  }
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

typedef struct valk_gc_page {
  struct valk_gc_page *next;
  struct valk_gc_page *next_partial;
  u32 page_id;
  u8 size_class;
  bool reclaimed;
  // Set when an LVAL_REF (the only type with a finalizer) is allocated in this
  // page. Sweep can skip touching dead object memory entirely on pages where
  // this is false, which is nearly all of them.
  bool has_refs;
  u8 _pad[1];
  _Atomic u32 num_allocated;
  u16 slots_per_page;
  u16 bitmap_bytes;
  // Byte offset from the page base to the (64-byte aligned) slot array.
  // Cached because recovering it from bitmap_bytes plus realignment showed up
  // as ~9% of collection time when done per pointer.
  u16 slots_offset;
} valk_gc_page_t;

static inline u8 *valk_gc_page_alloc_bitmap(valk_gc_page_t *page) {
  return (u8 *)(page + 1);
}

static inline u8 *valk_gc_page_mark_bitmap(valk_gc_page_t *page) {
  return (u8 *)(page + 1) + page->bitmap_bytes;
}

// log2 of a size class's slot size: classes are 16 << c.
#define VALK_GC_SLOT_SHIFT(_c) ((u8)(4 + (_c)))

// Must match the original layout exactly: bitmaps start right after the page
// struct, and the slot array is 64-byte aligned after them.
static inline u16 valk_gc_page_slots_offset(u16 bitmap_bytes) {
  sz after_bitmaps = sizeof(valk_gc_page_t) + 2 * (sz)bitmap_bytes;
  return (u16)((after_bitmaps + 63) & ~(sz)63);
}

static inline u8 *valk_gc_page_slots(valk_gc_page_t *page) {
  return (u8 *)page + page->slots_offset;
}

static inline void *valk_gc_page_slot_ptr(valk_gc_page_t *page, u32 slot_idx) {
  return valk_gc_page_slots(page) +
         ((sz)slot_idx << VALK_GC_SLOT_SHIFT(page->size_class));
}

static inline bool valk_gc_page_try_mark(valk_gc_page_t *page, u32 slot) {
  return valk_gc_bitmap_try_set_atomic(valk_gc_page_mark_bitmap(page), slot);
}

// Solo variant: valid only when exactly one thread participates in the mark
// phase, so no other marker can touch this bitmap byte. Skips the locked RMW,
// which is otherwise paid once per live object.
static inline bool valk_gc_page_try_mark_solo(valk_gc_page_t *page, u32 slot) {
  u8 *byte = &valk_gc_page_mark_bitmap(page)[slot / 8];
  u8 bit = (u8)(1 << (slot % 8));
  if (*byte & bit) return false;
  *byte = (u8)(*byte | bit);
  return true;
}

static inline bool valk_gc_page_is_marked(valk_gc_page_t *page, u32 slot) {
  return valk_gc_bitmap_test_atomic(valk_gc_page_mark_bitmap(page), slot);
}

static inline bool valk_gc_page_is_allocated(valk_gc_page_t *page, u32 slot) {
  return valk_gc_bitmap_test(valk_gc_page_alloc_bitmap(page), slot);
}

// ============================================================================
// Per-Class Page List
// ============================================================================

typedef struct valk_gc_page_list {
  pthread_mutex_t lock;
  valk_gc_page_t *all_pages;
  valk_gc_page_t *partial_pages;
  sz num_pages;
  _Atomic sz total_slots;
  _Atomic sz used_slots;
  _Atomic sz next_page_offset;
  u16 slot_size;
  u16 slots_per_page;
  sz region_start;
  sz region_size;
  sz page_size;
  // log2(page_size). Page totals are rounded up to VALK_GC_PAGE_SIZE, so this
  // is always exact, and it turns a per-pointer division into a shift.
  u8 page_shift;
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

typedef struct valk_gc_tlab {
  struct valk_gc_heap *owner_heap;
  u64 owner_generation;
  struct {
    valk_gc_page_t *page;
    u32 next_slot;
    u32 limit_slot;
    // First slot of the current batch. Blackening at the CONC_START pause
    // must cover [start_slot, limit_slot), not just the unconsumed
    // remainder: objects allocated between satb-on and this thread's
    // pause arrival come from the consumed part of a pre-satb batch and
    // were born WHITE - if their referencing structure churns around the
    // snapshot scan they are invisible to the cycle and swept while live.
    u32 start_slot;
  } classes[VALK_GC_NUM_SIZE_CLASSES];
} valk_gc_tlab_t;

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
  _Atomic u64 pause_ns_total;
  _Atomic u64 pause_ns_max;
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
#define VALK_GC_DEFAULT_HARD_LIMIT  (1024ULL * 1024 * 1024)
#define VALK_GC_DEFAULT_SOFT_LIMIT  (768ULL * 1024 * 1024)
#define VALK_GC_INITIAL_COMMIT      (16 * 1024 * 1024)

// Growth-based collection trigger: collect once the heap reaches
// GROWTH_FACTOR x the live set surviving the last collection (with a floor
// so tiny live sets don't thrash). Keeps pause times and RSS proportional
// to LIVE data instead of the configured limit — with a 4GB hard limit and
// a 40MB live set, the old pct-of-limit policy accumulated 3.2GB of garbage
// between collections and paused 400ms; this collects at ~128MB for ~15ms.
#define VALK_GC_GROWTH_FACTOR       3
#define VALK_GC_MIN_COLLECT_BYTES   (64ULL * 1024 * 1024)

// ============================================================================
// Main Heap Structure
// ============================================================================

struct valk_gc_heap {
  valk_mem_allocator_e type;
  _Atomic u64 generation;
  void *base;
  sz reserved;
  // log2 of the per-size-class region stride. Regions are laid out uniformly
  // at c * (1 << region_shift), so a pointer's size class is a shift rather
  // than a linear search over all 9 regions - and that search sat on the
  // hottest path in the marker.
  u8 region_shift;

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
  u64 last_gc_time_us;
  sz live_after_gc;

  _Atomic bool gc_in_progress;

  _Atomic u64 collections;
  _Atomic sz bytes_allocated_total;
  _Atomic sz bytes_reclaimed_total;

  valk_lenv_t *root_env;
  valk_gc_heap_stats_t stats;
  valk_gc_runtime_metrics_t runtime_metrics;
};

typedef struct valk_gc_heap valk_gc_heap_t;

static inline sz valk_gc_heap_used_bytes(valk_gc_heap_t *heap) {
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
  valk_gc_page_t *page;
  u32 slot;
  u8 size_class;
  bool is_valid;
} valk_gc_ptr_location_t;

// Fast path for the contiguous-reserve heap, inlined because the marker calls
// it once per pointer and an out-of-line call was ~15% of collection time.
// Falls back to the out-of-line version for the non-contiguous case.
bool valk_gc_ptr_to_location_slow(valk_gc_heap_t *heap, void *ptr,
                                  valk_gc_ptr_location_t *out);

static inline bool valk_gc_ptr_to_location_fast(valk_gc_heap_t *heap, void *ptr,
                                                valk_gc_ptr_location_t *out) {
  u8 *base = (u8 *)heap->base;
  u8 *addr = (u8 *)ptr;
  if (addr < base || addr >= base + heap->reserved) return false;

  sz offset = (sz)(addr - base);
  u8 c = (u8)(offset >> heap->region_shift);
  if (c >= VALK_GC_NUM_SIZE_CLASSES) return false;

  valk_gc_page_list_t *list = &heap->classes[c];
  sz offset_in_region = offset - list->region_start;

  // Relaxed: every caller runs inside the stop-the-world window, so no
  // allocation can be advancing this concurrently.
  if (offset_in_region >=
      atomic_load_explicit(&list->next_page_offset, memory_order_relaxed)) {
    return false;
  }

  valk_gc_page_t *page =
      (valk_gc_page_t *)(base + list->region_start +
                         ((offset_in_region >> list->page_shift)
                          << list->page_shift));

  u8 *slots_start = valk_gc_page_slots(page);
  if (addr < slots_start) return false;

  u32 slot = (u32)((sz)(addr - slots_start) >> VALK_GC_SLOT_SHIFT(c));
  if (slot >= page->slots_per_page) return false;

  out->page = page;
  out->slot = slot;
  out->size_class = c;
  out->is_valid = true;
  return true;
}

// Flag the owning page as containing a finalizable object. Called only when an
// LVAL_REF is created, which is rare.
static inline void valk_gc_mark_page_has_refs_in(valk_gc_heap_t *heap,
                                                 void *ptr) {
  if (!heap || !ptr || !heap->base || heap->reserved == 0) return;
  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location_fast(heap, ptr, &loc)) {
    loc.page->has_refs = true;
  }
}

static inline bool valk_gc_ptr_to_location(valk_gc_heap_t *heap, void *ptr,
                                           valk_gc_ptr_location_t *out) {
  if (!heap || !ptr || !out) {
    if (out) out->is_valid = false;
    return false;
  }
  out->is_valid = false;
  if (heap->base && heap->reserved > 0) {
    return valk_gc_ptr_to_location_fast(heap, ptr, out);
  }
  return valk_gc_ptr_to_location_slow(heap, ptr, out);
}

// ============================================================================
// GC Statistics Snapshot
// ============================================================================

typedef struct valk_gc_stats {
  sz used_bytes;
  sz committed_bytes;
  sz large_object_bytes;
  sz hard_limit;
  sz soft_limit;
  sz class_used_slots[VALK_GC_NUM_SIZE_CLASSES];
  sz class_total_slots[VALK_GC_NUM_SIZE_CLASSES];
  u64 collections;
  sz bytes_reclaimed_total;
} valk_gc_stats_t;

// ============================================================================
// Heap API
// ============================================================================

valk_gc_heap_t *valk_gc_heap_create(sz hard_limit);
void valk_gc_heap_destroy(valk_gc_heap_t *heap);
void *valk_gc_heap_alloc(valk_gc_heap_t *heap, sz bytes);
void *valk_gc_heap_realloc(valk_gc_heap_t *heap, void *ptr, sz new_size);

void valk_gc_tlab_init(valk_gc_tlab_t *tlab);
void valk_gc_tlab_reset(valk_gc_tlab_t *tlab);
void valk_gc_tlab_abandon(valk_gc_tlab_t *tlab);
void valk_gc_tlab_release_thread(void);
void valk_gc_tlab_invalidate_heap(valk_gc_heap_t *heap);

static inline void *valk_gc_tlab_alloc(valk_gc_tlab_t *tlab, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return nullptr;
  valk_gc_page_t *page = tlab->classes[size_class].page;
  if (__builtin_expect(page != nullptr &&
                       !page->reclaimed &&
                       tlab->classes[size_class].next_slot <
                       tlab->classes[size_class].limit_slot, 1)) {
    u32 slot = tlab->classes[size_class].next_slot++;
    return valk_gc_page_slot_ptr(page, slot);
  }
  return nullptr;
}

bool valk_gc_tlab_refill(valk_gc_tlab_t *tlab, valk_gc_heap_t *heap, u8 size_class);


bool valk_gc_mark_large_object(valk_gc_heap_t *heap, void *ptr);
sz valk_gc_sweep_page(valk_gc_page_t *page);
sz valk_gc_sweep_large_objects(valk_gc_heap_t *heap);
void valk_gc_rebuild_partial_lists(valk_gc_heap_t *heap);
sz valk_gc_reclaim_empty_pages(valk_gc_heap_t *heap);

void valk_gc_heap_get_stats(valk_gc_heap_t *heap, valk_gc_stats_t *out);
sz valk_gc_heap_collect(valk_gc_heap_t *heap);

__attribute__((noreturn))
void valk_gc_oom_abort(valk_gc_heap_t *heap, sz requested);

u64 valk_gc_heap_next_generation(void);
void valk_gc_heap_reset_after_fork(void);

void valk_gc_page_list_init(valk_gc_page_list_t *list, u8 size_class);
