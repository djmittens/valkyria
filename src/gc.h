#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <pthread.h>
#include "common.h"
#include "memory.h"
#include "types.h"

// Forward declarations
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;

// ============================================================================
// Runtime Initialization API
// ============================================================================

typedef struct {
  sz gc_heap_size;    // GC heap hard limit (default: 1GB)
} valk_runtime_config_t;

static inline valk_runtime_config_t valk_runtime_config_default(void) {
  return (valk_runtime_config_t){
    .gc_heap_size = 4ULL * 1024 * 1024 * 1024,  // 4GB default
  };
}

typedef void (*valk_thread_onboard_fn)(void);

int valk_runtime_init(valk_runtime_config_t *config);
void valk_runtime_shutdown(void);
void valk_runtime_thread_onboard(void);
valk_thread_onboard_fn valk_runtime_get_onboard_fn(void);
struct valk_gc_heap2 *valk_runtime_get_heap(void);
bool valk_runtime_is_initialized(void);

// GC allocation header - prepended to every GC-managed allocation
// This allows arbitrary-sized allocations while maintaining tracking metadata
typedef struct valk_gc_header_t {
  void* origin_allocator;              // Which heap allocated this
  struct valk_gc_header_t* gc_next;    // Linked list for GC tracking
  sz size;                         // User-requested allocation size
  // User data follows immediately after this header
} valk_gc_header_t;

// Forward declare slab allocator
struct valk_slab_t;

// Forward declare new size-class heap (defined below)
typedef struct valk_gc_heap2 valk_gc_heap2_t;

// GC heap statistics for telemetry
typedef struct {
  u64 overflow_allocations;      // Allocations received from scratch overflow
  u64 evacuations_from_scratch;  // Values received from scratch evacuation
  sz evacuation_bytes;          // Bytes received from scratch evacuation
  u64 evacuation_pointer_fixups; // Pointer updates during evacuation
  u64 emergency_collections;     // Emergency GCs triggered at hard limit
  sz peak_usage;                // Maximum allocated_bytes ever reached
} valk_gc_heap_stats_t;

// GC runtime metrics for observability (live counters, not telemetry snapshots)
typedef struct {
  _Atomic u64 cycles_total;           // Total GC collections
  _Atomic u64 pause_us_total;         // Cumulative pause time (microseconds)
  _Atomic u64 pause_us_max;           // Worst-case pause time
  _Atomic sz reclaimed_bytes_total;  // Total bytes reclaimed across all cycles
  _Atomic sz allocated_bytes_total;  // Total bytes ever allocated (for rate calc)
  _Atomic u64 objects_marked;         // Objects marked in last cycle
  _Atomic u64 objects_swept;          // Objects swept in last cycle
  _Atomic sz last_heap_before_gc;    // Heap size before last GC (for efficiency)
  _Atomic sz last_reclaimed;         // Bytes reclaimed in last GC cycle
  u64 last_cycle_start_us;            // Timing for current cycle (internal)

  // Object survival histogram - tracks how long objects live
  // Used to detect potential memory leaks (objects surviving many cycles)
  // Buckets: gen_0 (died in 1st GC), gen_1_5, gen_6_20, gen_21_plus (long-lived)
  _Atomic u64 survival_gen_0;         // Died in first GC (short-lived, expected)
  _Atomic u64 survival_gen_1_5;       // Survived 1-5 cycles (normal)
  _Atomic u64 survival_gen_6_20;      // Survived 6-20 cycles (medium-lived)
  _Atomic u64 survival_gen_21_plus;   // Survived 21+ cycles (potential leak)

  // Frame-time pause histogram - tracks GC pause impact on frame budgets
  // Used by game profile to show distribution of pauses relative to frame time
  // Buckets based on typical frame budgets: 60fps=16.6ms, 30fps=33.3ms
  _Atomic u64 pause_0_1ms;            // No impact (0-1ms)
  _Atomic u64 pause_1_5ms;            // Minor impact (1-5ms)
  _Atomic u64 pause_5_10ms;           // Noticeable (5-10ms)
  _Atomic u64 pause_10_16ms;          // Frame drop risk at 60fps (10-16ms)
  _Atomic u64 pause_16ms_plus;        // Frame drop certain at 60fps (16ms+)
} valk_gc_runtime_metrics_t;

// Legacy type alias - valk_gc_malloc_heap_t is now valk_gc_heap2_t
// All legacy API functions are implemented as wrappers around heap2
typedef valk_gc_heap2_t valk_gc_malloc_heap_t;

// Initialize GC malloc heap with hard limit (default 250MB if 0)
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(sz hard_limit);

// Set hard limit for GC heap (must be >= current allocated_bytes)
void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, sz limit);

// Allocate from GC malloc heap (uses malloc, triggers GC if needed)
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, sz bytes);

// Set root environment for marking
void valk_gc_malloc_set_root(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env);

// Perform mark & sweep collection
// If additional_root is non-nullptr, it will be marked in addition to root_env
sz valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap, valk_lval_t* additional_root);

// Check if GC should run (considers both slab and malloc usage as percentage)
bool valk_gc_malloc_should_collect(valk_gc_malloc_heap_t* heap);

// Get current heap usage as percentage (0-100)
// Combined: (slab_used + malloc_used) / (slab_capacity + hard_limit) * 100
u8 valk_gc_heap_usage_pct(valk_gc_malloc_heap_t* heap);

// Configure GC thresholds (call after init, or use defaults)
// threshold_pct: trigger GC when usage exceeds this (default 75)
// target_pct: aim to be below this after GC (default 50, informational)
// min_interval_ms: minimum time between GC cycles (default 1000)
void valk_gc_set_thresholds(valk_gc_malloc_heap_t* heap,
                            u8 threshold_pct,
                            u8 target_pct,
                            u32 min_interval_ms);

// Print GC statistics
void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap);

// Print combined memory statistics (scratch arena + GC heap)
void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out);

// Free all GC heap allocations and the heap itself (for clean shutdown)
void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap);

// Get GC runtime metrics for export (thread-safe reads)
void valk_gc_get_runtime_metrics(valk_gc_malloc_heap_t* heap,
                                  u64* cycles, u64* pause_us_total,
                                  u64* pause_us_max, sz* reclaimed,
                                  sz* heap_used, sz* heap_total);

// Get cumulative bytes allocated (for allocation rate calculation)
sz valk_gc_get_allocated_bytes_total(valk_gc_malloc_heap_t* heap);

// Get GC efficiency from last cycle (reclaimed / heap_before * 100, 0-100)
// Low efficiency suggests long-lived objects accumulating (potential leak)
u8 valk_gc_get_last_efficiency(valk_gc_malloc_heap_t* heap);

// Get object survival histogram (thread-safe reads)
// Buckets: gen_0 (died in 1st GC), gen_1_5, gen_6_20, gen_21_plus
void valk_gc_get_survival_histogram(valk_gc_malloc_heap_t* heap,
                                     u64* gen_0, u64* gen_1_5,
                                     u64* gen_6_20, u64* gen_21_plus);

// Get frame-time pause histogram (thread-safe reads)
// Buckets: 0-1ms, 1-5ms, 5-10ms, 10-16ms, 16ms+
// Used by game profile to show GC pause distribution relative to frame budgets
void valk_gc_get_pause_histogram(valk_gc_malloc_heap_t* heap,
                                  u64* pause_0_1ms, u64* pause_1_5ms,
                                  u64* pause_5_10ms, u64* pause_10_16ms,
                                  u64* pause_16ms_plus);

typedef struct {
  sz lval_slab_used;
  sz lval_slab_total;
  sz lval_slab_peak;
  sz lenv_slab_used;
  sz lenv_slab_total;
  sz lenv_slab_peak;
  sz malloc_allocated;
  sz malloc_limit;
  sz malloc_peak;
  u64 free_list_count;
  sz free_list_bytes;
  double lval_fragmentation;
  double lenv_fragmentation;
} valk_fragmentation_t;

void valk_gc_get_fragmentation(valk_gc_malloc_heap_t* heap, valk_fragmentation_t* out);

// ============================================================================
// Memory Snapshot for REPL Eval Tracking
// ============================================================================

typedef struct {
  sz heap_used_bytes;
  sz scratch_used_bytes;
  u64 lval_count;
  u64 lenv_count;
} valk_repl_mem_snapshot_t;

void valk_repl_mem_take_snapshot(valk_gc_malloc_heap_t* heap, valk_mem_arena_t* scratch,
                                 valk_repl_mem_snapshot_t* out);

void valk_repl_mem_snapshot_delta(valk_repl_mem_snapshot_t* before, valk_repl_mem_snapshot_t* after,
                                  i64* heap_delta, i64* scratch_delta,
                                  i64* lval_delta, i64* lenv_delta);

// REPL eval memory delta - exposes last eval's memory changes for dashboard
typedef struct {
  i64 heap_delta;
  i64 scratch_delta;
  i64 lval_delta;
  i64 lenv_delta;
  u64 eval_count;
} valk_repl_eval_delta_t;

// Get the last REPL eval memory delta (for SSE diagnostics)
// Returns false if no eval has occurred yet (running as server, not REPL)
bool valk_repl_get_last_eval_delta(valk_repl_eval_delta_t* out);

// Update REPL eval deltas (called from repl.c after each eval)
void valk_repl_set_eval_delta(i64 heap, i64 scratch, i64 lval, i64 lenv);

// Explicitly free a single GC heap object (for cleanup when switching allocators)
void valk_gc_free_object(void* heap, void* ptr);

// Arena-based GC (informational only, for backward compatibility)
sz valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena);
bool valk_gc_should_collect_arena(valk_mem_arena_t* arena);

// ============================================================================
// Forwarding Pointer Helpers (for scratch evacuation)
// ============================================================================

// Set forwarding pointer: mark src as forwarded, point to dst
void valk_lval_set_forward(valk_lval_t* src, valk_lval_t* dst);

// Check if value is a forwarding pointer
bool valk_lval_is_forwarded(valk_lval_t* v);

// Follow forwarding pointer chain to find final destination
valk_lval_t* valk_lval_follow_forward(valk_lval_t* v);

// ============================================================================
// Evacuation Context (for checkpoint-based memory management)
// ============================================================================

// Context for evacuation from scratch arena to GC heap
typedef struct {
  valk_mem_arena_t* scratch;      // Source arena
  valk_gc_malloc_heap_t* heap;    // Destination heap
  valk_lval_t** worklist;         // Stack of values to process children
  sz worklist_count;          // Current worklist size
  sz worklist_capacity;       // Allocated capacity
  valk_lval_t** evacuated;        // List of evacuated values (for pointer fixing)
  sz evacuated_count;         // Number of evacuated values
  sz evacuated_capacity;      // Allocated capacity for evacuated list
  u64 values_copied;           // Stats for this evacuation
  sz bytes_copied;            // Stats for this evacuation
  u64 pointers_fixed;          // Stats for this evacuation
} valk_evacuation_ctx_t;

// ============================================================================
// Checkpoint API
// ============================================================================

// Default threshold for triggering checkpoint (75% of scratch capacity)
#define VALK_CHECKPOINT_THRESHOLD_DEFAULT 0.75f

// Check if checkpoint should be triggered based on scratch usage
bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold);

// Perform checkpoint: evacuate reachable values from scratch to heap, then reset
void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap,
                     valk_lenv_t* root_env);

// Evacuate a single value and all its transitive dependencies to heap
// Use this for values that need to survive across checkpoints immediately
// (e.g., callbacks that may fire before next checkpoint)
valk_lval_t* valk_evacuate_to_heap(valk_lval_t* v);

// Add a value to the GC heap's object list (for evacuated values)
void valk_gc_add_to_objects(valk_gc_malloc_heap_t* heap, valk_lval_t* v);

// ============================================================================
// External GC marking functions
// ============================================================================

// Mark an lval and all its children
void valk_gc_mark_lval_external(valk_lval_t* v);

// Mark an environment and all its contents
void valk_gc_mark_env_external(valk_lenv_t* env);

// ============================================================================
// Parallel GC Infrastructure (Phase 0)
// ============================================================================

#define VALK_GC_MAX_THREADS 64

// GC phase states
typedef enum {
  VALK_GC_PHASE_IDLE = 0,
  VALK_GC_PHASE_STW_REQUESTED,
  VALK_GC_PHASE_MARKING,
  VALK_GC_PHASE_SWEEPING,
} valk_gc_phase_e;

// Atomic mark bit operations (thread-safe for parallel marking)
// Uses compare-and-swap to ensure exactly one thread marks each object
// Implemented in gc.c (need full type definition)
bool valk_gc_try_mark(valk_lval_t* obj);
bool valk_gc_is_marked(valk_lval_t* obj);
void valk_gc_clear_mark(valk_lval_t* obj);

// Work-stealing mark queue (Chase-Lev deque)
#define VALK_GC_MARK_QUEUE_SIZE 8192

typedef struct valk_gc_mark_queue {
  _Atomic(valk_lval_t*) items[VALK_GC_MARK_QUEUE_SIZE];
  _Atomic sz top;     // Thieves steal from here (FIFO end)
  _Atomic sz bottom;  // Owner pushes/pops here (LIFO end)
} valk_gc_mark_queue_t;

// Initialize mark queue
void valk_gc_mark_queue_init(valk_gc_mark_queue_t* q);

// Owner operations (local thread only, lock-free)
bool valk_gc_mark_queue_push(valk_gc_mark_queue_t* q, valk_lval_t* val);
valk_lval_t* valk_gc_mark_queue_pop(valk_gc_mark_queue_t* q);

// Thief operation (other threads, lock-free)
valk_lval_t* valk_gc_mark_queue_steal(valk_gc_mark_queue_t* q);

// Check if queue is empty (approximate, for termination detection)
bool valk_gc_mark_queue_empty(valk_gc_mark_queue_t* q);

// Per-thread GC info stored in coordinator
typedef struct valk_gc_thread_info {
  void* ctx;              // valk_thread_context_t* (forward ref)
  pthread_t thread_id;
  bool active;
  valk_gc_mark_queue_t mark_queue;
} valk_gc_thread_info_t;

// Portable barrier implementation (pthread_barrier_t not available on macOS)
typedef struct valk_barrier {
  pthread_mutex_t mutex;
  pthread_cond_t cond;
  sz count;
  sz waiting;
  sz phase;
} valk_barrier_t;

void valk_barrier_init(valk_barrier_t* b, sz count);
void valk_barrier_destroy(valk_barrier_t* b);
void valk_barrier_wait(valk_barrier_t* b);

// Global GC coordinator for multi-threaded GC
typedef struct valk_gc_coordinator {
  _Atomic valk_gc_phase_e phase;
  _Atomic u64 threads_registered;
  _Atomic u64 threads_paused;
  
  pthread_mutex_t lock;
  pthread_cond_t all_paused;   // Signaled when all threads at safe point
  pthread_cond_t gc_done;      // Signaled when GC complete
  valk_barrier_t barrier;      // Portable barrier for sync between GC phases
  bool barrier_initialized;
  
  valk_gc_thread_info_t threads[VALK_GC_MAX_THREADS];
  
  // Statistics
  _Atomic u64 parallel_cycles;
  _Atomic u64 parallel_pause_us_total;
} valk_gc_coordinator_t;

// Global coordinator instance
extern valk_gc_coordinator_t valk_gc_coord;

// Initialize parallel GC coordinator (call once at startup)
void valk_gc_coordinator_init(void);

// Thread registration for parallel GC
void valk_gc_thread_register(void);
void valk_gc_thread_unregister(void);

// Safe point - threads check for pending GC
#define VALK_GC_SAFE_POINT() \
  do { \
    if (__builtin_expect(atomic_load_explicit(&valk_gc_coord.phase, \
                         memory_order_acquire) != VALK_GC_PHASE_IDLE, 0)) { \
      valk_gc_safe_point_slow(); \
    } \
  } while (0)

// Safe point slow path (called when GC is pending)
void valk_gc_safe_point_slow(void);

// Global roots registry (for C-side persistent references)
#define VALK_GC_MAX_GLOBAL_ROOTS 1024

typedef struct valk_gc_global_roots {
  pthread_mutex_t lock;
  valk_lval_t** roots[VALK_GC_MAX_GLOBAL_ROOTS];
  u64 count;
} valk_gc_global_roots_t;

extern valk_gc_global_roots_t valk_gc_global_roots;

// Register/unregister global roots
void valk_gc_add_global_root(valk_lval_t** root);
void valk_gc_remove_global_root(valk_lval_t** root);

// ============================================================================
// Phase 1: Page-based Allocator with Mark Bitmaps (Parallel GC)
// ============================================================================

#define VALK_GC_PAGE_SIZE   (64 * 1024)   // 64 KB per page
#define VALK_GC_PAGE_ALIGN  64            // Cache line alignment
#define VALK_GC_TLAB_SLOTS  32            // Slots per TLAB refill

// Object slot size - must fit both valk_lval_t (72 bytes) and valk_lenv_t (80 bytes)
#define VALK_GC_SLOT_SIZE   80

// Number of slots per page: (64KB - header) / 80 = ~819
#define VALK_GC_SLOTS_PER_PAGE  819

// Bitmap size in bytes (1 bit per slot, rounded up)
#define VALK_GC_BITMAP_SIZE  ((VALK_GC_SLOTS_PER_PAGE + 7) / 8)

// ============================================================================
// Size Class System (Phase 1 - New Multi-Class Allocator)
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

// Page header size (conservative, includes alignment padding)
// Actual struct is smaller but we round up to cache line
#define VALK_GC_PAGE_HEADER_SIZE 64

// Calculate slots per page accounting for header and inline bitmaps
// Layout: [header (64B)][alloc_bitmap][mark_bitmap][slots...]
// Each slot needs slot_size bytes + 2 bits for bitmaps
static inline u16 valk_gc_slots_per_page(u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return 0;
  u16 slot_size = valk_gc_size_classes[size_class];
  
  // Usable space after header
  sz usable = VALK_GC_PAGE_SIZE - VALK_GC_PAGE_HEADER_SIZE;
  
  // Each slot costs: slot_size bytes + 2 bits (alloc + mark)
  // Solve: slots * slot_size + ceil(slots/8) * 2 <= usable
  // Approximate: slots * (slot_size + 0.25) <= usable
  // slots <= usable * 8 / (8 * slot_size + 2)
  u16 slots = (u16)((usable * 8) / (8 * slot_size + 2));
  
  return slots;
}

static inline u16 valk_gc_bitmap_bytes(u8 size_class) {
  u16 slots = valk_gc_slots_per_page(size_class);
  return (u16)((slots + 7) / 8);
}

// Calculate total page size including header, bitmaps, and slots
static inline sz valk_gc_page_total_size(u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return 0;
  u16 slots = valk_gc_slots_per_page(size_class);
  u16 bitmap_bytes = valk_gc_bitmap_bytes(size_class);
  u16 slot_size = valk_gc_size_classes[size_class];
  
  sz total = VALK_GC_PAGE_HEADER_SIZE + 2 * bitmap_bytes + slots * slot_size;
  total = (total + (VALK_GC_PAGE_SIZE - 1)) & ~(VALK_GC_PAGE_SIZE - 1);
  return total;
}

// Expected slots per class (for documentation/verification):
// Class 0 (16B):  usable=65472, slots = 65472*8/(8*16+2) = 4028
// Class 1 (32B):  usable=65472, slots = 65472*8/(8*32+2) = 2012  
// Class 2 (64B):  usable=65472, slots = 65472*8/(8*64+2) = 1005
// Class 3 (128B): usable=65472, slots = 65472*8/(8*128+2) = 510
// Class 4 (256B): usable=65472, slots = 65472*8/(8*256+2) = 255
// Class 5 (512B): usable=65472, slots = 65472*8/(8*512+2) = 127
// Class 6 (1KB):  usable=65472, slots = 65472*8/(8*1024+2) = 63
// Class 7 (2KB):  usable=65472, slots = 65472*8/(8*2048+2) = 31
// Class 8 (4KB):  usable=65472, slots = 65472*8/(8*4096+2) = 15

#define VALK_GC_VIRTUAL_RESERVE_PER_CLASS  (4ULL * 1024 * 1024 * 1024)
#define VALK_GC_VIRTUAL_RESERVE     (VALK_GC_VIRTUAL_RESERVE_PER_CLASS * VALK_GC_NUM_SIZE_CLASSES)
#define VALK_GC_DEFAULT_HARD_LIMIT  (512 * 1024 * 1024)
#define VALK_GC_DEFAULT_SOFT_LIMIT  (384 * 1024 * 1024)
#define VALK_GC_INITIAL_COMMIT      (16 * 1024 * 1024)

// Basic bitmap operations (non-atomic, for allocation bitmaps)
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

// ============================================================================
// New Multi-Class Page Structure (Phase 1)
// ============================================================================

// Page structure for size-class allocator
// Layout in memory: [valk_gc_page2_t header][alloc_bitmap][mark_bitmap][slots...]
// Bitmaps immediately follow the header, slots follow bitmaps
typedef struct valk_gc_page2 {
  struct valk_gc_page2 *next;           // Next page in all_pages list
  struct valk_gc_page2 *next_partial;   // Next page in partial_pages list
  u32 page_id;                     // For debugging
  u8 size_class;                   // Which size class (0-8)
  bool reclaimed;                  // True if madvise was called, committed_bytes decremented
  u8 _pad[2];                      // Alignment padding
  _Atomic u32 num_allocated;       // Slots currently in use
  u16 slots_per_page;              // Cached from size_class
  u16 bitmap_bytes;                // Cached bitmap size
  // Bitmaps and slots follow in memory (not in struct)
  // Use accessor functions below
} valk_gc_page2_t;

// Get pointer to allocation bitmap (follows header)
static inline u8 *valk_gc_page2_alloc_bitmap(valk_gc_page2_t *page) {
  return (u8 *)(page + 1);
}

// Get pointer to mark bitmap (follows alloc bitmap)
static inline u8 *valk_gc_page2_mark_bitmap(valk_gc_page2_t *page) {
  return (u8 *)(page + 1) + page->bitmap_bytes;
}

// Get pointer to slot data (follows both bitmaps, cache-aligned)
static inline u8 *valk_gc_page2_slots(valk_gc_page2_t *page) {
  u8 *after_bitmaps = (u8 *)(page + 1) + 2 * page->bitmap_bytes;
  // Align to 64-byte cache line (requires int for bit masking)
  uptr addr = (uptr)after_bitmaps;
  addr = (addr + 63) & ~63ULL;
  return (u8 *)addr;
}

// Get pointer to specific slot
static inline void *valk_gc_page2_slot_ptr(valk_gc_page2_t *page, u32 slot_idx) {
  u16 slot_size = valk_gc_size_classes[page->size_class];
  return valk_gc_page2_slots(page) + slot_idx * slot_size;
}

// Per-class page list
typedef struct valk_gc_page_list {
  pthread_mutex_t lock;
  valk_gc_page2_t *all_pages;           // All pages for this class
  valk_gc_page2_t *partial_pages;       // Pages with free slots
  sz num_pages;
  _Atomic sz total_slots;
  _Atomic sz used_slots;
  _Atomic u32 next_page_offset;    // For allocation within virtual region
  u16 slot_size;                   // Cached
  u16 slots_per_page;              // Cached
  sz region_start;                  // Offset from heap base to this class's region
  sz region_size;                   // Maximum size of this class's region
  sz page_size;                     // Cached page size for this class
} valk_gc_page_list_t;

// Large object tracking (>4KB allocations)
typedef struct valk_gc_large_obj {
  struct valk_gc_large_obj *next;
  void *data;                           // mmap'd region
  sz size;                          // Allocation size
  bool marked;                          // GC mark
} valk_gc_large_obj_t;

// Multi-class TLAB with per-class state
typedef struct valk_gc_tlab2 {
  struct valk_gc_heap2 *owner_heap;     // Heap this TLAB is associated with
  u64 owner_generation;                 // Generation of owner_heap when attached
  struct {
    valk_gc_page2_t *page;              // Current page for this class
    u32 next_slot;                 // Next slot to allocate
    u32 limit_slot;                // End of claimed range
  } classes[VALK_GC_NUM_SIZE_CLASSES];
} valk_gc_tlab2_t;

// Main heap structure with size classes
struct valk_gc_heap2 {
  valk_mem_allocator_e type;            // VALK_ALLOC_GC_HEAP
  u64 generation;                       // Unique generation for this heap instance
  void *base;                           // mmap'd base (PROT_NONE reserved)
  sz reserved;                      // Total virtual reservation
  
  valk_gc_page_list_t classes[VALK_GC_NUM_SIZE_CLASSES];
  
  valk_gc_large_obj_t *large_objects;   // Linked list of large allocations
  pthread_mutex_t large_lock;
  
  _Atomic sz committed_bytes;       // Physical pages committed
  _Atomic sz used_bytes;            // Bytes in allocated slots
  _Atomic sz large_object_bytes;    // Bytes in large objects
  
  sz hard_limit;                    // Absolute maximum (abort if exceeded)
  sz soft_limit;                    // Emergency GC trigger
  u8 gc_threshold_pct;             // Normal GC trigger (% of committed)
  u8 gc_target_pct;                // Target usage after GC (informational)
  u32 min_gc_interval_ms;          // Minimum ms between GC cycles
  u64 last_gc_time_us;             // Timestamp of last GC
  
  _Atomic bool gc_in_progress;
  bool in_emergency_gc;
  
  _Atomic u64 collections;
  _Atomic sz bytes_allocated_total;
  _Atomic sz bytes_reclaimed_total;
  
  valk_lenv_t *root_env;                // Root environment for marking
  valk_gc_heap_stats_t stats;           // Telemetry statistics
  valk_gc_runtime_metrics_t runtime_metrics; // Runtime metrics for observability
};

// Initialize new multi-class heap
valk_gc_heap2_t *valk_gc_heap2_create(sz hard_limit);

// Destroy heap and release all memory
void valk_gc_heap2_destroy(valk_gc_heap2_t *heap);

// Allocate from heap (selects size class or large object path)
void *valk_gc_heap2_alloc(valk_gc_heap2_t *heap, sz bytes);

// Reallocate - grow or shrink allocation
void *valk_gc_heap2_realloc(valk_gc_heap2_t *heap, void *ptr, sz new_size);

// Get current usage
static inline sz valk_gc_heap2_used_bytes(valk_gc_heap2_t *heap) {
  sz total = atomic_load(&heap->large_object_bytes);
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    total += atomic_load(&heap->classes[c].used_slots) * valk_gc_size_classes[c];
  }
  return total;
}

// Initialize multi-class TLAB
void valk_gc_tlab2_init(valk_gc_tlab2_t *tlab);

// Allocate from TLAB (fast path)
static inline void *valk_gc_tlab2_alloc(valk_gc_tlab2_t *tlab, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return nullptr;
  
  if (__builtin_expect(tlab->classes[size_class].page != nullptr && 
                       tlab->classes[size_class].next_slot < 
                       tlab->classes[size_class].limit_slot, 1)) {
    u32 slot = tlab->classes[size_class].next_slot++;
    return valk_gc_page2_slot_ptr(tlab->classes[size_class].page, slot);
  }
  return nullptr;
}

// Refill TLAB for specific class (slow path)
bool valk_gc_tlab2_refill(valk_gc_tlab2_t *tlab, valk_gc_heap2_t *heap, u8 size_class);

// ============================================================================
// Phase 2: Pointer Location and Marking (Size Class Allocator)
// ============================================================================

// Result of pointer location lookup
typedef struct valk_gc_ptr_location {
  valk_gc_page2_t *page;
  u32 slot;
  u8 size_class;
  bool is_valid;
} valk_gc_ptr_location_t;

// Find the page and slot for a pointer
// Returns false if pointer is not in the heap (may be large object or external)
bool valk_gc_ptr_to_location(valk_gc_heap2_t *heap, void *ptr, valk_gc_ptr_location_t *out);

// Atomic bitmap operations for mark bitmap (used during parallel marking)
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

// Try to mark a slot (returns true if newly marked, false if already marked)
static inline bool valk_gc_page2_try_mark(valk_gc_page2_t *page, u32 slot) {
  return valk_gc_bitmap_try_set_atomic(valk_gc_page2_mark_bitmap(page), slot);
}

// Check if a slot is marked
static inline bool valk_gc_page2_is_marked(valk_gc_page2_t *page, u32 slot) {
  return valk_gc_bitmap_test_atomic(valk_gc_page2_mark_bitmap(page), slot);
}

// Check if a slot is allocated
static inline bool valk_gc_page2_is_allocated(valk_gc_page2_t *page, u32 slot) {
  return valk_gc_bitmap_test(valk_gc_page2_alloc_bitmap(page), slot);
}

// Mark a large object (returns true if newly marked)
bool valk_gc_mark_large_object(valk_gc_heap2_t *heap, void *ptr);

// Sweep a single page, returns number of slots freed
sz valk_gc_sweep_page2(valk_gc_page2_t *page);

// Sweep all large objects, returns bytes freed
sz valk_gc_sweep_large_objects(valk_gc_heap2_t *heap);

// Rebuild partial_pages lists after sweep
void valk_gc_rebuild_partial_lists(valk_gc_heap2_t *heap);

// Reclaim empty pages (release physical memory via madvise)
// Returns number of pages reclaimed
sz valk_gc_reclaim_empty_pages(valk_gc_heap2_t *heap);

// ============================================================================
// Phase 3: Memory Limits and GC Cycle
// ============================================================================

// GC statistics for diagnostics
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

// Get heap statistics
void valk_gc_heap2_get_stats(valk_gc_heap2_t *heap, valk_gc_stats2_t *out);

// Run a full GC collection cycle (mark + sweep)
// Returns bytes reclaimed
sz valk_gc_heap2_collect(valk_gc_heap2_t *heap);

// Auto-select single-threaded or parallel collection based on registered threads
sz valk_gc_heap2_collect_auto(valk_gc_heap2_t *heap);

// Reset all TLABs after GC
void valk_gc_tlab2_reset(valk_gc_tlab2_t *tlab);

// Abandon TLAB state without accessing owner heap (for heap switching)
void valk_gc_tlab2_abandon(valk_gc_tlab2_t *tlab);

// OOM abort with diagnostics (never returns)
__attribute__((noreturn))
void valk_gc_oom_abort(valk_gc_heap2_t *heap, sz requested);

// ============================================================================
// Phase 4: Mark Phase for heap2
// ============================================================================

typedef struct valk_gc_mark_ctx2 {
  valk_gc_heap2_t *heap;
  valk_gc_mark_queue_t *queue;
} valk_gc_mark_ctx2_t;

void valk_gc_heap2_mark_object(valk_gc_mark_ctx2_t *ctx, void *ptr);
void valk_gc_heap2_mark_roots(valk_gc_heap2_t *heap);

// ============================================================================
// Phase 7: Parallel Mark/Sweep for heap2
// ============================================================================

void valk_gc_heap2_parallel_mark(valk_gc_heap2_t *heap);

void valk_gc_heap2_parallel_sweep(valk_gc_heap2_t *heap);

sz valk_gc_heap2_parallel_collect(valk_gc_heap2_t *heap);

bool valk_gc_heap2_request_stw(valk_gc_heap2_t *heap);

// ============================================================================
// Legacy Single-Class Page Structure (existing, for backward compatibility)
// ============================================================================

typedef struct valk_gc_page {
  struct valk_gc_page *next;      // Next page in pool list
  _Atomic u32 num_allocated; // Slots currently in use
  u32 page_id;               // For debugging
  u8 mark_bits[VALK_GC_BITMAP_SIZE];  // Mark bitmap (1 = marked)
  u8 alloc_bits[VALK_GC_BITMAP_SIZE]; // Allocation bitmap (1 = in use)
  _Alignas(VALK_GC_PAGE_ALIGN) u8 slots[VALK_GC_SLOTS_PER_PAGE * VALK_GC_SLOT_SIZE];
} valk_gc_page_t;

typedef struct valk_gc_page_pool {
  pthread_mutex_t lock;
  valk_gc_page_t *all_pages;      // All allocated pages (for sweep)
  valk_gc_page_t *partial_pages;  // Pages with free space
  sz num_pages;
  _Atomic sz total_slots;
  _Atomic sz used_slots;
  _Atomic sz gc_threshold;    // Trigger GC when used_slots exceeds
} valk_gc_page_pool_t;

// TLAB (Thread-Local Allocation Buffer)
typedef struct valk_gc_tlab {
  valk_gc_page_t *page;        // Current page
  u32 next_slot;          // Next slot index to allocate from
  u32 limit_slot;         // Last slot in TLAB range (exclusive)
} valk_gc_tlab_t;

// Initialize page pool
void valk_gc_page_pool_init(valk_gc_page_pool_t *pool);

// Destroy page pool (frees all pages)
void valk_gc_page_pool_destroy(valk_gc_page_pool_t *pool);

// Allocate a new page and add to pool
valk_gc_page_t *valk_gc_page_alloc(valk_gc_page_pool_t *pool);

// Initialize TLAB (must be called per-thread)
void valk_gc_tlab_init(valk_gc_tlab_t *tlab);

// Refill TLAB from page pool (slow path)
bool valk_gc_tlab_refill(valk_gc_tlab_t *tlab, valk_gc_page_pool_t *pool);

// Fast path allocation from TLAB (inline for performance)
// Note: alloc_bits are pre-set during tlab_refill, so we just bump the pointer
static inline void *valk_gc_tlab_alloc(valk_gc_tlab_t *tlab) {
  if (__builtin_expect(tlab->page != nullptr && tlab->next_slot < tlab->limit_slot, 1)) {
    u32 slot = tlab->next_slot++;
    return &tlab->page->slots[slot * VALK_GC_SLOT_SIZE];
  }
  return nullptr;  // TLAB exhausted, need slow path
}

// Get page pool statistics
void valk_gc_page_pool_stats(valk_gc_page_pool_t *pool, 
                              sz *out_pages, sz *out_total, 
                              sz *out_used);

// ============================================================================
// Phase 2: GC Triggering and Participation
// ============================================================================

void valk_gc_request_collection(void);

void valk_gc_participate(void);

// ============================================================================
// Phase 3: Root Enumeration
// ============================================================================

typedef struct valk_gc_root {
  sz saved_count;
} valk_gc_root_t;

static inline valk_gc_root_t valk_gc_root_push(valk_lval_t *val);
static inline void valk_gc_root_pop(void);
static inline void valk_gc_root_cleanup(valk_gc_root_t *r);

#define VALK_GC_ROOT(var) \
  __attribute__((cleanup(valk_gc_root_cleanup))) \
  valk_gc_root_t __gc_root_##var = valk_gc_root_push(var)

typedef void (*valk_gc_root_visitor_t)(valk_lval_t *root, void *ctx);

void valk_gc_visit_thread_roots(valk_gc_root_visitor_t visitor, void *ctx);
void valk_gc_visit_global_roots(valk_gc_root_visitor_t visitor, void *ctx);
void valk_gc_visit_env_roots(valk_lenv_t *env, valk_gc_root_visitor_t visitor, void *ctx);

// ============================================================================
// Phase 4: Parallel Mark
// ============================================================================

void valk_gc_parallel_mark(void);
bool valk_gc_check_termination(void);

// ============================================================================
// Phase 5: Parallel Sweep
// ============================================================================

void valk_gc_parallel_sweep(valk_gc_page_pool_t *pool);

// ============================================================================
// Phase 6: Integration - GC Trigger and Full Cycle
// ============================================================================

void valk_gc_maybe_collect(valk_gc_page_pool_t *pool);
void valk_gc_full_cycle(valk_gc_page_pool_t *pool);

// ============================================================================
// Global Page Pool for TLAB Allocation
// ============================================================================

extern valk_gc_page_pool_t valk_gc_global_pool;

void valk_gc_global_pool_init(void);
void valk_gc_global_pool_destroy(void);

void *valk_gc_tlab_alloc_slow(sz bytes);

// ============================================================================
// Root Stack Inline Implementations
// ============================================================================

static inline valk_gc_root_t valk_gc_root_push(valk_lval_t *val) {
  valk_thread_context_t *ctx = &valk_thread_ctx;
  
  if (ctx->root_stack == nullptr) {
    return (valk_gc_root_t){ 0 };
  }
  
  if (ctx->root_stack_count >= ctx->root_stack_capacity) {
    ctx->root_stack_capacity *= 2;
    ctx->root_stack = realloc(ctx->root_stack,
                               sizeof(valk_lval_t*) * ctx->root_stack_capacity);
  }
  
  sz saved = ctx->root_stack_count;
  ctx->root_stack[ctx->root_stack_count++] = val;
  return (valk_gc_root_t){ saved };
}

static inline void valk_gc_root_pop(void) {
  if (valk_thread_ctx.root_stack_count > 0) {
    valk_thread_ctx.root_stack_count--;
  }
}

static inline void valk_gc_root_cleanup(valk_gc_root_t *r) {
  valk_thread_ctx.root_stack_count = r->saved_count;
}
