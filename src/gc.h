#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>
#include "memory.h"

// Forward declarations
typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;

// GC allocation header - prepended to every GC-managed allocation
// This allows arbitrary-sized allocations while maintaining tracking metadata
typedef struct valk_gc_header_t {
  void* origin_allocator;              // Which heap allocated this
  struct valk_gc_header_t* gc_next;    // Linked list for GC tracking
  size_t size;                         // User-requested allocation size
  // User data follows immediately after this header
} valk_gc_header_t;

// Forward declare slab allocator
struct valk_slab_t;

// GC heap statistics for telemetry
typedef struct {
  size_t overflow_allocations;      // Allocations received from scratch overflow
  size_t evacuations_from_scratch;  // Values received from scratch evacuation
  size_t evacuation_bytes;          // Bytes received from scratch evacuation
  size_t evacuation_pointer_fixups; // Pointer updates during evacuation
  size_t emergency_collections;     // Emergency GCs triggered at hard limit
  size_t peak_usage;                // Maximum allocated_bytes ever reached
} valk_gc_heap_stats_t;

// GC runtime metrics for observability (live counters, not telemetry snapshots)
typedef struct {
  _Atomic uint64_t cycles_total;           // Total GC collections
  _Atomic uint64_t pause_us_total;         // Cumulative pause time (microseconds)
  _Atomic uint64_t pause_us_max;           // Worst-case pause time
  _Atomic uint64_t reclaimed_bytes_total;  // Total bytes reclaimed across all cycles
  _Atomic uint64_t allocated_bytes_total;  // Total bytes ever allocated (for rate calc)
  _Atomic uint64_t objects_marked;         // Objects marked in last cycle
  _Atomic uint64_t objects_swept;          // Objects swept in last cycle
  _Atomic uint64_t last_heap_before_gc;    // Heap size before last GC (for efficiency)
  _Atomic uint64_t last_reclaimed;         // Bytes reclaimed in last GC cycle
  uint64_t last_cycle_start_us;            // Timing for current cycle (internal)

  // Object survival histogram - tracks how long objects live
  // Used to detect potential memory leaks (objects surviving many cycles)
  // Buckets: gen_0 (died in 1st GC), gen_1_5, gen_6_20, gen_21_plus (long-lived)
  _Atomic uint64_t survival_gen_0;         // Died in first GC (short-lived, expected)
  _Atomic uint64_t survival_gen_1_5;       // Survived 1-5 cycles (normal)
  _Atomic uint64_t survival_gen_6_20;      // Survived 6-20 cycles (medium-lived)
  _Atomic uint64_t survival_gen_21_plus;   // Survived 21+ cycles (potential leak)

  // Frame-time pause histogram - tracks GC pause impact on frame budgets
  // Used by game profile to show distribution of pauses relative to frame time
  // Buckets based on typical frame budgets: 60fps=16.6ms, 30fps=33.3ms
  _Atomic uint64_t pause_0_1ms;            // No impact (0-1ms)
  _Atomic uint64_t pause_1_5ms;            // Minor impact (1-5ms)
  _Atomic uint64_t pause_5_10ms;           // Noticeable (5-10ms)
  _Atomic uint64_t pause_10_16ms;          // Frame drop risk at 60fps (10-16ms)
  _Atomic uint64_t pause_16ms_plus;        // Frame drop certain at 60fps (16ms+)
} valk_gc_runtime_metrics_t;

// GC malloc heap - malloc-based allocator with mark & sweep collection
typedef struct {
  valk_mem_allocator_e type;  // VALK_ALLOC_GC_HEAP
  size_t allocated_bytes;     // Current malloc memory usage (excludes slab)
  size_t hard_limit;          // Absolute maximum heap size (abort if exceeded)
  size_t num_collections;     // Number of GC runs performed
  bool in_emergency_gc;       // Prevent recursive emergency GC
  valk_gc_header_t* objects;  // Linked list of all allocated object headers
  valk_lenv_t* root_env;      // Root environment for marking
  valk_gc_header_t* free_list;  // Free-list for fast reuse of swept objects
  size_t free_list_size;      // Number of objects in free list
  valk_slab_t* lval_slab;     // Fast slab allocator for valk_lval_t objects
  size_t lval_size;           // Size of valk_lval_t for slab allocation
  valk_slab_t* lenv_slab;     // Fast slab allocator for valk_lenv_t objects
  size_t lenv_size;           // Size of valk_lenv_t for slab allocation
  valk_gc_heap_stats_t stats; // Telemetry statistics
  valk_gc_runtime_metrics_t runtime_metrics; // Runtime metrics for observability

  uint8_t gc_threshold_pct;   // Trigger GC when heap usage exceeds this % (default: 75)
  uint8_t gc_target_pct;      // After GC, aim to be below this % (default: 50)
  uint64_t last_gc_time_us;   // Timestamp of last GC (for rate limiting)
  uint32_t min_gc_interval_ms; // Minimum ms between GC cycles (default: 1000)
} valk_gc_malloc_heap_t;

// Initialize GC malloc heap with hard limit (default 250MB if 0)
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t hard_limit);

// Set hard limit for GC heap (must be >= current allocated_bytes)
void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, size_t limit);

// Allocate from GC malloc heap (uses malloc, triggers GC if needed)
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, size_t bytes);

// Set root environment for marking
void valk_gc_malloc_set_root(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env);

// Perform mark & sweep collection
// If additional_root is non-NULL, it will be marked in addition to root_env
size_t valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap, valk_lval_t* additional_root);

// Check if GC should run (considers both slab and malloc usage as percentage)
bool valk_gc_malloc_should_collect(valk_gc_malloc_heap_t* heap);

// Get current heap usage as percentage (0-100)
// Combined: (slab_used + malloc_used) / (slab_capacity + hard_limit) * 100
uint8_t valk_gc_heap_usage_pct(valk_gc_malloc_heap_t* heap);

// Configure GC thresholds (call after init, or use defaults)
// threshold_pct: trigger GC when usage exceeds this (default 75)
// target_pct: aim to be below this after GC (default 50, informational)
// min_interval_ms: minimum time between GC cycles (default 1000)
void valk_gc_set_thresholds(valk_gc_malloc_heap_t* heap,
                            uint8_t threshold_pct,
                            uint8_t target_pct,
                            uint32_t min_interval_ms);

// Print GC statistics
void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap);

// Print combined memory statistics (scratch arena + GC heap)
void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out);

// Free all GC heap allocations and the heap itself (for clean shutdown)
void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap);

// Get GC runtime metrics for export (thread-safe reads)
void valk_gc_get_runtime_metrics(valk_gc_malloc_heap_t* heap,
                                  uint64_t* cycles, uint64_t* pause_us_total,
                                  uint64_t* pause_us_max, uint64_t* reclaimed,
                                  size_t* heap_used, size_t* heap_total);

// Get cumulative bytes allocated (for allocation rate calculation)
uint64_t valk_gc_get_allocated_bytes_total(valk_gc_malloc_heap_t* heap);

// Get GC efficiency from last cycle (reclaimed / heap_before * 100, 0-100)
// Low efficiency suggests long-lived objects accumulating (potential leak)
uint8_t valk_gc_get_last_efficiency(valk_gc_malloc_heap_t* heap);

// Get object survival histogram (thread-safe reads)
// Buckets: gen_0 (died in 1st GC), gen_1_5, gen_6_20, gen_21_plus
void valk_gc_get_survival_histogram(valk_gc_malloc_heap_t* heap,
                                     uint64_t* gen_0, uint64_t* gen_1_5,
                                     uint64_t* gen_6_20, uint64_t* gen_21_plus);

// Get frame-time pause histogram (thread-safe reads)
// Buckets: 0-1ms, 1-5ms, 5-10ms, 10-16ms, 16ms+
// Used by game profile to show GC pause distribution relative to frame budgets
void valk_gc_get_pause_histogram(valk_gc_malloc_heap_t* heap,
                                  uint64_t* pause_0_1ms, uint64_t* pause_1_5ms,
                                  uint64_t* pause_5_10ms, uint64_t* pause_10_16ms,
                                  uint64_t* pause_16ms_plus);

typedef struct {
  size_t lval_slab_used;
  size_t lval_slab_total;
  size_t lval_slab_peak;
  size_t lenv_slab_used;
  size_t lenv_slab_total;
  size_t lenv_slab_peak;
  size_t malloc_allocated;
  size_t malloc_limit;
  size_t malloc_peak;
  size_t free_list_count;
  size_t free_list_bytes;
  double lval_fragmentation;
  double lenv_fragmentation;
} valk_fragmentation_t;

#define VALK_RETAINED_SET_MAX 10
#define VALK_RETAINED_SET_NAME_MAX 64

typedef struct {
  char name[VALK_RETAINED_SET_NAME_MAX];
  size_t retained_bytes;
  size_t object_count;
} valk_retained_set_t;

typedef struct {
  valk_retained_set_t sets[VALK_RETAINED_SET_MAX];
  size_t count;
} valk_retained_sets_t;

void valk_gc_get_fragmentation(valk_gc_malloc_heap_t* heap, valk_fragmentation_t* out);

void valk_gc_sample_retained_sets(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env,
                                   valk_retained_sets_t* out);

// ============================================================================
// Memory Snapshot for REPL Eval Tracking
// ============================================================================

typedef struct {
  size_t heap_used_bytes;
  size_t scratch_used_bytes;
  size_t lval_count;
  size_t lenv_count;
} valk_repl_mem_snapshot_t;

void valk_repl_mem_take_snapshot(valk_gc_malloc_heap_t* heap, valk_mem_arena_t* scratch,
                                 valk_repl_mem_snapshot_t* out);

void valk_repl_mem_snapshot_delta(valk_repl_mem_snapshot_t* before, valk_repl_mem_snapshot_t* after,
                                  int64_t* heap_delta, int64_t* scratch_delta,
                                  int64_t* lval_delta, int64_t* lenv_delta);

// REPL eval memory delta - exposes last eval's memory changes for dashboard
typedef struct {
  int64_t heap_delta;
  int64_t scratch_delta;
  int64_t lval_delta;
  int64_t lenv_delta;
  uint64_t eval_count;
} valk_repl_eval_delta_t;

// Get the last REPL eval memory delta (for SSE diagnostics)
// Returns false if no eval has occurred yet (running as server, not REPL)
bool valk_repl_get_last_eval_delta(valk_repl_eval_delta_t* out);

// Update REPL eval deltas (called from repl.c after each eval)
void valk_repl_set_eval_delta(int64_t heap, int64_t scratch, int64_t lval, int64_t lenv);

// Explicitly free a single GC heap object (for cleanup when switching allocators)
void valk_gc_free_object(void* heap, void* ptr);

// Arena-based GC (informational only, for backward compatibility)
size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena);
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
  size_t worklist_count;          // Current worklist size
  size_t worklist_capacity;       // Allocated capacity
  valk_lval_t** evacuated;        // List of evacuated values (for pointer fixing)
  size_t evacuated_count;         // Number of evacuated values
  size_t evacuated_capacity;      // Allocated capacity for evacuated list
  size_t values_copied;           // Stats for this evacuation
  size_t bytes_copied;            // Stats for this evacuation
  size_t pointers_fixed;          // Stats for this evacuation
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
  _Atomic size_t top;     // Thieves steal from here (FIFO end)
  _Atomic size_t bottom;  // Owner pushes/pops here (LIFO end)
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
  size_t count;
  size_t waiting;
  size_t phase;
} valk_barrier_t;

void valk_barrier_init(valk_barrier_t* b, size_t count);
void valk_barrier_destroy(valk_barrier_t* b);
void valk_barrier_wait(valk_barrier_t* b);

// Global GC coordinator for multi-threaded GC
typedef struct valk_gc_coordinator {
  _Atomic valk_gc_phase_e phase;
  _Atomic size_t threads_registered;
  _Atomic size_t threads_paused;
  
  pthread_mutex_t lock;
  pthread_cond_t all_paused;   // Signaled when all threads at safe point
  pthread_cond_t gc_done;      // Signaled when GC complete
  valk_barrier_t barrier;      // Portable barrier for sync between GC phases
  bool barrier_initialized;
  
  valk_gc_thread_info_t threads[VALK_GC_MAX_THREADS];
  
  // Statistics
  _Atomic uint64_t parallel_cycles;
  _Atomic uint64_t parallel_pause_us_total;
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
  size_t count;
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

typedef struct valk_gc_page {
  struct valk_gc_page *next;      // Next page in pool list
  _Atomic uint32_t num_allocated; // Slots currently in use
  uint32_t page_id;               // For debugging
  uint8_t mark_bits[VALK_GC_BITMAP_SIZE];  // Mark bitmap (1 = marked)
  uint8_t alloc_bits[VALK_GC_BITMAP_SIZE]; // Allocation bitmap (1 = in use)
  _Alignas(VALK_GC_PAGE_ALIGN) uint8_t slots[VALK_GC_SLOTS_PER_PAGE * VALK_GC_SLOT_SIZE];
} valk_gc_page_t;

typedef struct valk_gc_page_pool {
  pthread_mutex_t lock;
  valk_gc_page_t *all_pages;      // All allocated pages (for sweep)
  valk_gc_page_t *partial_pages;  // Pages with free space
  size_t num_pages;
  _Atomic size_t total_slots;
  _Atomic size_t used_slots;
  _Atomic size_t gc_threshold;    // Trigger GC when used_slots exceeds
} valk_gc_page_pool_t;

// TLAB (Thread-Local Allocation Buffer)
typedef struct valk_gc_tlab {
  valk_gc_page_t *page;        // Current page
  uint32_t next_slot;          // Next slot index to allocate from
  uint32_t limit_slot;         // Last slot in TLAB range (exclusive)
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
  if (__builtin_expect(tlab->page != NULL && tlab->next_slot < tlab->limit_slot, 1)) {
    uint32_t slot = tlab->next_slot++;
    return &tlab->page->slots[slot * VALK_GC_SLOT_SIZE];
  }
  return NULL;  // TLAB exhausted, need slow path
}

// Bitmap operations
static inline bool valk_gc_bitmap_test(const uint8_t *bitmap, uint32_t idx) {
  return (bitmap[idx / 8] & (1 << (idx % 8))) != 0;
}

static inline void valk_gc_bitmap_set(uint8_t *bitmap, uint32_t idx) {
  bitmap[idx / 8] |= (uint8_t)(1 << (idx % 8));
}

static inline void valk_gc_bitmap_clear(uint8_t *bitmap, uint32_t idx) {
  bitmap[idx / 8] &= (uint8_t)~(1 << (idx % 8));
}

// Get page pool statistics
void valk_gc_page_pool_stats(valk_gc_page_pool_t *pool, 
                              size_t *out_pages, size_t *out_total, 
                              size_t *out_used);

// ============================================================================
// Phase 2: GC Triggering and Participation
// ============================================================================

void valk_gc_request_collection(void);

void valk_gc_participate(void);

// ============================================================================
// Phase 3: Root Enumeration
// ============================================================================

typedef struct valk_gc_root {
  size_t saved_count;
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

void *valk_gc_tlab_alloc_slow(size_t bytes);

// ============================================================================
// Root Stack Inline Implementations
// ============================================================================

static inline valk_gc_root_t valk_gc_root_push(valk_lval_t *val) {
  valk_thread_context_t *ctx = &valk_thread_ctx;
  
  if (ctx->root_stack == NULL) {
    return (valk_gc_root_t){ 0 };
  }
  
  if (ctx->root_stack_count >= ctx->root_stack_capacity) {
    ctx->root_stack_capacity *= 2;
    ctx->root_stack = realloc(ctx->root_stack,
                               sizeof(valk_lval_t*) * ctx->root_stack_capacity);
  }
  
  size_t saved = ctx->root_stack_count;
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
