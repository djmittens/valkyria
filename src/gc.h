#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <pthread.h>
#include "common.h"
#include "memory.h"
#include "types.h"
#include "gc_heap.h"

typedef struct valk_lenv_t valk_lenv_t;
typedef struct valk_lval_t valk_lval_t;

// ============================================================================
// Runtime Initialization API
// ============================================================================

typedef struct {
  sz gc_heap_size;
} valk_runtime_config_t;

static inline valk_runtime_config_t valk_runtime_config_default(void) {
  return (valk_runtime_config_t){
    .gc_heap_size = 4ULL * 1024 * 1024 * 1024,
  };
}

typedef void (*valk_thread_onboard_fn)(void);

int valk_runtime_init(valk_runtime_config_t *config);
void valk_runtime_shutdown(void);
void valk_runtime_thread_onboard(void);
valk_thread_onboard_fn valk_runtime_get_onboard_fn(void);
valk_gc_heap_t *valk_runtime_get_heap(void);
bool valk_runtime_is_initialized(void);

void valk_gc_reset_after_fork(void);
void valk_gc_mark_reset_after_fork(void);

// ============================================================================
// GC Allocation Header (legacy)
// ============================================================================

typedef struct valk_gc_header_t {
  void* origin_allocator;
  struct valk_gc_header_t* gc_next;
  sz size;
} valk_gc_header_t;

struct valk_slab_t;

// ============================================================================
// GC Heap API
// ============================================================================

void valk_gc_set_hard_limit(valk_gc_heap_t* heap, sz limit);
void valk_gc_set_root(valk_gc_heap_t* heap, valk_lenv_t* root_env);
bool valk_gc_should_collect(valk_gc_heap_t* heap);
u8 valk_gc_heap_usage_pct(valk_gc_heap_t* heap);
void valk_gc_set_thresholds(valk_gc_heap_t* heap,
                            u8 threshold_pct, u8 target_pct, u32 min_interval_ms);
void valk_gc_print_stats(valk_gc_heap_t* heap);
void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_heap_t* heap, FILE* out);

// ============================================================================
// GC Metrics Export
// ============================================================================

void valk_gc_get_runtime_metrics(valk_gc_heap_t* heap,
                                  u64* cycles, u64* pause_us_total,
                                  u64* pause_us_max, sz* reclaimed,
                                  sz* heap_used, sz* heap_total);
sz valk_gc_get_allocated_bytes_total(valk_gc_heap_t* heap);
u8 valk_gc_get_last_efficiency(valk_gc_heap_t* heap);
void valk_gc_get_survival_histogram(valk_gc_heap_t* heap,
                                     u64* gen_0, u64* gen_1_5,
                                     u64* gen_6_20, u64* gen_21_plus);
void valk_gc_get_pause_histogram(valk_gc_heap_t* heap,
                                  u64* pause_0_1ms, u64* pause_1_5ms,
                                  u64* pause_5_10ms, u64* pause_10_16ms,
                                  u64* pause_16ms_plus);

typedef struct {
  sz heap_allocated;
  sz heap_limit;
  sz heap_peak;
} valk_fragmentation_t;

void valk_gc_get_fragmentation(valk_gc_heap_t* heap, valk_fragmentation_t* out);

// ============================================================================
// Memory Snapshot for REPL Eval Tracking
// ============================================================================

typedef struct {
  sz heap_used_bytes;
  sz scratch_used_bytes;
  u64 lval_count;
  u64 lenv_count;
} valk_repl_mem_snapshot_t;

void valk_repl_mem_take_snapshot(valk_gc_heap_t* heap, valk_mem_arena_t* scratch,
                                 valk_repl_mem_snapshot_t* out);
void valk_repl_mem_snapshot_delta(valk_repl_mem_snapshot_t* before, valk_repl_mem_snapshot_t* after,
                                  i64* heap_delta, i64* scratch_delta,
                                  i64* lval_delta, i64* lenv_delta);

typedef struct {
  i64 heap_delta;
  i64 scratch_delta;
  i64 lval_delta;
  i64 lenv_delta;
  u64 eval_count;
} valk_repl_eval_delta_t;

bool valk_repl_get_last_eval_delta(valk_repl_eval_delta_t* out);
void valk_repl_set_eval_delta(i64 heap, i64 scratch, i64 lval, i64 lenv);

// ============================================================================
// Lifetime and Region Types
// ============================================================================

typedef enum {
  VALK_LIFETIME_IMMORTAL,
  VALK_LIFETIME_SESSION,
  VALK_LIFETIME_REQUEST,
  VALK_LIFETIME_SCRATCH,
} valk_lifetime_e;

typedef struct valk_region_stats {
  _Atomic sz bytes_allocated;
  sz bytes_limit;
  _Atomic sz bytes_promoted;
  _Atomic u64 alloc_count;
  _Atomic u64 promotion_count;
  _Atomic u64 overflow_count;
} valk_region_stats_t;

typedef struct valk_region {
  valk_mem_allocator_e type;
  valk_lifetime_e lifetime;
  struct valk_region *parent;
  valk_mem_arena_t *arena;
  valk_gc_heap_t *gc_heap;
  bool owns_arena;
  valk_region_stats_t stats;
} valk_region_t;

valk_region_t *valk_region_create(valk_lifetime_e lifetime, valk_region_t *parent);
valk_region_t *valk_region_create_with_arena(valk_lifetime_e lifetime,
                                              valk_region_t *parent,
                                              valk_mem_arena_t *arena);
void valk_region_init(valk_region_t *region, valk_lifetime_e lifetime,
                      valk_region_t *parent, valk_mem_arena_t *arena);
void valk_region_destroy(valk_region_t *region);
void valk_region_reset(valk_region_t *region);
void *valk_region_alloc(valk_region_t *region, sz bytes);
bool valk_region_set_limit(valk_region_t *region, sz limit);
void valk_region_get_stats(valk_region_t *region, valk_region_stats_t *out);

// ============================================================================
// Cross-Region Reference Checking
// ============================================================================

static inline bool valk_lifetime_can_reference(valk_lifetime_e from, valk_lifetime_e to) {
  return from >= to;
}

valk_lifetime_e valk_allocator_lifetime(void *allocator);
bool valk_region_write_barrier(void *parent_allocator, void *child_allocator,
                                bool promote_on_escape);
struct valk_lval_t *valk_region_promote_lval(valk_region_t *target,
                                              struct valk_lval_t *val);
struct valk_lval_t *valk_region_ensure_safe_ref(struct valk_lval_t *parent,
                                                 struct valk_lval_t *child);

// ============================================================================
// Pointer Map
// ============================================================================

#define VALK_PTR_MAP_INIT_CAPACITY 256
#define VALK_PTR_MAP_LOAD_FACTOR 0.75f

typedef struct {
  void *src;
  void *dst;
} valk_ptr_map_entry_t;

typedef struct {
  valk_ptr_map_entry_t *entries;
  sz count;
  sz capacity;
} valk_ptr_map_t;

void valk_ptr_map_init(valk_ptr_map_t *map);
void valk_ptr_map_free(valk_ptr_map_t *map);
void valk_ptr_map_put(valk_ptr_map_t *map, void *src, void *dst);
void *valk_ptr_map_get(valk_ptr_map_t *map, void *src);

// ============================================================================
// Handle Table
// ============================================================================

#define VALK_HANDLE_TABLE_INIT_SIZE 64

typedef struct {
  u32 index;
  u32 generation;
} valk_handle_t;

typedef struct {
  pthread_mutex_t lock;
  valk_lval_t **slots;
  u32 *generations;
  u32 capacity;
  u32 count;
  u32 free_head;
} valk_handle_table_t;

void valk_handle_table_init(valk_handle_table_t *table);
void valk_handle_table_free(valk_handle_table_t *table);
valk_handle_t valk_handle_create(valk_handle_table_t *table, valk_lval_t *val);
valk_lval_t *valk_handle_resolve(valk_handle_table_t *table, valk_handle_t h);
void valk_handle_release(valk_handle_table_t *table, valk_handle_t h);
void valk_handle_table_visit(valk_handle_table_t *table,
                             void (*visitor)(valk_lval_t*, void*), void *ctx);

extern valk_handle_table_t valk_global_handle_table;

// ============================================================================
// Evacuation Context
// ============================================================================

typedef struct {
  valk_mem_arena_t* scratch;
  valk_gc_heap_t* heap;
  valk_lval_t** worklist;
  sz worklist_count;
  sz worklist_capacity;
  valk_lval_t** evacuated;
  sz evacuated_count;
  sz evacuated_capacity;
  u64 values_copied;
  sz bytes_copied;
  u64 pointers_fixed;
  valk_ptr_map_t ptr_map;
} valk_evacuation_ctx_t;

// ============================================================================
// Checkpoint API
// ============================================================================

#define VALK_CHECKPOINT_THRESHOLD_DEFAULT 0.75f

bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold);
void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_heap_t* heap,
                     valk_lenv_t* root_env);
valk_lval_t* valk_evacuate_to_heap(valk_lval_t* v);

// ============================================================================
// Parallel GC Infrastructure
// ============================================================================

#define VALK_GC_MAX_THREADS 64

typedef enum {
  VALK_GC_PHASE_IDLE = 0,
  VALK_GC_PHASE_STW_REQUESTED,
  VALK_GC_PHASE_CHECKPOINT_REQUESTED,
  VALK_GC_PHASE_MARKING,
  VALK_GC_PHASE_SWEEPING,
} valk_gc_phase_e;

#include "aio_chase_lev.h"

#define VALK_GC_MARK_QUEUE_INITIAL_SIZE 8192

typedef valk_chase_lev_deque_t valk_gc_mark_queue_t;

void valk_gc_mark_queue_init(valk_gc_mark_queue_t* q);
void valk_gc_mark_queue_destroy(valk_gc_mark_queue_t* q);
void valk_gc_mark_queue_push(valk_gc_mark_queue_t* q, valk_lval_t* val);
valk_lval_t* valk_gc_mark_queue_pop(valk_gc_mark_queue_t* q);
valk_lval_t* valk_gc_mark_queue_steal(valk_gc_mark_queue_t* q);
bool valk_gc_mark_queue_empty(valk_gc_mark_queue_t* q);

typedef struct valk_gc_thread_info {
  void* ctx;
  pthread_t thread_id;
  bool active;
  valk_gc_mark_queue_t mark_queue;
} valk_gc_thread_info_t;

typedef struct valk_barrier {
  pthread_mutex_t mutex;
  pthread_cond_t cond;
  _Atomic sz count;
  _Atomic sz waiting;
  _Atomic sz phase;
} valk_barrier_t;

void valk_barrier_init(valk_barrier_t* b, sz count);
void valk_barrier_destroy(valk_barrier_t* b);
void valk_barrier_wait(valk_barrier_t* b);
void valk_barrier_reset(valk_barrier_t* b, sz count);

typedef struct valk_gc_coordinator {
  _Atomic valk_gc_phase_e phase;
  _Atomic u64 threads_registered;
  _Atomic u64 threads_paused;
  _Atomic u64 checkpoint_epoch;

  pthread_mutex_t lock;
  pthread_cond_t all_paused;
  pthread_cond_t gc_done;
  valk_barrier_t barrier;
  bool barrier_initialized;

  valk_gc_thread_info_t threads[VALK_GC_MAX_THREADS];

  _Atomic u64 parallel_cycles;
  _Atomic u64 parallel_pause_us_total;
} valk_gc_coordinator_t;

extern valk_gc_coordinator_t valk_gc_coord;

void valk_gc_coordinator_init(void);
void valk_gc_thread_register(void);
void valk_gc_thread_unregister(void);

#define VALK_GC_SAFE_POINT() \
  do { \
    if (__builtin_expect(atomic_load_explicit(&valk_gc_coord.phase, \
                         memory_order_acquire) != VALK_GC_PHASE_IDLE, 0)) { \
      valk_gc_safe_point_slow(); \
    } \
  } while (0)

void valk_gc_safe_point_slow(void);
void valk_gc_participate_in_parallel_gc(void);

// ============================================================================
// Mark Context
// ============================================================================

typedef struct valk_gc_mark_ctx {
  valk_gc_heap_t *heap;
  valk_gc_mark_queue_t *queue;
} valk_gc_mark_ctx_t;

void valk_gc_heap_mark_object(valk_gc_mark_ctx_t *ctx, void *ptr);
void valk_gc_heap_parallel_mark(valk_gc_heap_t *heap);
void valk_gc_heap_parallel_sweep(valk_gc_heap_t *heap);
bool valk_gc_heap_request_stw(valk_gc_heap_t *heap);

// ============================================================================
// Root Enumeration
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

// ============================================================================
// Diagnostic Dump
// ============================================================================

void valk_diag_dump_on_timeout(void);
