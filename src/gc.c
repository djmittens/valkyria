#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include "aio/aio.h"  // For valk_async_handle_t
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <sched.h>
#include <uv.h>
#ifdef __linux__
#include <dirent.h>
#endif

// ============================================================================
// Runtime Initialization
// ============================================================================

static valk_gc_malloc_heap_t *__runtime_heap = nullptr;
static bool __runtime_initialized = false;

// LCOV_EXCL_BR_START - runtime init/shutdown defensive checks
int valk_runtime_init(valk_runtime_config_t *config) {
  if (__runtime_initialized) {
    VALK_WARN("Runtime already initialized");
    return 0;
  }

  valk_gc_coordinator_init();
  valk_handle_table_init(&valk_global_handle_table);

  valk_runtime_config_t cfg = config ? *config : valk_runtime_config_default();

  __runtime_heap = valk_gc_heap2_create(cfg.gc_heap_size);
  if (!__runtime_heap) {
    VALK_ERROR("Failed to create runtime GC heap");
    return -1;
  }

  valk_runtime_thread_onboard();

  __runtime_initialized = true;
  VALK_INFO("Runtime initialized: gc_heap_size=%zu", cfg.gc_heap_size);
  return 0;
}

void valk_runtime_shutdown(void) {
  if (!__runtime_initialized) return;

  if (__runtime_heap) {
    valk_gc_heap2_destroy(__runtime_heap);
    __runtime_heap = nullptr;
  }

  __runtime_initialized = false;
  VALK_INFO("Runtime shutdown complete");
}

void valk_runtime_thread_onboard(void) {
  if (!__runtime_heap) {
    VALK_ERROR("Cannot onboard thread: runtime not initialized");
    return;
  }

  valk_mem_init_malloc();
  valk_thread_ctx.heap = __runtime_heap;
  valk_gc_thread_register();

  VALK_DEBUG("Thread onboarded to runtime heap: %p (gc_thread_id=%llu)", 
             __runtime_heap, (unsigned long long)valk_thread_ctx.gc_thread_id);
}
// LCOV_EXCL_BR_STOP

valk_thread_onboard_fn valk_runtime_get_onboard_fn(void) {
  return valk_runtime_thread_onboard;
}

valk_gc_heap2_t *valk_runtime_get_heap(void) {
  return __runtime_heap;
}

bool valk_runtime_is_initialized(void) {
  return __runtime_initialized;
}

// ============================================================================
// Parallel GC Infrastructure (Phase 0)
// ============================================================================

// Global coordinator instance
valk_gc_coordinator_t valk_gc_coord = {0};



// Portable barrier implementation
void valk_barrier_init(valk_barrier_t* b, sz count) {
  pthread_mutex_init(&b->mutex, nullptr);
  pthread_cond_init(&b->cond, nullptr);
  atomic_store(&b->count, count);
  atomic_store(&b->waiting, 0);
  atomic_store(&b->phase, 0);
}

void valk_barrier_destroy(valk_barrier_t* b) {
  pthread_mutex_destroy(&b->mutex);
  pthread_cond_destroy(&b->cond);
}

void valk_barrier_reset(valk_barrier_t* b, sz count) {
  pthread_mutex_lock(&b->mutex);
  atomic_store(&b->count, count);
  atomic_store(&b->waiting, 0);
  pthread_mutex_unlock(&b->mutex);
}

void valk_barrier_wait(valk_barrier_t* b) {
  pthread_mutex_lock(&b->mutex);
  sz my_phase = atomic_load(&b->phase);
  sz waiting = atomic_fetch_add(&b->waiting, 1) + 1;
  sz count = atomic_load(&b->count);
  if (waiting == count) {
    atomic_store(&b->waiting, 0);
    atomic_fetch_add(&b->phase, 1);
    pthread_cond_broadcast(&b->cond);
  } else {
    while (atomic_load(&b->phase) == my_phase) {
      pthread_cond_wait(&b->cond, &b->mutex);
    }
  }
  pthread_mutex_unlock(&b->mutex);
}

// LCOV_EXCL_BR_START - GC marking null checks and CAS loops
// Atomic mark bit operations
bool valk_gc_try_mark(valk_lval_t* obj) {
  if (obj == nullptr) return false;
  u64 expected = atomic_load_explicit(&obj->flags, memory_order_relaxed);
  do {
    if (expected & LVAL_FLAG_GC_MARK) {
      return false;
    }
  } while (!atomic_compare_exchange_weak_explicit(
      &obj->flags, &expected, expected | LVAL_FLAG_GC_MARK,
      memory_order_acq_rel, memory_order_relaxed));
  return true;
}

bool valk_gc_is_marked(valk_lval_t* obj) {
  if (obj == nullptr) return true;
  return (atomic_load_explicit(&obj->flags, memory_order_acquire) & LVAL_FLAG_GC_MARK) != 0;
}

void valk_gc_clear_mark(valk_lval_t* obj) {
  if (obj == nullptr) return;
  atomic_fetch_and_explicit(&obj->flags, ~LVAL_FLAG_GC_MARK, memory_order_release);
}

// Chase-Lev work-stealing deque implementation
void valk_gc_mark_queue_init(valk_gc_mark_queue_t* q) {
  atomic_store(&q->top, 0);
  atomic_store(&q->bottom, 0);
  for (u64 i = 0; i < VALK_GC_MARK_QUEUE_SIZE; i++) {
    atomic_store(&q->items[i], nullptr);
  }
}

bool valk_gc_mark_queue_push(valk_gc_mark_queue_t* q, valk_lval_t* val) {
  sz b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  sz t = atomic_load_explicit(&q->top, memory_order_acquire);
  
  if (b - t >= VALK_GC_MARK_QUEUE_SIZE) {
    return false;  // Queue full
  }
  
  atomic_store_explicit(&q->items[b % VALK_GC_MARK_QUEUE_SIZE], val,
                        memory_order_relaxed);
  atomic_thread_fence(memory_order_release);
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  return true;
}

valk_lval_t* valk_gc_mark_queue_pop(valk_gc_mark_queue_t* q) {
  sz b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  sz t = atomic_load_explicit(&q->top, memory_order_relaxed);
  
  if (t >= b) {
    return nullptr;
  }
  
  b = b - 1;
  atomic_store_explicit(&q->bottom, b, memory_order_relaxed);
  atomic_thread_fence(memory_order_seq_cst);
  
  t = atomic_load_explicit(&q->top, memory_order_relaxed);
  
  if (t <= b) {
    valk_lval_t* val = atomic_load_explicit(
        &q->items[b % VALK_GC_MARK_QUEUE_SIZE], memory_order_relaxed);
    
    if (t == b) {
      if (!atomic_compare_exchange_strong(&q->top, &t, t + 1)) {
        val = nullptr;
      }
      atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
    }
    return val;
  }
  
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  return nullptr;
}

valk_lval_t* valk_gc_mark_queue_steal(valk_gc_mark_queue_t* q) {
  sz t = atomic_load_explicit(&q->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  sz b = atomic_load_explicit(&q->bottom, memory_order_acquire);
  
  if (t >= b) {
    return nullptr;
  }
  
  valk_lval_t* val = atomic_load_explicit(
      &q->items[t % VALK_GC_MARK_QUEUE_SIZE], memory_order_relaxed);
  
  if (!atomic_compare_exchange_strong(&q->top, &t, t + 1)) {
    return nullptr;
  }
  
  return val;
}

bool valk_gc_mark_queue_empty(valk_gc_mark_queue_t* q) {
  sz t = atomic_load_explicit(&q->top, memory_order_acquire);
  sz b = atomic_load_explicit(&q->bottom, memory_order_acquire);
  return t >= b;
}
// LCOV_EXCL_BR_STOP

// Coordinator initialization
void valk_gc_coordinator_init(void) {
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  atomic_store(&valk_gc_coord.threads_registered, 0);
  atomic_store(&valk_gc_coord.threads_paused, 0);
  
  pthread_mutex_init(&valk_gc_coord.lock, nullptr);
  pthread_cond_init(&valk_gc_coord.all_paused, nullptr);
  pthread_cond_init(&valk_gc_coord.gc_done, nullptr);
  valk_gc_coord.barrier_initialized = false;
  
  for (u64 i = 0; i < VALK_GC_MAX_THREADS; i++) {
    valk_gc_coord.threads[i].ctx = nullptr;
    valk_gc_coord.threads[i].active = false;
    valk_gc_mark_queue_init(&valk_gc_coord.threads[i].mark_queue);
  }
  
  atomic_store(&valk_gc_coord.parallel_cycles, 0);
  atomic_store(&valk_gc_coord.parallel_pause_us_total, 0);
}

// LCOV_EXCL_BR_START - thread registration error paths
// Thread registration
void valk_gc_thread_register(void) {
  u64 idx = atomic_fetch_add(&valk_gc_coord.threads_registered, 1);
  
  if (idx >= VALK_GC_MAX_THREADS) {
    VALK_ERROR("Too many threads registered with GC (max %d)", VALK_GC_MAX_THREADS);
    atomic_fetch_sub(&valk_gc_coord.threads_registered, 1);
    return;
  }
  
  valk_thread_ctx.gc_thread_id = idx;
  valk_thread_ctx.gc_registered = true;
  
  valk_thread_ctx.root_stack = malloc(sizeof(valk_lval_t*) * 256);
  valk_thread_ctx.root_stack_capacity = 256;
  valk_thread_ctx.root_stack_count = 0;
  
  valk_gc_coord.threads[idx].ctx = &valk_thread_ctx;
  valk_gc_coord.threads[idx].thread_id = pthread_self();
  valk_gc_coord.threads[idx].active = true;
  valk_gc_mark_queue_init(&valk_gc_coord.threads[idx].mark_queue);
  
  VALK_DEBUG("Thread registered with GC: idx=%zu", idx);
}

void valk_gc_thread_unregister(void) {
  if (!valk_thread_ctx.gc_registered) return;
  
  VALK_GC_SAFE_POINT();
  
  u64 idx = valk_thread_ctx.gc_thread_id;
  valk_gc_coord.threads[idx].active = false;
  valk_gc_coord.threads[idx].ctx = nullptr;
  
  atomic_fetch_sub(&valk_gc_coord.threads_registered, 1);
  
  if (valk_thread_ctx.root_stack) {
    free(valk_thread_ctx.root_stack);
    valk_thread_ctx.root_stack = nullptr;
  }
  valk_thread_ctx.gc_registered = false;
  
  VALK_DEBUG("Thread unregistered from GC: idx=%zu", idx);
}
// LCOV_EXCL_BR_STOP

static void valk_gc_participate_in_parallel_gc(void);

// LCOV_EXCL_START - safe point slow path requires STW coordination from parallel GC
void valk_gc_safe_point_slow(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);

  if (phase == VALK_GC_PHASE_CHECKPOINT_REQUESTED) {
    u64 paused = atomic_fetch_add(&valk_gc_coord.threads_paused, 1) + 1;
    u64 registered = atomic_load(&valk_gc_coord.threads_registered);

    if (paused == registered) {
      pthread_mutex_lock(&valk_gc_coord.lock);
      pthread_cond_signal(&valk_gc_coord.all_paused);
      pthread_mutex_unlock(&valk_gc_coord.lock);
    }

    // Wait for THIS checkpoint to complete. Use a simple wait without re-checking
    // the phase in a loop - if a new checkpoint starts after we wake, we'll handle
    // it on the next VALK_GC_SAFE_POINT() call, not by re-entering the wait.
    pthread_mutex_lock(&valk_gc_coord.lock);
    pthread_cond_wait(&valk_gc_coord.gc_done, &valk_gc_coord.lock);
    pthread_mutex_unlock(&valk_gc_coord.lock);
    return;
  }

  if (phase == VALK_GC_PHASE_STW_REQUESTED) {
    if (valk_thread_ctx.scratch && valk_thread_ctx.scratch->offset > 0 &&
        valk_thread_ctx.heap && valk_thread_ctx.root_env) {
      valk_checkpoint(valk_thread_ctx.scratch,
                      valk_thread_ctx.heap,
                      valk_thread_ctx.root_env);
    }

    u64 paused = atomic_fetch_add(&valk_gc_coord.threads_paused, 1) + 1;
    u64 registered = atomic_load(&valk_gc_coord.threads_registered);

    if (paused == registered) {
      pthread_mutex_lock(&valk_gc_coord.lock);
      pthread_cond_signal(&valk_gc_coord.all_paused);
      pthread_mutex_unlock(&valk_gc_coord.lock);
    }

    valk_gc_participate_in_parallel_gc();
  }
}
// LCOV_EXCL_STOP

// ============================================================================
// Phase 1: Page-based Allocator (Parallel GC)
// ============================================================================

static _Atomic u32 __page_id_counter = 0;

// ============================================================================
// Phase 2: GC Triggering and Participation
// ============================================================================

// LCOV_EXCL_START - Parallel GC STW coordination requires multi-threaded test infrastructure
void valk_gc_request_collection(void) {
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected,
                                       VALK_GC_PHASE_STW_REQUESTED)) {
    return;
  }

  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  if (num_threads == 0) {
    atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
    return;
  }

  if (valk_gc_coord.barrier_initialized) {
    valk_barrier_reset(&valk_gc_coord.barrier, num_threads);
  } else {
    valk_barrier_init(&valk_gc_coord.barrier, num_threads);
    valk_gc_coord.barrier_initialized = true;
  }

  pthread_mutex_lock(&valk_gc_coord.lock);
  while (atomic_load(&valk_gc_coord.threads_paused) < num_threads) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_nsec += 100000000;
    if (ts.tv_nsec >= 1000000000) {
      ts.tv_sec++;
      ts.tv_nsec -= 1000000000;
    }
    pthread_cond_timedwait(&valk_gc_coord.all_paused, &valk_gc_coord.lock, &ts);
  }
  pthread_mutex_unlock(&valk_gc_coord.lock);
}

void valk_gc_participate(void) {
  valk_barrier_wait(&valk_gc_coord.barrier);

  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_MARKING);
  valk_gc_parallel_mark();

  valk_barrier_wait(&valk_gc_coord.barrier);

  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_SWEEPING);

  valk_barrier_wait(&valk_gc_coord.barrier);

  pthread_mutex_lock(&valk_gc_coord.lock);
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  pthread_cond_broadcast(&valk_gc_coord.gc_done);
  pthread_mutex_unlock(&valk_gc_coord.lock);

  atomic_fetch_add(&valk_gc_coord.parallel_cycles, 1);
}
// LCOV_EXCL_STOP

// ============================================================================
// Phase 3: Root Enumeration
// ============================================================================

// LCOV_EXCL_BR_START - defensive null checks in root iteration
void valk_gc_visit_thread_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  valk_thread_context_t *tc = &valk_thread_ctx;

  if (tc->root_stack == nullptr) return;

  for (u64 i = 0; i < tc->root_stack_count; i++) {
    if (tc->root_stack[i] != nullptr) {
      visitor(tc->root_stack[i], ctx);
    }
  }
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - defensive null checks in env root iteration
void valk_gc_visit_env_roots(valk_lenv_t *env, valk_gc_root_visitor_t visitor, void *ctx) {
  if (env == nullptr) return;

  for (u64 i = 0; i < env->vals.count; i++) {
    if (env->vals.items[i] != nullptr) {
      visitor(env->vals.items[i], ctx);
    }
  }

  valk_gc_visit_env_roots(env->parent, visitor, ctx);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - defensive null checks in global root iteration
void valk_gc_visit_global_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  valk_handle_table_visit(&valk_global_handle_table, visitor, ctx);

  for (u64 i = 0; i < VALK_GC_MAX_THREADS; i++) {
    if (valk_gc_coord.threads[i].active && valk_gc_coord.threads[i].ctx != nullptr) {
      valk_thread_context_t *tc = valk_gc_coord.threads[i].ctx;
      if (tc->root_env != nullptr) {
        valk_gc_visit_env_roots(tc->root_env, visitor, ctx);
      }
    }
  }
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Phase 4: Parallel Mark
// ============================================================================

// LCOV_EXCL_START - Parallel GC marking infrastructure requires multi-threaded coordination
static void mark_and_push(valk_lval_t *obj, void *ctx);
static void mark_children(valk_lval_t *obj, valk_gc_mark_queue_t *queue);
static void mark_env_parallel(valk_lenv_t *env, valk_gc_mark_queue_t *queue);

static void mark_env_parallel(valk_lenv_t *env, valk_gc_mark_queue_t *queue) {
  if (env == nullptr) return;

  for (u64 i = 0; i < env->vals.count; i++) {
    mark_and_push(env->vals.items[i], queue);
  }

  mark_env_parallel(env->parent, queue);
}

static void mark_children(valk_lval_t *obj, valk_gc_mark_queue_t *queue) {
  if (obj == nullptr) return;
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
      mark_and_push(obj->cons.head, queue);
      mark_and_push(obj->cons.tail, queue);
      break;
    case LVAL_FUN:
      if (obj->fun.builtin == nullptr) {
        mark_and_push(obj->fun.formals, queue);
        mark_and_push(obj->fun.body, queue);
        if (obj->fun.env) mark_env_parallel(obj->fun.env, queue);
      }
      break;
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_and_push(obj->async.handle->on_complete, queue);
        mark_and_push(obj->async.handle->on_error, queue);
        mark_and_push(obj->async.handle->on_cancel, queue);
        mark_and_push(atomic_load_explicit(&obj->async.handle->result, memory_order_acquire), queue);
        mark_and_push(atomic_load_explicit(&obj->async.handle->error, memory_order_acquire), queue);
        if (obj->async.handle->env) mark_env_parallel(obj->async.handle->env, queue);
      }
      break;
    default:
      break;
  }
}

static void mark_and_push(valk_lval_t *obj, void *ctx) {
  valk_gc_mark_queue_t *queue = ctx;

  if (obj == nullptr) return;
  if (obj->flags & LVAL_FLAG_IMMORTAL) return;
  if (!valk_gc_try_mark(obj)) return;

  if (!valk_gc_mark_queue_push(queue, obj)) {
    mark_children(obj, queue);
  }
}

static _Atomic u64 __gc_idle_count = 0;
static _Atomic bool __gc_terminated = false;

bool valk_gc_check_termination(void) {
  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  u64 idle = atomic_fetch_add(&__gc_idle_count, 1) + 1;

  if (idle == num_threads) {
    bool all_empty = true;
    for (u64 i = 0; i < num_threads; i++) {
      if (!valk_gc_coord.threads[i].active) continue;
      valk_gc_mark_queue_t *q = &valk_gc_coord.threads[i].mark_queue;
      if (!valk_gc_mark_queue_empty(q)) {
        all_empty = false;
        break;
      }
    }

    if (all_empty) {
      atomic_store(&__gc_terminated, true);
    }
  }

  for (int i = 0; i < 100; i++) {
    if (atomic_load(&__gc_terminated)) {
      return true;
    }
#if defined(__x86_64__) || defined(__i386__)
    __builtin_ia32_pause();
#else
    sched_yield();
#endif
  }

  atomic_fetch_sub(&__gc_idle_count, 1);
  return false;
}

void valk_gc_parallel_mark(void) {
  if (!valk_thread_ctx.gc_registered) return;

  u64 my_id = valk_thread_ctx.gc_thread_id;
  valk_gc_mark_queue_t *my_queue = &valk_gc_coord.threads[my_id].mark_queue;

  atomic_store(&__gc_idle_count, 0);
  atomic_store(&__gc_terminated, false);

  valk_gc_mark_queue_init(my_queue);

  valk_gc_visit_thread_roots(mark_and_push, my_queue);

  if (my_id == 0) {
    valk_gc_visit_global_roots(mark_and_push, my_queue);
  }

  valk_barrier_wait(&valk_gc_coord.barrier);

  u64 idle_spins = 0;
  const u64 MAX_IDLE_SPINS = 1000;

  while (true) {
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != nullptr) {
      mark_children(obj, my_queue);
      idle_spins = 0;
    }

    bool found_work = false;
    u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);

    for (u64 i = 1; i <= num_threads; i++) {
      u64 victim = (my_id + i) % num_threads;
      if (!valk_gc_coord.threads[victim].active) continue;

      obj = valk_gc_mark_queue_steal(&valk_gc_coord.threads[victim].mark_queue);
      if (obj != nullptr) {
        mark_children(obj, my_queue);
        found_work = true;
        idle_spins = 0;
        break;
      }
    }

    if (!found_work) {
      idle_spins++;
      if (idle_spins >= MAX_IDLE_SPINS) {
        if (valk_gc_check_termination()) {
          break;
        }
        idle_spins = 0;
      }
      sched_yield();
    }
  }
}
// LCOV_EXCL_STOP



// Forward declarations
static void valk_gc_mark_lval(valk_lval_t* v);
static void valk_gc_mark_env(valk_lenv_t* env);

// ============================================================================
// GC Heap - Legacy API wrappers around valk_gc_heap2_t
// ============================================================================

// Initialize GC heap (now delegates to valk_gc_heap2_create)
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(sz hard_limit) {
  return valk_gc_heap2_create(hard_limit);
}

// Set hard limit for GC heap
void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, sz limit) {
  if (!heap) return;
  sz used = valk_gc_heap2_used_bytes(heap);
  if (limit < used) {
    VALK_WARN("Cannot set hard limit below current usage (%zu < %zu)", limit, used);
    return;
  }
  heap->hard_limit = limit;
  heap->soft_limit = (limit * 3) / 4;
}

// Set root environment for GC marking
void valk_gc_malloc_set_root(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env) {
  if (heap) heap->root_env = root_env;
}

// Get heap usage as percentage (0-100)
u8 valk_gc_heap_usage_pct(valk_gc_malloc_heap_t* heap) {
  if (!heap || heap->hard_limit == 0) return 0;
  sz used = valk_gc_heap2_used_bytes(heap);
  u8 pct = (u8)((used * 100) / heap->hard_limit);
  return pct > 100 ? 100 : pct;
}

// Configure GC thresholds
void valk_gc_set_thresholds(valk_gc_malloc_heap_t* heap,
                            u8 threshold_pct,
                            u8 target_pct,
                            u32 min_interval_ms) {
  if (!heap) return;
  heap->gc_threshold_pct = threshold_pct > 0 ? threshold_pct : 75;
  heap->gc_target_pct = target_pct > 0 ? target_pct : 50;
  heap->min_gc_interval_ms = min_interval_ms;
}

// Check if GC should run
// LCOV_EXCL_BR_START - rate limiting branches depend on timing state
bool valk_gc_malloc_should_collect(valk_gc_malloc_heap_t* heap) {
  if (!heap) return false;
  u8 usage_pct = valk_gc_heap_usage_pct(heap);
  if (usage_pct < heap->gc_threshold_pct) return false;
  if (heap->min_gc_interval_ms > 0 && heap->last_gc_time_us > 0) {
    u64 now_us = uv_hrtime() / 1000;
    u64 elapsed_ms = (now_us - heap->last_gc_time_us) / 1000;
    if (elapsed_ms < heap->min_gc_interval_ms) return false;
  }
  return true;
}
// LCOV_EXCL_BR_STOP

// Allocate from GC heap (delegates to heap2)
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, sz bytes) {
  return valk_gc_heap2_alloc(heap, bytes);
}


// ============================================================================
// Legacy GC API - Implemented using valk_gc_heap2_t
// ============================================================================

// Perform mark & sweep collection (delegates to heap2)
// Uses collect_auto which coordinates STW with other threads when multi-threaded
sz valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap, valk_lval_t* additional_root) {
  if (!heap) return 0;
  (void)additional_root;
  return valk_gc_heap2_collect_auto(heap);
}

// Destroy heap (delegates to heap2)
void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap) {
  valk_gc_heap2_destroy(heap);
}

// ============================================================================
// GC Runtime Metrics Export
// ============================================================================

void valk_gc_get_runtime_metrics(valk_gc_malloc_heap_t* heap,
                                  u64* cycles, u64* pause_us_total,
                                  u64* pause_us_max, sz* reclaimed,
                                  sz* heap_used, sz* heap_total) {
  if (!heap) return;

  if (cycles) *cycles = atomic_load(&heap->runtime_metrics.cycles_total);
  if (pause_us_total) *pause_us_total = atomic_load(&heap->runtime_metrics.pause_us_total);
  if (pause_us_max) *pause_us_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  if (reclaimed) *reclaimed = atomic_load(&heap->runtime_metrics.reclaimed_bytes_total);

  if (heap_used) *heap_used = valk_gc_heap2_used_bytes(heap);
  if (heap_total) *heap_total = heap->hard_limit;
}

sz valk_gc_get_allocated_bytes_total(valk_gc_malloc_heap_t* heap) {
  if (!heap) return 0;
  return atomic_load(&heap->runtime_metrics.allocated_bytes_total);
}

u8 valk_gc_get_last_efficiency(valk_gc_malloc_heap_t* heap) {
  if (!heap) return 0;
  sz before = atomic_load(&heap->runtime_metrics.last_heap_before_gc);
  sz reclaimed = atomic_load(&heap->runtime_metrics.last_reclaimed);
  if (before == 0) return 0;
  sz pct = (reclaimed * 100) / before;
  return (u8)(pct > 100 ? 100 : pct);
}

void valk_gc_get_survival_histogram(valk_gc_malloc_heap_t* heap,
                                     u64* gen_0, u64* gen_1_5,
                                     u64* gen_6_20, u64* gen_21_plus) {
  if (!heap) return;
  if (gen_0) *gen_0 = atomic_load(&heap->runtime_metrics.survival_gen_0);
  if (gen_1_5) *gen_1_5 = atomic_load(&heap->runtime_metrics.survival_gen_1_5);
  if (gen_6_20) *gen_6_20 = atomic_load(&heap->runtime_metrics.survival_gen_6_20);
  if (gen_21_plus) *gen_21_plus = atomic_load(&heap->runtime_metrics.survival_gen_21_plus);
}

void valk_gc_get_pause_histogram(valk_gc_malloc_heap_t* heap,
                                  u64* pause_0_1ms, u64* pause_1_5ms,
                                  u64* pause_5_10ms, u64* pause_10_16ms,
                                  u64* pause_16ms_plus) {
  if (!heap) return;
  if (pause_0_1ms) *pause_0_1ms = atomic_load(&heap->runtime_metrics.pause_0_1ms);
  if (pause_1_5ms) *pause_1_5ms = atomic_load(&heap->runtime_metrics.pause_1_5ms);
  if (pause_5_10ms) *pause_5_10ms = atomic_load(&heap->runtime_metrics.pause_5_10ms);
  if (pause_10_16ms) *pause_10_16ms = atomic_load(&heap->runtime_metrics.pause_10_16ms);
  if (pause_16ms_plus) *pause_16ms_plus = atomic_load(&heap->runtime_metrics.pause_16ms_plus);
}

void valk_gc_get_fragmentation(valk_gc_malloc_heap_t* heap, valk_fragmentation_t* out) {
  if (!heap || !out) return;
  memset(out, 0, sizeof(*out));

  out->lval_slab_total = 0;
  out->lval_slab_used = 0;
  out->lval_slab_peak = 0;
  out->lval_fragmentation = 0;

  out->lenv_slab_total = 0;
  out->lenv_slab_used = 0;
  out->lenv_slab_peak = 0;
  out->lenv_fragmentation = 0;

  out->malloc_allocated = valk_gc_heap2_used_bytes(heap);
  out->malloc_limit = heap->hard_limit;
  out->malloc_peak = atomic_load(&heap->stats.peak_usage);

  out->free_list_count = 0;
  out->free_list_bytes = 0;
}

// ============================================================================
// GC Statistics Printing (heap2)
// ============================================================================

void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap) {
  if (heap == nullptr) return;

  valk_gc_stats2_t stats;
  valk_gc_heap2_get_stats(heap, &stats);

  fprintf(stderr, "\n=== GC Heap Statistics ===\n");
  u8 usage_pct = valk_gc_heap_usage_pct(heap);
  fprintf(stderr, "Heap usage:       %u%% (threshold: %u%%, hard limit: %zu bytes)\n",
          usage_pct, heap->gc_threshold_pct, heap->hard_limit);
  fprintf(stderr, "Used bytes:       %zu bytes\n", stats.used_bytes);
  fprintf(stderr, "Committed bytes:  %zu bytes\n", stats.committed_bytes);
  fprintf(stderr, "Large objects:    %zu bytes\n", stats.large_object_bytes);
  fprintf(stderr, "Peak usage:       %zu bytes\n", atomic_load(&heap->stats.peak_usage));
  fprintf(stderr, "Collections:      %llu\n", (unsigned long long)stats.collections);
  fprintf(stderr, "Emergency GCs:    %llu\n", (unsigned long long)heap->stats.emergency_collections);

  fprintf(stderr, "--- Per-Class Usage ---\n");
  // LCOV_EXCL_START - conditional output formatting for debug/diagnostic use
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    if (stats.class_total_slots[c] > 0) {
      u64 pct = (stats.class_used_slots[c] * 100) / stats.class_total_slots[c];
      fprintf(stderr, "  Class %d (%4u B): %llu / %llu slots (%llu%%)\n",
              c, valk_gc_size_classes[c],
              (unsigned long long)stats.class_used_slots[c], (unsigned long long)stats.class_total_slots[c], (unsigned long long)pct);
    }
  }

  if (heap->stats.evacuations_from_scratch > 0) {
    fprintf(stderr, "--- Evacuation Stats ---\n");
    fprintf(stderr, "Values evacuated: %llu\n", (unsigned long long)heap->stats.evacuations_from_scratch);
    fprintf(stderr, "Bytes evacuated:  %zu\n", heap->stats.evacuation_bytes);
    fprintf(stderr, "Pointers fixed:   %llu\n", (unsigned long long)heap->stats.evacuation_pointer_fixups);
  }
  // LCOV_EXCL_STOP
  fprintf(stderr, "=========================\n\n");
}

void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out) {
  if (out == nullptr) out = stderr;

  fprintf(out, "\n=== Memory Statistics ===\n");

  if (scratch != nullptr) {
    double usage = (double)scratch->offset / scratch->capacity * 100.0;
    u64 overflow_fallbacks = atomic_load_explicit(&scratch->stats.overflow_fallbacks, memory_order_relaxed);
    fprintf(out, "Scratch Arena:\n");
    fprintf(out, "  Usage:       %.1f%% (%zu / %zu bytes)\n",
            usage, scratch->offset, scratch->capacity);
    fprintf(out, "  High Water:  %zu bytes\n",
            atomic_load_explicit(&scratch->stats.high_water_mark, memory_order_relaxed));
    fprintf(out, "  Allocations: %llu\n",
            (unsigned long long)atomic_load_explicit(&scratch->stats.total_allocations, memory_order_relaxed));
    fprintf(out, "  Resets:      %llu\n",
            (unsigned long long)atomic_load_explicit(&scratch->stats.num_resets, memory_order_relaxed));
    fprintf(out, "  Checkpoints: %llu\n",
            (unsigned long long)atomic_load_explicit(&scratch->stats.num_checkpoints, memory_order_relaxed));
    if (overflow_fallbacks > 0) {
      fprintf(out, "  Overflows:   %llu (%zu bytes)\n",
              (unsigned long long)overflow_fallbacks,
              atomic_load_explicit(&scratch->stats.overflow_bytes, memory_order_relaxed));
    }
    fprintf(out, "\n");
  }

  if (heap != nullptr) {
    valk_gc_stats2_t stats;
    valk_gc_heap2_get_stats(heap, &stats);

    double usage = (double)stats.used_bytes / heap->hard_limit * 100.0;
    fprintf(out, "GC Heap (heap2):\n");
    fprintf(out, "  Usage:       %.1f%% (%zu / %zu bytes)\n",
            usage, stats.used_bytes, heap->hard_limit);
    fprintf(out, "  Committed:   %zu bytes\n", stats.committed_bytes);
    fprintf(out, "  Large objs:  %zu bytes\n", stats.large_object_bytes);
    fprintf(out, "  Collections: %llu\n", (unsigned long long)stats.collections);
    fprintf(out, "  Reclaimed:   %zu bytes total\n",
            stats.bytes_reclaimed_total);
  }

  fprintf(out, "=========================\n\n");
}

// ============================================================================
// Memory Snapshot for REPL Eval Tracking
// ============================================================================

void valk_repl_mem_take_snapshot(valk_gc_malloc_heap_t* heap, valk_mem_arena_t* scratch,
                                 valk_repl_mem_snapshot_t* out) {
  if (!out) return;
  memset(out, 0, sizeof(*out));

  if (heap) {
    out->heap_used_bytes = valk_gc_heap2_used_bytes(heap);
    out->lval_count = 0;
    out->lenv_count = 0;
  }

  if (scratch) {
    out->scratch_used_bytes = scratch->offset;
  }
}

void valk_repl_mem_snapshot_delta(valk_repl_mem_snapshot_t* before, valk_repl_mem_snapshot_t* after,
                                  i64* heap_delta, i64* scratch_delta,
                                  i64* lval_delta, i64* lenv_delta) {
  if (!before || !after) return;
  if (heap_delta) *heap_delta = (i64)after->heap_used_bytes - (i64)before->heap_used_bytes;
  if (scratch_delta) *scratch_delta = (i64)after->scratch_used_bytes - (i64)before->scratch_used_bytes;
  if (lval_delta) *lval_delta = (i64)after->lval_count - (i64)before->lval_count;
  if (lenv_delta) *lenv_delta = (i64)after->lenv_count - (i64)before->lenv_count;
}

// ============================================================================
// REPL Eval Delta Tracking (for dashboard REPL profile)
// ============================================================================

static valk_repl_eval_delta_t g_repl_eval_delta = {0};
static bool g_repl_eval_delta_valid = false;

bool valk_repl_get_last_eval_delta(valk_repl_eval_delta_t* out) {
  if (!out || !g_repl_eval_delta_valid) return false;
  *out = g_repl_eval_delta;
  return true;
}

void valk_repl_set_eval_delta(i64 heap, i64 scratch, i64 lval, i64 lenv) {
  g_repl_eval_delta.heap_delta = heap;
  g_repl_eval_delta.scratch_delta = scratch;
  g_repl_eval_delta.lval_delta = lval;
  g_repl_eval_delta.lenv_delta = lenv;
  g_repl_eval_delta.eval_count++;
  g_repl_eval_delta_valid = true;
}

// ============================================================================
// Pointer Map - hashmap for src->dst tracking during evacuation
// ============================================================================

// LCOV_EXCL_BR_START - internal hash map operations with collision handling
static inline sz valk_ptr_hash(void *ptr) {
  uptr p = (uptr)ptr;
  p = (p ^ (p >> 30)) * 0xbf58476d1ce4e5b9ULL;
  p = (p ^ (p >> 27)) * 0x94d049bb133111ebULL;
  return (sz)(p ^ (p >> 31));
}

void valk_ptr_map_init(valk_ptr_map_t *map) {
  map->capacity = VALK_PTR_MAP_INIT_CAPACITY;
  map->count = 0;
  map->entries = calloc(map->capacity, sizeof(valk_ptr_map_entry_t));
}

void valk_ptr_map_free(valk_ptr_map_t *map) {
  if (map->entries) {
    free(map->entries);
    map->entries = nullptr;
  }
  map->count = 0;
  map->capacity = 0;
}

static void valk_ptr_map_grow(valk_ptr_map_t *map) {
  sz old_cap = map->capacity;
  valk_ptr_map_entry_t *old_entries = map->entries;
  
  map->capacity = old_cap * 2;
  map->entries = calloc(map->capacity, sizeof(valk_ptr_map_entry_t));
  map->count = 0;
  
  for (sz i = 0; i < old_cap; i++) {
    if (old_entries[i].src != nullptr) {
      valk_ptr_map_put(map, old_entries[i].src, old_entries[i].dst);
    }
  }
  
  free(old_entries);
}

void valk_ptr_map_put(valk_ptr_map_t *map, void *src, void *dst) {
  if ((float)map->count / map->capacity >= VALK_PTR_MAP_LOAD_FACTOR) {
    valk_ptr_map_grow(map);
  }
  
  sz idx = valk_ptr_hash(src) % map->capacity;
  while (map->entries[idx].src != nullptr) {
    if (map->entries[idx].src == src) {
      map->entries[idx].dst = dst;
      return;
    }
    idx = (idx + 1) % map->capacity;
  }
  
  map->entries[idx].src = src;
  map->entries[idx].dst = dst;
  map->count++;
}

void *valk_ptr_map_get(valk_ptr_map_t *map, void *src) {
  if (map->count == 0) return nullptr;
  
  sz idx = valk_ptr_hash(src) % map->capacity;
  sz start = idx;
  
  while (map->entries[idx].src != nullptr) {
    if (map->entries[idx].src == src) {
      return map->entries[idx].dst;
    }
    idx = (idx + 1) % map->capacity;
    if (idx == start) break;
  }
  
  return nullptr;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Handle Table - for cross-region references
// ============================================================================

// LCOV_EXCL_BR_START - handle table internal defensive checks
valk_handle_table_t valk_global_handle_table = {0};

void valk_handle_table_init(valk_handle_table_t *table) {
  pthread_mutex_init(&table->lock, nullptr);
  table->capacity = VALK_HANDLE_TABLE_INIT_SIZE;
  table->count = 0;
  table->free_head = UINT32_MAX;
  table->slots = calloc(table->capacity, sizeof(valk_lval_t *));
  table->generations = calloc(table->capacity, sizeof(u32));
}

void valk_handle_table_free(valk_handle_table_t *table) {
  pthread_mutex_lock(&table->lock);
  if (table->slots) {
    free(table->slots);
    table->slots = nullptr;
  }
  if (table->generations) {
    free(table->generations);
    table->generations = nullptr;
  }
  table->capacity = 0;
  table->count = 0;
  table->free_head = UINT32_MAX;
  pthread_mutex_unlock(&table->lock);
  pthread_mutex_destroy(&table->lock);
}

static void valk_handle_table_grow(valk_handle_table_t *table) {
  u32 old_cap = table->capacity;
  u32 new_cap = old_cap * 2;

  valk_lval_t **new_slots = realloc(table->slots, new_cap * sizeof(valk_lval_t *));
  u32 *new_gens = realloc(table->generations, new_cap * sizeof(u32));

  // LCOV_EXCL_BR_START - handle table realloc OOM
  if (!new_slots || !new_gens) {
    VALK_ERROR("Failed to grow handle table");
    return;
  }
  // LCOV_EXCL_BR_STOP
  
  table->slots = new_slots;
  table->generations = new_gens;
  
  for (u32 i = old_cap; i < new_cap; i++) {
    table->slots[i] = nullptr;
    table->generations[i] = 0;
  }
  
  table->capacity = new_cap;
}

valk_handle_t valk_handle_create(valk_handle_table_t *table, valk_lval_t *val) {
  pthread_mutex_lock(&table->lock);
  
  u32 idx;
  if (table->free_head != UINT32_MAX) {
    idx = table->free_head;
    table->free_head = (u32)(uptr)table->slots[idx];
  } else {
    if (table->count >= table->capacity) {
      valk_handle_table_grow(table);
    }
    idx = table->count++;
  }
  
  table->slots[idx] = val;
  table->generations[idx]++;
  
  valk_handle_t h = {.index = idx, .generation = table->generations[idx]};
  pthread_mutex_unlock(&table->lock);
  return h;
}

valk_lval_t *valk_handle_resolve(valk_handle_table_t *table, valk_handle_t h) {
  pthread_mutex_lock(&table->lock);
  valk_lval_t *result = nullptr;
  if (h.index < table->capacity && table->generations[h.index] == h.generation) {
    result = table->slots[h.index];
  }
  pthread_mutex_unlock(&table->lock);
  return result;
}

void valk_handle_release(valk_handle_table_t *table, valk_handle_t h) {
  pthread_mutex_lock(&table->lock);
  if (h.index < table->capacity && table->generations[h.index] == h.generation) {
    table->slots[h.index] = (valk_lval_t *)(uptr)table->free_head;
    table->free_head = h.index;
  }
  pthread_mutex_unlock(&table->lock);
}

void valk_handle_table_visit(valk_handle_table_t *table,
                             void (*visitor)(valk_lval_t*, void*), void *ctx) {
  if (!table || !table->slots) return;
  
  pthread_mutex_lock(&table->lock);
  for (u32 i = 0; i < table->count; i++) {
    valk_lval_t *val = table->slots[i];
    if (val != nullptr && ((uptr)val > table->capacity)) {
      visitor(val, ctx);
    }
  }
  pthread_mutex_unlock(&table->lock);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Region API Implementation
// ============================================================================

// LCOV_EXCL_BR_START - region API defensive null checks and lifetime switches
#define VALK_REGION_DEFAULT_SIZE (64 * 1024)

void valk_region_init(valk_region_t *region, valk_lifetime_e lifetime, 
                      valk_region_t *parent, valk_mem_arena_t *arena) {
  region->type = VALK_ALLOC_REGION;
  region->lifetime = lifetime;
  region->parent = parent;
  region->arena = arena;
  region->owns_arena = false;
  region->gc_heap = nullptr;
  memset(&region->stats, 0, sizeof(region->stats));
  
  if (lifetime == VALK_LIFETIME_SESSION) {
    region->gc_heap = valk_runtime_get_heap();
  }
}

// LCOV_EXCL_BR_START - region creation switch/OOM branches
valk_region_t *valk_region_create(valk_lifetime_e lifetime, valk_region_t *parent) {
  valk_region_t *region = malloc(sizeof(valk_region_t));
  if (!region) return nullptr;

  region->type = VALK_ALLOC_REGION;
  region->lifetime = lifetime;
  region->parent = parent;
  region->gc_heap = nullptr;
  region->arena = nullptr;
  region->owns_arena = false;
  memset(&region->stats, 0, sizeof(region->stats));

  switch (lifetime) {
    case VALK_LIFETIME_IMMORTAL:
      break;

    case VALK_LIFETIME_SESSION:
      region->gc_heap = valk_runtime_get_heap();
      break;

    case VALK_LIFETIME_REQUEST:
    case VALK_LIFETIME_SCRATCH: {
      sz arena_size = sizeof(valk_mem_arena_t) + VALK_REGION_DEFAULT_SIZE;
      region->arena = malloc(arena_size);
      if (!region->arena) {
        free(region);
        return nullptr;
      }
      valk_mem_arena_init(region->arena, VALK_REGION_DEFAULT_SIZE);
      region->owns_arena = true;
      break;
    }
  }
  
  return region;
}

valk_region_t *valk_region_create_with_arena(valk_lifetime_e lifetime, 
                                              valk_region_t *parent,
                                              valk_mem_arena_t *arena) {
  valk_region_t *region = malloc(sizeof(valk_region_t));
  if (!region) return nullptr;
  
  region->type = VALK_ALLOC_REGION;
  region->lifetime = lifetime;
  region->parent = parent;
  region->arena = arena;
  region->owns_arena = false;
  region->gc_heap = nullptr;
  memset(&region->stats, 0, sizeof(region->stats));
  
  if (lifetime == VALK_LIFETIME_SESSION) {
    region->gc_heap = valk_runtime_get_heap();
  }
  
  return region;
}

void valk_region_destroy(valk_region_t *region) {
  if (!region) return;
  
  if (region->arena && region->owns_arena) {
    free(region->arena);
    region->arena = nullptr;
  }
  
  free(region);
}

void valk_region_reset(valk_region_t *region) {
  if (!region) return;
  
  if (region->arena) {
    valk_mem_arena_reset(region->arena);
  }
  
  sz limit = region->stats.bytes_limit;
  atomic_store_explicit(&region->stats.bytes_allocated, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.bytes_promoted, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.alloc_count, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.promotion_count, 0, memory_order_relaxed);
  atomic_store_explicit(&region->stats.overflow_count, 0, memory_order_relaxed);
  region->stats.bytes_limit = limit;
}

void *valk_region_alloc(valk_region_t *region, sz bytes) {
  if (!region) return nullptr;
  
  sz limit = region->stats.bytes_limit;
  if (limit > 0) {
    sz current = atomic_load_explicit(&region->stats.bytes_allocated, memory_order_relaxed);
    if (current + bytes > limit) {
      if (region->parent) {
        atomic_fetch_add_explicit(&region->stats.overflow_count, 1, memory_order_relaxed);
        return valk_region_alloc(region->parent, bytes);
      }
      return nullptr;
    }
  }
  
  void *ptr = nullptr;
  
  switch (region->lifetime) {
    case VALK_LIFETIME_IMMORTAL:
      return nullptr;
      
    case VALK_LIFETIME_SESSION:
      if (region->gc_heap) {
        ptr = valk_gc_heap2_alloc(region->gc_heap, bytes);
      }
      break;
      
    case VALK_LIFETIME_REQUEST:
    case VALK_LIFETIME_SCRATCH:
      if (region->arena) {
        ptr = valk_mem_arena_alloc(region->arena, bytes);
      }
      if (!ptr && region->parent) {
        atomic_fetch_add_explicit(&region->stats.overflow_count, 1, memory_order_relaxed);
        return valk_region_alloc(region->parent, bytes);
      }
      break;
  }
  
  if (ptr) {
    atomic_fetch_add_explicit(&region->stats.bytes_allocated, bytes, memory_order_relaxed);
    atomic_fetch_add_explicit(&region->stats.alloc_count, 1, memory_order_relaxed);
  }
  
  return ptr;
}

bool valk_region_set_limit(valk_region_t *region, sz limit) {
  if (!region) return false;
  if (limit > 0 && atomic_load_explicit(&region->stats.bytes_allocated, memory_order_relaxed) > limit) {
    return false;
  }
  region->stats.bytes_limit = limit;
  return true;
}

void valk_region_get_stats(valk_region_t *region, valk_region_stats_t *out) {
  if (!region || !out) return;
  atomic_store_explicit(&out->bytes_allocated, 
      atomic_load_explicit(&region->stats.bytes_allocated, memory_order_relaxed), memory_order_relaxed);
  out->bytes_limit = region->stats.bytes_limit;
  atomic_store_explicit(&out->bytes_promoted,
      atomic_load_explicit(&region->stats.bytes_promoted, memory_order_relaxed), memory_order_relaxed);
  atomic_store_explicit(&out->alloc_count,
      atomic_load_explicit(&region->stats.alloc_count, memory_order_relaxed), memory_order_relaxed);
  atomic_store_explicit(&out->promotion_count,
      atomic_load_explicit(&region->stats.promotion_count, memory_order_relaxed), memory_order_relaxed);
  atomic_store_explicit(&out->overflow_count,
      atomic_load_explicit(&region->stats.overflow_count, memory_order_relaxed), memory_order_relaxed);
}

// ============================================================================
// Cross-Region Reference Checking
// ============================================================================

valk_lifetime_e valk_allocator_lifetime(void *allocator) {
  if (!allocator) return VALK_LIFETIME_SCRATCH;
  
  valk_mem_allocator_t *alloc = (valk_mem_allocator_t *)allocator;
  switch (alloc->type) {
    case VALK_ALLOC_REGION: {
      valk_region_t *region = (valk_region_t *)allocator;
      return region->lifetime;
    }
    case VALK_ALLOC_GC_HEAP:
      return VALK_LIFETIME_SESSION;
    case VALK_ALLOC_ARENA:
      return VALK_LIFETIME_SCRATCH;
    case VALK_ALLOC_MALLOC:
      return VALK_LIFETIME_IMMORTAL;
    default:
      return VALK_LIFETIME_SCRATCH;
  }
}

bool valk_region_write_barrier(void *parent_allocator, void *child_allocator,
                                bool promote_on_escape) {
  if (!parent_allocator || !child_allocator) return true;
  
  valk_lifetime_e parent_lifetime = valk_allocator_lifetime(parent_allocator);
  valk_lifetime_e child_lifetime = valk_allocator_lifetime(child_allocator);
  
  if (valk_lifetime_can_reference(parent_lifetime, child_lifetime)) {
    return true;
  }
  
  if (promote_on_escape) {
    return false;
  }
  
  return false;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_START - region copy requires specific inter-region promotion scenario with complex values
static valk_lval_t *region_copy_lval_recursive(valk_region_t *target, valk_lval_t *src,
                                                valk_ptr_map_t *copied) {
  if (!src) return nullptr;

  valk_lval_t *existing = valk_ptr_map_get(copied, src);
  if (existing) return existing;

  valk_lifetime_e src_lifetime = valk_allocator_lifetime(src->origin_allocator);
  if (valk_lifetime_can_reference(target->lifetime, src_lifetime)) {
    return src;
  }

  sz lval_size = sizeof(valk_lval_t);
  valk_lval_t *copy = valk_region_alloc(target, lval_size);
  if (!copy) return nullptr;

  memcpy(copy, src, lval_size);
  copy->origin_allocator = target;
  copy->gc_next = nullptr;

  valk_ptr_map_put(copied, src, copy);

  valk_ltype_e type = LVAL_TYPE(src);
  switch (type) {
    case LVAL_CONS:
      copy->cons.head = region_copy_lval_recursive(target, src->cons.head, copied);
      copy->cons.tail = region_copy_lval_recursive(target, src->cons.tail, copied);
      break;

    case LVAL_FUN:
      if (src->fun.name) {
        sz len = strlen(src->fun.name) + 1;
        copy->fun.name = valk_region_alloc(target, len);
        if (copy->fun.name) memcpy(copy->fun.name, src->fun.name, len);
      }
      copy->fun.formals = region_copy_lval_recursive(target, src->fun.formals, copied);
      copy->fun.body = region_copy_lval_recursive(target, src->fun.body, copied);
      break;

    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      if (src->str) {
        sz len = strlen(src->str) + 1;
        copy->str = valk_region_alloc(target, len);
        if (copy->str) memcpy(copy->str, src->str, len);
      }
      break;

    default:
      break;
  }

  atomic_fetch_add_explicit(&target->stats.bytes_promoted, lval_size, memory_order_relaxed);
  atomic_fetch_add_explicit(&target->stats.promotion_count, 1, memory_order_relaxed);

  return copy;
}
// LCOV_EXCL_STOP

valk_lval_t *valk_region_promote_lval(valk_region_t *target, valk_lval_t *val) {
  if (!target || !val) return val;
  
  valk_lifetime_e val_lifetime = valk_allocator_lifetime(val->origin_allocator);
  if (valk_lifetime_can_reference(target->lifetime, val_lifetime)) {
    return val;
  }
  
  valk_ptr_map_t copied;
  valk_ptr_map_init(&copied);
  
  valk_lval_t *promoted = region_copy_lval_recursive(target, val, &copied);
  
  valk_ptr_map_free(&copied);
  
  return promoted;
}

valk_lval_t *valk_region_ensure_safe_ref(valk_lval_t *parent, valk_lval_t *child) {
  if (!parent || !child) return child;
  
  void *parent_alloc = parent->origin_allocator;
  void *child_alloc = child->origin_allocator;
  
  if (!parent_alloc || !child_alloc) return child;
  
  if (valk_region_write_barrier(parent_alloc, child_alloc, false)) {
    return child;
  }
  
  valk_mem_allocator_t *alloc = (valk_mem_allocator_t *)parent_alloc;
  if (alloc->type == VALK_ALLOC_REGION) {
    return valk_region_promote_lval((valk_region_t *)parent_alloc, child);
  }
  
  return child;
}

// ============================================================================
// Environment and Lval Worklists for Iterative Traversal
// ============================================================================

// LCOV_EXCL_BR_START - worklist internal defensive checks and growth paths
#define ENV_WORKLIST_INITIAL_CAPACITY 64

typedef struct {
  valk_lenv_t** items;
  sz count;
  sz capacity;
} valk_env_worklist_t;

static void env_worklist_init(valk_env_worklist_t* wl) {
  wl->items = malloc(ENV_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lenv_t*));
  wl->count = 0;
  wl->capacity = ENV_WORKLIST_INITIAL_CAPACITY;
}

static void env_worklist_free(valk_env_worklist_t* wl) {
  if (wl->items) {
    free(wl->items);
    wl->items = nullptr;
  }
  wl->count = 0;
  wl->capacity = 0;
}

static void env_worklist_push(valk_env_worklist_t* wl, valk_lenv_t* env) {
  if (env == nullptr) return;
  if (wl->count >= wl->capacity) {
    sz new_cap = wl->capacity * 2;
    valk_lenv_t** new_items = realloc(wl->items, new_cap * sizeof(valk_lenv_t*));
    if (new_items == nullptr) {
      VALK_ERROR("Failed to grow env worklist");
      return;
    }
    wl->items = new_items;
    wl->capacity = new_cap;
  }
  wl->items[wl->count++] = env;
}

static valk_lenv_t* env_worklist_pop(valk_env_worklist_t* wl) {
  if (wl->count == 0) return nullptr;
  return wl->items[--wl->count];
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Checkpoint-based Evacuation (Phase 3)
// ============================================================================

// LCOV_EXCL_BR_START - evacuation context internal defensive checks
// Initial worklist capacity
#define EVAC_WORKLIST_INITIAL_CAPACITY 256

// Initialize evacuation context lists
static void evac_ctx_init(valk_evacuation_ctx_t* ctx) {
  ctx->worklist = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->worklist_count = 0;
  ctx->worklist_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;

  ctx->evacuated = malloc(EVAC_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = EVAC_WORKLIST_INITIAL_CAPACITY;
  
  valk_ptr_map_init(&ctx->ptr_map);
}

// Free evacuation context lists
static void evac_ctx_free(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist) {
    free(ctx->worklist);
    ctx->worklist = nullptr;
  }
  ctx->worklist_count = 0;
  ctx->worklist_capacity = 0;

  if (ctx->evacuated) {
    free(ctx->evacuated);
    ctx->evacuated = nullptr;
  }
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = 0;
  
  valk_ptr_map_free(&ctx->ptr_map);
}

// Add value to evacuated list (for pointer fixing phase)
static void evac_add_evacuated(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;

  // Grow if at capacity
  // LCOV_EXCL_BR_START - evacuation list realloc OOM
  if (ctx->evacuated_count >= ctx->evacuated_capacity) {
    sz new_cap = ctx->evacuated_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->evacuated, new_cap * sizeof(valk_lval_t*));
    if (new_list == nullptr) {
      VALK_ERROR("Failed to grow evacuated list");
      return;
    }
    ctx->evacuated = new_list;
    ctx->evacuated_capacity = new_cap;
  }
  // LCOV_EXCL_BR_STOP

  ctx->evacuated[ctx->evacuated_count++] = v;
}

// Push value to worklist
static void evac_worklist_push(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;

  // Grow if at capacity
  // LCOV_EXCL_BR_START - worklist realloc OOM
  if (ctx->worklist_count >= ctx->worklist_capacity) {
    sz new_cap = ctx->worklist_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->worklist, new_cap * sizeof(valk_lval_t*));
    if (new_list == nullptr) {
      VALK_ERROR("Failed to grow evacuation worklist");
      return;
    }
    ctx->worklist = new_list;
    ctx->worklist_capacity = new_cap;
  }
  // LCOV_EXCL_BR_STOP

  ctx->worklist[ctx->worklist_count++] = v;
}

// Pop value from worklist
static valk_lval_t* evac_worklist_pop(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist_count == 0) return nullptr;
  return ctx->worklist[--ctx->worklist_count];
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// GC Marking Functions (legacy wrappers for heap2)
// ============================================================================

// LCOV_EXCL_BR_START - GC marking null checks and type dispatch
static void valk_gc_mark_lval(valk_lval_t* v) {
  if (v == nullptr) return;
  if (v->flags & LVAL_FLAG_IMMORTAL) return;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return;
  if (v->flags & LVAL_FLAG_GC_MARK) return;
  v->flags |= LVAL_FLAG_GC_MARK;

  switch (LVAL_TYPE(v)) {
    case LVAL_FUN:
      if (v->fun.env) valk_gc_mark_env(v->fun.env);
      valk_gc_mark_lval(v->fun.formals);
      valk_gc_mark_lval(v->fun.body);
      break;
    case LVAL_CONS:
      valk_gc_mark_lval(v->cons.head);
      valk_gc_mark_lval(v->cons.tail);
      break;
    case LVAL_HANDLE:
      if (v->async.handle) {
        valk_gc_mark_lval(v->async.handle->on_complete);
        valk_gc_mark_lval(v->async.handle->on_error);
        valk_gc_mark_lval(v->async.handle->on_cancel);
        valk_gc_mark_lval(atomic_load_explicit(&v->async.handle->result, memory_order_acquire));
        valk_gc_mark_lval(atomic_load_explicit(&v->async.handle->error, memory_order_acquire));
        if (v->async.handle->env) valk_gc_mark_env(v->async.handle->env);
      }
      break;
    default:
      break;
  }
}

static void valk_gc_mark_env(valk_lenv_t* env) {
  if (env == nullptr) return;
  for (u64 i = 0; i < env->vals.count; i++) {
    valk_gc_mark_lval(env->vals.items[i]);
  }
  if (env->parent) valk_gc_mark_env(env->parent);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// External GC marking functions
// ============================================================================

// Mark an lval and all its children (wrapper around internal function)
void valk_gc_mark_lval_external(valk_lval_t* v) {
  valk_gc_mark_lval(v);
}

// Mark an environment and all its contents (wrapper around internal function)
void valk_gc_mark_env_external(valk_lenv_t* env) {
  valk_gc_mark_env(env);
}

// Check if checkpoint should be triggered
bool valk_should_checkpoint(valk_mem_arena_t* scratch, float threshold) {
  if (scratch == nullptr) return false;
  return (float)scratch->offset / scratch->capacity > threshold;
}

// Forward declarations for evacuation helpers
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);

// LCOV_EXCL_START - evacuation checkpoint requires active eval stack from evaluator
static inline void evac_value_and_process_env(valk_evacuation_ctx_t* ctx, valk_lval_t** ptr) {
  valk_lval_t* val = *ptr;
  if (val == nullptr) return;
  valk_lval_t* new_val = valk_evacuate_value(ctx, val);
  if (new_val != val) {
    *ptr = new_val;
  } else if (LVAL_TYPE(val) == LVAL_FUN && val->fun.builtin == nullptr && val->fun.env != nullptr) {
    valk_evacuate_env(ctx, val->fun.env);
  }
}

static void evac_checkpoint_eval_stack(valk_evacuation_ctx_t* ctx) {
  if (valk_thread_ctx.eval_stack == nullptr) return;

  valk_eval_stack_t* stack = (valk_eval_stack_t*)valk_thread_ctx.eval_stack;
  for (u64 i = 0; i < stack->count; i++) {
    valk_cont_frame_t* frame = &stack->frames[i];
    switch (frame->kind) {
      case CONT_EVAL_ARGS:
        evac_value_and_process_env(ctx, &frame->eval_args.func);
        evac_value_and_process_env(ctx, &frame->eval_args.remaining);
        break;
      case CONT_COLLECT_ARG:
        evac_value_and_process_env(ctx, &frame->collect_arg.func);
        evac_value_and_process_env(ctx, &frame->collect_arg.remaining);
        for (u64 j = 0; j < frame->collect_arg.count; j++) {
          evac_value_and_process_env(ctx, &frame->collect_arg.args[j]);
        }
        break;
      case CONT_IF_BRANCH:
        evac_value_and_process_env(ctx, &frame->if_branch.true_branch);
        evac_value_and_process_env(ctx, &frame->if_branch.false_branch);
        break;
      case CONT_DO_NEXT:
        evac_value_and_process_env(ctx, &frame->do_next.remaining);
        break;
      case CONT_SELECT_CHECK:
        evac_value_and_process_env(ctx, &frame->select_check.result_expr);
        evac_value_and_process_env(ctx, &frame->select_check.remaining);
        evac_value_and_process_env(ctx, &frame->select_check.original_args);
        break;
      case CONT_BODY_NEXT:
        evac_value_and_process_env(ctx, &frame->body_next.remaining);
        break;
      case CONT_CTX_DEADLINE:
        evac_value_and_process_env(ctx, &frame->ctx_deadline.body);
        break;
      case CONT_CTX_WITH:
        evac_value_and_process_env(ctx, &frame->ctx_with.value_expr);
        evac_value_and_process_env(ctx, &frame->ctx_with.body);
        break;
      default:
        break;
    }
  }

  evac_value_and_process_env(ctx, &valk_thread_ctx.eval_expr);
  evac_value_and_process_env(ctx, &valk_thread_ctx.eval_value);
}
// LCOV_EXCL_STOP



// ============================================================================
// Phase 1: Copy Values from Scratch to Heap
// ============================================================================

// LCOV_EXCL_BR_START - evacuation value copy null checks and type dispatch
// Evacuate a single value from scratch to heap using hashmap deduplication
// Returns the new location (or original if not in scratch or already copied)
// This is a single-pass approach - no forwarding pointers needed
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return nullptr;

  // Immortal objects are never evacuated
  if (v->flags & LVAL_FLAG_IMMORTAL) {
    return v;
  }

  // Not in scratch? Return as-is (already in heap or global)
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) {
    return v;
  }
  
  // Check if already copied using hashmap (replaces forward pointer check)
  void *existing = valk_ptr_map_get(&ctx->ptr_map, v);
  if (existing != nullptr) {
    return (valk_lval_t *)existing;
  }
  
  // Allocate new value in heap
  valk_lval_t* new_val = nullptr;
  VALK_WITH_ALLOC((void*)ctx->heap) {
    new_val = valk_mem_alloc(sizeof(valk_lval_t));
  }

  if (new_val == nullptr) {
    VALK_ERROR("Failed to allocate value during evacuation");
    return v;
  }

  // Register in hashmap BEFORE copying to handle cycles
  valk_ptr_map_put(&ctx->ptr_map, v, new_val);

  // Copy the value data
  memcpy(new_val, v, sizeof(valk_lval_t));

  // Update allocation flags: clear scratch, set heap
  new_val->flags = (new_val->flags & ~LVAL_ALLOC_MASK) | LVAL_ALLOC_HEAP;
  new_val->origin_allocator = ctx->heap;

  // Copy strings for string types (they're also in scratch arena)
  // If scratch is NULL but value was SCRATCH-allocated, conservatively copy all strings
  // This handles the case where evacuation runs from event loop thread without scratch context
  bool needs_string_copy = (ctx->scratch == nullptr);
  
  switch (LVAL_TYPE(new_val)) {
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      if (new_val->str != nullptr && 
          (needs_string_copy || valk_ptr_in_arena(ctx->scratch, new_val->str))) {
        u64 len = strlen(v->str) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->str = valk_mem_alloc(len);
        }
        if (new_val->str) {
          memcpy(new_val->str, v->str, len);
          ctx->bytes_copied += len;
        }
      }
      break;

    case LVAL_FUN:
      // Copy function name if it's a lambda (not builtin) and in scratch
      if (new_val->fun.name != nullptr && new_val->fun.builtin == nullptr &&
          (needs_string_copy || valk_ptr_in_arena(ctx->scratch, new_val->fun.name))) {
        u64 len = strlen(v->fun.name) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->fun.name = valk_mem_alloc(len);
        }
        if (new_val->fun.name) {
          memcpy(new_val->fun.name, v->fun.name, len);
          ctx->bytes_copied += len;
        }
      }
      break;

    case LVAL_REF:
      // Copy ref type string if it's in scratch
      if (new_val->ref.type != nullptr && 
          (needs_string_copy || valk_ptr_in_arena(ctx->scratch, new_val->ref.type))) {
        u64 len = strlen(v->ref.type) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->ref.type = valk_mem_alloc(len);
        }
        if (new_val->ref.type) {
          memcpy(new_val->ref.type, v->ref.type, len);
          ctx->bytes_copied += len;
        }
      }
      break;

    default:
      break;
  }

  // Add to evacuated list (still useful for stats and iteration)
  evac_add_evacuated(ctx, new_val);

  // Update stats
  ctx->values_copied++;
  ctx->bytes_copied += sizeof(valk_lval_t);

  return new_val;
}

// Evacuate children of a value (push to worklist for processing)
static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
      // Evacuate and queue head (only if freshly evacuated, not already processed)
      if (v->cons.head != nullptr) {
        valk_lval_t* old_head = v->cons.head;
        valk_lval_t* new_head = valk_evacuate_value(ctx, old_head);
        // LCOV_EXCL_START - invariant check: evacuation should never return scratch arena
        if ((void*)new_head == (void*)ctx->scratch) {
          fprintf(stderr, "BUG in evacuation: new_head == scratch! old_head=%p new_head=%p scratch=%p\n",
                  (void*)old_head, (void*)new_head, (void*)ctx->scratch);
          fprintf(stderr, "  old_head type=%d alloc=%llu\n", LVAL_TYPE(old_head), 
                  (unsigned long long)LVAL_ALLOC(old_head));
          abort();
        }
        // LCOV_EXCL_STOP
        if (new_head != old_head) {
          v->cons.head = new_head;
          // Only push if pointer changed (freshly evacuated from scratch)
          if (new_head != nullptr) {
            evac_worklist_push(ctx, new_head);
          }
        }
      }
      // Evacuate and queue tail (only if freshly evacuated, not already processed)
      if (v->cons.tail != nullptr) {
        valk_lval_t* old_tail = v->cons.tail;
        valk_lval_t* new_tail = valk_evacuate_value(ctx, old_tail);
        if (new_tail != old_tail) {
          v->cons.tail = new_tail;
          // Only push if pointer changed (freshly evacuated from scratch)
          if (new_tail != nullptr) {
            evac_worklist_push(ctx, new_tail);
          }
        }
      }
      break;

    case LVAL_FUN:
      // Evacuate function name string (for lambdas only, not builtins)
      // Original fun.name is strdup'd (raw malloc), new one will be GC-allocated
      // NOTE: We don't free the old name here because partial applications can
      // share the same name pointer. The strdup'd memory becomes unreachable
      // and leaks (small leak, typically just "<lambda>" strings).
      // TODO(networking): Consider using GC-allocated names from the start to avoid this leak.
      if (v->fun.name != nullptr && v->fun.builtin == nullptr &&
          !valk_ptr_in_arena(ctx->scratch, v->fun.name)) {
        u64 len = strlen(v->fun.name) + 1;
        char* new_name = nullptr;
        VALK_WITH_ALLOC((void*)ctx->heap) { new_name = valk_mem_alloc(len); }
        if (new_name) {
          memcpy(new_name, v->fun.name, len);
          v->fun.name = new_name;
          ctx->bytes_copied += len;
        }
      }

      if (v->fun.builtin == nullptr) {
        // Evacuate formals (only if freshly evacuated)
        if (v->fun.formals != nullptr) {
          valk_lval_t* old_formals = v->fun.formals;
          valk_lval_t* new_formals = valk_evacuate_value(ctx, old_formals);
          if (new_formals != old_formals) {
            v->fun.formals = new_formals;
            if (new_formals != nullptr) {
              evac_worklist_push(ctx, new_formals);
            }
          }
        }
        // Evacuate body (only if freshly evacuated)
        if (v->fun.body != nullptr) {
          valk_lval_t* old_body = v->fun.body;
          valk_lval_t* new_body = valk_evacuate_value(ctx, old_body);
          if (new_body != old_body) {
            v->fun.body = new_body;
            if (new_body != nullptr) {
              evac_worklist_push(ctx, new_body);
            }
          }
        }
        // Evacuate closure environment
        if (v->fun.env != nullptr) {
          valk_evacuate_env(ctx, v->fun.env);
        }
      }
      break;

    case LVAL_STR:
    case LVAL_SYM:
    case LVAL_ERR:
      // Evacuate ALL string data to GC heap unconditionally
      // This ensures GC heap self-containment (handles scratch AND libc malloc strings)
      if (v->str != nullptr) {
        u64 len = strlen(v->str) + 1;
        char* new_str = nullptr;
        VALK_WITH_ALLOC((void*)ctx->heap) { new_str = valk_mem_alloc(len); }
        if (new_str && new_str != v->str) {  // Only copy if got NEW allocation
          memcpy(new_str, v->str, len);
          v->str = new_str;
          ctx->bytes_copied += len;
        }
      }
      break;

    default:
      // Leaf types (NUM, REF, NIL) have no children
      break;
  }
}

// Process a single environment's arrays and values (non-recursive)
// Takes env_worklist to queue lambda envs for processing (avoids recursive calls)
static void valk_evacuate_env_single(valk_evacuation_ctx_t* ctx, valk_lenv_t* env,
                                     valk_env_worklist_t* env_worklist) {
  // If scratch is NULL, conservatively copy all arrays
  // This handles evacuation from event loop thread without scratch context
  bool needs_array_copy = (ctx->scratch == nullptr);
  
  // Evacuate symbol strings array if in scratch
  if (env->symbols.items != nullptr && 
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->symbols.items))) {
    u64 array_size = env->symbols.capacity * sizeof(char*);
    char** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_items = valk_mem_alloc(array_size);
    }
    if (new_items) {
      memcpy(new_items, env->symbols.items, env->symbols.count * sizeof(char*));
      env->symbols.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  // Evacuate ALL symbol strings to GC heap unconditionally
  // This ensures GC heap self-containment:
  // - Scratch strings get evacuated (normal case)
  // - Libc malloc strings get evacuated (builtins registered before GC init)
  // After first checkpoint, all symbols will be in GC heap
  // NOTE: Only iterate if symbols.items is valid, but don't early return - 
  // we still need to evacuate vals below!
  if (env->symbols.items != nullptr) {
    for (u64 i = 0; i < env->symbols.count; i++) {
      char* sym = env->symbols.items[i];
      if (sym == nullptr) continue;

      // Allocate new string in GC heap
      u64 len = strlen(sym) + 1;
      char* new_str = nullptr;
      VALK_WITH_ALLOC((void*)ctx->heap) {
        new_str = valk_mem_alloc(len);
      }
      if (new_str && new_str != sym) {  // Only copy if we got a NEW allocation
        memcpy(new_str, sym, len);
        env->symbols.items[i] = new_str;
        ctx->bytes_copied += len;
      }
    }
  }

  // Evacuate values array if in scratch
  if (env->vals.items != nullptr && 
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->vals.items))) {
    u64 array_size = env->vals.capacity * sizeof(valk_lval_t*);
    valk_lval_t** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_items = valk_mem_alloc(array_size);
    }
    if (new_items) {
      memcpy(new_items, env->vals.items, env->vals.count * sizeof(valk_lval_t*));
      env->vals.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  // Evacuate each value in the environment
  if (env->vals.items != nullptr) {
    for (u64 i = 0; i < env->vals.count; i++) {
      valk_lval_t* val = env->vals.items[i];
      if (val != nullptr) {
        valk_lval_t* new_val = valk_evacuate_value(ctx, val);
        if (new_val != val) {
          env->vals.items[i] = new_val;
          // Push freshly evacuated values to worklist for children processing
          if (new_val != nullptr) {
            evac_worklist_push(ctx, new_val);
          }
        } else {
          // Value was already on heap - but we still need to process its env
          // to evacuate any scratch pointers it contains (e.g., nested closures)
          if (val != nullptr && LVAL_TYPE(val) == LVAL_FUN && 
              val->fun.builtin == nullptr && val->fun.env != nullptr) {
            env_worklist_push(env_worklist, val->fun.env);
          }
        }
      }
    }
  }
}

// Evacuate an environment's arrays and values (iterative to avoid stack overflow)
static void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == nullptr) return;

  // Use iterative worklist to avoid stack overflow on deep env chains
  valk_env_worklist_t worklist;
  env_worklist_init(&worklist);

  // Track visited environments to prevent infinite loops on cycles
  valk_env_worklist_t visited;
  env_worklist_init(&visited);

  env_worklist_push(&worklist, env);

  while (worklist.count > 0) {
    valk_lenv_t* current = env_worklist_pop(&worklist);
    if (current == nullptr) continue;

    // Check if already visited (linear search, but usually small number of envs)
    bool already_visited = false;
    for (u64 i = 0; i < visited.count; i++) {
      if (visited.items[i] == current) {
        already_visited = true;
        break;
      }
    }
    if (already_visited) continue;

    // Mark as visited
    env_worklist_push(&visited, current);

    // Process this environment (pass worklist so it can queue lambda envs)
    valk_evacuate_env_single(ctx, current, &worklist);

    // Queue parent for processing unconditionally.
    // We must traverse ALL reachable environments, not just scratch-allocated ones,
    // because heap-allocated environments may contain pointers to scratch-allocated
    // values that need to be evacuated.
    if (current->parent != nullptr) {
      env_worklist_push(&worklist, current->parent);
    }
  }

  env_worklist_free(&worklist);
  env_worklist_free(&visited);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Phase 2: Fix Pointers to Use New Locations
// ============================================================================

// LCOV_EXCL_START - pointer fixing requires active evacuation context from checkpoint
// Helper: Check if pointer is in scratch and handle accordingly using hashmap
// Returns true if pointer was updated, false otherwise
static inline bool fix_scratch_pointer(valk_evacuation_ctx_t* ctx, valk_lval_t** ptr) {
  valk_lval_t* val = *ptr;
  if (val == nullptr) return false;

  // Immortal objects are never updated
  if (val->flags & LVAL_FLAG_IMMORTAL) {
    return false;
  }

  // Check hashmap for already-copied value
  void *new_loc = valk_ptr_map_get(&ctx->ptr_map, val);
  if (new_loc != nullptr) {
    VALK_DEBUG("Fixing pointer via hashmap %p -> %p", (void*)val, new_loc);
    *ptr = (valk_lval_t *)new_loc;
    ctx->pointers_fixed++;
    return true;
  }

  // If in scratch but NOT in hashmap, try to evacuate it now
  // This can happen if Phase 1 didn't reach this value through its traversal
  bool in_scratch = (ctx->scratch != nullptr && valk_ptr_in_arena(ctx->scratch, val)) ||
                    (LVAL_ALLOC(val) == LVAL_ALLOC_SCRATCH);
  if (in_scratch) {
    valk_lval_t* new_val = valk_evacuate_value(ctx, val);
    if (new_val != val) {
      *ptr = new_val;
      ctx->pointers_fixed++;
      return true;
    }
    *ptr = nullptr;
    return true;
  }

  return false;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_BR_START - pointer fixing null checks and type dispatch
// Fix pointers in a value to follow forwarding pointers
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == nullptr) return;

  // Skip if still in scratch (shouldn't happen after proper evacuation)
  if (LVAL_ALLOC(v) == LVAL_ALLOC_SCRATCH) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
      fix_scratch_pointer(ctx, &v->cons.head);
      fix_scratch_pointer(ctx, &v->cons.tail);
      break;

    case LVAL_FUN:
      if (v->fun.builtin == nullptr) {
        fix_scratch_pointer(ctx, &v->fun.formals);
        fix_scratch_pointer(ctx, &v->fun.body);
        if (v->fun.env != nullptr) {
          valk_fix_env_pointers(ctx, v->fun.env);
        }
      }
      break;

    default:
      // Leaf types have no pointer children
      break;
  }
}

// Process a single environment for pointer fixing (non-recursive)
static void valk_fix_env_pointers_single(valk_evacuation_ctx_t* ctx, valk_lenv_t* env,
                                         valk_env_worklist_t* env_worklist) {
  // If scratch is NULL, conservatively copy all arrays
  // This handles evacuation from event loop thread without scratch context
  bool needs_array_copy = (ctx->scratch == nullptr);
  
  // Evacuate symbols.items array if in scratch
  if (env->symbols.items != nullptr && 
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->symbols.items))) {
    u64 array_size = env->symbols.capacity * sizeof(char*);
    char** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) { new_items = valk_mem_alloc(array_size); }
    if (new_items) {
      if (env->symbols.count > 0) {
        memcpy(new_items, env->symbols.items, env->symbols.count * sizeof(char*));
      }
      env->symbols.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  // Evacuate individual symbol strings if in scratch
  // NOTE: Only iterate if symbols.items is valid, but don't early return -
  // we still need to fix vals pointers below!
  if (env->symbols.items != nullptr) {
    for (u64 i = 0; i < env->symbols.count; i++) {
      if (env->symbols.items[i] && 
          (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->symbols.items[i]))) {
        u64 len = strlen(env->symbols.items[i]) + 1;
        char* new_str = nullptr;
        VALK_WITH_ALLOC((void*)ctx->heap) { new_str = valk_mem_alloc(len); }
        if (new_str) {
          memcpy(new_str, env->symbols.items[i], len);
          env->symbols.items[i] = new_str;
          ctx->bytes_copied += len;
        }
      }
    }
  }

  // Evacuate vals.items array if in scratch
  if (env->vals.items != nullptr && 
      (needs_array_copy || valk_ptr_in_arena(ctx->scratch, env->vals.items))) {
    u64 array_size = env->vals.capacity * sizeof(valk_lval_t*);
    valk_lval_t** new_items = nullptr;
    VALK_WITH_ALLOC((void*)ctx->heap) { new_items = valk_mem_alloc(array_size); }
    if (new_items) {
      if (env->vals.count > 0) {
        memcpy(new_items, env->vals.items, env->vals.count * sizeof(valk_lval_t*));
      }
      env->vals.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  // Fix all value pointers using the helper
  // Also queue heap lambdas' envs for processing (they may contain scratch pointers)
  if (env->vals.items != nullptr) {
    for (u64 i = 0; i < env->vals.count; i++) {
      fix_scratch_pointer(ctx, &env->vals.items[i]);
      // If value is a heap lambda, queue its env for processing
      valk_lval_t* val = env->vals.items[i];  // Read after fix (might have been updated)
      if (val != nullptr && LVAL_TYPE(val) == LVAL_FUN &&
          val->fun.builtin == nullptr && val->fun.env != nullptr) {
        env_worklist_push(env_worklist, val->fun.env);
      }
    }
  }
}

// Fix pointers in an environment (iterative to avoid stack overflow)
static void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == nullptr) return;

  // Use iterative worklist to avoid stack overflow on deep env chains
  valk_env_worklist_t worklist;
  env_worklist_init(&worklist);

  // Simple visited tracking using a separate list
  // (environments don't have a "fixed" flag, so we track what we've processed)
  valk_env_worklist_t visited;
  env_worklist_init(&visited);

  env_worklist_push(&worklist, env);

  while (worklist.count > 0) {
    valk_lenv_t* current = env_worklist_pop(&worklist);
    if (current == nullptr) continue;

    // Check if already visited (linear search, but usually small number of envs)
    bool already_visited = false;
    for (u64 i = 0; i < visited.count; i++) {
      if (visited.items[i] == current) {
        already_visited = true;
        break;
      }
    }
    if (already_visited) continue;

    // Mark as visited
    env_worklist_push(&visited, current);

    // Process this environment (pass worklist so it can queue lambda envs)
    valk_fix_env_pointers_single(ctx, current, &worklist);

    // Queue parent for processing
    if (current->parent != nullptr) {
      env_worklist_push(&worklist, current->parent);
    }
  }

  env_worklist_free(&worklist);
  env_worklist_free(&visited);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Checkpoint: Evacuate and Reset
// ============================================================================

static void valk_checkpoint_request_stw(void) {
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected,
                                       VALK_GC_PHASE_CHECKPOINT_REQUESTED)) {
    return;
  }

  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  if (num_threads <= 1) {
    atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
    return;
  }

  valk_aio_wake_all_for_gc();

  atomic_fetch_add(&valk_gc_coord.threads_paused, 1);

  pthread_mutex_lock(&valk_gc_coord.lock);
  while (atomic_load(&valk_gc_coord.threads_paused) < num_threads) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_nsec += 100000000;
    if (ts.tv_nsec >= 1000000000) {
      ts.tv_sec++;
      ts.tv_nsec -= 1000000000;
    }
    pthread_cond_timedwait(&valk_gc_coord.all_paused, &valk_gc_coord.lock, &ts);
  }
  pthread_mutex_unlock(&valk_gc_coord.lock);
}

static void valk_checkpoint_release_stw(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);
  if (phase != VALK_GC_PHASE_CHECKPOINT_REQUESTED) {
    return;
  }

  atomic_store(&valk_gc_coord.threads_paused, 0);

  pthread_mutex_lock(&valk_gc_coord.lock);
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  pthread_cond_broadcast(&valk_gc_coord.gc_done);
  pthread_mutex_unlock(&valk_gc_coord.lock);
}

// LCOV_EXCL_BR_START - checkpoint null checks and iteration
void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap,
                     valk_lenv_t* root_env) {
  if (scratch == nullptr || heap == nullptr) {
    VALK_WARN("Checkpoint called with nullptr scratch or heap");
    return;
  }
  
  VALK_DEBUG("Checkpoint starting, scratch offset=%llu", (unsigned long long)scratch->offset);

  valk_checkpoint_request_stw();

  // Initialize evacuation context
  valk_evacuation_ctx_t ctx = {
    .scratch = scratch,
    .heap = heap,
    .worklist = nullptr,
    .worklist_count = 0,
    .worklist_capacity = 0,
    .evacuated = nullptr,
    .evacuated_count = 0,
    .evacuated_capacity = 0,
    .values_copied = 0,
    .bytes_copied = 0,
    .pointers_fixed = 0,
  };

  evac_ctx_init(&ctx);

  // Phase 1: Evacuate all reachable values from root environment and global roots
  VALK_DEBUG("Checkpoint Phase 1: Starting evacuation from scratch arena");
  if (root_env != nullptr) {
    valk_evacuate_env(&ctx, root_env);
  }

  evac_checkpoint_eval_stack(&ctx);

  // Process worklist until empty (evacuate children)
  while (ctx.worklist_count > 0) {
    valk_lval_t* v = evac_worklist_pop(&ctx);
    valk_evacuate_children(&ctx, v);
  }

  VALK_DEBUG("Checkpoint Phase 1: Evacuated %zu values (%zu bytes)",
             ctx.values_copied, ctx.bytes_copied);

  // Phase 2: Fix all pointers in evacuated values only
  // This avoids iterating heap pages which may contain non-value allocations
  for (u64 i = 0; i < ctx.evacuated_count; i++) {
    valk_fix_pointers(&ctx, ctx.evacuated[i]);
  }

  // Fix pointers in root environment
  if (root_env != nullptr) {
    valk_fix_env_pointers(&ctx, root_env);
  }

  VALK_DEBUG("Checkpoint Phase 2: Fixed %zu pointers", ctx.pointers_fixed);

  // Update scratch arena stats
  atomic_fetch_add_explicit(&scratch->stats.num_checkpoints, 1, memory_order_relaxed);
  atomic_fetch_add_explicit(&scratch->stats.bytes_evacuated, ctx.bytes_copied, memory_order_relaxed);
  atomic_fetch_add_explicit(&scratch->stats.values_evacuated, ctx.values_copied, memory_order_relaxed);

  // Update heap stats
  heap->stats.evacuations_from_scratch += ctx.values_copied;
  heap->stats.evacuation_bytes += ctx.bytes_copied;
  heap->stats.evacuation_pointer_fixups += ctx.pointers_fixed;

  VALK_INFO("Checkpoint: evacuated %zu values (%zu bytes), fixed %zu pointers",
            ctx.values_copied, ctx.bytes_copied, ctx.pointers_fixed);

  // Reset scratch arena for next round of allocations
  valk_mem_arena_reset(scratch);

  // Cleanup
  evac_ctx_free(&ctx);

  valk_checkpoint_release_stw();
}

// Evacuate a single value and all its transitive dependencies to heap
// This is used for values that need to survive across checkpoints
// (e.g., interval timer callbacks that may fire before next checkpoint)
valk_lval_t* valk_evacuate_to_heap(valk_lval_t* v) {
  if (v == nullptr) return nullptr;
  
  // Already on heap? Return as-is
  if (LVAL_ALLOC(v) == LVAL_ALLOC_HEAP) {
    return v;
  }
  
  // Not in scratch? Already safe (could be global/static or other allocation)
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) {
    return v;
  }
  
  valk_mem_arena_t* scratch = valk_thread_ctx.scratch;
  valk_gc_malloc_heap_t* heap = valk_thread_ctx.heap;
  
  // If thread context doesn't have heap, try the runtime heap
  if (!heap) {
    heap = valk_runtime_get_heap();
  }
  
  if (!heap) {
    VALK_ERROR("valk_evacuate_to_heap: no heap available (scratch=%p, heap=%p, v alloc=%u)",
               (void*)scratch, (void*)heap, LVAL_ALLOC(v));
    return v;
  }
  
  // Note: scratch can be NULL when called from event loop thread
  // In that case, we conservatively copy all strings from scratch-allocated values
  //
  // No STW needed - we're just copying values to heap, not modifying shared state.
  // The original values remain valid until checkpoint resets the scratch arena.
  
  // Create a mini evacuation context
  valk_evacuation_ctx_t ctx = {
    .scratch = scratch,
    .heap = heap,
    .values_copied = 0,
    .bytes_copied = 0,
    .pointers_fixed = 0,
  };
  evac_ctx_init(&ctx);
  
  // Evacuate the value
  valk_lval_t* new_val = valk_evacuate_value(&ctx, v);
  
  // If it's a function, evacuate its environment too
  if (new_val && LVAL_TYPE(new_val) == LVAL_FUN && 
      new_val->fun.builtin == nullptr && new_val->fun.env != nullptr) {
    valk_evacuate_env(&ctx, new_val->fun.env);
  }
  
  // Process worklist to evacuate all children
  while (ctx.worklist_count > 0) {
    valk_lval_t* val = evac_worklist_pop(&ctx);
    valk_evacuate_children(&ctx, val);
  }
  
  // Fix pointers in all evacuated values
  for (u64 i = 0; i < ctx.evacuated_count; i++) {
    valk_fix_pointers(&ctx, ctx.evacuated[i]);
  }
  
  // If the original value was evacuated, fix pointers in its env
  if (new_val != nullptr && new_val != v && LVAL_TYPE(new_val) == LVAL_FUN && 
      new_val->fun.builtin == nullptr && new_val->fun.env != nullptr) {
    valk_fix_env_pointers(&ctx, new_val->fun.env);
  }
  
  evac_ctx_free(&ctx);
  
  return new_val;
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// Phase 1: Multi-Class Heap Implementation (New Size Class Allocator)
// ============================================================================

#include <sys/mman.h>

// Initialize a page list for a specific size class
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

// Initialize multi-class TLAB
void valk_gc_tlab2_init(valk_gc_tlab2_t *tlab) {
  tlab->owner_heap = nullptr;
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = nullptr;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
}

// Allocate a new page for a specific size class
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

static _Atomic u64 g_heap_generation = 1;

#define VALK_GC_MAX_LIVE_HEAPS 64
static valk_gc_heap2_t *g_live_heaps[VALK_GC_MAX_LIVE_HEAPS];
static pthread_mutex_t g_live_heaps_lock = PTHREAD_MUTEX_INITIALIZER;

static void valk_gc_register_heap(valk_gc_heap2_t *heap) {
  pthread_mutex_lock(&g_live_heaps_lock);
  for (int i = 0; i < VALK_GC_MAX_LIVE_HEAPS; i++) {
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

// LCOV_EXCL_BR_START - heap creation calloc/mmap failures
// Create new multi-class heap
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

void valk_gc_tlab2_invalidate_heap(valk_gc_heap2_t *heap);

// Destroy heap and release all memory
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
    if (large->data) {
      munmap(large->data, large->size);
    }
    free(large);
    large = next;
  }
  pthread_mutex_unlock(&heap->large_lock);
  pthread_mutex_destroy(&heap->large_lock);
  
  if (heap->base && heap->reserved > 0) {
    munmap(heap->base, heap->reserved);
  }
  
  VALK_INFO("Destroyed multi-class GC heap");
  free(heap);
}

// LCOV_EXCL_BR_START - TLAB refill internal bitmap search and page management
// Find free slots in a page's allocation bitmap
// Returns starting slot index, or UINT32_MAX if not found
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

// Refill TLAB for specific class (slow path)
bool valk_gc_tlab2_refill(valk_gc_tlab2_t *tlab, valk_gc_heap2_t *heap, u8 size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return false;
  
  valk_gc_page_list_t *list = &heap->classes[size_class];
  
  pthread_mutex_lock(&list->lock);
  
  valk_gc_page2_t *page = list->partial_pages;
  u32 start_slot = 0;
  u32 num_slots = VALK_GC_TLAB_SLOTS;
  
  if (page) {
    // Try to find contiguous free slots in existing partial page
    start_slot = valk_gc_page2_find_free_slots(page, num_slots);
    if (start_slot == UINT32_MAX) {
      // Page is actually full, remove from partial list
      list->partial_pages = page->next_partial;
      page = nullptr;
    // LCOV_EXCL_START - page reclaim path requires MADV_DONTNEED to zero page
    } else if (page->reclaimed) {
      // Page was reclaimed (MADV_DONTNEED zeroed the memory), re-initialize header
      // The header was zeroed, so restore it
      page->size_class = size_class;
      page->slots_per_page = list->slots_per_page;
      page->bitmap_bytes = valk_gc_bitmap_bytes(size_class);
      atomic_store(&page->num_allocated, 0);
      // Clear bitmaps
      memset(valk_gc_page2_alloc_bitmap(page), 0, page->bitmap_bytes);
      memset(valk_gc_page2_mark_bitmap(page), 0, page->bitmap_bytes);
      // Re-add to committed_bytes
      atomic_fetch_add(&heap->committed_bytes, list->page_size);
      page->reclaimed = false;
    }
    // LCOV_EXCL_STOP
  }
  
  if (!page) {
    // Need a new page
    pthread_mutex_unlock(&list->lock);
    page = valk_gc_page2_alloc(heap, size_class);
    if (!page) return false;
    pthread_mutex_lock(&list->lock);
    
    // Add to lists
    page->next = list->all_pages;
    list->all_pages = page;
    page->next_partial = list->partial_pages;
    list->partial_pages = page;
    list->num_pages++;
    atomic_fetch_add(&list->total_slots, page->slots_per_page);
    
    start_slot = 0;
  }
  
  // Clamp to available slots
  if (start_slot + num_slots > page->slots_per_page) {
    num_slots = page->slots_per_page - start_slot;
  }
  
  // Pre-set allocation bits
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
  
  // Check if page is now full
  if (atomic_load(&page->num_allocated) >= page->slots_per_page) {
    // Remove from partial list
    valk_gc_page2_t **pp = &list->partial_pages;
    while (*pp && *pp != page) {
      pp = &(*pp)->next_partial;
    }
    if (*pp == page) {
      *pp = page->next_partial;
    }
  }
  
  pthread_mutex_unlock(&list->lock);
  
  // Update TLAB
  tlab->classes[size_class].page = page;
  tlab->classes[size_class].next_slot = start_slot;
  tlab->classes[size_class].limit_slot = start_slot + num_slots;
  
  return true;
}
// LCOV_EXCL_BR_STOP

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
      valk_gc_heap2_collect_auto(heap);
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

static __thread valk_gc_tlab2_t *valk_gc_local_tlab = nullptr;

void valk_gc_tlab2_invalidate_heap(valk_gc_heap2_t *heap) {
  if (!valk_gc_local_tlab) return;
  if (valk_gc_local_tlab->owner_heap == heap) {
    valk_gc_tlab2_abandon(valk_gc_local_tlab);
  }
}

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
      valk_gc_heap2_collect_auto(heap);
    }
  }

  if (!valk_gc_local_tlab) {
    valk_gc_local_tlab = malloc(sizeof(valk_gc_tlab2_t));
    if (!valk_gc_local_tlab) return nullptr;
    valk_gc_tlab2_init(valk_gc_local_tlab);
  }
  
  if (valk_gc_local_tlab->owner_heap != heap) {
    if (valk_gc_local_tlab->owner_heap && valk_gc_is_heap_alive(valk_gc_local_tlab->owner_heap)) {
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

void *valk_gc_heap2_realloc(valk_gc_heap2_t *heap, void *ptr, sz new_size) {
  if (ptr == nullptr) {
    return valk_gc_heap2_alloc(heap, new_size);
  }
  if (new_size == 0) {
    return nullptr;
  }
  
  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(heap, ptr, &loc)) {
    sz old_size = valk_gc_size_classes[loc.size_class];
    if (new_size <= old_size) {
      return ptr;
    }
    void *new_ptr = valk_gc_heap2_alloc(heap, new_size);
    if (new_ptr) {
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
// Phase 2: Pointer Location and Marking
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
        uptr offset = (uptr)ptr - (uptr)slots_start;
        if (offset % slot_size == 0) {
          out->page = page;
          out->slot = (u32)(offset / slot_size);
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
            if (LVAL_TYPE(v) == LVAL_REF && v->ref.free != nullptr) {
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
  if (!heap) return 0;
  
  sz freed = 0;
  
  pthread_mutex_lock(&heap->large_lock);
  
  valk_gc_large_obj_t **pp = &heap->large_objects;
  while (*pp != nullptr) {
    valk_gc_large_obj_t *obj = *pp;
    
    if (!obj->marked) {
      *pp = obj->next;
      
      if (obj->data) {
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

// ============================================================================
// Phase 4: Mark Phase for heap2
// ============================================================================

// LCOV_EXCL_BR_START - heap2 mark phase null checks and type dispatch
static void mark_children2(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx);
static void mark_env2(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx);

static bool mark_ptr_only(void *ptr, valk_gc_mark_ctx2_t *ctx) {
  if (ptr == nullptr) return false;
  
  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(ctx->heap, ptr, &loc)) {
    return valk_gc_page2_try_mark(loc.page, loc.slot);
  } else {
    return valk_gc_mark_large_object(ctx->heap, ptr);
  }
}

// LCOV_EXCL_START - Heap2 marking with complex types requires runtime context from real GC cycle
static void mark_lval2(valk_lval_t *lval, valk_gc_mark_ctx2_t *ctx) {
  if (lval == nullptr) return;
  if (!mark_ptr_only(lval, ctx)) return;
  if (!valk_gc_mark_queue_push(ctx->queue, lval)) {
    mark_children2(lval, ctx);
  }
}

#define MARK_ENV_VISITED_MAX 128

static void mark_env2(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx) {
  valk_lenv_t *visited[MARK_ENV_VISITED_MAX];
  u64 visited_count = 0;

  while (env != nullptr) {
    for (u64 i = 0; i < visited_count; i++) {
      if (visited[i] == env) return;
    }
    if (visited_count < MARK_ENV_VISITED_MAX) {
      visited[visited_count++] = env;
    }

    mark_ptr_only(env, ctx);
    mark_ptr_only(env->symbols.items, ctx);
    mark_ptr_only(env->vals.items, ctx);
    for (u64 i = 0; i < env->symbols.count; i++) {
      mark_ptr_only(env->symbols.items[i], ctx);
    }
    for (u64 i = 0; i < env->vals.count; i++) {
      mark_lval2(env->vals.items[i], ctx);
    }
    env = env->parent;
  }
}

static void mark_children2(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx) {
  if (obj == nullptr) return;
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
      mark_lval2(obj->cons.head, ctx);
      mark_lval2(obj->cons.tail, ctx);
      break;
    case LVAL_FUN:
      if (obj->fun.builtin == nullptr) {
        mark_lval2(obj->fun.formals, ctx);
        mark_lval2(obj->fun.body, ctx);
        if (obj->fun.env) mark_env2(obj->fun.env, ctx);
      }
      mark_ptr_only(obj->fun.name, ctx);
      break;
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_lval2(obj->async.handle->on_complete, ctx);
        mark_lval2(obj->async.handle->on_error, ctx);
        mark_lval2(obj->async.handle->on_cancel, ctx);
        mark_lval2(atomic_load_explicit(&obj->async.handle->result, memory_order_acquire), ctx);
        mark_lval2(atomic_load_explicit(&obj->async.handle->error, memory_order_acquire), ctx);
        if (obj->async.handle->env) mark_env2(obj->async.handle->env, ctx);
      }
      break;
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      mark_ptr_only(obj->str, ctx);
      break;
    case LVAL_REF:
      mark_ptr_only(obj->ref.type, ctx);
      break;
    default:
      break;
  }
}
// LCOV_EXCL_STOP

static void mark_root_visitor2(valk_lval_t *val, void *user) {
  valk_gc_mark_ctx2_t *ctx = user;
  mark_lval2(val, ctx);
}

void valk_gc_heap2_mark_object(valk_gc_mark_ctx2_t *ctx, void *ptr) {
  mark_lval2(ptr, ctx);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - heap2 mark roots and collect null checks
void valk_gc_heap2_mark_roots(valk_gc_heap2_t *heap) {
  if (!heap) return;
  
  valk_gc_mark_queue_t local_queue;
  valk_gc_mark_queue_init(&local_queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = &local_queue
  };
  
  if (heap->root_env != nullptr) {
    mark_env2(heap->root_env, &ctx);
  }
  
  valk_gc_visit_global_roots(mark_root_visitor2, &ctx);
  
  if (valk_thread_ctx.gc_registered) {
    valk_gc_visit_thread_roots(mark_root_visitor2, &ctx);
  }
  
  valk_lval_t *obj;
  while ((obj = valk_gc_mark_queue_pop(&local_queue)) != nullptr) {
    mark_children2(obj, &ctx);
  }
}

// ============================================================================
// Phase 3: Memory Limits and GC Cycle
// ============================================================================

void valk_gc_heap2_get_stats(valk_gc_heap2_t *heap, valk_gc_stats2_t *out) {
  if (!heap || !out) return;
  
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

void valk_gc_tlab2_abandon(valk_gc_tlab2_t *tlab) {
  if (!tlab) return;
  
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = nullptr;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
  
  tlab->owner_heap = nullptr;
}

void valk_gc_tlab2_reset(valk_gc_tlab2_t *tlab) {
  if (!tlab) return;

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

sz valk_gc_heap2_collect(valk_gc_heap2_t *heap) {
  if (!heap) return 0;
  
  u64 start_ns = uv_hrtime();
  
  atomic_store(&heap->gc_in_progress, true);
  atomic_fetch_add(&heap->collections, 1);
  
  sz bytes_before = valk_gc_heap2_used_bytes(heap);
  sz freed_slots_total = 0;
  sz freed_large = 0;
  
  valk_gc_heap2_mark_roots(heap);
  
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    for (valk_gc_page2_t *page = list->all_pages; page != nullptr; page = page->next) {
      sz freed = valk_gc_sweep_page2(page);
      freed_slots_total += freed;
      atomic_fetch_sub(&list->used_slots, freed);
    }
  }
  
  freed_large = valk_gc_sweep_large_objects(heap);
  
  valk_gc_rebuild_partial_lists(heap);
  
  sz pages_reclaimed = valk_gc_reclaim_empty_pages(heap);
  
  sz bytes_after = valk_gc_heap2_used_bytes(heap);
  sz reclaimed = 0;
  if (bytes_before > bytes_after) {
    reclaimed = bytes_before - bytes_after;
  }
  
  atomic_fetch_add(&heap->bytes_reclaimed_total, reclaimed);
  atomic_store(&heap->gc_in_progress, false);
  
  u64 end_ns = uv_hrtime();
  u64 pause_us = (end_ns - start_ns) / 1000;
  
  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_us_total, pause_us);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);
  atomic_store(&heap->runtime_metrics.last_heap_before_gc, bytes_before);
  atomic_store(&heap->runtime_metrics.last_reclaimed, reclaimed);
  
  u64 current_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  while (pause_us > current_max) {
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_us_max, &current_max, pause_us)) {
      break;
    }
  }
  
  VALK_DEBUG("GC cycle complete: reclaimed %zu bytes (%zu slots + %zu large, %zu empty pages) in %llu us",
             reclaimed, freed_slots_total, freed_large, pages_reclaimed, (unsigned long long)pause_us);
  
  return reclaimed;
}

sz valk_gc_heap2_collect_auto(valk_gc_heap2_t *heap) {
  if (!heap) return 0;
  
  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  
  if (num_threads <= 1) {
    return valk_gc_heap2_collect(heap);
  }
  
  if (!valk_thread_ctx.gc_registered) {
    return valk_gc_heap2_collect(heap);
  }
  
  if (!valk_gc_heap2_request_stw(heap)) {
    return valk_gc_heap2_collect(heap);
  }
  
  return valk_gc_heap2_parallel_collect(heap);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_START - emergency GC triggered at hard limit requires specific memory pressure conditions
static bool valk_gc_heap2_try_emergency_gc(valk_gc_heap2_t *heap, u64 needed) {
  if (heap->in_emergency_gc) {
    return false;
  }

  heap->in_emergency_gc = true;

  VALK_WARN("Emergency GC: need %zu bytes, used %zu / %zu",
            needed, valk_gc_heap2_used_bytes(heap), heap->hard_limit);

  u64 reclaimed = valk_gc_heap2_collect_auto(heap);

  heap->in_emergency_gc = false;

  u64 after = valk_gc_heap2_used_bytes(heap);
  if (after + needed <= heap->hard_limit) {
    VALK_INFO("Emergency GC recovered %zu bytes, allocation can proceed", reclaimed);
    return true;
  }

  return false;
}
// LCOV_EXCL_STOP

// ============================================================================
// Phase 7: Parallel Mark/Sweep for heap2
// ============================================================================

static _Atomic u64 __gc_heap2_idle_count = 0;
static _Atomic bool __gc_heap2_terminated = false;
static _Atomic(valk_gc_heap2_t *) __gc_heap2_current = nullptr;

static bool valk_gc_heap2_check_termination(void) {
  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  u64 idle = atomic_fetch_add(&__gc_heap2_idle_count, 1) + 1;
  
  if (idle == num_threads) {
    bool all_empty = true;
    for (u64 i = 0; i < num_threads; i++) {
      if (!valk_gc_coord.threads[i].active) continue;
      valk_gc_mark_queue_t *q = &valk_gc_coord.threads[i].mark_queue;
      if (!valk_gc_mark_queue_empty(q)) {
        all_empty = false;
        break;
      }
    }
    
    if (all_empty) {
      atomic_store(&__gc_heap2_terminated, true);
    }
  }
  
  for (int i = 0; i < 16; i++) {
    if (atomic_load(&__gc_heap2_terminated)) {
      return true;
    }
#if defined(__x86_64__) || defined(__i386__)
    __builtin_ia32_pause();
#else
    sched_yield();
#endif
  }
  
  atomic_fetch_sub(&__gc_heap2_idle_count, 1);
  return false;
}

// LCOV_EXCL_START - Heap2 parallel mark/sweep requires multi-threaded STW coordination
static void mark_children2_parallel(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx);
static void mark_env2_parallel(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx);

static void mark_lval2_parallel(valk_lval_t *lval, valk_gc_mark_ctx2_t *ctx) {
  if (lval == nullptr) return;
  if (!mark_ptr_only(lval, ctx)) return;
  if (!valk_gc_mark_queue_push(ctx->queue, lval)) {
    mark_children2_parallel(lval, ctx);
  }
}

static void mark_env2_parallel(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx) {
  valk_lenv_t *visited[MARK_ENV_VISITED_MAX];
  u64 visited_count = 0;

  while (env != nullptr) {
    for (u64 i = 0; i < visited_count; i++) {
      if (visited[i] == env) return;
    }
    if (visited_count < MARK_ENV_VISITED_MAX) {
      visited[visited_count++] = env;
    }

    mark_ptr_only(env, ctx);
    mark_ptr_only(env->symbols.items, ctx);
    mark_ptr_only(env->vals.items, ctx);
    for (u64 i = 0; i < env->symbols.count; i++) {
      mark_ptr_only(env->symbols.items[i], ctx);
    }
    for (u64 i = 0; i < env->vals.count; i++) {
      mark_lval2_parallel(env->vals.items[i], ctx);
    }
    env = env->parent;
  }
}

static void mark_children2_parallel(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx) {
  if (obj == nullptr) return;
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
      mark_lval2_parallel(obj->cons.head, ctx);
      mark_lval2_parallel(obj->cons.tail, ctx);
      break;
    case LVAL_FUN:
      if (obj->fun.builtin == nullptr) {
        mark_lval2_parallel(obj->fun.formals, ctx);
        mark_lval2_parallel(obj->fun.body, ctx);
        if (obj->fun.env) mark_env2_parallel(obj->fun.env, ctx);
      }
      mark_ptr_only(obj->fun.name, ctx);
      break;
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_lval2_parallel(obj->async.handle->on_complete, ctx);
        mark_lval2_parallel(obj->async.handle->on_error, ctx);
        mark_lval2_parallel(obj->async.handle->on_cancel, ctx);
        mark_lval2_parallel(atomic_load_explicit(&obj->async.handle->result, memory_order_acquire), ctx);
        mark_lval2_parallel(atomic_load_explicit(&obj->async.handle->error, memory_order_acquire), ctx);
        if (obj->async.handle->env) mark_env2_parallel(obj->async.handle->env, ctx);
      }
      break;
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      mark_ptr_only(obj->str, ctx);
      break;
    case LVAL_REF:
      mark_ptr_only(obj->ref.type, ctx);
      break;
    default:
      break;
  }
}

static void mark_root_visitor2_parallel(valk_lval_t *val, void *user) {
  valk_gc_mark_ctx2_t *ctx = user;
  mark_lval2_parallel(val, ctx);
}

void valk_gc_heap2_parallel_mark(valk_gc_heap2_t *heap) {
  if (!heap) return;
  if (!valk_thread_ctx.gc_registered) return;
  
  u64 my_id = valk_thread_ctx.gc_thread_id;
  valk_gc_mark_queue_t *my_queue = &valk_gc_coord.threads[my_id].mark_queue;
  
  valk_gc_mark_queue_init(my_queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = my_queue
  };
  
  valk_gc_visit_thread_roots(mark_root_visitor2_parallel, &ctx);
  
  if (my_id == 0) {
    valk_gc_visit_global_roots(mark_root_visitor2_parallel, &ctx);
  }
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  u64 idle_spins = 0;
  const u64 MAX_IDLE_SPINS = 64;
  
  while (true) {
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != nullptr) {
      mark_children2_parallel(obj, &ctx);
      idle_spins = 0;
    }
    
    bool found_work = false;
    u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
    
    for (u64 i = 1; i <= num_threads; i++) {
      u64 victim = (my_id + i) % num_threads;
      if (!valk_gc_coord.threads[victim].active) continue;
      
      obj = valk_gc_mark_queue_steal(&valk_gc_coord.threads[victim].mark_queue);
      if (obj != nullptr) {
        mark_children2_parallel(obj, &ctx);
        found_work = true;
        idle_spins = 0;
        break;
      }
    }
    
    if (!found_work) {
      idle_spins++;
      if (idle_spins >= MAX_IDLE_SPINS) {
        if (valk_gc_heap2_check_termination()) {
          break;
        }
        idle_spins = 0;
      }
      sched_yield();
    }
  }
}

void valk_gc_heap2_parallel_sweep(valk_gc_heap2_t *heap) {
  if (!heap) return;
  if (!valk_thread_ctx.gc_registered) return;
  
  u64 my_id = valk_thread_ctx.gc_thread_id;
  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  
  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    u64 num_pages = list->num_pages;
    if (num_pages == 0) continue;
    
    u64 pages_per_thread = (num_pages + num_threads - 1) / num_threads;
    u64 my_start = my_id * pages_per_thread;
    u64 my_end = (my_id + 1) * pages_per_thread;
    if (my_end > num_pages) my_end = num_pages;
    
    valk_gc_page2_t *page = list->all_pages;
    for (u64 i = 0; i < my_start && page != nullptr; i++) {
      page = page->next;
    }
    
    u64 freed_slots = 0;
    for (u64 i = my_start; i < my_end && page != nullptr; i++) {
      freed_slots += valk_gc_sweep_page2(page);
      page = page->next;
    }
    
    if (freed_slots > 0) {
      atomic_fetch_sub(&list->used_slots, freed_slots);
    }
  }
  
  if (my_id == 0) {
    valk_gc_sweep_large_objects(heap);
  }
}

bool valk_gc_heap2_request_stw(valk_gc_heap2_t *heap) {
  if (!heap) return false;
  
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected,
                                       VALK_GC_PHASE_STW_REQUESTED)) {
    return false;
  }
  
  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  if (num_threads == 0) {
    atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
    return false;
  }
  
  if (valk_gc_coord.barrier_initialized) {
    valk_barrier_reset(&valk_gc_coord.barrier, num_threads);
  } else {
    valk_barrier_init(&valk_gc_coord.barrier, num_threads);
    valk_gc_coord.barrier_initialized = true;
  }
  
  atomic_store(&__gc_heap2_current, heap);
  
  valk_aio_wake_all_for_gc();
  
  atomic_fetch_add(&valk_gc_coord.threads_paused, 1);
  
  if (num_threads > 1) {
    pthread_mutex_lock(&valk_gc_coord.lock);
    while (atomic_load(&valk_gc_coord.threads_paused) < num_threads) {
      struct timespec ts;
      clock_gettime(CLOCK_REALTIME, &ts);
      ts.tv_nsec += 100000000;
      if (ts.tv_nsec >= 1000000000) {
        ts.tv_sec++;
        ts.tv_nsec -= 1000000000;
      }
      pthread_cond_timedwait(&valk_gc_coord.all_paused, &valk_gc_coord.lock, &ts);
    }
    pthread_mutex_unlock(&valk_gc_coord.lock);
  }
  
  return true;
}

sz valk_gc_heap2_parallel_collect(valk_gc_heap2_t *heap) {
  if (!heap) return 0;
  
  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  
  if (num_threads <= 1) {
    return valk_gc_heap2_collect(heap);
  }
  
  if (!valk_thread_ctx.gc_registered) {
    return valk_gc_heap2_collect(heap);
  }
  
  u64 start_ns = uv_hrtime();
  
  atomic_store(&heap->gc_in_progress, true);
  atomic_fetch_add(&heap->collections, 1);
  
  u64 bytes_before = valk_gc_heap2_used_bytes(heap);
  
  atomic_store(&__gc_heap2_idle_count, 0);
  atomic_store(&__gc_heap2_terminated, false);
  
  // BARRIER 1: Sync before mark phase
  // All threads (initiator + workers) must hit this barrier before marking starts
  // Workers enter via valk_gc_participate_in_parallel_gc()
  valk_barrier_wait(&valk_gc_coord.barrier);

  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_MARKING);
  valk_gc_heap2_parallel_mark(heap);
  
  // BARRIER 2: Sync after mark phase
  // Ensures all marking is complete before sweep begins
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_SWEEPING);
  valk_gc_heap2_parallel_sweep(heap);
  
  // BARRIER 3: Sync after sweep phase
  // Ensures all sweeping is complete before page reclamation
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  if (valk_thread_ctx.gc_thread_id == 0) {
    valk_gc_rebuild_partial_lists(heap);
    valk_gc_reclaim_empty_pages(heap);
  }
  
  // Set phase to IDLE and broadcast BEFORE barrier 4
  // This ensures all threads see IDLE phase when they pass the barrier
  atomic_store(&valk_gc_coord.threads_paused, 0);
  pthread_mutex_lock(&valk_gc_coord.lock);
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  pthread_cond_broadcast(&valk_gc_coord.gc_done);
  pthread_mutex_unlock(&valk_gc_coord.lock);
  
  // BARRIER 4: Sync after reclamation and phase reset
  // All threads pass this barrier together, ensuring they all see IDLE phase
  // before any can start a new GC/checkpoint
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  u64 bytes_after = valk_gc_heap2_used_bytes(heap);
  u64 reclaimed = 0;
  if (bytes_before > bytes_after) {
    reclaimed = bytes_before - bytes_after;
  }
  
  atomic_fetch_add(&heap->bytes_reclaimed_total, reclaimed);
  atomic_store(&heap->gc_in_progress, false);
  
  u64 end_ns = uv_hrtime();
  u64 pause_us = (end_ns - start_ns) / 1000;
  
  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_us_total, pause_us);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);
  atomic_store(&heap->runtime_metrics.last_heap_before_gc, bytes_before);
  atomic_store(&heap->runtime_metrics.last_reclaimed, reclaimed);
  
  u64 current_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  while (pause_us > current_max) {
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_us_max, &current_max, pause_us)) {
      break;
    }
  }
  
  atomic_fetch_add(&valk_gc_coord.parallel_cycles, 1);
  atomic_fetch_add(&valk_gc_coord.parallel_pause_us_total, pause_us);
  
  VALK_DEBUG("Parallel GC heap2 cycle complete: reclaimed %zu bytes in %llu us (%zu threads)",
             reclaimed, (unsigned long long)pause_us, num_threads);
  
  return reclaimed;
}

static void valk_gc_participate_in_parallel_gc(void) {
  valk_gc_heap2_t *heap = atomic_load(&__gc_heap2_current);
  if (!heap) {
    pthread_mutex_lock(&valk_gc_coord.lock);
    while (atomic_load(&valk_gc_coord.phase) != VALK_GC_PHASE_IDLE) {
      pthread_cond_wait(&valk_gc_coord.gc_done, &valk_gc_coord.lock);
    }
    pthread_mutex_unlock(&valk_gc_coord.lock);
    return;
  }
  
  // BARRIER 1: Sync before mark phase (matches parallel_collect)
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  valk_gc_heap2_parallel_mark(heap);
  
  // BARRIER 2: Sync after mark phase (matches parallel_collect)
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  valk_gc_heap2_parallel_sweep(heap);
  
  // BARRIER 3: Sync after sweep phase (matches parallel_collect)
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  // BARRIER 4: Sync after reclamation (matches parallel_collect)
  // Phase is set to IDLE before this barrier, so all threads see it
  // No need to wait on gc_done - the barrier ensures synchronization
  valk_barrier_wait(&valk_gc_coord.barrier);
}
// LCOV_EXCL_STOP

// ============================================================================
// Fork Safety - Reset global state after fork() in child process
// ============================================================================

// LCOV_EXCL_START - fork safety function requires actual fork() which is unsafe in test harness
void valk_gc_reset_after_fork(void) {
  __runtime_heap = nullptr;
  __runtime_initialized = false;

  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  atomic_store(&valk_gc_coord.threads_registered, 0);
  atomic_store(&valk_gc_coord.threads_paused, 0);
  valk_gc_coord.barrier_initialized = false;

  for (u64 i = 0; i < VALK_GC_MAX_THREADS; i++) {
    valk_gc_coord.threads[i].ctx = nullptr;
    valk_gc_coord.threads[i].active = false;
  }

  atomic_store(&valk_gc_coord.parallel_cycles, 0);
  atomic_store(&valk_gc_coord.parallel_pause_us_total, 0);

  atomic_store(&__gc_heap2_idle_count, 0);
  atomic_store(&__gc_heap2_terminated, false);
  atomic_store(&__gc_heap2_current, nullptr);

  pthread_mutex_lock(&g_live_heaps_lock);
  for (int i = 0; i < VALK_GC_MAX_LIVE_HEAPS; i++) {
    g_live_heaps[i] = nullptr;
  }
  pthread_mutex_unlock(&g_live_heaps_lock);

  valk_thread_ctx.heap = nullptr;
  valk_thread_ctx.scratch = nullptr;
  valk_thread_ctx.root_env = nullptr;
  valk_thread_ctx.gc_registered = false;
  valk_thread_ctx.gc_thread_id = 0;
  valk_thread_ctx.eval_stack = nullptr;
  valk_thread_ctx.eval_expr = nullptr;
  valk_thread_ctx.eval_value = nullptr;

  if (valk_thread_ctx.root_stack) {
    free(valk_thread_ctx.root_stack);
    valk_thread_ctx.root_stack = nullptr;
  }
  valk_thread_ctx.root_stack_count = 0;
  valk_thread_ctx.root_stack_capacity = 0;
}
// LCOV_EXCL_STOP

// ============================================================================
// Diagnostic Dump for Debugging Hangs
// ============================================================================

static const char *valk_gc_phase_name(valk_gc_phase_e phase) {
  switch (phase) {
    case VALK_GC_PHASE_IDLE: return "IDLE";
    case VALK_GC_PHASE_STW_REQUESTED: return "STW_REQUESTED";
    case VALK_GC_PHASE_CHECKPOINT_REQUESTED: return "CHECKPOINT_REQUESTED";
    case VALK_GC_PHASE_MARKING: return "MARKING";
    case VALK_GC_PHASE_SWEEPING: return "SWEEPING";
    default: return "UNKNOWN";
  }
}

void valk_diag_dump_on_timeout(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);
  u64 registered = atomic_load(&valk_gc_coord.threads_registered);
  u64 paused = atomic_load(&valk_gc_coord.threads_paused);
  
  fprintf(stderr, "\n");
  fprintf(stderr, "╔══════════════════════════════════════════════════════════════╗\n");
  fprintf(stderr, "║  TIMEOUT DIAGNOSTIC DUMP                                     ║\n");
  fprintf(stderr, "╚══════════════════════════════════════════════════════════════╝\n");
  fprintf(stderr, "\n");
  
  fprintf(stderr, "=== GC Coordinator State ===\n");
  fprintf(stderr, "  phase:              %s (%d)\n", valk_gc_phase_name(phase), phase);
  fprintf(stderr, "  threads_registered: %llu\n", (unsigned long long)registered);
  fprintf(stderr, "  threads_paused:     %llu\n", (unsigned long long)paused);
  fprintf(stderr, "  barrier_init:       %s\n", valk_gc_coord.barrier_initialized ? "yes" : "no");
  fprintf(stderr, "\n");
  
  if (phase != VALK_GC_PHASE_IDLE) {
    fprintf(stderr, "  *** GC is NOT idle - possible deadlock in GC coordination ***\n");
    if (paused < registered) {
      fprintf(stderr, "  *** Waiting for %llu threads to reach safe point ***\n",
              (unsigned long long)(registered - paused));
    }
    fprintf(stderr, "\n");
  }
  
  fprintf(stderr, "=== Registered Threads ===\n");
  for (u64 i = 0; i < VALK_GC_MAX_THREADS && i < 16; i++) {
    if (valk_gc_coord.threads[i].active) {
      valk_thread_context_t *tc = valk_gc_coord.threads[i].ctx;
      fprintf(stderr, "  [%llu] pthread=%lu active=yes", 
              (unsigned long long)i,
              (unsigned long)valk_gc_coord.threads[i].thread_id);
      if (tc) {
        fprintf(stderr, " gc_id=%llu", (unsigned long long)tc->gc_thread_id);
      }
      fprintf(stderr, "\n");
    }
  }
  fprintf(stderr, "\n");
  
  fprintf(stderr, "=== Current Thread Context ===\n");
  fprintf(stderr, "  gc_registered:   %s\n", valk_thread_ctx.gc_registered ? "yes" : "no");
  fprintf(stderr, "  gc_thread_id:    %llu\n", (unsigned long long)valk_thread_ctx.gc_thread_id);
  fprintf(stderr, "  root_stack_cnt:  %zu\n", valk_thread_ctx.root_stack_count);
  fprintf(stderr, "\n");

#ifdef __linux__
  fprintf(stderr, "=== Thread Stacks (from /proc) ===\n");
  char path[64];
  snprintf(path, sizeof(path), "/proc/%d/task", getpid());
  DIR *dir = opendir(path);
  if (dir) {
    struct dirent *ent;
    while ((ent = readdir(dir)) != nullptr) {
      if (ent->d_name[0] == '.') continue;
      char stack_path[128];
      snprintf(stack_path, sizeof(stack_path), "/proc/%d/task/%s/stack", getpid(), ent->d_name);
      FILE *f = fopen(stack_path, "r");
      if (f) {
        fprintf(stderr, "--- Thread %s ---\n", ent->d_name);
        char line[256];
        int lines = 0;
        while (fgets(line, sizeof(line), f) && lines < 10) {
          fprintf(stderr, "  %s", line);
          lines++;
        }
        fclose(f);
      }
    }
    closedir(dir);
  }
  fprintf(stderr, "\n");
#endif

  fprintf(stderr, "=== Likely Cause ===\n");
  if (phase == VALK_GC_PHASE_STW_REQUESTED || phase == VALK_GC_PHASE_CHECKPOINT_REQUESTED) {
    fprintf(stderr, "  GC/checkpoint requested but not all threads reached safe point.\n");
    fprintf(stderr, "  A thread may be stuck in a long-running operation without\n");
    fprintf(stderr, "  calling VALK_GC_SAFE_POINT().\n");
  } else if (phase == VALK_GC_PHASE_MARKING || phase == VALK_GC_PHASE_SWEEPING) {
    fprintf(stderr, "  GC is in progress. Threads may be stuck at a barrier.\n");
    fprintf(stderr, "  Check barrier_wait calls in gc.c.\n");
  } else {
    fprintf(stderr, "  GC is idle. Hang may be in application logic:\n");
    fprintf(stderr, "  - Event loop waiting for I/O that never arrives\n");
    fprintf(stderr, "  - Deadlock in application mutex\n");
    fprintf(stderr, "  - Infinite loop in user code\n");
  }
  fprintf(stderr, "\n");
  
  fflush(stderr);
}
