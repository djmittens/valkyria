#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "log.h"
#include "aio/aio.h"  // For valk_async_handle_t
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <sched.h>
#include <uv.h>

// ============================================================================
// Parallel GC Infrastructure (Phase 0)
// ============================================================================

// Global coordinator instance
valk_gc_coordinator_t valk_gc_coord = {0};

// Global roots registry
valk_gc_global_roots_t valk_gc_global_roots = {0};

// Global page pool for TLAB allocation
valk_gc_page_pool_t valk_gc_global_pool = {0};
static bool __global_pool_initialized = false;

// Portable barrier implementation
void valk_barrier_init(valk_barrier_t* b, size_t count) {
  pthread_mutex_init(&b->mutex, NULL);
  pthread_cond_init(&b->cond, NULL);
  b->count = count;
  b->waiting = 0;
  b->phase = 0;
}

void valk_barrier_destroy(valk_barrier_t* b) {
  pthread_mutex_destroy(&b->mutex);
  pthread_cond_destroy(&b->cond);
}

void valk_barrier_wait(valk_barrier_t* b) {
  pthread_mutex_lock(&b->mutex);
  size_t my_phase = b->phase;
  b->waiting++;
  if (b->waiting == b->count) {
    b->waiting = 0;
    b->phase++;
    pthread_cond_broadcast(&b->cond);
  } else {
    while (b->phase == my_phase) {
      pthread_cond_wait(&b->cond, &b->mutex);
    }
  }
  pthread_mutex_unlock(&b->mutex);
}

// Atomic mark bit operations
bool valk_gc_try_mark(valk_lval_t* obj) {
  if (obj == NULL) return false;
  uint64_t expected = atomic_load_explicit(&obj->flags, memory_order_relaxed);
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
  if (obj == NULL) return true;
  return (atomic_load_explicit(&obj->flags, memory_order_acquire) & LVAL_FLAG_GC_MARK) != 0;
}

void valk_gc_clear_mark(valk_lval_t* obj) {
  if (obj == NULL) return;
  atomic_fetch_and_explicit(&obj->flags, ~LVAL_FLAG_GC_MARK, memory_order_release);
}

// Chase-Lev work-stealing deque implementation
void valk_gc_mark_queue_init(valk_gc_mark_queue_t* q) {
  atomic_store(&q->top, 0);
  atomic_store(&q->bottom, 0);
  for (size_t i = 0; i < VALK_GC_MARK_QUEUE_SIZE; i++) {
    atomic_store(&q->items[i], NULL);
  }
}

bool valk_gc_mark_queue_push(valk_gc_mark_queue_t* q, valk_lval_t* val) {
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  
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
  size_t b = atomic_load_explicit(&q->bottom, memory_order_relaxed);
  size_t t = atomic_load_explicit(&q->top, memory_order_relaxed);
  
  if (t >= b) {
    return NULL;
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
        val = NULL;
      }
      atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
    }
    return val;
  }
  
  atomic_store_explicit(&q->bottom, b + 1, memory_order_relaxed);
  return NULL;
}

valk_lval_t* valk_gc_mark_queue_steal(valk_gc_mark_queue_t* q) {
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  atomic_thread_fence(memory_order_seq_cst);
  size_t b = atomic_load_explicit(&q->bottom, memory_order_acquire);
  
  if (t >= b) {
    return NULL;
  }
  
  valk_lval_t* val = atomic_load_explicit(
      &q->items[t % VALK_GC_MARK_QUEUE_SIZE], memory_order_relaxed);
  
  if (!atomic_compare_exchange_strong(&q->top, &t, t + 1)) {
    return NULL;
  }
  
  return val;
}

bool valk_gc_mark_queue_empty(valk_gc_mark_queue_t* q) {
  size_t t = atomic_load_explicit(&q->top, memory_order_acquire);
  size_t b = atomic_load_explicit(&q->bottom, memory_order_acquire);
  return t >= b;
}

// Coordinator initialization
void valk_gc_coordinator_init(void) {
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  atomic_store(&valk_gc_coord.threads_registered, 0);
  atomic_store(&valk_gc_coord.threads_paused, 0);
  
  pthread_mutex_init(&valk_gc_coord.lock, NULL);
  pthread_cond_init(&valk_gc_coord.all_paused, NULL);
  pthread_cond_init(&valk_gc_coord.gc_done, NULL);
  valk_gc_coord.barrier_initialized = false;
  
  for (size_t i = 0; i < VALK_GC_MAX_THREADS; i++) {
    valk_gc_coord.threads[i].ctx = NULL;
    valk_gc_coord.threads[i].active = false;
    valk_gc_mark_queue_init(&valk_gc_coord.threads[i].mark_queue);
  }
  
  atomic_store(&valk_gc_coord.parallel_cycles, 0);
  atomic_store(&valk_gc_coord.parallel_pause_us_total, 0);
  
  pthread_mutex_init(&valk_gc_global_roots.lock, NULL);
  valk_gc_global_roots.count = 0;
}

// Thread registration
void valk_gc_thread_register(void) {
  size_t idx = atomic_fetch_add(&valk_gc_coord.threads_registered, 1);
  
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
  
  size_t idx = valk_thread_ctx.gc_thread_id;
  valk_gc_coord.threads[idx].active = false;
  valk_gc_coord.threads[idx].ctx = NULL;
  
  atomic_fetch_sub(&valk_gc_coord.threads_registered, 1);
  
  if (valk_thread_ctx.root_stack) {
    free(valk_thread_ctx.root_stack);
    valk_thread_ctx.root_stack = NULL;
  }
  valk_thread_ctx.gc_registered = false;
  
  VALK_DEBUG("Thread unregistered from GC: idx=%zu", idx);
}

// Safe point slow path
void valk_gc_safe_point_slow(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);
  
  if (phase == VALK_GC_PHASE_STW_REQUESTED) {
    if (valk_thread_ctx.scratch && valk_thread_ctx.scratch->offset > 0 &&
        valk_thread_ctx.heap && valk_thread_ctx.root_env) {
      valk_checkpoint(valk_thread_ctx.scratch, 
                      valk_thread_ctx.heap,
                      valk_thread_ctx.root_env);
    }
    
    size_t paused = atomic_fetch_add(&valk_gc_coord.threads_paused, 1) + 1;
    size_t registered = atomic_load(&valk_gc_coord.threads_registered);
    
    if (paused == registered) {
      pthread_mutex_lock(&valk_gc_coord.lock);
      pthread_cond_signal(&valk_gc_coord.all_paused);
      pthread_mutex_unlock(&valk_gc_coord.lock);
    }
    
    pthread_mutex_lock(&valk_gc_coord.lock);
    while (atomic_load(&valk_gc_coord.phase) != VALK_GC_PHASE_IDLE) {
      pthread_cond_wait(&valk_gc_coord.gc_done, &valk_gc_coord.lock);
    }
    pthread_mutex_unlock(&valk_gc_coord.lock);
    
    atomic_fetch_sub(&valk_gc_coord.threads_paused, 1);
  }
}

// Global roots
void valk_gc_add_global_root(valk_lval_t** root) {
  pthread_mutex_lock(&valk_gc_global_roots.lock);
  if (valk_gc_global_roots.count < VALK_GC_MAX_GLOBAL_ROOTS) {
    valk_gc_global_roots.roots[valk_gc_global_roots.count++] = root;
  } else {
    VALK_WARN("Global roots registry full");
  }
  pthread_mutex_unlock(&valk_gc_global_roots.lock);
}

void valk_gc_remove_global_root(valk_lval_t** root) {
  pthread_mutex_lock(&valk_gc_global_roots.lock);
  for (size_t i = 0; i < valk_gc_global_roots.count; i++) {
    if (valk_gc_global_roots.roots[i] == root) {
      valk_gc_global_roots.roots[i] = valk_gc_global_roots.roots[--valk_gc_global_roots.count];
      break;
    }
  }
  pthread_mutex_unlock(&valk_gc_global_roots.lock);
}

// ============================================================================
// Phase 1: Page-based Allocator (Parallel GC)
// ============================================================================

static _Atomic uint32_t __page_id_counter = 0;

void valk_gc_page_pool_init(valk_gc_page_pool_t *pool) {
  pthread_mutex_init(&pool->lock, NULL);
  pool->all_pages = NULL;
  pool->partial_pages = NULL;
  pool->num_pages = 0;
  atomic_store(&pool->total_slots, 0);
  atomic_store(&pool->used_slots, 0);
  atomic_store(&pool->gc_threshold, VALK_GC_SLOTS_PER_PAGE * 10);
}

void valk_gc_page_pool_destroy(valk_gc_page_pool_t *pool) {
  pthread_mutex_lock(&pool->lock);
  valk_gc_page_t *page = pool->all_pages;
  while (page) {
    valk_gc_page_t *next = page->next;
    free(page);
    page = next;
  }
  pool->all_pages = NULL;
  pool->partial_pages = NULL;
  pool->num_pages = 0;
  atomic_store(&pool->total_slots, 0);
  atomic_store(&pool->used_slots, 0);
  pthread_mutex_unlock(&pool->lock);
  pthread_mutex_destroy(&pool->lock);
}

valk_gc_page_t *valk_gc_page_alloc(valk_gc_page_pool_t *pool) {
  valk_gc_page_t *page = aligned_alloc(VALK_GC_PAGE_ALIGN, sizeof(valk_gc_page_t));
  if (!page) {
    VALK_ERROR("Failed to allocate GC page");
    return NULL;
  }
  
  memset(page, 0, sizeof(valk_gc_page_t));
  page->page_id = atomic_fetch_add(&__page_id_counter, 1);
  atomic_store(&page->num_allocated, 0);
  
  pthread_mutex_lock(&pool->lock);
  page->next = pool->all_pages;
  pool->all_pages = page;
  pool->num_pages++;
  atomic_fetch_add(&pool->total_slots, VALK_GC_SLOTS_PER_PAGE);
  pthread_mutex_unlock(&pool->lock);
  
  return page;
}

void valk_gc_tlab_init(valk_gc_tlab_t *tlab) {
  tlab->page = NULL;
  tlab->next_slot = 0;
  tlab->limit_slot = 0;
}

bool valk_gc_tlab_refill(valk_gc_tlab_t *tlab, valk_gc_page_pool_t *pool) {
  pthread_mutex_lock(&pool->lock);
  
  valk_gc_page_t *page = pool->partial_pages;
  uint32_t start_slot = 0;
  uint32_t num_slots = VALK_GC_TLAB_SLOTS;
  
  if (page) {
    uint32_t allocated = atomic_load(&page->num_allocated);
    if (allocated + VALK_GC_TLAB_SLOTS <= VALK_GC_SLOTS_PER_PAGE) {
      for (uint32_t i = 0; i < VALK_GC_SLOTS_PER_PAGE; i++) {
        if (!valk_gc_bitmap_test(page->alloc_bits, i)) {
          uint32_t free_run = 0;
          for (uint32_t j = i; j < VALK_GC_SLOTS_PER_PAGE && free_run < VALK_GC_TLAB_SLOTS; j++) {
            if (!valk_gc_bitmap_test(page->alloc_bits, j)) {
              free_run++;
            } else {
              break;
            }
          }
          if (free_run >= VALK_GC_TLAB_SLOTS) {
            start_slot = i;
            goto found;
          }
          i += free_run;
        }
      }
    }
    pool->partial_pages = page->next;
    page = NULL;
  }
  
  if (!page) {
    pthread_mutex_unlock(&pool->lock);
    page = valk_gc_page_alloc(pool);
    if (!page) return false;
    pthread_mutex_lock(&pool->lock);
    start_slot = 0;
  }

found:;
  uint32_t limit = start_slot + num_slots;
  if (limit > VALK_GC_SLOTS_PER_PAGE) {
    limit = VALK_GC_SLOTS_PER_PAGE;
    num_slots = limit - start_slot;
  }
  
  for (uint32_t i = start_slot; i < limit; i++) {
    valk_gc_bitmap_set(page->alloc_bits, i);
  }
  atomic_fetch_add(&page->num_allocated, num_slots);
  atomic_fetch_add(&pool->used_slots, num_slots);
  
  if (page != pool->partial_pages) {
    page->next = pool->partial_pages;
    pool->partial_pages = page;
  }
  pthread_mutex_unlock(&pool->lock);
  
  tlab->page = page;
  tlab->next_slot = start_slot;
  tlab->limit_slot = limit;
  
  return true;
}

void valk_gc_page_pool_stats(valk_gc_page_pool_t *pool, 
                              size_t *out_pages, size_t *out_total, 
                              size_t *out_used) {
  if (out_pages) *out_pages = pool->num_pages;
  if (out_total) *out_total = atomic_load(&pool->total_slots);
  if (out_used) *out_used = atomic_load(&pool->used_slots);
}

// ============================================================================
// Phase 2: GC Triggering and Participation
// ============================================================================

void valk_gc_request_collection(void) {
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected, 
                                       VALK_GC_PHASE_STW_REQUESTED)) {
    return;
  }
  
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  if (num_threads == 0) {
    atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
    return;
  }
  
  if (valk_gc_coord.barrier_initialized) {
    valk_barrier_destroy(&valk_gc_coord.barrier);
  }
  valk_barrier_init(&valk_gc_coord.barrier, num_threads);
  valk_gc_coord.barrier_initialized = true;
  
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

// ============================================================================
// Phase 3: Root Enumeration
// ============================================================================

void valk_gc_visit_thread_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  valk_thread_context_t *tc = &valk_thread_ctx;
  
  if (tc->root_stack == NULL) return;
  
  for (size_t i = 0; i < tc->root_stack_count; i++) {
    if (tc->root_stack[i] != NULL) {
      visitor(tc->root_stack[i], ctx);
    }
  }
}

void valk_gc_visit_env_roots(valk_lenv_t *env, valk_gc_root_visitor_t visitor, void *ctx) {
  if (env == NULL) return;
  
  for (size_t i = 0; i < env->vals.count; i++) {
    if (env->vals.items[i] != NULL) {
      visitor(env->vals.items[i], ctx);
    }
  }
  
  valk_gc_visit_env_roots(env->parent, visitor, ctx);
  valk_gc_visit_env_roots(env->fallback, visitor, ctx);
}

void valk_gc_visit_global_roots(valk_gc_root_visitor_t visitor, void *ctx) {
  pthread_mutex_lock(&valk_gc_global_roots.lock);
  for (size_t i = 0; i < valk_gc_global_roots.count; i++) {
    valk_lval_t *val = *valk_gc_global_roots.roots[i];
    if (val != NULL) {
      visitor(val, ctx);
    }
  }
  pthread_mutex_unlock(&valk_gc_global_roots.lock);
  
  for (size_t i = 0; i < VALK_GC_MAX_THREADS; i++) {
    if (valk_gc_coord.threads[i].active && valk_gc_coord.threads[i].ctx != NULL) {
      valk_thread_context_t *tc = valk_gc_coord.threads[i].ctx;
      if (tc->root_env != NULL) {
        valk_gc_visit_env_roots(tc->root_env, visitor, ctx);
      }
    }
  }
}

// ============================================================================
// Phase 4: Parallel Mark
// ============================================================================

static void mark_and_push(valk_lval_t *obj, void *ctx);
static void mark_children(valk_lval_t *obj, valk_gc_mark_queue_t *queue);
static void mark_env_parallel(valk_lenv_t *env, valk_gc_mark_queue_t *queue);

static void mark_and_push(valk_lval_t *obj, void *ctx) {
  valk_gc_mark_queue_t *queue = ctx;
  
  if (obj == NULL) return;
  if (!valk_gc_try_mark(obj)) return;
  
  if (!valk_gc_mark_queue_push(queue, obj)) {
    mark_children(obj, queue);
  }
}

static void mark_env_parallel(valk_lenv_t *env, valk_gc_mark_queue_t *queue) {
  if (env == NULL) return;
  
  for (size_t i = 0; i < env->vals.count; i++) {
    mark_and_push(env->vals.items[i], queue);
  }
  
  mark_env_parallel(env->parent, queue);
  mark_env_parallel(env->fallback, queue);
}

static void mark_children(valk_lval_t *obj, valk_gc_mark_queue_t *queue) {
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      mark_and_push(obj->cons.head, queue);
      mark_and_push(obj->cons.tail, queue);
      break;
      
    case LVAL_FUN:
      if (obj->fun.builtin == NULL) {
        mark_and_push(obj->fun.formals, queue);
        mark_and_push(obj->fun.body, queue);
        if (obj->fun.env) {
          mark_env_parallel(obj->fun.env, queue);
        }
      }
      break;
      
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_and_push(obj->async.handle->on_complete, queue);
        mark_and_push(obj->async.handle->on_error, queue);
        mark_and_push(obj->async.handle->on_cancel, queue);
        mark_and_push(obj->async.handle->result, queue);
        mark_and_push(obj->async.handle->error, queue);
        if (obj->async.handle->env) {
          mark_env_parallel(obj->async.handle->env, queue);
        }
      }
      break;
      
    default:
      break;
  }
}

static _Atomic size_t __gc_idle_count = 0;
static _Atomic bool __gc_terminated = false;

bool valk_gc_check_termination(void) {
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  size_t idle = atomic_fetch_add(&__gc_idle_count, 1) + 1;
  
  if (idle == num_threads) {
    bool all_empty = true;
    for (size_t i = 0; i < num_threads; i++) {
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
  
  size_t my_id = valk_thread_ctx.gc_thread_id;
  valk_gc_mark_queue_t *my_queue = &valk_gc_coord.threads[my_id].mark_queue;
  
  atomic_store(&__gc_idle_count, 0);
  atomic_store(&__gc_terminated, false);
  
  valk_gc_mark_queue_init(my_queue);
  
  valk_gc_visit_thread_roots(mark_and_push, my_queue);
  
  if (my_id == 0) {
    valk_gc_visit_global_roots(mark_and_push, my_queue);
  }
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  size_t idle_spins = 0;
  const size_t MAX_IDLE_SPINS = 1000;
  
  while (true) {
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != NULL) {
      mark_children(obj, my_queue);
      idle_spins = 0;
    }
    
    bool found_work = false;
    size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
    
    for (size_t i = 1; i <= num_threads; i++) {
      size_t victim = (my_id + i) % num_threads;
      if (!valk_gc_coord.threads[victim].active) continue;
      
      obj = valk_gc_mark_queue_steal(&valk_gc_coord.threads[victim].mark_queue);
      if (obj != NULL) {
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

// ============================================================================
// Phase 5: Parallel Sweep
// ============================================================================

static size_t sweep_page(valk_gc_page_t *page) {
  size_t freed = 0;
  
  for (uint32_t slot = 0; slot < VALK_GC_SLOTS_PER_PAGE; slot++) {
    if (valk_gc_bitmap_test(page->alloc_bits, slot)) {
      if (!valk_gc_bitmap_test(page->mark_bits, slot)) {
        valk_gc_bitmap_clear(page->alloc_bits, slot);
        freed++;
      } else {
        valk_gc_bitmap_clear(page->mark_bits, slot);
      }
    }
  }
  
  if (freed > 0) {
    atomic_fetch_sub(&page->num_allocated, freed);
  }
  
  return freed;
}

void valk_gc_parallel_sweep(valk_gc_page_pool_t *pool) {
  if (!valk_thread_ctx.gc_registered || pool == NULL) return;
  
  size_t my_id = valk_thread_ctx.gc_thread_id;
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  
  pthread_mutex_lock(&pool->lock);
  size_t num_pages = pool->num_pages;
  valk_gc_page_t *pages_start = pool->all_pages;
  pthread_mutex_unlock(&pool->lock);
  
  if (num_pages == 0) return;
  
  size_t pages_per_thread = (num_pages + num_threads - 1) / num_threads;
  size_t my_start = my_id * pages_per_thread;
  size_t my_end = (my_id + 1) * pages_per_thread;
  if (my_end > num_pages) my_end = num_pages;
  
  size_t freed_slots = 0;
  valk_gc_page_t *page = pages_start;
  
  for (size_t i = 0; i < my_end && page != NULL; i++) {
    if (i >= my_start) {
      freed_slots += sweep_page(page);
    }
    page = page->next;
  }
  
  if (freed_slots > 0) {
    atomic_fetch_sub(&pool->used_slots, freed_slots);
  }
}

// ============================================================================
// Phase 6: Integration - GC Trigger and Full Cycle
// ============================================================================

void valk_gc_full_cycle(valk_gc_page_pool_t *pool) {
  if (!valk_thread_ctx.gc_registered) return;
  
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  if (num_threads == 0) return;
  
  uint64_t start_ns = 0;
  #ifdef VALK_METRICS_ENABLED
  start_ns = uv_hrtime();
  #endif
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_MARKING);
  valk_gc_parallel_mark();
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_SWEEPING);
  valk_gc_parallel_sweep(pool);
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  #ifdef VALK_METRICS_ENABLED
  uint64_t end_ns = uv_hrtime();
  uint64_t pause_us = (end_ns - start_ns) / 1000;
  atomic_fetch_add(&valk_gc_coord.parallel_pause_us_total, pause_us);
  #endif
  
  atomic_store(&valk_gc_coord.threads_paused, 0);
  
  pthread_mutex_lock(&valk_gc_coord.lock);
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  pthread_cond_broadcast(&valk_gc_coord.gc_done);
  pthread_mutex_unlock(&valk_gc_coord.lock);
  
  atomic_fetch_add(&valk_gc_coord.parallel_cycles, 1);
}

void valk_gc_maybe_collect(valk_gc_page_pool_t *pool) {
  if (!valk_thread_ctx.gc_registered || pool == NULL) return;
  
  size_t used = atomic_load(&pool->used_slots);
  size_t threshold = atomic_load(&pool->gc_threshold);
  
  if (used < threshold) return;
  
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected,
                                       VALK_GC_PHASE_STW_REQUESTED)) {
    return;
  }
  
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  if (num_threads == 0) {
    atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
    return;
  }
  
  if (valk_gc_coord.barrier_initialized) {
    valk_barrier_destroy(&valk_gc_coord.barrier);
  }
  valk_barrier_init(&valk_gc_coord.barrier, num_threads);
  valk_gc_coord.barrier_initialized = true;
  
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
  
  valk_gc_full_cycle(pool);
  
  VALK_DEBUG("Parallel GC cycle complete: used=%zu freed=%zu", 
             atomic_load(&pool->used_slots), used - atomic_load(&pool->used_slots));
}

// ============================================================================
// Global Page Pool for TLAB Allocation
// ============================================================================

void valk_gc_global_pool_init(void) {
  if (__global_pool_initialized) return;
  valk_gc_page_pool_init(&valk_gc_global_pool);
  __global_pool_initialized = true;
}

void valk_gc_global_pool_destroy(void) {
  if (!__global_pool_initialized) return;
  valk_gc_page_pool_destroy(&valk_gc_global_pool);
  __global_pool_initialized = false;
}

void *valk_gc_tlab_alloc_slow(size_t bytes) {
  if (bytes > VALK_GC_SLOT_SIZE) {
    VALK_ERROR("TLAB allocation too large: %zu > %d", bytes, VALK_GC_SLOT_SIZE);
    return NULL;
  }
  
  valk_thread_context_t *ctx = &valk_thread_ctx;
  
  if (!ctx->tlab) {
    ctx->tlab = malloc(sizeof(valk_gc_tlab_t));
    if (!ctx->tlab) return NULL;
    valk_gc_tlab_init(ctx->tlab);
  }
  
  if (!ctx->tlab_enabled) {
    if (!__global_pool_initialized) {
      valk_gc_global_pool_init();
    }
    ctx->tlab_enabled = true;
  }
  
  void *ptr = valk_gc_tlab_alloc(ctx->tlab);
  if (ptr) {
    memset(ptr, 0, bytes);
    return ptr;
  }
  
  if (!valk_gc_tlab_refill(ctx->tlab, &valk_gc_global_pool)) {
    VALK_ERROR("Failed to refill TLAB from global pool");
    return NULL;
  }
  
  ptr = valk_gc_tlab_alloc(ctx->tlab);
  if (ptr) {
    memset(ptr, 0, bytes);
  }
  return ptr;
}

// Forward declarations
static void valk_gc_mark_lval(valk_lval_t* v);
static void valk_gc_mark_env(valk_lenv_t* env);
static void valk_gc_mark_allocation(void* ptr);
static void valk_gc_clear_marks_recursive(valk_lval_t* v);

// ============================================================================
// Forwarding Pointer Helpers (for scratch evacuation)
// ============================================================================

// Set forwarding pointer: mark src as forwarded, point to dst
void valk_lval_set_forward(valk_lval_t* src, valk_lval_t* dst) {
  // Preserve allocation bits but set type to LVAL_FORWARD
  src->flags = LVAL_FORWARD | (src->flags & ~LVAL_TYPE_MASK);
  src->forward = dst;
}

// Check if value is a forwarding pointer
bool valk_lval_is_forwarded(valk_lval_t* v) {
  return v != NULL && LVAL_TYPE(v) == LVAL_FORWARD;
}

// Follow forwarding pointer chain to find final destination
valk_lval_t* valk_lval_follow_forward(valk_lval_t* v) {
  while (v != NULL && LVAL_TYPE(v) == LVAL_FORWARD) {
    v = v->forward;
  }
  return v;
}

// ============================================================================
// GC Heap - Legacy API wrappers around valk_gc_heap2_t
// ============================================================================

// Initialize GC heap (now delegates to valk_gc_heap2_create)
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t hard_limit) {
  return valk_gc_heap2_create(hard_limit);
}

// Set hard limit for GC heap
void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, size_t limit) {
  if (!heap) return;
  size_t used = valk_gc_heap2_used_bytes(heap);
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
uint8_t valk_gc_heap_usage_pct(valk_gc_malloc_heap_t* heap) {
  if (!heap || heap->hard_limit == 0) return 0;
  size_t used = valk_gc_heap2_used_bytes(heap);
  uint8_t pct = (uint8_t)((used * 100) / heap->hard_limit);
  return pct > 100 ? 100 : pct;
}

// Configure GC thresholds
void valk_gc_set_thresholds(valk_gc_malloc_heap_t* heap,
                            uint8_t threshold_pct,
                            uint8_t target_pct,
                            uint32_t min_interval_ms) {
  if (!heap) return;
  heap->gc_threshold_pct = threshold_pct > 0 ? threshold_pct : 75;
  heap->gc_target_pct = target_pct > 0 ? target_pct : 50;
  heap->min_gc_interval_ms = min_interval_ms;
}

// Check if GC should run
bool valk_gc_malloc_should_collect(valk_gc_malloc_heap_t* heap) {
  if (!heap) return false;
  uint8_t usage_pct = valk_gc_heap_usage_pct(heap);
  if (usage_pct < heap->gc_threshold_pct) return false;
  if (heap->min_gc_interval_ms > 0 && heap->last_gc_time_us > 0) {
    uint64_t now_us = uv_hrtime() / 1000;
    uint64_t elapsed_ms = (now_us - heap->last_gc_time_us) / 1000;
    if (elapsed_ms < heap->min_gc_interval_ms) return false;
  }
  return true;
}

// Allocate from GC heap (delegates to heap2)
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, size_t bytes) {
  return valk_gc_heap2_alloc(heap, bytes);
}


// ============================================================================
// Legacy GC API - Implemented using valk_gc_heap2_t
// ============================================================================

// Perform mark & sweep collection (delegates to heap2)
size_t valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap, valk_lval_t* additional_root) {
  if (!heap) return 0;
  (void)additional_root;
  return valk_gc_heap2_collect(heap);
}

// Explicitly free a single GC heap object (no-op for heap2 - objects are freed during sweep)
void valk_gc_free_object(void* heap_ptr, void* user_ptr) {
  (void)heap_ptr;
  (void)user_ptr;
}

// Destroy heap (delegates to heap2)
void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap) {
  valk_gc_heap2_destroy(heap);
}

// ============================================================================
// GC Runtime Metrics Export
// ============================================================================

void valk_gc_get_runtime_metrics(valk_gc_malloc_heap_t* heap,
                                  uint64_t* cycles, uint64_t* pause_us_total,
                                  uint64_t* pause_us_max, uint64_t* reclaimed,
                                  size_t* heap_used, size_t* heap_total) {
  if (!heap) return;

  if (cycles) *cycles = atomic_load(&heap->runtime_metrics.cycles_total);
  if (pause_us_total) *pause_us_total = atomic_load(&heap->runtime_metrics.pause_us_total);
  if (pause_us_max) *pause_us_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  if (reclaimed) *reclaimed = atomic_load(&heap->runtime_metrics.reclaimed_bytes_total);

  if (heap_used) *heap_used = valk_gc_heap2_used_bytes(heap);
  if (heap_total) *heap_total = heap->hard_limit;
}

uint64_t valk_gc_get_allocated_bytes_total(valk_gc_malloc_heap_t* heap) {
  if (!heap) return 0;
  return atomic_load(&heap->runtime_metrics.allocated_bytes_total);
}

uint8_t valk_gc_get_last_efficiency(valk_gc_malloc_heap_t* heap) {
  if (!heap) return 0;
  uint64_t before = atomic_load(&heap->runtime_metrics.last_heap_before_gc);
  uint64_t reclaimed = atomic_load(&heap->runtime_metrics.last_reclaimed);
  if (before == 0) return 0;
  uint64_t pct = (reclaimed * 100) / before;
  return (uint8_t)(pct > 100 ? 100 : pct);
}

void valk_gc_get_survival_histogram(valk_gc_malloc_heap_t* heap,
                                     uint64_t* gen_0, uint64_t* gen_1_5,
                                     uint64_t* gen_6_20, uint64_t* gen_21_plus) {
  if (!heap) return;
  if (gen_0) *gen_0 = atomic_load(&heap->runtime_metrics.survival_gen_0);
  if (gen_1_5) *gen_1_5 = atomic_load(&heap->runtime_metrics.survival_gen_1_5);
  if (gen_6_20) *gen_6_20 = atomic_load(&heap->runtime_metrics.survival_gen_6_20);
  if (gen_21_plus) *gen_21_plus = atomic_load(&heap->runtime_metrics.survival_gen_21_plus);
}

void valk_gc_get_pause_histogram(valk_gc_malloc_heap_t* heap,
                                  uint64_t* pause_0_1ms, uint64_t* pause_1_5ms,
                                  uint64_t* pause_5_10ms, uint64_t* pause_10_16ms,
                                  uint64_t* pause_16ms_plus) {
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
  out->malloc_peak = heap->stats.peak_usage;

  out->free_list_count = 0;
  out->free_list_bytes = 0;
}

// ============================================================================
// GC Statistics Printing (heap2)
// ============================================================================

void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap) {
  if (heap == NULL) return;

  valk_gc_stats2_t stats;
  valk_gc_heap2_get_stats(heap, &stats);

  fprintf(stderr, "\n=== GC Heap Statistics ===\n");
  uint8_t usage_pct = valk_gc_heap_usage_pct(heap);
  fprintf(stderr, "Heap usage:       %u%% (threshold: %u%%, hard limit: %zu bytes)\n",
          usage_pct, heap->gc_threshold_pct, heap->hard_limit);
  fprintf(stderr, "Used bytes:       %zu bytes\n", stats.used_bytes);
  fprintf(stderr, "Committed bytes:  %zu bytes\n", stats.committed_bytes);
  fprintf(stderr, "Large objects:    %zu bytes\n", stats.large_object_bytes);
  fprintf(stderr, "Peak usage:       %zu bytes\n", heap->stats.peak_usage);
  fprintf(stderr, "Collections:      %llu\n", (unsigned long long)stats.collections);
  fprintf(stderr, "Emergency GCs:    %zu\n", heap->stats.emergency_collections);

  fprintf(stderr, "--- Per-Class Usage ---\n");
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    if (stats.class_total_slots[c] > 0) {
      size_t pct = (stats.class_used_slots[c] * 100) / stats.class_total_slots[c];
      fprintf(stderr, "  Class %d (%4u B): %zu / %zu slots (%zu%%)\n",
              c, valk_gc_size_classes[c],
              stats.class_used_slots[c], stats.class_total_slots[c], pct);
    }
  }

  if (heap->stats.evacuations_from_scratch > 0) {
    fprintf(stderr, "--- Evacuation Stats ---\n");
    fprintf(stderr, "Values evacuated: %zu\n", heap->stats.evacuations_from_scratch);
    fprintf(stderr, "Bytes evacuated:  %zu\n", heap->stats.evacuation_bytes);
    fprintf(stderr, "Pointers fixed:   %zu\n", heap->stats.evacuation_pointer_fixups);
  }
  fprintf(stderr, "=========================\n\n");
}

void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out) {
  if (out == NULL) out = stderr;

  fprintf(out, "\n=== Memory Statistics ===\n");

  if (scratch != NULL) {
    double usage = (double)scratch->offset / scratch->capacity * 100.0;
    fprintf(out, "Scratch Arena:\n");
    fprintf(out, "  Usage:       %.1f%% (%zu / %zu bytes)\n",
            usage, scratch->offset, scratch->capacity);
    fprintf(out, "  High Water:  %zu bytes\n", scratch->stats.high_water_mark);
    fprintf(out, "  Allocations: %zu\n", scratch->stats.total_allocations);
    fprintf(out, "  Resets:      %zu\n", scratch->stats.num_resets);
    fprintf(out, "  Checkpoints: %zu\n", scratch->stats.num_checkpoints);
    if (scratch->stats.overflow_fallbacks > 0) {
      fprintf(out, "  Overflows:   %zu (%zu bytes)\n",
              scratch->stats.overflow_fallbacks, scratch->stats.overflow_bytes);
    }
    fprintf(out, "\n");
  }

  if (heap != NULL) {
    valk_gc_stats2_t stats;
    valk_gc_heap2_get_stats(heap, &stats);

    double usage = (double)stats.used_bytes / heap->hard_limit * 100.0;
    fprintf(out, "GC Heap (heap2):\n");
    fprintf(out, "  Usage:       %.1f%% (%zu / %zu bytes)\n",
            usage, stats.used_bytes, heap->hard_limit);
    fprintf(out, "  Committed:   %zu bytes\n", stats.committed_bytes);
    fprintf(out, "  Large objs:  %zu bytes\n", stats.large_object_bytes);
    fprintf(out, "  Collections: %llu\n", (unsigned long long)stats.collections);
    fprintf(out, "  Reclaimed:   %llu bytes total\n",
            (unsigned long long)stats.bytes_reclaimed_total);
  }

  fprintf(out, "=========================\n\n");
}

// ============================================================================
// Retained Size Sampling - Sample top bindings by retained memory
// ============================================================================

static size_t estimate_lval_size(valk_lval_t* v, valk_gc_malloc_heap_t* heap) {
  (void)heap;
  if (v == NULL) return 0;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return 0;

  size_t size = sizeof(valk_lval_t);

  switch (LVAL_TYPE(v)) {
    case LVAL_STR:
    case LVAL_SYM:
    case LVAL_ERR:
      if (v->str != NULL) {
        size += strlen(v->str) + 1;
      }
      break;
    case LVAL_FUN:
      if (v->fun.name != NULL) {
        size += strlen(v->fun.name) + 1;
      }
      size += estimate_lval_size(v->fun.formals, heap);
      size += estimate_lval_size(v->fun.body, heap);
      break;
    case LVAL_CONS:
    case LVAL_QEXPR:
      size += estimate_lval_size(v->cons.head, heap);
      size += estimate_lval_size(v->cons.tail, heap);
      break;
    default:
      break;
  }
  return size;
}

static size_t count_lval_objects(valk_lval_t* v) {
  if (v == NULL) return 0;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return 0;

  size_t count = 1;
  switch (LVAL_TYPE(v)) {
    case LVAL_FUN:
      count += count_lval_objects(v->fun.formals);
      count += count_lval_objects(v->fun.body);
      break;
    case LVAL_CONS:
    case LVAL_QEXPR:
      count += count_lval_objects(v->cons.head);
      count += count_lval_objects(v->cons.tail);
      break;
    default:
      break;
  }
  return count;
}

void valk_gc_sample_retained_sets(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env,
                                   valk_retained_sets_t* out) {
  if (!out) return;
  memset(out, 0, sizeof(*out));
  if (!heap || !root_env) return;

  for (size_t i = 0; i < root_env->vals.count && out->count < VALK_RETAINED_SET_MAX; i++) {
    const char* sym = root_env->symbols.items[i];
    valk_lval_t* val = root_env->vals.items[i];

    if (sym == NULL || val == NULL) continue;
    if (LVAL_TYPE(val) == LVAL_FUN && val->fun.builtin != NULL) continue;

    size_t retained_bytes = estimate_lval_size(val, heap);
    size_t object_count = count_lval_objects(val);

    if (retained_bytes == 0) continue;

    size_t insert_pos = out->count;
    for (size_t j = 0; j < out->count; j++) {
      if (retained_bytes > out->sets[j].retained_bytes) {
        insert_pos = j;
        break;
      }
    }

    if (insert_pos < VALK_RETAINED_SET_MAX) {
      if (out->count < VALK_RETAINED_SET_MAX) {
        for (size_t j = out->count; j > insert_pos; j--) {
          out->sets[j] = out->sets[j - 1];
        }
        out->count++;
      } else {
        for (size_t j = VALK_RETAINED_SET_MAX - 1; j > insert_pos; j--) {
          out->sets[j] = out->sets[j - 1];
        }
      }

      valk_retained_set_t* set = &out->sets[insert_pos];
      strncpy(set->name, sym, VALK_RETAINED_SET_NAME_MAX - 1);
      set->name[VALK_RETAINED_SET_NAME_MAX - 1] = '\0';
      set->retained_bytes = retained_bytes;
      set->object_count = object_count;
    }
  }
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
                                  int64_t* heap_delta, int64_t* scratch_delta,
                                  int64_t* lval_delta, int64_t* lenv_delta) {
  if (!before || !after) return;
  if (heap_delta) *heap_delta = (int64_t)after->heap_used_bytes - (int64_t)before->heap_used_bytes;
  if (scratch_delta) *scratch_delta = (int64_t)after->scratch_used_bytes - (int64_t)before->scratch_used_bytes;
  if (lval_delta) *lval_delta = (int64_t)after->lval_count - (int64_t)before->lval_count;
  if (lenv_delta) *lenv_delta = (int64_t)after->lenv_count - (int64_t)before->lenv_count;
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

void valk_repl_set_eval_delta(int64_t heap, int64_t scratch, int64_t lval, int64_t lenv) {
  g_repl_eval_delta.heap_delta = heap;
  g_repl_eval_delta.scratch_delta = scratch;
  g_repl_eval_delta.lval_delta = lval;
  g_repl_eval_delta.lenv_delta = lenv;
  g_repl_eval_delta.eval_count++;
  g_repl_eval_delta_valid = true;
}

// ============================================================================
// Arena-based GC (backward compatibility, informational only)
// ============================================================================

bool valk_gc_should_collect_arena(valk_mem_arena_t* arena) {
  return (arena->offset > (arena->capacity * 9 / 10));
}

size_t valk_gc_collect_arena(valk_lenv_t* root_env, valk_mem_arena_t* arena) {
  if (root_env == NULL) {
    return 0;
  }

  // Mark from roots
  valk_gc_mark_env(root_env);

  // Count dead objects (can't actually free from arena)
  size_t dead_count = 0;
  uint8_t* ptr = arena->heap;
  uint8_t* end = arena->heap + arena->offset;

  while (ptr < end) {
    valk_lval_t* v = (valk_lval_t*)ptr;
    if ((v->flags & LVAL_TYPE_MASK) <= LVAL_FORWARD) {
      if (!(v->flags & LVAL_FLAG_GC_MARK)) {
        dead_count++;
      }
    }
    ptr += sizeof(valk_lval_t);
  }

  // Clear marks
  for (size_t i = 0; i < root_env->vals.count; i++) {
    valk_gc_clear_marks_recursive(root_env->vals.items[i]);
  }

  return dead_count * sizeof(valk_lval_t);
}

// ============================================================================
// Environment and Lval Worklists for Iterative Traversal
// ============================================================================

#define ENV_WORKLIST_INITIAL_CAPACITY 64

typedef struct {
  valk_lenv_t** items;
  size_t count;
  size_t capacity;
} valk_env_worklist_t;

static void env_worklist_init(valk_env_worklist_t* wl) {
  wl->items = malloc(ENV_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lenv_t*));
  wl->count = 0;
  wl->capacity = ENV_WORKLIST_INITIAL_CAPACITY;
}

static void env_worklist_free(valk_env_worklist_t* wl) {
  if (wl->items) {
    free(wl->items);
    wl->items = NULL;
  }
  wl->count = 0;
  wl->capacity = 0;
}

static void env_worklist_push(valk_env_worklist_t* wl, valk_lenv_t* env) {
  if (env == NULL) return;
  if (wl->count >= wl->capacity) {
    size_t new_cap = wl->capacity * 2;
    valk_lenv_t** new_items = realloc(wl->items, new_cap * sizeof(valk_lenv_t*));
    if (new_items == NULL) {
      VALK_ERROR("Failed to grow env worklist");
      return;
    }
    wl->items = new_items;
    wl->capacity = new_cap;
  }
  wl->items[wl->count++] = env;
}

static valk_lenv_t* env_worklist_pop(valk_env_worklist_t* wl) {
  if (wl->count == 0) return NULL;
  return wl->items[--wl->count];
}

// ============================================================================
// Checkpoint-based Evacuation (Phase 3)
// ============================================================================

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
}

// Free evacuation context lists
static void evac_ctx_free(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist) {
    free(ctx->worklist);
    ctx->worklist = NULL;
  }
  ctx->worklist_count = 0;
  ctx->worklist_capacity = 0;

  if (ctx->evacuated) {
    free(ctx->evacuated);
    ctx->evacuated = NULL;
  }
  ctx->evacuated_count = 0;
  ctx->evacuated_capacity = 0;
}

// Add value to evacuated list (for pointer fixing phase)
static void evac_add_evacuated(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  // Grow if at capacity
  if (ctx->evacuated_count >= ctx->evacuated_capacity) {
    size_t new_cap = ctx->evacuated_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->evacuated, new_cap * sizeof(valk_lval_t*));
    if (new_list == NULL) {
      VALK_ERROR("Failed to grow evacuated list");
      return;
    }
    ctx->evacuated = new_list;
    ctx->evacuated_capacity = new_cap;
  }

  ctx->evacuated[ctx->evacuated_count++] = v;
}

// Push value to worklist
static void evac_worklist_push(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  // Grow if at capacity
  if (ctx->worklist_count >= ctx->worklist_capacity) {
    size_t new_cap = ctx->worklist_capacity * 2;
    valk_lval_t** new_list = realloc(ctx->worklist, new_cap * sizeof(valk_lval_t*));
    if (new_list == NULL) {
      VALK_ERROR("Failed to grow evacuation worklist");
      return;
    }
    ctx->worklist = new_list;
    ctx->worklist_capacity = new_cap;
  }

  ctx->worklist[ctx->worklist_count++] = v;
}

// Pop value from worklist
static valk_lval_t* evac_worklist_pop(valk_evacuation_ctx_t* ctx) {
  if (ctx->worklist_count == 0) return NULL;
  return ctx->worklist[--ctx->worklist_count];
}

// Add an already-allocated value to GC heap's object tracking
// NOTE: With heap2, objects are tracked via page allocation bitmaps,
// so this function is now a no-op. Kept for API compatibility.
void valk_gc_add_to_objects(valk_gc_malloc_heap_t* heap, valk_lval_t* v) {
  (void)heap;
  (void)v;
}

// ============================================================================
// GC Marking Functions (legacy wrappers for heap2)
// ============================================================================

static void valk_gc_mark_lval(valk_lval_t* v) {
  if (v == NULL) return;
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
    case LVAL_QEXPR:
      valk_gc_mark_lval(v->cons.head);
      valk_gc_mark_lval(v->cons.tail);
      break;
    case LVAL_HANDLE:
      if (v->async.handle) {
        valk_gc_mark_lval(v->async.handle->on_complete);
        valk_gc_mark_lval(v->async.handle->on_error);
        valk_gc_mark_lval(v->async.handle->on_cancel);
        valk_gc_mark_lval(v->async.handle->result);
        valk_gc_mark_lval(v->async.handle->error);
        if (v->async.handle->env) valk_gc_mark_env(v->async.handle->env);
      }
      break;
    default:
      break;
  }
}

static void valk_gc_mark_env(valk_lenv_t* env) {
  if (env == NULL) return;
  for (size_t i = 0; i < env->vals.count; i++) {
    valk_gc_mark_lval(env->vals.items[i]);
  }
  if (env->parent) valk_gc_mark_env(env->parent);
  if (env->fallback) valk_gc_mark_env(env->fallback);
}

static void valk_gc_clear_marks_recursive(valk_lval_t* v) {
  if (v == NULL) return;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return;
  if (!(v->flags & LVAL_FLAG_GC_MARK)) return;
  v->flags &= ~LVAL_FLAG_GC_MARK;

  switch (LVAL_TYPE(v)) {
    case LVAL_FUN:
      if (v->fun.env) {
        for (size_t i = 0; i < v->fun.env->vals.count; i++) {
          valk_gc_clear_marks_recursive(v->fun.env->vals.items[i]);
        }
      }
      valk_gc_clear_marks_recursive(v->fun.formals);
      valk_gc_clear_marks_recursive(v->fun.body);
      break;
    case LVAL_CONS:
    case LVAL_QEXPR:
      valk_gc_clear_marks_recursive(v->cons.head);
      valk_gc_clear_marks_recursive(v->cons.tail);
      break;
    default:
      break;
  }
}

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
  if (scratch == NULL) return false;
  return (float)scratch->offset / scratch->capacity > threshold;
}

// Forward declarations for evacuation helpers
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v);
static void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env);

// ============================================================================
// Phase 1: Copy Values from Scratch to Heap
// ============================================================================

// Evacuate a single value from scratch to heap
// Returns the new location (or original if not in scratch or already forwarded)
static valk_lval_t* valk_evacuate_value(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return NULL;

  // Already forwarded? Return destination
  if (LVAL_TYPE(v) == LVAL_FORWARD) {
    return v->forward;
  }

  // Not in scratch? Return as-is (already in heap or global)
  if (LVAL_ALLOC(v) != LVAL_ALLOC_SCRATCH) {
    return v;
  }

  // Allocate new value in heap
  valk_lval_t* new_val = NULL;
  VALK_WITH_ALLOC((void*)ctx->heap) {
    new_val = valk_mem_alloc(sizeof(valk_lval_t));
  }

  if (new_val == NULL) {
    VALK_ERROR("Failed to allocate value during evacuation");
    return v;
  }

  // Copy the value data
  memcpy(new_val, v, sizeof(valk_lval_t));

  // Update allocation flags: clear scratch, set heap
  new_val->flags = (new_val->flags & ~LVAL_ALLOC_MASK) | LVAL_ALLOC_HEAP;
  new_val->origin_allocator = ctx->heap;

  // Copy strings for string types (they're also in scratch arena)
  switch (LVAL_TYPE(new_val)) {
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      if (new_val->str != NULL && valk_ptr_in_arena(ctx->scratch, new_val->str)) {
        size_t len = strlen(v->str) + 1;
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
      if (new_val->fun.name != NULL && new_val->fun.builtin == NULL &&
          valk_ptr_in_arena(ctx->scratch, new_val->fun.name)) {
        size_t len = strlen(v->fun.name) + 1;
        VALK_WITH_ALLOC((void*)ctx->heap) {
          new_val->fun.name = valk_mem_alloc(len);
        }
        if (new_val->fun.name) {
          memcpy(new_val->fun.name, v->fun.name, len);
          ctx->bytes_copied += len;
        }
      }
      break;

    default:
      break;
  }

  // Set forwarding pointer in old location
  valk_lval_set_forward(v, new_val);

  // Add to evacuated list for pointer fixing phase
  evac_add_evacuated(ctx, new_val);

  // Update stats
  ctx->values_copied++;
  ctx->bytes_copied += sizeof(valk_lval_t);

  return new_val;
}

// Evacuate children of a value (push to worklist for processing)
static void valk_evacuate_children(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      // Evacuate and queue head (only if freshly evacuated, not already processed)
      if (v->cons.head != NULL) {
        valk_lval_t* old_head = v->cons.head;
        valk_lval_t* new_head = valk_evacuate_value(ctx, old_head);
        if (new_head != old_head) {
          v->cons.head = new_head;
          // Only push if pointer changed (freshly evacuated from scratch)
          if (new_head != NULL) {
            evac_worklist_push(ctx, new_head);
          }
        }
      }
      // Evacuate and queue tail (only if freshly evacuated, not already processed)
      if (v->cons.tail != NULL) {
        valk_lval_t* old_tail = v->cons.tail;
        valk_lval_t* new_tail = valk_evacuate_value(ctx, old_tail);
        if (new_tail != old_tail) {
          v->cons.tail = new_tail;
          // Only push if pointer changed (freshly evacuated from scratch)
          if (new_tail != NULL) {
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
      if (v->fun.name != NULL && v->fun.builtin == NULL &&
          !valk_ptr_in_arena(ctx->scratch, v->fun.name)) {
        size_t len = strlen(v->fun.name) + 1;
        char* new_name = NULL;
        VALK_WITH_ALLOC((void*)ctx->heap) { new_name = valk_mem_alloc(len); }
        if (new_name) {
          memcpy(new_name, v->fun.name, len);
          v->fun.name = new_name;
          ctx->bytes_copied += len;
        }
      }

      if (v->fun.builtin == NULL) {
        // Evacuate formals (only if freshly evacuated)
        if (v->fun.formals != NULL) {
          valk_lval_t* old_formals = v->fun.formals;
          valk_lval_t* new_formals = valk_evacuate_value(ctx, old_formals);
          if (new_formals != old_formals) {
            v->fun.formals = new_formals;
            if (new_formals != NULL) {
              evac_worklist_push(ctx, new_formals);
            }
          }
        }
        // Evacuate body (only if freshly evacuated)
        if (v->fun.body != NULL) {
          valk_lval_t* old_body = v->fun.body;
          valk_lval_t* new_body = valk_evacuate_value(ctx, old_body);
          if (new_body != old_body) {
            v->fun.body = new_body;
            if (new_body != NULL) {
              evac_worklist_push(ctx, new_body);
            }
          }
        }
        // Evacuate closure environment
        if (v->fun.env != NULL) {
          valk_evacuate_env(ctx, v->fun.env);
        }
      }
      break;

    case LVAL_STR:
    case LVAL_SYM:
    case LVAL_ERR:
      // Evacuate ALL string data to GC heap unconditionally
      // This ensures GC heap self-containment (handles scratch AND libc malloc strings)
      if (v->str != NULL) {
        size_t len = strlen(v->str) + 1;
        char* new_str = NULL;
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
static void valk_evacuate_env_single(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  // Evacuate symbol strings array if in scratch
  if (env->symbols.items != NULL && valk_ptr_in_arena(ctx->scratch, env->symbols.items)) {
    size_t array_size = env->symbols.capacity * sizeof(char*);
    char** new_items = NULL;
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
  for (size_t i = 0; i < env->symbols.count; i++) {
    char* sym = env->symbols.items[i];
    if (sym == NULL) continue;

    // Allocate new string in GC heap
    size_t len = strlen(sym) + 1;
    char* new_str = NULL;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_str = valk_mem_alloc(len);
    }
    if (new_str && new_str != sym) {  // Only copy if we got a NEW allocation
      memcpy(new_str, sym, len);
      env->symbols.items[i] = new_str;
      ctx->bytes_copied += len;
    }
  }

  // Evacuate values array if in scratch
  if (env->vals.items != NULL && valk_ptr_in_arena(ctx->scratch, env->vals.items)) {
    size_t array_size = env->vals.capacity * sizeof(valk_lval_t*);
    valk_lval_t** new_items = NULL;
    VALK_WITH_ALLOC((void*)ctx->heap) {
      new_items = valk_mem_alloc(array_size);
    }
    if (new_items) {
      memcpy(new_items, env->vals.items, env->vals.count * sizeof(valk_lval_t*));
      env->vals.items = new_items;
      ctx->bytes_copied += array_size;
    }
  }

  // Evacuate each value in the environment (only push if freshly evacuated)
  for (size_t i = 0; i < env->vals.count; i++) {
    valk_lval_t* val = env->vals.items[i];
    if (val != NULL) {
      valk_lval_t* new_val = valk_evacuate_value(ctx, val);
      if (new_val != val) {
        env->vals.items[i] = new_val;
        // Only push to worklist if freshly evacuated (pointer changed)
        if (new_val != NULL) {
          evac_worklist_push(ctx, new_val);
        }
      }
    }
  }
}

// Evacuate an environment's arrays and values (iterative to avoid stack overflow)
static void valk_evacuate_env(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == NULL) return;

  // Use iterative worklist to avoid stack overflow on deep env chains
  valk_env_worklist_t worklist;
  env_worklist_init(&worklist);

  // Track visited environments to prevent infinite loops on cycles
  valk_env_worklist_t visited;
  env_worklist_init(&visited);

  env_worklist_push(&worklist, env);

  while (worklist.count > 0) {
    valk_lenv_t* current = env_worklist_pop(&worklist);
    if (current == NULL) continue;

    // Check if already visited (linear search, but usually small number of envs)
    bool already_visited = false;
    for (size_t i = 0; i < visited.count; i++) {
      if (visited.items[i] == current) {
        already_visited = true;
        break;
      }
    }
    if (already_visited) continue;

    // Mark as visited
    env_worklist_push(&visited, current);

    // Process this environment
    valk_evacuate_env_single(ctx, current);

    // Queue parent and fallback for processing unconditionally.
    // We must traverse ALL reachable environments, not just scratch-allocated ones,
    // because heap-allocated environments may contain pointers to scratch-allocated
    // values that need to be evacuated.
    if (current->parent != NULL) {
      env_worklist_push(&worklist, current->parent);
    }
    if (current->fallback != NULL) {
      env_worklist_push(&worklist, current->fallback);
    }
  }

  env_worklist_free(&worklist);
  env_worklist_free(&visited);
}

// ============================================================================
// Phase 2: Fix Pointers to Use New Locations
// ============================================================================

// Helper: Check if pointer is in scratch and handle accordingly
// Returns true if pointer was in scratch (and should be handled), false otherwise
static inline bool fix_scratch_pointer(valk_evacuation_ctx_t* ctx, valk_lval_t** ptr) {
  valk_lval_t* val = *ptr;
  if (val == NULL) return false;

  // If in scratch and forwarded, update to new location
  if (valk_lval_is_forwarded(val)) {
    *ptr = valk_lval_follow_forward(val);
    ctx->pointers_fixed++;
    return true;
  }

  // If in scratch but NOT forwarded, it's unreachable - null it out
  if (valk_ptr_in_arena(ctx->scratch, val)) {
    *ptr = NULL;
    return true;
  }

  return false;
}

// Fix pointers in a value to follow forwarding pointers
static void valk_fix_pointers(valk_evacuation_ctx_t* ctx, valk_lval_t* v) {
  if (v == NULL) return;

  // Skip if still in scratch (shouldn't happen after proper evacuation)
  if (LVAL_ALLOC(v) == LVAL_ALLOC_SCRATCH) return;

  switch (LVAL_TYPE(v)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      fix_scratch_pointer(ctx, &v->cons.head);
      fix_scratch_pointer(ctx, &v->cons.tail);
      break;

    case LVAL_FUN:
      if (v->fun.builtin == NULL) {
        fix_scratch_pointer(ctx, &v->fun.formals);
        fix_scratch_pointer(ctx, &v->fun.body);
        if (v->fun.env != NULL) {
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
static void valk_fix_env_pointers_single(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  // Evacuate symbols.items array if in scratch
  if (env->symbols.items != NULL && valk_ptr_in_arena(ctx->scratch, env->symbols.items)) {
    size_t array_size = env->symbols.capacity * sizeof(char*);
    char** new_items = NULL;
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
  for (size_t i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items[i] && valk_ptr_in_arena(ctx->scratch, env->symbols.items[i])) {
      size_t len = strlen(env->symbols.items[i]) + 1;
      char* new_str = NULL;
      VALK_WITH_ALLOC((void*)ctx->heap) { new_str = valk_mem_alloc(len); }
      if (new_str) {
        memcpy(new_str, env->symbols.items[i], len);
        env->symbols.items[i] = new_str;
        ctx->bytes_copied += len;
      }
    }
  }

  // Evacuate vals.items array if in scratch
  if (env->vals.items != NULL && valk_ptr_in_arena(ctx->scratch, env->vals.items)) {
    size_t array_size = env->vals.capacity * sizeof(valk_lval_t*);
    valk_lval_t** new_items = NULL;
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
  for (size_t i = 0; i < env->vals.count; i++) {
    fix_scratch_pointer(ctx, &env->vals.items[i]);
  }
}

// Fix pointers in an environment (iterative to avoid stack overflow)
static void valk_fix_env_pointers(valk_evacuation_ctx_t* ctx, valk_lenv_t* env) {
  if (env == NULL) return;

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
    if (current == NULL) continue;

    // Check if already visited (linear search, but usually small number of envs)
    bool already_visited = false;
    for (size_t i = 0; i < visited.count; i++) {
      if (visited.items[i] == current) {
        already_visited = true;
        break;
      }
    }
    if (already_visited) continue;

    // Mark as visited
    env_worklist_push(&visited, current);

    // Process this environment
    valk_fix_env_pointers_single(ctx, current);

    // Queue parent and fallback for processing
    if (current->parent != NULL) {
      env_worklist_push(&worklist, current->parent);
    }
    if (current->fallback != NULL) {
      env_worklist_push(&worklist, current->fallback);
    }
  }

  env_worklist_free(&worklist);
  env_worklist_free(&visited);
}

// ============================================================================
// Checkpoint: Evacuate and Reset
// ============================================================================

void valk_checkpoint(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap,
                     valk_lenv_t* root_env) {
  if (scratch == NULL || heap == NULL) {
    VALK_WARN("Checkpoint called with NULL scratch or heap");
    return;
  }



  // Initialize evacuation context
  valk_evacuation_ctx_t ctx = {
    .scratch = scratch,
    .heap = heap,
    .worklist = NULL,
    .worklist_count = 0,
    .worklist_capacity = 0,
    .evacuated = NULL,
    .evacuated_count = 0,
    .evacuated_capacity = 0,
    .values_copied = 0,
    .bytes_copied = 0,
    .pointers_fixed = 0,
  };

  evac_ctx_init(&ctx);

  // Phase 1: Evacuate all reachable values from root environment
  VALK_DEBUG("Checkpoint Phase 1: Starting evacuation from scratch arena");
  if (root_env != NULL) {
    valk_evacuate_env(&ctx, root_env);

    // Process worklist until empty (evacuate children)
    while (ctx.worklist_count > 0) {
      valk_lval_t* v = evac_worklist_pop(&ctx);
      valk_evacuate_children(&ctx, v);
    }
  }
  VALK_DEBUG("Checkpoint Phase 1: Evacuated %zu values (%zu bytes)",
             ctx.values_copied, ctx.bytes_copied);

  // Phase 2: Fix all pointers in evacuated values only
  // This avoids iterating heap pages which may contain non-value allocations
  VALK_DEBUG("Checkpoint Phase 2: Fixing pointers in %zu evacuated values",
             ctx.evacuated_count);
  for (size_t i = 0; i < ctx.evacuated_count; i++) {
    valk_fix_pointers(&ctx, ctx.evacuated[i]);
  }

  // Fix pointers in root environment
  if (root_env != NULL) {
    valk_fix_env_pointers(&ctx, root_env);
  }
  VALK_DEBUG("Checkpoint Phase 2: Fixed %zu pointers", ctx.pointers_fixed);

  // Update scratch arena stats
  scratch->stats.num_checkpoints++;
  scratch->stats.bytes_evacuated += ctx.bytes_copied;
  scratch->stats.values_evacuated += ctx.values_copied;

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
}

// ============================================================================
// Phase 1: Multi-Class Heap Implementation (New Size Class Allocator)
// ============================================================================

#include <sys/mman.h>

// Initialize a page list for a specific size class
static void valk_gc_page_list_init(valk_gc_page_list_t *list, uint8_t size_class) {
  pthread_mutex_init(&list->lock, NULL);
  list->all_pages = NULL;
  list->partial_pages = NULL;
  list->num_pages = 0;
  atomic_store(&list->total_slots, 0);
  atomic_store(&list->used_slots, 0);
  atomic_store(&list->next_page_offset, 0);
  list->slot_size = valk_gc_size_classes[size_class];
  list->slots_per_page = valk_gc_slots_per_page(size_class);
}

// Initialize multi-class TLAB
void valk_gc_tlab2_init(valk_gc_tlab2_t *tlab) {
  tlab->owner_heap = NULL;
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = NULL;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
}

// Allocate a new page for a specific size class
static valk_gc_page2_t *valk_gc_page2_alloc(valk_gc_heap2_t *heap, uint8_t size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return NULL;
  
  size_t page_size = valk_gc_page_total_size(size_class);
  uint16_t slots = valk_gc_slots_per_page(size_class);
  uint16_t bitmap_bytes = valk_gc_bitmap_bytes(size_class);
  
  // Check hard limit before committing
  size_t current = atomic_load(&heap->committed_bytes);
  if (current + page_size > heap->hard_limit) {
    VALK_WARN("Cannot allocate page: would exceed hard limit (%zu + %zu > %zu)",
              current, page_size, heap->hard_limit);
    return NULL;
  }
  
  // Allocate page (for now using malloc, will switch to mmap from reserved region)
  valk_gc_page2_t *page = aligned_alloc(VALK_GC_PAGE_ALIGN, page_size);
  if (!page) {
    VALK_ERROR("Failed to allocate GC page for class %d", size_class);
    return NULL;
  }
  
  // Initialize page header
  memset(page, 0, sizeof(valk_gc_page2_t));
  page->page_id = atomic_fetch_add(&__page_id_counter, 1);
  page->size_class = size_class;
  page->slots_per_page = slots;
  page->bitmap_bytes = bitmap_bytes;
  atomic_store(&page->num_allocated, 0);
  
  // Zero out bitmaps (they follow the header)
  memset(valk_gc_page2_alloc_bitmap(page), 0, bitmap_bytes);
  memset(valk_gc_page2_mark_bitmap(page), 0, bitmap_bytes);
  
  // Update accounting
  atomic_fetch_add(&heap->committed_bytes, page_size);
  
  return page;
}

// Create new multi-class heap
valk_gc_heap2_t *valk_gc_heap2_create(size_t hard_limit) {
  valk_gc_heap2_t *heap = calloc(1, sizeof(valk_gc_heap2_t));
  if (!heap) {
    VALK_ERROR("Failed to allocate heap structure");
    return NULL;
  }
  
  heap->type = VALK_ALLOC_GC_HEAP;
  heap->hard_limit = hard_limit > 0 ? hard_limit : VALK_GC_DEFAULT_HARD_LIMIT;
  heap->soft_limit = heap->hard_limit * 3 / 4;
  heap->gc_threshold_pct = 75;
  
  // For now, skip virtual address reservation (macOS has issues with large PROT_NONE mmaps)
  // We'll use malloc for pages and add mmap later
  heap->base = NULL;
  heap->reserved = 0;
  
  // Initialize per-class page lists
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_init(&heap->classes[c], c);
  }
  
  // Initialize large object list
  heap->large_objects = NULL;
  pthread_mutex_init(&heap->large_lock, NULL);
  
  // Initialize accounting
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
  
  VALK_INFO("Created multi-class GC heap: hard_limit=%zu soft_limit=%zu",
            heap->hard_limit, heap->soft_limit);
  
  return heap;
}

// Destroy heap and release all memory
void valk_gc_heap2_destroy(valk_gc_heap2_t *heap) {
  if (!heap) return;
  
  // Free all pages in each size class
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    pthread_mutex_lock(&list->lock);
    
    valk_gc_page2_t *page = list->all_pages;
    while (page) {
      valk_gc_page2_t *next = page->next;
      free(page);
      page = next;
    }
    
    pthread_mutex_unlock(&list->lock);
    pthread_mutex_destroy(&list->lock);
  }
  
  // Free large objects
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
  
  VALK_INFO("Destroyed multi-class GC heap");
  free(heap);
}

// Find free slots in a page's allocation bitmap
// Returns starting slot index, or UINT32_MAX if not found
static uint32_t valk_gc_page2_find_free_slots(valk_gc_page2_t *page, uint32_t count) {
  uint8_t *bitmap = valk_gc_page2_alloc_bitmap(page);
  uint16_t slots = page->slots_per_page;
  
  for (uint32_t i = 0; i < slots; i++) {
    if (!valk_gc_bitmap_test(bitmap, i)) {
      uint32_t run = 1;
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
bool valk_gc_tlab2_refill(valk_gc_tlab2_t *tlab, valk_gc_heap2_t *heap, uint8_t size_class) {
  if (size_class >= VALK_GC_NUM_SIZE_CLASSES) return false;
  
  valk_gc_page_list_t *list = &heap->classes[size_class];
  
  pthread_mutex_lock(&list->lock);
  
  valk_gc_page2_t *page = list->partial_pages;
  uint32_t start_slot = 0;
  uint32_t num_slots = VALK_GC_TLAB_SLOTS;
  
  if (page) {
    // Try to find contiguous free slots in existing partial page
    start_slot = valk_gc_page2_find_free_slots(page, num_slots);
    if (start_slot == UINT32_MAX) {
      // Page is actually full, remove from partial list
      list->partial_pages = page->next_partial;
      page = NULL;
    }
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
  uint8_t *bitmap = valk_gc_page2_alloc_bitmap(page);
  for (uint32_t i = start_slot; i < start_slot + num_slots; i++) {
    valk_gc_bitmap_set(bitmap, i);
  }
  atomic_fetch_add(&page->num_allocated, num_slots);
  atomic_fetch_add(&list->used_slots, num_slots);
  size_t added_bytes = num_slots * list->slot_size;
  size_t new_used = atomic_fetch_add(&heap->used_bytes, added_bytes) + added_bytes;
  if (new_used > heap->stats.peak_usage) {
    heap->stats.peak_usage = new_used;
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

static bool valk_gc_heap2_try_emergency_gc(valk_gc_heap2_t *heap, size_t needed);

static void *valk_gc_heap2_alloc_large(valk_gc_heap2_t *heap, size_t bytes) {
  size_t alloc_size = (bytes + 4095) & ~4095ULL;
  
  size_t current = valk_gc_heap2_used_bytes(heap);
  
  if (current + alloc_size > heap->hard_limit) {
    if (!valk_gc_heap2_try_emergency_gc(heap, alloc_size)) {
      valk_gc_oom_abort(heap, bytes);
    }
  } else if (current + alloc_size > heap->soft_limit) {
    if (!heap->in_emergency_gc && !atomic_load(&heap->gc_in_progress)) {
      valk_gc_heap2_collect(heap);
    }
  }
  
  void *data = mmap(NULL, alloc_size, PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (data == MAP_FAILED) {
    VALK_ERROR("mmap failed for large object of %zu bytes", alloc_size);
    return NULL;
  }
  
  valk_gc_large_obj_t *obj = malloc(sizeof(valk_gc_large_obj_t));
  if (!obj) {
    munmap(data, alloc_size);
    return NULL;
  }
  obj->data = data;
  obj->size = alloc_size;
  obj->marked = false;
  
  pthread_mutex_lock(&heap->large_lock);
  obj->next = heap->large_objects;
  heap->large_objects = obj;
  pthread_mutex_unlock(&heap->large_lock);
  
  atomic_fetch_add(&heap->large_object_bytes, alloc_size);
  size_t used = valk_gc_heap2_used_bytes(heap);
  if (used > heap->stats.peak_usage) {
    heap->stats.peak_usage = used;
  }
  
  return data;
}

void *valk_gc_heap2_alloc(valk_gc_heap2_t *heap, size_t bytes) {
  if (bytes == 0) return NULL;
  
  if (bytes > VALK_GC_LARGE_THRESHOLD) {
    return valk_gc_heap2_alloc_large(heap, bytes);
  }
  
  uint8_t size_class = valk_gc_size_class(bytes);
  if (size_class == UINT8_MAX) {
    return valk_gc_heap2_alloc_large(heap, bytes);
  }
  
  size_t alloc_size = valk_gc_size_classes[size_class];
  size_t current = valk_gc_heap2_used_bytes(heap);
  
  if (current + alloc_size > heap->hard_limit) {
    if (!valk_gc_heap2_try_emergency_gc(heap, alloc_size)) {
      valk_gc_oom_abort(heap, bytes);
    }
  } else if (current + alloc_size > heap->soft_limit) {
    if (!heap->in_emergency_gc && !atomic_load(&heap->gc_in_progress)) {
      valk_gc_heap2_collect(heap);
    }
  }
  
  static __thread valk_gc_tlab2_t *local_tlab = NULL;
  if (!local_tlab) {
    local_tlab = malloc(sizeof(valk_gc_tlab2_t));
    if (!local_tlab) return NULL;
    valk_gc_tlab2_init(local_tlab);
  }
  
  if (local_tlab->owner_heap != heap) {
    valk_gc_tlab2_reset(local_tlab);
    local_tlab->owner_heap = heap;
  }
  
  void *ptr = valk_gc_tlab2_alloc(local_tlab, size_class);
  if (ptr) {
    memset(ptr, 0, alloc_size);
    return ptr;
  }
  
  if (!valk_gc_tlab2_refill(local_tlab, heap, size_class)) {
    VALK_ERROR("Failed to refill TLAB for class %d", size_class);
    return NULL;
  }
  
  ptr = valk_gc_tlab2_alloc(local_tlab, size_class);
  if (ptr) {
    memset(ptr, 0, alloc_size);
  }
  return ptr;
}

void *valk_gc_heap2_realloc(valk_gc_heap2_t *heap, void *ptr, size_t new_size) {
  if (ptr == NULL) {
    return valk_gc_heap2_alloc(heap, new_size);
  }
  if (new_size == 0) {
    return NULL;
  }
  
  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(heap, ptr, &loc)) {
    size_t old_size = valk_gc_size_classes[loc.size_class];
    if (new_size <= old_size) {
      return ptr;
    }
    void *new_ptr = valk_gc_heap2_alloc(heap, new_size);
    if (new_ptr) {
      memcpy(new_ptr, ptr, old_size);
    }
    return new_ptr;
  }
  
  pthread_mutex_lock(&heap->large_lock);
  for (valk_gc_large_obj_t *obj = heap->large_objects; obj != NULL; obj = obj->next) {
    if (obj->data == ptr) {
      size_t old_size = obj->size;
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
  return NULL;
}

// ============================================================================
// Phase 2: Pointer Location and Marking
// ============================================================================

bool valk_gc_ptr_to_location(valk_gc_heap2_t *heap, void *ptr, valk_gc_ptr_location_t *out) {
  if (!heap || !ptr || !out) {
    if (out) out->is_valid = false;
    return false;
  }
  
  out->is_valid = false;
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    uint16_t slot_size = valk_gc_size_classes[c];
    
    for (valk_gc_page2_t *page = list->all_pages; page != NULL; page = page->next) {
      uint8_t *slots_start = valk_gc_page2_slots(page);
      uint8_t *slots_end = slots_start + page->slots_per_page * slot_size;
      
      if ((uint8_t *)ptr >= slots_start && (uint8_t *)ptr < slots_end) {
        uintptr_t offset = (uintptr_t)ptr - (uintptr_t)slots_start;
        if (offset % slot_size == 0) {
          out->page = page;
          out->slot = (uint32_t)(offset / slot_size);
          out->size_class = c;
          out->is_valid = true;
          return true;
        }
      }
    }
  }
  
  return false;
}

bool valk_gc_mark_large_object(valk_gc_heap2_t *heap, void *ptr) {
  if (!heap || !ptr) return false;
  
  pthread_mutex_lock(&heap->large_lock);
  
  for (valk_gc_large_obj_t *obj = heap->large_objects; obj != NULL; obj = obj->next) {
    if (ptr >= obj->data && (uint8_t *)ptr < (uint8_t *)obj->data + obj->size) {
      bool was_unmarked = !obj->marked;
      obj->marked = true;
      pthread_mutex_unlock(&heap->large_lock);
      return was_unmarked;
    }
  }
  
  pthread_mutex_unlock(&heap->large_lock);
  return false;
}

size_t valk_gc_sweep_page2(valk_gc_page2_t *page) {
  if (!page) return 0;
  
  size_t freed = 0;
  uint16_t slots = page->slots_per_page;
  uint16_t slot_size = valk_gc_size_classes[page->size_class];
  
  uint8_t *alloc_bitmap = valk_gc_page2_alloc_bitmap(page);
  uint8_t *mark_bitmap = valk_gc_page2_mark_bitmap(page);
  
  size_t num_words = (slots + 63) / 64;
  uint64_t *alloc_words = (uint64_t *)alloc_bitmap;
  uint64_t *mark_words = (uint64_t *)mark_bitmap;
  
  for (size_t w = 0; w < num_words; w++) {
    uint64_t alloc = alloc_words[w];
    uint64_t mark = mark_words[w];
    
    uint64_t garbage = alloc & ~mark;
    
    if (garbage != 0) {
      freed += (size_t)__builtin_popcountll(garbage);
      alloc_words[w] = alloc & mark;
      
      uint64_t temp = garbage;
      while (temp) {
        size_t bit = (size_t)__builtin_ctzll(temp);
        size_t slot = w * 64 + bit;
        
        if (slot < slots) {
          void *ptr = valk_gc_page2_slot_ptr(page, (uint32_t)slot);
          
          if (slot_size >= sizeof(valk_lval_t)) {
            valk_lval_t *v = (valk_lval_t *)ptr;
            if (LVAL_TYPE(v) == LVAL_REF && v->ref.free != NULL) {
              v->ref.free(v->ref.ptr);
            }
          }
        }
        
        temp &= temp - 1;
      }
    }
    
    mark_words[w] = 0;
  }
  
  atomic_fetch_sub(&page->num_allocated, (uint32_t)freed);
  
  return freed;
}

size_t valk_gc_sweep_large_objects(valk_gc_heap2_t *heap) {
  if (!heap) return 0;
  
  size_t freed = 0;
  
  pthread_mutex_lock(&heap->large_lock);
  
  valk_gc_large_obj_t **pp = &heap->large_objects;
  while (*pp != NULL) {
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

void valk_gc_rebuild_partial_lists(valk_gc_heap2_t *heap) {
  if (!heap) return;
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    pthread_mutex_lock(&list->lock);
    
    list->partial_pages = NULL;
    
    for (valk_gc_page2_t *page = list->all_pages; page != NULL; page = page->next) {
      uint32_t allocated = atomic_load(&page->num_allocated);
      
      if (allocated < page->slots_per_page) {
        page->next_partial = list->partial_pages;
        list->partial_pages = page;
      }
    }
    
    pthread_mutex_unlock(&list->lock);
  }
}

size_t valk_gc_reclaim_empty_pages(valk_gc_heap2_t *heap) {
  if (!heap) return 0;
  
  size_t pages_reclaimed = 0;
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    pthread_mutex_lock(&list->lock);
    
    for (valk_gc_page2_t *page = list->all_pages; page != NULL; page = page->next) {
      uint32_t allocated = atomic_load(&page->num_allocated);
      
      if (allocated == 0) {
        size_t page_size = valk_gc_page_total_size(valk_gc_size_classes[c]);
#ifdef __APPLE__
        madvise(page, page_size, MADV_FREE);
#else
        madvise(page, page_size, MADV_DONTNEED);
#endif
        pages_reclaimed++;
      }
    }
    
    pthread_mutex_unlock(&list->lock);
  }
  
  return pages_reclaimed;
}

// ============================================================================
// Phase 4: Mark Phase for heap2
// ============================================================================

static void mark_children2(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx);
static void mark_env2(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx);

static void mark_and_push2(void *ptr, valk_gc_mark_ctx2_t *ctx) {
  if (ptr == NULL) return;
  
  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(ctx->heap, ptr, &loc)) {
    if (!valk_gc_page2_try_mark(loc.page, loc.slot)) {
      return;
    }
  } else {
    if (!valk_gc_mark_large_object(ctx->heap, ptr)) {
      return;
    }
  }
  
  if (!valk_gc_mark_queue_push(ctx->queue, ptr)) {
    mark_children2(ptr, ctx);
  }
}

static void mark_env2(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx) {
  if (env == NULL) return;
  
  mark_and_push2(env, ctx);
  mark_and_push2(env->symbols.items, ctx);
  mark_and_push2(env->vals.items, ctx);
  
  for (size_t i = 0; i < env->symbols.count; i++) {
    mark_and_push2(env->symbols.items[i], ctx);
  }
  for (size_t i = 0; i < env->vals.count; i++) {
    mark_and_push2(env->vals.items[i], ctx);
  }
  
  mark_env2(env->parent, ctx);
  mark_env2(env->fallback, ctx);
}

static void mark_children2(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx) {
  if (obj == NULL) return;
  
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      mark_and_push2(obj->cons.head, ctx);
      mark_and_push2(obj->cons.tail, ctx);
      break;
      
    case LVAL_FUN:
      if (obj->fun.builtin == NULL) {
        mark_and_push2(obj->fun.formals, ctx);
        mark_and_push2(obj->fun.body, ctx);
        if (obj->fun.env) {
          mark_env2(obj->fun.env, ctx);
        }
      }
      mark_and_push2(obj->fun.name, ctx);
      break;
      
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_and_push2(obj->async.handle->on_complete, ctx);
        mark_and_push2(obj->async.handle->on_error, ctx);
        mark_and_push2(obj->async.handle->on_cancel, ctx);
        mark_and_push2(obj->async.handle->result, ctx);
        mark_and_push2(obj->async.handle->error, ctx);
        if (obj->async.handle->env) {
          mark_env2(obj->async.handle->env, ctx);
        }
      }
      break;
      
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      mark_and_push2(obj->str, ctx);
      break;
      
    case LVAL_REF:
      mark_and_push2(obj->ref.type, ctx);
      break;
      
    default:
      break;
  }
}

static void mark_root_visitor2(valk_lval_t *val, void *user) {
  valk_gc_mark_ctx2_t *ctx = user;
  mark_and_push2(val, ctx);
}

void valk_gc_heap2_mark_object(valk_gc_mark_ctx2_t *ctx, void *ptr) {
  mark_and_push2(ptr, ctx);
}

void valk_gc_heap2_mark_roots(valk_gc_heap2_t *heap) {
  if (!heap) return;
  
  valk_gc_mark_queue_t local_queue;
  valk_gc_mark_queue_init(&local_queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = &local_queue
  };
  
  valk_gc_visit_global_roots(mark_root_visitor2, &ctx);
  
  if (valk_thread_ctx.gc_registered) {
    valk_gc_visit_thread_roots(mark_root_visitor2, &ctx);
  }
  
  valk_lval_t *obj;
  while ((obj = valk_gc_mark_queue_pop(&local_queue)) != NULL) {
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
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    out->class_used_slots[c] = atomic_load(&heap->classes[c].used_slots);
    out->class_total_slots[c] = atomic_load(&heap->classes[c].total_slots);
  }
}

void valk_gc_tlab2_reset(valk_gc_tlab2_t *tlab) {
  if (!tlab) return;
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    tlab->classes[c].page = NULL;
    tlab->classes[c].next_slot = 0;
    tlab->classes[c].limit_slot = 0;
  }
}

__attribute__((noreturn))
void valk_gc_oom_abort(valk_gc_heap2_t *heap, size_t requested) {
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
        size_t pct = (stats.class_used_slots[c] * 100) / stats.class_total_slots[c];
        fprintf(stderr, "   Class %d (%4u B): %8zu / %8zu slots (%3zu%%)\n",
                c, valk_gc_size_classes[c], 
                stats.class_used_slots[c], stats.class_total_slots[c], pct);
      }
    }
    fprintf(stderr, " Large Objects: %12zu bytes\n", stats.large_object_bytes);
    fprintf(stderr, "----------------------------------------------------------------\n");
    fprintf(stderr, " GC cycles: %llu, Total reclaimed: %llu bytes\n",
            (unsigned long long)stats.collections,
            (unsigned long long)stats.bytes_reclaimed_total);
    fprintf(stderr, "----------------------------------------------------------------\n");
    fprintf(stderr, " Increase limit: VALK_HEAP_HARD_LIMIT=%zu\n", stats.hard_limit * 2);
  }
  fprintf(stderr, "================================================================\n");
  
  abort();
}

size_t valk_gc_heap2_collect(valk_gc_heap2_t *heap) {
  if (!heap) return 0;
  
  uint64_t start_ns = uv_hrtime();
  
  atomic_store(&heap->gc_in_progress, true);
  atomic_fetch_add(&heap->collections, 1);
  
  size_t bytes_before = valk_gc_heap2_used_bytes(heap);
  size_t freed_slots_total = 0;
  size_t freed_large = 0;
  
  valk_gc_heap2_mark_roots(heap);
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    for (valk_gc_page2_t *page = list->all_pages; page != NULL; page = page->next) {
      size_t freed = valk_gc_sweep_page2(page);
      freed_slots_total += freed;
      atomic_fetch_sub(&list->used_slots, freed);
    }
  }
  
  freed_large = valk_gc_sweep_large_objects(heap);
  
  valk_gc_rebuild_partial_lists(heap);
  
  size_t pages_reclaimed = valk_gc_reclaim_empty_pages(heap);
  
  size_t bytes_after = valk_gc_heap2_used_bytes(heap);
  size_t reclaimed = 0;
  if (bytes_before > bytes_after) {
    reclaimed = bytes_before - bytes_after;
  }
  
  atomic_fetch_add(&heap->bytes_reclaimed_total, reclaimed);
  atomic_store(&heap->gc_in_progress, false);
  
  uint64_t end_ns = uv_hrtime();
  uint64_t pause_us = (end_ns - start_ns) / 1000;
  
  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_us_total, pause_us);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);
  atomic_store(&heap->runtime_metrics.last_heap_before_gc, bytes_before);
  atomic_store(&heap->runtime_metrics.last_reclaimed, reclaimed);
  
  uint64_t current_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  while (pause_us > current_max) {
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_us_max, &current_max, pause_us)) {
      break;
    }
  }
  
  VALK_DEBUG("GC cycle complete: reclaimed %zu bytes (%zu slots + %zu large, %zu empty pages) in %llu us",
             reclaimed, freed_slots_total, freed_large, pages_reclaimed, (unsigned long long)pause_us);
  
  return reclaimed;
}

static bool valk_gc_heap2_try_emergency_gc(valk_gc_heap2_t *heap, size_t needed) {
  if (heap->in_emergency_gc) {
    return false;
  }
  
  heap->in_emergency_gc = true;
  
  VALK_WARN("Emergency GC: need %zu bytes, used %zu / %zu",
            needed, valk_gc_heap2_used_bytes(heap), heap->hard_limit);
  
  size_t reclaimed = valk_gc_heap2_collect(heap);
  
  heap->in_emergency_gc = false;
  
  size_t after = valk_gc_heap2_used_bytes(heap);
  if (after + needed <= heap->hard_limit) {
    VALK_INFO("Emergency GC recovered %zu bytes, allocation can proceed", reclaimed);
    return true;
  }
  
  return false;
}

// ============================================================================
// Phase 7: Parallel Mark/Sweep for heap2
// ============================================================================

static _Atomic size_t __gc_heap2_idle_count = 0;
static _Atomic bool __gc_heap2_terminated = false;
static valk_gc_heap2_t *__gc_heap2_current = NULL;

static bool valk_gc_heap2_check_termination(void) {
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  size_t idle = atomic_fetch_add(&__gc_heap2_idle_count, 1) + 1;
  
  if (idle == num_threads) {
    bool all_empty = true;
    for (size_t i = 0; i < num_threads; i++) {
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
  
  for (int i = 0; i < 100; i++) {
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

static void mark_and_push2_parallel(void *ptr, valk_gc_mark_ctx2_t *ctx);
static void mark_children2_parallel(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx);
static void mark_env2_parallel(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx);

static void mark_and_push2_parallel(void *ptr, valk_gc_mark_ctx2_t *ctx) {
  if (ptr == NULL) return;
  
  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(ctx->heap, ptr, &loc)) {
    if (!valk_gc_page2_try_mark(loc.page, loc.slot)) {
      return;
    }
  } else {
    if (!valk_gc_mark_large_object(ctx->heap, ptr)) {
      return;
    }
  }
  
  if (!valk_gc_mark_queue_push(ctx->queue, ptr)) {
    mark_children2_parallel(ptr, ctx);
  }
}

static void mark_env2_parallel(valk_lenv_t *env, valk_gc_mark_ctx2_t *ctx) {
  if (env == NULL) return;
  
  mark_and_push2_parallel(env, ctx);
  mark_and_push2_parallel(env->symbols.items, ctx);
  mark_and_push2_parallel(env->vals.items, ctx);
  
  for (size_t i = 0; i < env->symbols.count; i++) {
    mark_and_push2_parallel(env->symbols.items[i], ctx);
  }
  for (size_t i = 0; i < env->vals.count; i++) {
    mark_and_push2_parallel(env->vals.items[i], ctx);
  }
  
  mark_env2_parallel(env->parent, ctx);
  mark_env2_parallel(env->fallback, ctx);
}

static void mark_children2_parallel(valk_lval_t *obj, valk_gc_mark_ctx2_t *ctx) {
  if (obj == NULL) return;
  
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
    case LVAL_QEXPR:
      mark_and_push2_parallel(obj->cons.head, ctx);
      mark_and_push2_parallel(obj->cons.tail, ctx);
      break;
      
    case LVAL_FUN:
      if (obj->fun.builtin == NULL) {
        mark_and_push2_parallel(obj->fun.formals, ctx);
        mark_and_push2_parallel(obj->fun.body, ctx);
        if (obj->fun.env) {
          mark_env2_parallel(obj->fun.env, ctx);
        }
      }
      mark_and_push2_parallel(obj->fun.name, ctx);
      break;
      
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_and_push2_parallel(obj->async.handle->on_complete, ctx);
        mark_and_push2_parallel(obj->async.handle->on_error, ctx);
        mark_and_push2_parallel(obj->async.handle->on_cancel, ctx);
        mark_and_push2_parallel(obj->async.handle->result, ctx);
        mark_and_push2_parallel(obj->async.handle->error, ctx);
        if (obj->async.handle->env) {
          mark_env2_parallel(obj->async.handle->env, ctx);
        }
      }
      break;
      
    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      mark_and_push2_parallel(obj->str, ctx);
      break;
      
    case LVAL_REF:
      mark_and_push2_parallel(obj->ref.type, ctx);
      break;
      
    default:
      break;
  }
}

static void mark_root_visitor2_parallel(valk_lval_t *val, void *user) {
  valk_gc_mark_ctx2_t *ctx = user;
  mark_and_push2_parallel(val, ctx);
}

void valk_gc_heap2_parallel_mark(valk_gc_heap2_t *heap) {
  if (!heap) return;
  if (!valk_thread_ctx.gc_registered) return;
  
  size_t my_id = valk_thread_ctx.gc_thread_id;
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
  
  size_t idle_spins = 0;
  const size_t MAX_IDLE_SPINS = 1000;
  
  while (true) {
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != NULL) {
      mark_children2_parallel(obj, &ctx);
      idle_spins = 0;
    }
    
    bool found_work = false;
    size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
    
    for (size_t i = 1; i <= num_threads; i++) {
      size_t victim = (my_id + i) % num_threads;
      if (!valk_gc_coord.threads[victim].active) continue;
      
      obj = valk_gc_mark_queue_steal(&valk_gc_coord.threads[victim].mark_queue);
      if (obj != NULL) {
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
  
  size_t my_id = valk_thread_ctx.gc_thread_id;
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  
  for (uint8_t c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];
    
    size_t num_pages = list->num_pages;
    if (num_pages == 0) continue;
    
    size_t pages_per_thread = (num_pages + num_threads - 1) / num_threads;
    size_t my_start = my_id * pages_per_thread;
    size_t my_end = (my_id + 1) * pages_per_thread;
    if (my_end > num_pages) my_end = num_pages;
    
    valk_gc_page2_t *page = list->all_pages;
    for (size_t i = 0; i < my_start && page != NULL; i++) {
      page = page->next;
    }
    
    size_t freed_slots = 0;
    for (size_t i = my_start; i < my_end && page != NULL; i++) {
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
  
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  if (num_threads == 0) {
    atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
    return false;
  }
  
  if (valk_gc_coord.barrier_initialized) {
    valk_barrier_destroy(&valk_gc_coord.barrier);
  }
  valk_barrier_init(&valk_gc_coord.barrier, num_threads);
  valk_gc_coord.barrier_initialized = true;
  
  __gc_heap2_current = heap;
  
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
  
  return true;
}

size_t valk_gc_heap2_parallel_collect(valk_gc_heap2_t *heap) {
  if (!heap) return 0;
  
  size_t num_threads = atomic_load(&valk_gc_coord.threads_registered);
  
  if (num_threads <= 1) {
    return valk_gc_heap2_collect(heap);
  }
  
  if (!valk_thread_ctx.gc_registered) {
    return valk_gc_heap2_collect(heap);
  }
  
  uint64_t start_ns = uv_hrtime();
  
  atomic_store(&heap->gc_in_progress, true);
  atomic_fetch_add(&heap->collections, 1);
  
  size_t bytes_before = valk_gc_heap2_used_bytes(heap);
  
  atomic_store(&__gc_heap2_idle_count, 0);
  atomic_store(&__gc_heap2_terminated, false);
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_MARKING);
  valk_gc_heap2_parallel_mark(heap);
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_SWEEPING);
  valk_gc_heap2_parallel_sweep(heap);
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  if (valk_thread_ctx.gc_thread_id == 0) {
    valk_gc_rebuild_partial_lists(heap);
    valk_gc_reclaim_empty_pages(heap);
  }
  
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  atomic_store(&valk_gc_coord.threads_paused, 0);
  
  pthread_mutex_lock(&valk_gc_coord.lock);
  atomic_store(&valk_gc_coord.phase, VALK_GC_PHASE_IDLE);
  pthread_cond_broadcast(&valk_gc_coord.gc_done);
  pthread_mutex_unlock(&valk_gc_coord.lock);
  
  size_t bytes_after = valk_gc_heap2_used_bytes(heap);
  size_t reclaimed = 0;
  if (bytes_before > bytes_after) {
    reclaimed = bytes_before - bytes_after;
  }
  
  atomic_fetch_add(&heap->bytes_reclaimed_total, reclaimed);
  atomic_store(&heap->gc_in_progress, false);
  
  uint64_t end_ns = uv_hrtime();
  uint64_t pause_us = (end_ns - start_ns) / 1000;
  
  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_us_total, pause_us);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);
  atomic_store(&heap->runtime_metrics.last_heap_before_gc, bytes_before);
  atomic_store(&heap->runtime_metrics.last_reclaimed, reclaimed);
  
  uint64_t current_max = atomic_load(&heap->runtime_metrics.pause_us_max);
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
