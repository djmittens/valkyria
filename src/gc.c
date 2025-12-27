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
// GC Heap - Malloc-based allocator with mark & sweep
// ============================================================================

// Initialize GC heap
valk_gc_malloc_heap_t* valk_gc_malloc_heap_init(size_t hard_limit) {
  valk_gc_malloc_heap_t* heap = malloc(sizeof(valk_gc_malloc_heap_t));
  if (!heap) {
    VALK_ERROR("Failed to allocate GC heap structure");
    return NULL;
  }

  heap->type = VALK_ALLOC_GC_HEAP;
  heap->allocated_bytes = 0;
  heap->hard_limit = hard_limit > 0 ? hard_limit : 250 * 1024 * 1024;  // 250 MiB default
  heap->num_collections = 0;
  heap->in_emergency_gc = false;
  heap->objects = NULL;
  heap->root_env = NULL;
  heap->free_list = NULL;
  heap->free_list_size = 0;

  // Initialize statistics to zero
  heap->stats.overflow_allocations = 0;
  heap->stats.evacuations_from_scratch = 0;
  heap->stats.evacuation_bytes = 0;
  heap->stats.evacuation_pointer_fixups = 0;
  heap->stats.emergency_collections = 0;
  heap->stats.peak_usage = 0;

  // Initialize runtime metrics
  atomic_store(&heap->runtime_metrics.cycles_total, 0);
  atomic_store(&heap->runtime_metrics.pause_us_total, 0);
  atomic_store(&heap->runtime_metrics.pause_us_max, 0);
  atomic_store(&heap->runtime_metrics.reclaimed_bytes_total, 0);
  atomic_store(&heap->runtime_metrics.allocated_bytes_total, 0);
  atomic_store(&heap->runtime_metrics.objects_marked, 0);
  atomic_store(&heap->runtime_metrics.objects_swept, 0);
  heap->runtime_metrics.last_cycle_start_us = 0;

  // Initialize survival histogram counters
  atomic_store(&heap->runtime_metrics.survival_gen_0, 0);
  atomic_store(&heap->runtime_metrics.survival_gen_1_5, 0);
  atomic_store(&heap->runtime_metrics.survival_gen_6_20, 0);
  atomic_store(&heap->runtime_metrics.survival_gen_21_plus, 0);

  // Initialize frame-time pause histogram counters
  atomic_store(&heap->runtime_metrics.pause_0_1ms, 0);
  atomic_store(&heap->runtime_metrics.pause_1_5ms, 0);
  atomic_store(&heap->runtime_metrics.pause_5_10ms, 0);
  atomic_store(&heap->runtime_metrics.pause_10_16ms, 0);
  atomic_store(&heap->runtime_metrics.pause_16ms_plus, 0);

  // Create fast slab allocator for valk_lval_t objects
  // Fixed large size - simple and fast, no threshold complexity
  extern size_t __valk_lval_size;  // Defined in parser.c
  heap->lval_size = __valk_lval_size;

  // Fixed slab size: 256K objects = ~64MB for 256-byte lval_t+header
  // Large enough for most workloads, avoids exhaustion during heavy copying
  size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
  size_t num_lvals = 256 * 1024;  // 256K objects

  size_t slab_size = valk_slab_size(slab_item_size, num_lvals);
  heap->lval_slab = malloc(slab_size);
  if (heap->lval_slab == NULL) {
    VALK_WARN("Failed to allocate lval slab, will fall back to malloc");
  } else {
    valk_slab_init(heap->lval_slab, slab_item_size, num_lvals);
  }

  // Create fast slab allocator for valk_lenv_t objects
  // Environments are smaller and less numerous than lvals
  extern size_t __valk_lenv_size;  // Defined in parser.c
  heap->lenv_size = __valk_lenv_size;

  // Smaller capacity than lval slab: 64K environments should be plenty
  // Each lenv is ~80 bytes + header = ~96 bytes per slot
  size_t lenv_slab_item_size = sizeof(valk_gc_header_t) + heap->lenv_size;
  size_t num_lenvs = 64 * 1024;  // 64K environments

  size_t lenv_slab_size = valk_slab_size(lenv_slab_item_size, num_lenvs);
  heap->lenv_slab = malloc(lenv_slab_size);
  if (heap->lenv_slab == NULL) {
    VALK_WARN("Failed to allocate lenv slab, will fall back to malloc");
  } else {
    valk_slab_init(heap->lenv_slab, lenv_slab_item_size, num_lenvs);
  }

  // Initialize percentage-based GC tuning with sensible defaults
  heap->gc_threshold_pct = 75;    // Trigger GC at 75% heap usage
  heap->gc_target_pct = 50;       // Informational: aim to be below 50% after GC
  heap->min_gc_interval_ms = 1000; // At most one GC per second
  heap->last_gc_time_us = 0;

  return heap;
}

// Set hard limit for GC heap
void valk_gc_set_hard_limit(valk_gc_malloc_heap_t* heap, size_t limit) {
  if (limit < heap->allocated_bytes) {
    VALK_WARN("Cannot set hard limit below current usage (%zu < %zu)",
              limit, heap->allocated_bytes);
    return;
  }
  heap->hard_limit = limit;
}

// Set root environment for GC marking
void valk_gc_malloc_set_root(valk_gc_malloc_heap_t* heap, valk_lenv_t* root_env) {
  heap->root_env = root_env;
}

// Get heap usage percentages for all tiers
// Returns the MAX of lval_slab%, lenv_slab% and malloc% - triggers on whichever is fuller
uint8_t valk_gc_heap_usage_pct(valk_gc_malloc_heap_t* heap) {
  if (!heap) return 0;

  // Calculate lval slab usage percentage
  uint8_t lval_slab_pct = 0;
  if (heap->lval_slab != NULL && heap->lval_slab->numItems > 0) {
    size_t slab_used = heap->lval_slab->numItems - heap->lval_slab->numFree;
    lval_slab_pct = (uint8_t)((slab_used * 100) / heap->lval_slab->numItems);
  }

  // Calculate lenv slab usage percentage
  uint8_t lenv_slab_pct = 0;
  if (heap->lenv_slab != NULL && heap->lenv_slab->numItems > 0) {
    size_t slab_used = heap->lenv_slab->numItems - heap->lenv_slab->numFree;
    lenv_slab_pct = (uint8_t)((slab_used * 100) / heap->lenv_slab->numItems);
  }

  // Calculate malloc usage percentage
  uint8_t malloc_pct = 0;
  if (heap->hard_limit > 0) {
    malloc_pct = (uint8_t)((heap->allocated_bytes * 100) / heap->hard_limit);
    if (malloc_pct > 100) malloc_pct = 100;
  }

  // Return the highest - GC triggers if ANY tier is full
  uint8_t max_pct = lval_slab_pct > lenv_slab_pct ? lval_slab_pct : lenv_slab_pct;
  return max_pct > malloc_pct ? max_pct : malloc_pct;
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
// Uses percentage-based threshold considering both slab and malloc usage
// Also rate-limits to avoid GC thrashing
bool valk_gc_malloc_should_collect(valk_gc_malloc_heap_t* heap) {
  if (!heap) return false;

  // Check percentage threshold
  uint8_t usage_pct = valk_gc_heap_usage_pct(heap);
  if (usage_pct < heap->gc_threshold_pct) {
    return false;  // Below threshold, no GC needed
  }

  // Above threshold - check rate limiting
  if (heap->min_gc_interval_ms > 0 && heap->last_gc_time_us > 0) {
    uint64_t now_us = uv_hrtime() / 1000;
    uint64_t elapsed_ms = (now_us - heap->last_gc_time_us) / 1000;
    if (elapsed_ms < heap->min_gc_interval_ms) {
      return false;  // Too soon since last GC
    }
  }

  return true;
}

// Allocate from GC heap with header-based tracking
void* valk_gc_malloc_heap_alloc(valk_gc_malloc_heap_t* heap, size_t bytes) {
  size_t total_size = sizeof(valk_gc_header_t) + bytes;

  // Check hard limit BEFORE allocation - trigger emergency GC if approaching
  if (heap->allocated_bytes + total_size > heap->hard_limit) {
    // Try emergency GC if not already in one
    if (!heap->in_emergency_gc && heap->root_env != NULL) {
      heap->in_emergency_gc = true;

      size_t before = heap->allocated_bytes;
      valk_gc_malloc_collect(heap, NULL);  // Emergency GC, no additional roots
      size_t reclaimed = before - heap->allocated_bytes;

      heap->stats.emergency_collections++;
      heap->in_emergency_gc = false;

    }

    // Re-check after emergency GC
    if (heap->allocated_bytes + total_size > heap->hard_limit) {
      // Still can't allocate - fatal error
      VALK_ERROR("=== FATAL: HEAP EXHAUSTED ===");
      VALK_ERROR("Requested: %zu bytes (+ %zu header = %zu total)",
                 bytes, sizeof(valk_gc_header_t), total_size);
      VALK_ERROR("Current:   %zu bytes", heap->allocated_bytes);
      VALK_ERROR("Hard limit: %zu bytes", heap->hard_limit);
      VALK_ERROR("Shortfall: %zu bytes",
                 (heap->allocated_bytes + total_size) - heap->hard_limit);

      // Dump full diagnostics
      valk_gc_malloc_print_stats(heap);

      VALK_ERROR("Consider increasing VALK_HEAP_HARD_LIMIT environment variable");
      VALK_ERROR("Current: VALK_HEAP_HARD_LIMIT=%zu", heap->hard_limit);

      abort();
    }
  }

  valk_gc_header_t* header = NULL;
  bool from_slab = false;

  // Fastest path: Slab allocator for valk_lval_t objects (most common case)
  if (bytes == heap->lval_size && heap->lval_slab != NULL) {
    header = valk_mem_allocator_alloc((void*)heap->lval_slab, total_size);
    if (header != NULL) {
      from_slab = true;
      VALK_TRACE("GC alloc: %zu bytes from lval slab at %p", bytes, (void*)(header + 1));
    }
  }

  // Second fast path: Slab allocator for valk_lenv_t objects
  if (header == NULL && bytes == heap->lenv_size && heap->lenv_slab != NULL) {
    header = valk_mem_allocator_alloc((void*)heap->lenv_slab, total_size);
    if (header != NULL) {
      from_slab = true;
      VALK_TRACE("GC alloc: %zu bytes from lenv slab at %p", bytes, (void*)(header + 1));
    }
  }

  // Slow path: malloc if not found in slab
  if (header == NULL) {
    header = malloc(total_size);
    if (header == NULL) {
      VALK_ERROR("GC heap malloc failed for %zu bytes (+ %zu header)",
                 bytes, sizeof(valk_gc_header_t));
      return NULL;
    }
    // Track allocation (header + user data)
    heap->allocated_bytes += total_size;
    VALK_TRACE("GC alloc: %zu bytes via malloc at %p", bytes, (void*)(header + 1));
  }

  // Initialize header
  header->origin_allocator = heap;
  header->gc_next = heap->objects;
  header->size = bytes;

  // Always zero out user data for safety - whether from slab or malloc
  void* user_data = (void*)(header + 1);
  memset(user_data, 0, bytes);

  // Add to live objects linked list
  heap->objects = header;

  // Track peak usage
  if (heap->allocated_bytes > heap->stats.peak_usage) {
    heap->stats.peak_usage = heap->allocated_bytes;
  }

  // Track cumulative allocation (for rate calculations)
  atomic_fetch_add(&heap->runtime_metrics.allocated_bytes_total, bytes);

  // Return pointer to user data (NOT header!)
  return (void*)(header + 1);
}

// ============================================================================
// Conservative Stack Scanning - Mark objects referenced from C stack
// ============================================================================

// Helper: Check if a pointer-sized value looks like it points into GC heap
__attribute__((unused))
static bool valk_gc_is_heap_pointer(valk_gc_malloc_heap_t* heap, void* ptr) {
  if (ptr == NULL) return false;

  // Conservative scan: check if this pointer matches any object in our heap
  for (valk_gc_header_t* header = heap->objects; header != NULL; header = header->gc_next) {
    void* user_data = (void*)(header + 1);
    // Check if ptr points to this allocation (within user data range)
    if (ptr >= user_data && ptr < (void*)((uint8_t*)user_data + header->size)) {
      return true;
    }
  }
  return false;
}

// ============================================================================
// Mark Phase - Traverse from roots and mark reachable objects
// ============================================================================

// Thread-local heap pointer for safe marking checks
static __thread valk_gc_malloc_heap_t* gc_current_heap = NULL;

// Environment worklist for iterative traversal (avoids stack overflow)
#define ENV_WORKLIST_INITIAL_CAPACITY 64

typedef struct {
  valk_lenv_t** items;
  size_t count;
  size_t capacity;
} valk_env_worklist_t;

// Lval worklist for iterative marking (avoids stack overflow on deep lists)
#define LVAL_WORKLIST_INITIAL_CAPACITY 256

typedef struct {
  valk_lval_t** items;
  size_t count;
  size_t capacity;
} valk_lval_worklist_t;

static void lval_worklist_init(valk_lval_worklist_t* wl) {
  wl->items = malloc(LVAL_WORKLIST_INITIAL_CAPACITY * sizeof(valk_lval_t*));
  wl->count = 0;
  wl->capacity = LVAL_WORKLIST_INITIAL_CAPACITY;
}

static void lval_worklist_free(valk_lval_worklist_t* wl) {
  if (wl->items) {
    free(wl->items);
    wl->items = NULL;
  }
  wl->count = 0;
  wl->capacity = 0;
}

static void lval_worklist_push(valk_lval_worklist_t* wl, valk_lval_t* v) {
  if (v == NULL) return;
  if (wl->count >= wl->capacity) {
    size_t new_cap = wl->capacity * 2;
    valk_lval_t** new_items = realloc(wl->items, new_cap * sizeof(valk_lval_t*));
    if (new_items == NULL) {
      VALK_ERROR("Failed to grow lval worklist");
      return;
    }
    wl->items = new_items;
    wl->capacity = new_cap;
  }
  wl->items[wl->count++] = v;
}

static valk_lval_t* lval_worklist_pop(valk_lval_worklist_t* wl) {
  if (wl->count == 0) return NULL;
  return wl->items[--wl->count];
}

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

// Process a single lval for marking, pushing children to worklist (non-recursive)
static void valk_gc_mark_lval_single(valk_lval_t* v, valk_lval_worklist_t* wl) {
  if (v == NULL) return;

  // Only mark objects allocated by the GC heap - don't mark scratch/arena objects
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return;

  // Already marked - avoid infinite loops
  if (v->flags & LVAL_FLAG_GC_MARK) return;

  // Mark this value
  v->flags |= LVAL_FLAG_GC_MARK;

  switch (LVAL_TYPE(v)) {
    case LVAL_NUM:
      // True leaf type - no children
      break;

    case LVAL_REF:
      // Mark the type string if it's GC-allocated
      if (v->ref.type != NULL) {
        valk_gc_mark_allocation(v->ref.type);
      }
      // Mark the ref ptr if it's GC-allocated (e.g., aio_system)
      if (v->ref.ptr != NULL) {
        valk_gc_mark_allocation(v->ref.ptr);
      }
      break;

    case LVAL_SYM:
    case LVAL_STR:
    case LVAL_ERR:
      // Mark the string data if it's GC-allocated (evacuated from scratch)
      if (v->str != NULL) {
        valk_gc_mark_allocation(v->str);
      }
      break;

    case LVAL_FUN:
      // Mark function name string if it's GC-allocated
      if (v->fun.name != NULL) {
        valk_gc_mark_allocation(v->fun.name);
      }
      // Mark function environment, formals, body
      if (v->fun.env) {
        valk_gc_mark_env(v->fun.env);
      }
      // Push children to worklist instead of recursing
      lval_worklist_push(wl, v->fun.formals);
      lval_worklist_push(wl, v->fun.body);
      break;

    case LVAL_CONS:
    case LVAL_QEXPR:
      // Push head and tail to worklist instead of recursing
      lval_worklist_push(wl, v->cons.head);
      lval_worklist_push(wl, v->cons.tail);
      break;
    case LVAL_NIL:
      // Nil has no children
      break;

    case LVAL_UNDEFINED:
    case LVAL_FORWARD:
      // Forwarding pointers should not exist during GC marking
      // (they only exist transiently during evacuation)
      break;

    case LVAL_HANDLE:
      // Mark the async handle's stored lval pointers
      // Note: The handle struct itself is malloc'd, not GC-allocated,
      // but the lvals it references (callbacks, result, error) may be GC-allocated
      if (v->async.handle != NULL) {
        // Push children to worklist instead of recursing
        lval_worklist_push(wl, v->async.handle->on_complete);
        lval_worklist_push(wl, v->async.handle->on_error);
        lval_worklist_push(wl, v->async.handle->on_cancel);
        lval_worklist_push(wl, v->async.handle->result);
        lval_worklist_push(wl, v->async.handle->error);
        if (v->async.handle->env) {
          valk_gc_mark_env(v->async.handle->env);
        }
      }
      break;
  }
}

// Iterative lval marking to avoid stack overflow on deep structures
static void valk_gc_mark_lval(valk_lval_t* v) {
  if (v == NULL) return;

  valk_lval_worklist_t worklist;
  lval_worklist_init(&worklist);

  // Push initial value
  lval_worklist_push(&worklist, v);

  // Process worklist iteratively
  while (worklist.count > 0) {
    valk_lval_t* current = lval_worklist_pop(&worklist);
    valk_gc_mark_lval_single(current, &worklist);
  }

  lval_worklist_free(&worklist);
}

// Helper to check if env is already marked (uses same marking scheme as valk_gc_mark_allocation)
static bool valk_gc_env_is_marked(valk_lenv_t* env) {
  if (env == NULL) return true;  // NULL counts as "already processed"

  // Skip scratch arena environments - they're not GC-managed yet
  if (valk_thread_ctx.scratch && valk_ptr_in_arena(valk_thread_ctx.scratch, env)) {
    return false;  // Not marked, but safe to skip
  }

  // Check if already marked by looking at header's origin_allocator low bit
  valk_gc_header_t* header = ((valk_gc_header_t*)env) - 1;
  return ((uintptr_t)header->origin_allocator & 1) != 0;
}

// Process a single environment (marks its direct contents, returns parent/fallback for worklist)
static void valk_gc_mark_env_contents(valk_lenv_t* env, valk_env_worklist_t* wl) {
  // Mark the environment structure itself if it's GC-allocated
  valk_gc_mark_allocation(env);

  // Mark all lval values in this environment
  for (size_t i = 0; i < env->vals.count; i++) {
    valk_gc_mark_lval(env->vals.items[i]);
  }

  // Mark the arrays themselves if they're GC-allocated
  if (env->symbols.items != NULL) {
    valk_gc_mark_allocation(env->symbols.items);
  }
  if (env->vals.items != NULL) {
    valk_gc_mark_allocation(env->vals.items);
  }

  // Mark individual symbol strings if they're GC-allocated
  for (size_t i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items[i] != NULL) {
      valk_gc_mark_allocation(env->symbols.items[i]);
    }
  }

  // Push parent and fallback to worklist for iterative processing
  if (env->parent != NULL && !valk_gc_env_is_marked(env->parent)) {
    env_worklist_push(wl, env->parent);
  }
  if (env->fallback != NULL && !valk_gc_env_is_marked(env->fallback)) {
    env_worklist_push(wl, env->fallback);
  }
}

static void valk_gc_mark_env(valk_lenv_t* env) {
  if (env == NULL) return;

  // Use iterative worklist to avoid stack overflow on deep env chains
  valk_env_worklist_t worklist;
  env_worklist_init(&worklist);

  // Push initial environment
  env_worklist_push(&worklist, env);

  // Process all environments iteratively
  while (worklist.count > 0) {
    valk_lenv_t* current = env_worklist_pop(&worklist);
    if (current == NULL) continue;

    // Skip if already marked (prevents infinite loops on cycles)
    if (valk_gc_env_is_marked(current)) continue;

    valk_gc_mark_env_contents(current, &worklist);
  }

  env_worklist_free(&worklist);
}

// Mark an arbitrary GC heap allocation (for evacuated strings/arrays)
// This function should ONLY be called on GC-allocated pointers.
// NOTE: GC can only run at checkpoint boundaries (between expressions).
// During expression evaluation, scratch arena pointers are not safe to mark.
static void valk_gc_mark_allocation(void* ptr) {
  if (ptr == NULL || gc_current_heap == NULL) return;

  // Skip scratch arena pointers - they don't have GC headers and aren't managed by GC yet
  // They'll be evacuated at the next checkpoint if they're still reachable
  // This is the ONLY check we need - O(1) range check instead of O(n) list scan
  if (valk_thread_ctx.scratch && valk_ptr_in_arena(valk_thread_ctx.scratch, ptr)) {
    return;  // Scratch pointer - wait for evacuation at checkpoint
  }

  // If not in scratch arena, it must be GC heap or libc malloc
  // Both can be safely freed with valk_mem_free
  // Trust the pointer and dereference the header
  valk_gc_header_t* header = ((valk_gc_header_t*)ptr) - 1;

  // Short-circuit: if already marked, return immediately (O(1))
  // This makes repeated marking of the same object very fast
  if ((uintptr_t)header->origin_allocator & 1) {
    return;  // Already marked
  }

  // Mark it by setting the low bit of origin_allocator
  void* allocator = (void*)((uintptr_t)header->origin_allocator & ~(uintptr_t)1);
  header->origin_allocator = (void*)((uintptr_t)allocator | 1);
}

// ============================================================================
// Sweep Phase - Free unmarked objects
// ============================================================================

static void record_survival_histogram(valk_gc_malloc_heap_t* heap, uint64_t gen) {
  if (gen == 0) {
    atomic_fetch_add(&heap->runtime_metrics.survival_gen_0, 1);
  } else if (gen <= 5) {
    atomic_fetch_add(&heap->runtime_metrics.survival_gen_1_5, 1);
  } else if (gen <= 20) {
    atomic_fetch_add(&heap->runtime_metrics.survival_gen_6_20, 1);
  } else {
    atomic_fetch_add(&heap->runtime_metrics.survival_gen_21_plus, 1);
  }
}

static size_t valk_gc_malloc_sweep(valk_gc_malloc_heap_t* heap, size_t* out_freed_count) {
  size_t reclaimed = 0;
  size_t freed_count = 0;
  valk_gc_header_t** header_ptr = &heap->objects;

  while (*header_ptr != NULL) {
    valk_gc_header_t* header = *header_ptr;
    void* user_data = (void*)(header + 1);

    // Extract mark bit from origin_allocator (we use low bit as mark flag)
    bool is_marked = ((uintptr_t)header->origin_allocator & 1) != 0;
    void* origin_allocator = (void*)((uintptr_t)header->origin_allocator & ~(uintptr_t)1);

    // Safety check: verify allocator pointer (after clearing mark bit)
    if (origin_allocator != heap) {
      VALK_ERROR("GC sweep found header with wrong allocator!");
      VALK_ERROR("  Expected GC heap: %p", heap);
      VALK_ERROR("  Got allocator: %p (mark bit: %d)", origin_allocator, is_marked);
      VALK_ERROR("  Header pointer: %p", header);
      VALK_ERROR("  User data: %p", user_data);
      VALK_ERROR("  Header size: %zu", header->size);

      VALK_ERROR("BREAKING TRAVERSAL to prevent infinite loop");
      // Break the list here to prevent following corrupted pointers
      *header_ptr = NULL;
      break;
    }

    // Check if this is an lval object or a raw allocation (string/array)
    bool is_lval = (header->size == heap->lval_size);
    bool lval_marked = false;

    if (is_lval) {
      // Cast to lval and check its mark bit too
      valk_lval_t* obj = (valk_lval_t*)user_data;
      lval_marked = (obj->flags & LVAL_FLAG_GC_MARK) != 0;
    }

    // Object is live if either the header mark bit OR the lval mark bit is set
    if (is_marked || lval_marked) {
      // Object is live - keep it and clear mark bit for next GC cycle
      header->origin_allocator = origin_allocator;
      header_ptr = &header->gc_next;
    } else {
      // Object is garbage - free based on allocation source (slab vs malloc)
      *header_ptr = header->gc_next;  // Remove from live objects list

      size_t total_size = sizeof(valk_gc_header_t) + header->size;
      freed_count++;

      // Free internal resources before freeing the lval structure itself
      // NOTE: Most internal allocations (lval->str, fun.name) use valk_mem_alloc
      // and are tracked as separate GC objects - they will be swept independently.
      // Only manually free resources allocated via raw malloc/strdup.
      if (is_lval) {
        valk_lval_t* obj = (valk_lval_t*)user_data;

        // Record generation in survival histogram before freeing
        uint64_t gen = LVAL_GC_GEN(obj);
        record_survival_histogram(heap, gen);

        switch (LVAL_TYPE(obj)) {
          case LVAL_REF:
            // References have custom free functions (raw malloc)
            if (obj->ref.free != NULL && obj->ref.ptr != NULL) {
              obj->ref.free(obj->ref.ptr);
            }
            // ref.type is strdup'd (raw malloc)
            if (obj->ref.type != NULL) {
              free(obj->ref.type);
            }
            break;
          default:
            break;
        }
      }

      // Check if object is from lval slab via address range check
      uintptr_t obj_addr = (uintptr_t)header;
      bool from_lval_slab = false;
      if (heap->lval_slab != NULL) {
        uintptr_t slab_start = (uintptr_t)heap->lval_slab;
        size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
        size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
        uintptr_t slab_end = slab_start + slab_total_size;
        from_lval_slab = (obj_addr >= slab_start && obj_addr < slab_end);
      }

      // Check if object is from lenv slab
      bool from_lenv_slab = false;
      if (!from_lval_slab && heap->lenv_slab != NULL) {
        uintptr_t slab_start = (uintptr_t)heap->lenv_slab;
        size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lenv_size;
        size_t slab_total_size = valk_slab_size(slab_item_size, 64 * 1024);
        uintptr_t slab_end = slab_start + slab_total_size;
        from_lenv_slab = (obj_addr >= slab_start && obj_addr < slab_end);
      }

      if (from_lval_slab) {
        // Return to lval slab allocator - don't count towards reclaimed bytes
        // since slab allocations aren't tracked in allocated_bytes
        valk_mem_allocator_free((void*)heap->lval_slab, header);
        VALK_TRACE("GC sweep: returned lval %p to slab", user_data);
      } else if (from_lenv_slab) {
        // Return to lenv slab allocator
        valk_mem_allocator_free((void*)heap->lenv_slab, header);
        VALK_TRACE("GC sweep: returned lenv %p to slab", user_data);
      } else {
        // Free malloc'd objects directly
        // Count towards reclaimed bytes since malloc'd objects are tracked in allocated_bytes
        reclaimed += total_size;
        free(header);
        VALK_TRACE("GC sweep: freed %p (malloc)", user_data);
      }
    }
  }

  // Only subtract reclaimed bytes (from malloc'd objects) from allocated_bytes
  if (reclaimed <= heap->allocated_bytes) {
    heap->allocated_bytes -= reclaimed;
  } else {
    // Safety: prevent underflow
    VALK_WARN("GC sweep: reclaimed (%zu) > allocated_bytes (%zu), resetting to 0",
              reclaimed, heap->allocated_bytes);
    heap->allocated_bytes = 0;
  }

  VALK_INFO("GC sweep: freed %zu objects, reclaimed %zu bytes",
            freed_count, reclaimed);

  if (out_freed_count) {
    *out_freed_count = freed_count;
  }
  return reclaimed;
}

// ============================================================================
// Clear marks for next collection
// ============================================================================

// Clear marks on a single lval, pushing children to worklist (non-recursive)
static void valk_gc_clear_marks_single(valk_lval_t* v, valk_lval_worklist_t* wl) {
  if (v == NULL) return;

  // Only clear marks on GC heap objects - don't touch scratch/arena objects
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return;

  // Already cleared
  if (!(v->flags & LVAL_FLAG_GC_MARK)) return;

  // Clear mark
  v->flags &= ~LVAL_FLAG_GC_MARK;

  // Push children to worklist - note that children might have been freed if unmarked,
  // so the recursive calls will check marks before accessing
  switch (LVAL_TYPE(v)) {
    case LVAL_FUN:
      if (v->fun.env) {
        for (size_t i = 0; i < v->fun.env->vals.count; i++) {
          lval_worklist_push(wl, v->fun.env->vals.items[i]);
        }
      }
      lval_worklist_push(wl, v->fun.formals);
      lval_worklist_push(wl, v->fun.body);
      break;

    case LVAL_CONS:
    case LVAL_QEXPR:
      lval_worklist_push(wl, v->cons.head);
      lval_worklist_push(wl, v->cons.tail);
      break;
    case LVAL_NIL:
      // Nil has no children
      break;

    default:
      break;
  }
}

// Iterative mark clearing to avoid stack overflow on deep structures
static void valk_gc_clear_marks_recursive(valk_lval_t* v) {
  if (v == NULL) return;

  valk_lval_worklist_t worklist;
  lval_worklist_init(&worklist);

  // Push initial value
  lval_worklist_push(&worklist, v);

  // Process worklist iteratively
  while (worklist.count > 0) {
    valk_lval_t* current = lval_worklist_pop(&worklist);
    valk_gc_clear_marks_single(current, &worklist);
  }

  lval_worklist_free(&worklist);
}

// ============================================================================
// Main GC Collection
// ============================================================================

void valk_gc_malloc_print_stats(valk_gc_malloc_heap_t* heap) {
  if (heap == NULL) return;

  // Count live objects by traversing headers
  size_t object_count = 0;
  size_t traversal_limit = 1000000;  // Safety limit
  for (valk_gc_header_t* header = heap->objects;
       header != NULL && object_count < traversal_limit;
       header = header->gc_next) {
    object_count++;
  }

  fprintf(stderr, "\n=== GC Heap Statistics ===\n");
  uint8_t usage_pct = valk_gc_heap_usage_pct(heap);
  fprintf(stderr, "Heap usage:       %u%% (threshold: %u%%, hard limit: %zu bytes)\n",
          usage_pct, heap->gc_threshold_pct, heap->hard_limit);
  fprintf(stderr, "Allocated bytes:  %zu bytes\n", heap->allocated_bytes);
  fprintf(stderr, "Peak usage:       %zu bytes\n", heap->stats.peak_usage);
  fprintf(stderr, "Live objects:     %zu\n", object_count);
  fprintf(stderr, "Collections:      %zu\n", heap->num_collections);
  fprintf(stderr, "Emergency GCs:    %zu\n", heap->stats.emergency_collections);
  fprintf(stderr, "Avg allocation:   %.1f bytes/object\n",
          object_count > 0 ? (double)heap->allocated_bytes / object_count : 0.0);

  // Evacuation stats (from scratch arena)
  if (heap->stats.evacuations_from_scratch > 0) {
    fprintf(stderr, "--- Evacuation Stats ---\n");
    fprintf(stderr, "Values evacuated: %zu\n", heap->stats.evacuations_from_scratch);
    fprintf(stderr, "Bytes evacuated:  %zu\n", heap->stats.evacuation_bytes);
    fprintf(stderr, "Pointers fixed:   %zu\n", heap->stats.evacuation_pointer_fixups);
  }

  // Overflow stats
  if (heap->stats.overflow_allocations > 0) {
    fprintf(stderr, "--- Overflow Stats ---\n");
    fprintf(stderr, "⚠️  Overflow allocs: %zu\n", heap->stats.overflow_allocations);
  }

  fprintf(stderr, "=========================\n\n");
}

// Format bytes with human-readable units into provided buffer
// Buffer should be at least 12 chars. Output is 10 chars wide for alignment.
static void format_bytes_buf(char* out, size_t outsize, size_t bytes) {
  if (bytes >= 1024 * 1024 * 1024) {
    snprintf(out, outsize, "%7.2f GB", bytes / (1024.0 * 1024.0 * 1024.0));
  } else if (bytes >= 1024 * 1024) {
    snprintf(out, outsize, "%7.2f MB", bytes / (1024.0 * 1024.0));
  } else if (bytes >= 1024) {
    snprintf(out, outsize, "%7.2f KB", bytes / 1024.0);
  } else {
    snprintf(out, outsize, "%8zu B", bytes);
  }
}

// Format a progress bar into buffer. Width is number of cells (each 1 char wide visually).
// Uses bordered style: [████░░░░░░] with filled and empty blocks
static void format_progress_bar(char* out, size_t outsize, double fraction, int width) {
  if (fraction < 0.0) fraction = 0.0;
  if (fraction > 1.0) fraction = 1.0;

  int filled = (int)(fraction * width + 0.5);
  if (filled > width) filled = width;

  char* p = out;
  char* end = out + outsize - 1;

  // Opening bracket
  if (p < end) *p++ = '[';

  // Filled blocks (█ = U+2588, 3 bytes in UTF-8)
  for (int i = 0; i < filled && p + 3 < end; i++) {
    *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x88';  // █
  }

  // Empty blocks (░ = U+2591, 3 bytes in UTF-8)
  for (int i = filled; i < width && p + 3 < end; i++) {
    *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x91';  // ░
  }

  // Closing bracket
  if (p < end) *p++ = ']';
  *p = '\0';
}

// Format a segmented progress bar for a region within a larger bar (no brackets).
// - total_width: total bar width in characters
// - region_start: where this region starts (0.0-1.0 fraction of total)
// - region_end: where this region ends (0.0-1.0 fraction of total)
// - fill_fraction: how much of THIS region is filled (0.0-1.0)
// Outputs: spaces before region, filled░empty for region, spaces after (total_width chars)
static void format_segment_bar(char* out, size_t outsize, int total_width,
                               double region_start, double region_end,
                               double fill_fraction) {
  if (fill_fraction < 0.0) fill_fraction = 0.0;
  if (fill_fraction > 1.0) fill_fraction = 1.0;

  int start_col = (int)(region_start * total_width + 0.5);
  int end_col = (int)(region_end * total_width + 0.5);
  if (start_col < 0) start_col = 0;
  if (end_col > total_width) end_col = total_width;
  int region_width = end_col - start_col;
  if (region_width < 1) region_width = 1;

  int filled = (int)(fill_fraction * region_width + 0.5);
  if (filled > region_width) filled = region_width;

  char* p = out;
  char* end = out + outsize - 1;

  // Leading spaces (before this region)
  for (int i = 0; i < start_col && p < end; i++) {
    *p++ = ' ';
  }

  // Filled blocks (█ = U+2588)
  for (int i = 0; i < filled && p + 3 < end; i++) {
    *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x88';
  }

  // Empty blocks (░ = U+2591)
  for (int i = filled; i < region_width && p + 3 < end; i++) {
    *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x91';
  }

  // Trailing spaces (after this region)
  for (int i = end_col; i < total_width && p < end; i++) {
    *p++ = ' ';
  }

  *p = '\0';
}

// Calculate display width (accounts for multi-byte UTF-8 characters)
static int display_width(const char* s) {
  int width = 0;
  while (*s) {
    // UTF-8: if high bit set, it's a multi-byte sequence
    if ((*s & 0x80) == 0) {
      // ASCII character
      width++;
      s++;
    } else if ((*s & 0xE0) == 0xC0) {
      // 2-byte UTF-8 (display width 1)
      width++;
      s += 2;
    } else if ((*s & 0xF0) == 0xE0) {
      // 3-byte UTF-8 (display width 1) - box drawing chars
      width++;
      s += 3;
    } else if ((*s & 0xF8) == 0xF0) {
      // 4-byte UTF-8 (display width 1 or 2 for emoji, assume 1)
      width++;
      s += 4;
    } else {
      // Invalid UTF-8, treat as 1 byte
      width++;
      s++;
    }
  }
  return width;
}

// Print a line with box drawing, auto-padded to width
static void print_boxed_line(FILE* out, const char* content) {
  int len = display_width(content);
  int padding = 64 - len;
  if (padding < 0) padding = 0;
  fprintf(out, "║ %s%*s ║\n", content, padding, "");
}

// Pad a label to a fixed display width (accounting for UTF-8 multi-byte chars)
// Returns pointer to static buffer - use immediately or copy
static const char* pad_label(const char* label, int target_width) {
  static char padded[64];
  int dw = display_width(label);
  int pad = target_width - dw;
  if (pad < 0) pad = 0;
  snprintf(padded, sizeof(padded), "%s%*s", label, pad, "");
  return padded;
}

// Print combined memory statistics (scratch arena + GC heap)
void valk_memory_print_stats(valk_mem_arena_t* scratch, valk_gc_malloc_heap_t* heap, FILE* out) {
  if (out == NULL) out = stderr;
  char buf[256];
  char fmt1[16], fmt2[16];  // For formatted byte values
  char bar[128];            // For progress bars

  // Calculate capacities to determine relative bar sizes
  size_t scratch_capacity = scratch ? scratch->capacity : 0;
  size_t heap_capacity = 0;
  size_t slab_capacity = 0;
  size_t malloc_capacity = 0;
  if (heap) {
    if (heap->lval_slab) {
      slab_capacity = heap->lval_slab->numItems * heap->lval_slab->itemSize;
    }
    malloc_capacity = heap->hard_limit;
    heap_capacity = slab_capacity + malloc_capacity;
  }

  // Find max capacity for scaling bars (compare all memory regions)
  size_t max_capacity = 0;
  if (scratch_capacity > max_capacity) max_capacity = scratch_capacity;
  if (heap_capacity > max_capacity) max_capacity = heap_capacity;
  if (max_capacity == 0) max_capacity = 1;  // Avoid division by zero

  // Calculate max bar width dynamically
  // Box content width is 64 chars. Line format with padded labels is:
  // "GC HEAP             [BAR] XXXXX.XX KB / XXXXX.XX MB"
  //  ^-- 20 chars --^   ^2^   ^-- 10 --^    ^-- 10 --^
  // = LABEL_WIDTH(20) + "[" (1) + BAR + "] " (2) + value (10) + " / " (3) + value (10) = 46 + BAR
  const int BOX_CONTENT_WIDTH = 64;
  const int LABEL_WIDTH = 20;       // display width for label column
  const int FIXED_TEXT_WIDTH = LABEL_WIDTH + 1 + 2 + 10 + 3 + 10;  // 46 chars
  const int MAX_BAR_WIDTH = BOX_CONTENT_WIDTH - FIXED_TEXT_WIDTH;  // 18 chars

  fprintf(out, "\n╔══════════════════════════════════════════════════════════════════╗\n");
  print_boxed_line(out, "                   MEMORY STATISTICS");
  fprintf(out, "╠══════════════════════════════════════════════════════════════════╣\n");

  if (scratch != NULL) {
    double scratch_frac = (double)scratch->offset / scratch->capacity;
    double hwm_frac = (double)scratch->stats.high_water_mark / scratch->capacity;
    int scratch_bar_width = (int)((double)scratch_capacity / max_capacity * MAX_BAR_WIDTH + 0.5);
    if (scratch_bar_width < 3) scratch_bar_width = 3;

    // SCRATCH ARENA header with bar
    format_bytes_buf(fmt1, sizeof(fmt1), scratch->offset);
    format_bytes_buf(fmt2, sizeof(fmt2), scratch->capacity);
    format_progress_bar(bar, sizeof(bar), scratch_frac, scratch_bar_width);
    snprintf(buf, sizeof(buf), "%s%s %s / %s",
            pad_label("SCRATCH ARENA", LABEL_WIDTH), bar, fmt1, fmt2);
    print_boxed_line(out, buf);

    // High water mark
    format_bytes_buf(fmt1, sizeof(fmt1), scratch->stats.high_water_mark);
    format_progress_bar(bar, sizeof(bar), hwm_frac, scratch_bar_width);
    snprintf(buf, sizeof(buf), "%s%s %s (hwm)",
            pad_label("", LABEL_WIDTH), bar, fmt1);
    print_boxed_line(out, buf);

    // Stats (no bars)
    snprintf(buf, sizeof(buf), "  Allocations: %zu  Resets: %zu  Checkpoints: %zu",
            scratch->stats.total_allocations, scratch->stats.num_resets,
            scratch->stats.num_checkpoints);
    print_boxed_line(out, buf);

    if (scratch->stats.overflow_fallbacks > 0) {
      format_bytes_buf(fmt1, sizeof(fmt1), scratch->stats.overflow_bytes);
      snprintf(buf, sizeof(buf), "  [!] Overflow fallbacks: %zu (%s)",
              scratch->stats.overflow_fallbacks, fmt1);
      print_boxed_line(out, buf);
    }
    fprintf(out, "╠══════════════════════════════════════════════════════════════════╣\n");
  }

  if (heap != NULL) {
    // Count live objects
    size_t object_count = 0;
    for (valk_gc_header_t* h = heap->objects; h != NULL && object_count < 1000000; h = h->gc_next) {
      object_count++;
    }

    // Calculate slab stats
    size_t slab_used = 0, slab_total = 0, slab_bytes_used = 0, slab_bytes_total = 0;
    if (heap->lval_slab != NULL) {
      slab_used = heap->lval_slab->numItems - heap->lval_slab->numFree;
      slab_total = heap->lval_slab->numItems;
      size_t slab_item_size = heap->lval_slab->itemSize;
      slab_bytes_used = slab_used * slab_item_size;
      slab_bytes_total = slab_total * slab_item_size;
    }

    // Total heap = slab + malloc tracked
    size_t total_heap_used = slab_bytes_used + heap->allocated_bytes;
    size_t total_heap_capacity = slab_bytes_total + heap->hard_limit;

    // Calculate heap bar width relative to max capacity
    int heap_bar_width = (int)((double)heap_capacity / max_capacity * MAX_BAR_WIDTH + 0.5);
    if (heap_bar_width < 3) heap_bar_width = 3;

    // Calculate region boundaries for stacked bar visualization
    // Slab is first (starts at 0), malloc is second (starts after slab)
    double slab_region_end = (double)slab_bytes_total / total_heap_capacity;
    double malloc_region_start = slab_region_end;
    double slab_fill = slab_bytes_total > 0 ? (double)slab_bytes_used / slab_bytes_total : 0;
    double malloc_fill = heap->hard_limit > 0 ? (double)heap->allocated_bytes / heap->hard_limit : 0;

    // Build combined heap bar
    {
      char* p = bar;
      char* end = bar + sizeof(bar) - 1;
      int slab_cols = (int)(slab_region_end * heap_bar_width + 0.5);
      int malloc_cols = heap_bar_width - slab_cols;
      int slab_filled = (int)(slab_fill * slab_cols + 0.5);
      int malloc_filled = (int)(malloc_fill * malloc_cols + 0.5);

      if (p < end) *p++ = '[';
      for (int i = 0; i < slab_filled && p + 3 < end; i++) {
        *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x88';
      }
      for (int i = slab_filled; i < slab_cols && p + 3 < end; i++) {
        *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x91';
      }
      for (int i = 0; i < malloc_filled && p + 3 < end; i++) {
        *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x88';
      }
      for (int i = malloc_filled; i < malloc_cols && p + 3 < end; i++) {
        *p++ = '\xe2'; *p++ = '\x96'; *p++ = '\x91';
      }
      if (p < end) *p++ = ']';
      *p = '\0';
    }

    // GC HEAP header with bar
    format_bytes_buf(fmt1, sizeof(fmt1), total_heap_used);
    format_bytes_buf(fmt2, sizeof(fmt2), total_heap_capacity);
    snprintf(buf, sizeof(buf), "%s%s %s / %s",
            pad_label("GC HEAP", LABEL_WIDTH), bar, fmt1, fmt2);
    print_boxed_line(out, buf);

    // Stats under heap (no bars, indented)
    snprintf(buf, sizeof(buf), "  Live: %zu  GCs: %zu  Evacuations: %zu",
            object_count, heap->num_collections, heap->stats.evacuations_from_scratch);
    print_boxed_line(out, buf);

    // Slab sub-allocator
    if (heap->lval_slab != NULL) {
      format_segment_bar(bar, sizeof(bar), heap_bar_width, 0.0, slab_region_end, slab_fill);
      format_bytes_buf(fmt1, sizeof(fmt1), slab_bytes_used);
      format_bytes_buf(fmt2, sizeof(fmt2), slab_bytes_total);
      snprintf(buf, sizeof(buf), "%s[%s] %s / %s",
              pad_label("  ├─Slab", LABEL_WIDTH), bar, fmt1, fmt2);
      print_boxed_line(out, buf);
      snprintf(buf, sizeof(buf), "  │   Objects: %zu / %zu", slab_used, slab_total);
      print_boxed_line(out, buf);
    }

    // Malloc sub-allocator
    format_segment_bar(bar, sizeof(bar), heap_bar_width, malloc_region_start, 1.0, malloc_fill);
    format_bytes_buf(fmt1, sizeof(fmt1), heap->allocated_bytes);
    format_bytes_buf(fmt2, sizeof(fmt2), heap->hard_limit);
    snprintf(buf, sizeof(buf), "%s[%s] %s / %s",
            pad_label("  └─Malloc", LABEL_WIDTH), bar, fmt1, fmt2);
    print_boxed_line(out, buf);
    snprintf(buf, sizeof(buf), "      Free list: %zu objects", heap->free_list_size);
    print_boxed_line(out, buf);
  }

  fprintf(out, "╚══════════════════════════════════════════════════════════════════╝\n\n");
}

size_t valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap, valk_lval_t* additional_root) {
  // Record start time for pause measurement
  uint64_t start_time_us = uv_hrtime() / 1000;

  size_t before = heap->allocated_bytes;

  VALK_INFO("GC: Starting collection #%zu (usage: %u%%, threshold: %u%%)",
            heap->num_collections + 1,
            valk_gc_heap_usage_pct(heap),
            heap->gc_threshold_pct);

  // Set thread-local heap pointer for safe marking checks
  gc_current_heap = heap;

  // Phase 1: Mark reachable objects from root environment and any additional roots
  // GC only runs at safe points (between expressions). Most live data is in the
  // environment, but parsed ASTs waiting for evaluation must also be marked.
  size_t objects_marked = 0;  // Will be counted during mark phase
  valk_gc_mark_env(heap->root_env);
  if (additional_root != NULL) {
    valk_gc_mark_lval(additional_root);
  }

  // Count marked objects
  for (valk_gc_header_t* header = heap->objects; header != NULL; header = header->gc_next) {
    bool is_marked = ((uintptr_t)header->origin_allocator & 1) != 0;
    if (header->size == heap->lval_size) {
      void* user_data = (void*)(header + 1);
      valk_lval_t* obj = (valk_lval_t*)user_data;
      if ((obj->flags & LVAL_FLAG_GC_MARK) != 0) {
        is_marked = true;
      }
    }
    if (is_marked) {
      objects_marked++;
    }
  }

  // Phase 2: Sweep unreachable objects
  size_t objects_swept = 0;
  size_t reclaimed = valk_gc_malloc_sweep(heap, &objects_swept);

  // Clear thread-local heap pointer
  gc_current_heap = NULL;

  // Phase 3: Clear marks and increment generation for surviving objects
  // Walk the object list (which now only contains live objects after sweep)
  for (valk_gc_header_t* header = heap->objects; header != NULL; header = header->gc_next) {
    // Clear header mark bit (used for non-lval allocations like strings/arrays)
    header->origin_allocator = (void*)((uintptr_t)header->origin_allocator & ~(uintptr_t)1);

    // Clear lval mark bit and increment generation for surviving lval objects
    if (header->size == heap->lval_size) {
      void* user_data = (void*)(header + 1);
      valk_lval_t* obj = (valk_lval_t*)user_data;
      obj->flags &= ~LVAL_FLAG_GC_MARK;
      LVAL_GC_GEN_INC(obj);
    }
  }

  size_t after = heap->allocated_bytes;
  heap->num_collections++;

  // Calculate pause time
  uint64_t end_time_us = uv_hrtime() / 1000;
  uint64_t pause_us = end_time_us - start_time_us;

  // Update runtime metrics atomically
  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_us_total, pause_us);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);
  atomic_store(&heap->runtime_metrics.objects_marked, objects_marked);
  atomic_store(&heap->runtime_metrics.objects_swept, objects_swept);
  atomic_store(&heap->runtime_metrics.last_heap_before_gc, before);
  atomic_store(&heap->runtime_metrics.last_reclaimed, reclaimed);

  // Update max pause time using compare-exchange
  uint64_t current_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  while (pause_us > current_max) {
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_us_max, &current_max, pause_us)) {
      break;
    }
  }

  // Record pause time in frame-budget histogram (for game profile)
  // Buckets: 0-1ms, 1-5ms, 5-10ms, 10-16ms, 16ms+
  uint64_t pause_ms = pause_us / 1000;
  if (pause_ms < 1) {
    atomic_fetch_add(&heap->runtime_metrics.pause_0_1ms, 1);
  } else if (pause_ms < 5) {
    atomic_fetch_add(&heap->runtime_metrics.pause_1_5ms, 1);
  } else if (pause_ms < 10) {
    atomic_fetch_add(&heap->runtime_metrics.pause_5_10ms, 1);
  } else if (pause_ms < 16) {
    atomic_fetch_add(&heap->runtime_metrics.pause_10_16ms, 1);
  } else {
    atomic_fetch_add(&heap->runtime_metrics.pause_16ms_plus, 1);
  }

  // Record GC timestamp for rate limiting
  heap->last_gc_time_us = end_time_us;

  // Calculate new usage percentage for logging
  uint8_t usage_pct = valk_gc_heap_usage_pct(heap);

  VALK_INFO("GC: Complete - reclaimed %zu bytes (before: %zu, after: %zu, %.1f%% freed), "
            "heap now at %u%%, pause: %llu us",
            reclaimed, before, after,
            before > 0 ? 100.0 * reclaimed / before : 0.0,
            usage_pct, (unsigned long long)pause_us);

  return reclaimed;
}

// ============================================================================
// GC Heap Object Management
// ============================================================================

// Explicitly free a single GC heap object
// Used when explicitly freeing an object (e.g., when switching allocators)
void valk_gc_free_object(void* heap_ptr, void* user_ptr) {
  if (user_ptr == NULL) return;

  valk_gc_malloc_heap_t* heap = (valk_gc_malloc_heap_t*)heap_ptr;

  // Get header (it's right before the user data)
  valk_gc_header_t* header = ((valk_gc_header_t*)user_ptr) - 1;

  // Remove from objects list
  valk_gc_header_t** current_ptr = &heap->objects;
  while (*current_ptr != NULL) {
    if (*current_ptr == header) {
      *current_ptr = header->gc_next;
      break;
    }
    current_ptr = &(*current_ptr)->gc_next;
  }

  // Determine if from lval slab, lenv slab, or malloc and free accordingly
  uintptr_t obj_addr = (uintptr_t)header;
  bool from_lval_slab = false;
  if (heap->lval_slab != NULL) {
    uintptr_t slab_start = (uintptr_t)heap->lval_slab;
    size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
    size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
    uintptr_t slab_end = slab_start + slab_total_size;
    from_lval_slab = (obj_addr >= slab_start && obj_addr < slab_end);
  }

  bool from_lenv_slab = false;
  if (!from_lval_slab && heap->lenv_slab != NULL) {
    uintptr_t slab_start = (uintptr_t)heap->lenv_slab;
    size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lenv_size;
    size_t slab_total_size = valk_slab_size(slab_item_size, 64 * 1024);
    uintptr_t slab_end = slab_start + slab_total_size;
    from_lenv_slab = (obj_addr >= slab_start && obj_addr < slab_end);
  }

  size_t total_size = sizeof(valk_gc_header_t) + header->size;

  if (from_lval_slab) {
    // Return to lval slab allocator
    valk_mem_allocator_free((void*)heap->lval_slab, header);
  } else if (from_lenv_slab) {
    // Return to lenv slab allocator
    valk_mem_allocator_free((void*)heap->lenv_slab, header);
  } else {
    // Free malloc'd memory directly
    heap->allocated_bytes -= total_size;
    free(header);
  }
}

// ============================================================================
// GC Heap Cleanup - Free all allocations for clean shutdown
// ============================================================================

void valk_gc_malloc_heap_destroy(valk_gc_malloc_heap_t* heap) {
  if (heap == NULL) return;

  VALK_INFO("GC: Destroying heap, freeing all %zu remaining objects",
            heap->allocated_bytes);

  // Free all objects in the linked list
  valk_gc_header_t* current = heap->objects;
  size_t freed_count = 0;
  size_t freed_bytes = 0;

  while (current != NULL) {
    valk_gc_header_t* next = current->gc_next;

    // Free internal resources for lval objects before freeing the structure
    // NOTE: Most internal allocations (fun.name, lval->str) use valk_mem_alloc
    // and are tracked separately. Only free raw malloc/strdup allocations.
    bool is_lval = (current->size == heap->lval_size);
    if (is_lval) {
      void* user_data = (void*)(current + 1);
      valk_lval_t* obj = (valk_lval_t*)user_data;
      switch (LVAL_TYPE(obj)) {
        case LVAL_REF:
          if (obj->ref.free != NULL && obj->ref.ptr != NULL) {
            obj->ref.free(obj->ref.ptr);
          }
          break;
        default:
          break;
      }
    }

    // Check if object is from lval slab via address range check
    uintptr_t obj_addr = (uintptr_t)current;
    bool from_lval_slab = false;
    if (heap->lval_slab != NULL) {
      uintptr_t slab_start = (uintptr_t)heap->lval_slab;
      size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
      size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
      uintptr_t slab_end = slab_start + slab_total_size;
      from_lval_slab = (obj_addr >= slab_start && obj_addr < slab_end);
    }

    // Check if object is from lenv slab
    bool from_lenv_slab = false;
    if (!from_lval_slab && heap->lenv_slab != NULL) {
      uintptr_t slab_start = (uintptr_t)heap->lenv_slab;
      size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lenv_size;
      size_t slab_total_size = valk_slab_size(slab_item_size, 64 * 1024);
      uintptr_t slab_end = slab_start + slab_total_size;
      from_lenv_slab = (obj_addr >= slab_start && obj_addr < slab_end);
    }

    if (!from_lval_slab && !from_lenv_slab) {
      // Free malloc'd objects directly (slab objects freed with slab itself)
      size_t total_size = sizeof(valk_gc_header_t) + current->size;
      freed_bytes += total_size;
      freed_count++;
      free(current);
    }
    current = next;
  }

  VALK_INFO("GC: Freed %zu objects (%zu bytes)", freed_count, freed_bytes);

  // Also free the free list (again, skip slab objects)
  current = heap->free_list;
  while (current != NULL) {
    valk_gc_header_t* next = current->gc_next;
    uintptr_t obj_addr = (uintptr_t)current;

    bool from_lval_slab = false;
    if (heap->lval_slab != NULL) {
      uintptr_t slab_start = (uintptr_t)heap->lval_slab;
      size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lval_size;
      size_t slab_total_size = valk_slab_size(slab_item_size, 256 * 1024);
      uintptr_t slab_end = slab_start + slab_total_size;
      from_lval_slab = (obj_addr >= slab_start && obj_addr < slab_end);
    }

    bool from_lenv_slab = false;
    if (!from_lval_slab && heap->lenv_slab != NULL) {
      uintptr_t slab_start = (uintptr_t)heap->lenv_slab;
      size_t slab_item_size = sizeof(valk_gc_header_t) + heap->lenv_size;
      size_t slab_total_size = valk_slab_size(slab_item_size, 64 * 1024);
      uintptr_t slab_end = slab_start + slab_total_size;
      from_lenv_slab = (obj_addr >= slab_start && obj_addr < slab_end);
    }

    if (!from_lval_slab && !from_lenv_slab) {
      free(current);
    }
    current = next;
  }

  // Free the slab allocators directly (don't use valk_slab_free which goes through valk_mem_free)
  if (heap->lval_slab != NULL) {
    free(heap->lval_slab);
  }
  if (heap->lenv_slab != NULL) {
    free(heap->lenv_slab);
  }

  // Free the heap structure itself
  free(heap);
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

  // Combined slabs + malloc usage for total heap metrics
  size_t lval_slab_bytes_used = 0;
  size_t lval_slab_bytes_total = 0;
  if (heap->lval_slab) {
    size_t slab_used = heap->lval_slab->numItems - heap->lval_slab->numFree;
    size_t item_size = heap->lval_slab->itemSize;
    lval_slab_bytes_used = slab_used * item_size;
    lval_slab_bytes_total = heap->lval_slab->numItems * item_size;
  }

  size_t lenv_slab_bytes_used = 0;
  size_t lenv_slab_bytes_total = 0;
  if (heap->lenv_slab) {
    size_t slab_used = heap->lenv_slab->numItems - heap->lenv_slab->numFree;
    size_t item_size = heap->lenv_slab->itemSize;
    lenv_slab_bytes_used = slab_used * item_size;
    lenv_slab_bytes_total = heap->lenv_slab->numItems * item_size;
  }

  if (heap_used) *heap_used = lval_slab_bytes_used + lenv_slab_bytes_used + heap->allocated_bytes;
  if (heap_total) *heap_total = lval_slab_bytes_total + lenv_slab_bytes_total + heap->hard_limit;
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

  if (heap->lval_slab) {
    out->lval_slab_total = heap->lval_slab->numItems;
    out->lval_slab_used = heap->lval_slab->numItems - heap->lval_slab->numFree;
    out->lval_slab_peak = heap->lval_slab->peakUsed;
    if (out->lval_slab_peak > 0) {
      out->lval_fragmentation = 1.0 - ((double)out->lval_slab_used / out->lval_slab_peak);
      if (out->lval_fragmentation < 0) out->lval_fragmentation = 0;
    }
  }

  if (heap->lenv_slab) {
    out->lenv_slab_total = heap->lenv_slab->numItems;
    out->lenv_slab_used = heap->lenv_slab->numItems - heap->lenv_slab->numFree;
    out->lenv_slab_peak = heap->lenv_slab->peakUsed;
    if (out->lenv_slab_peak > 0) {
      out->lenv_fragmentation = 1.0 - ((double)out->lenv_slab_used / out->lenv_slab_peak);
      if (out->lenv_fragmentation < 0) out->lenv_fragmentation = 0;
    }
  }

  out->malloc_allocated = heap->allocated_bytes;
  out->malloc_limit = heap->hard_limit;
  out->malloc_peak = heap->stats.peak_usage;

  out->free_list_count = heap->free_list_size;
  if (heap->free_list_size > 0) {
    size_t avg_size = heap->lval_size + sizeof(valk_gc_header_t);
    out->free_list_bytes = heap->free_list_size * avg_size;
  }
}

// ============================================================================
// Retained Size Sampling - Sample top bindings by retained memory
// ============================================================================

static size_t estimate_lval_size(valk_lval_t* v, valk_gc_malloc_heap_t* heap) {
  if (v == NULL) return 0;
  if (LVAL_ALLOC(v) != LVAL_ALLOC_HEAP) return 0;

  size_t size = heap->lval_size;

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
    if (heap->lval_slab) {
      size_t slab_used = heap->lval_slab->numItems - heap->lval_slab->numFree;
      out->heap_used_bytes += slab_used * heap->lval_slab->itemSize;
      out->lval_count = slab_used;
    }
    if (heap->lenv_slab) {
      size_t slab_used = heap->lenv_slab->numItems - heap->lenv_slab->numFree;
      out->heap_used_bytes += slab_used * heap->lenv_slab->itemSize;
      out->lenv_count = slab_used;
    }
    out->heap_used_bytes += heap->allocated_bytes;
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

// Add an already-allocated value to GC heap's object tracking list
void valk_gc_add_to_objects(valk_gc_malloc_heap_t* heap, valk_lval_t* v) {
  // Get the header (it's right before the user data)
  valk_gc_header_t* header = ((valk_gc_header_t*)v) - 1;

  // Add to live objects linked list
  header->gc_next = heap->objects;
  heap->objects = header;
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
  // This avoids iterating heap->objects which may contain non-value allocations
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
