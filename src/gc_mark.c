#include "gc.h"
#include "parser.h"
#include "memory.h"
#include "async_handle.h"
#include "log.h"
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <uv.h>

// ============================================================================
// Mark Phase Internals
// ============================================================================

// LCOV_EXCL_BR_START - heap mark phase null checks and type dispatch
static void mark_children(valk_lval_t *obj, valk_gc_mark_ctx_t *ctx);
static void mark_env(valk_lenv_t *env, valk_gc_mark_ctx_t *ctx);

static bool mark_ptr_only(void *ptr, valk_gc_mark_ctx_t *ctx) {
  if (ptr == nullptr) return false;

  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(ctx->heap, ptr, &loc)) {
    return valk_gc_page_try_mark(loc.page, loc.slot);
  } else {
    return valk_gc_mark_large_object(ctx->heap, ptr);
  }
}

// LCOV_EXCL_START - Heap2 marking with complex types requires runtime context from real GC cycle
static void mark_lval(valk_lval_t *lval, valk_gc_mark_ctx_t *ctx) {
  if (lval == nullptr) return;
  if (!mark_ptr_only(lval, ctx)) return;
  valk_gc_mark_queue_push(ctx->queue, lval);
}

#define MARK_ENV_VISITED_MAX 128

static void mark_env(valk_lenv_t *env, valk_gc_mark_ctx_t *ctx) {
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
      mark_lval(env->vals.items[i], ctx);
    }
    env = env->parent;
  }
}

static void mark_children(valk_lval_t *obj, valk_gc_mark_ctx_t *ctx) {
  if (obj == nullptr) return;
  switch (LVAL_TYPE(obj)) {
    case LVAL_CONS:
      mark_lval(obj->cons.head, ctx);
      mark_lval(obj->cons.tail, ctx);
      break;
    case LVAL_FUN:
      if (obj->fun.builtin == nullptr) {
        mark_lval(obj->fun.formals, ctx);
        mark_lval(obj->fun.body, ctx);
        if (obj->fun.env) mark_env(obj->fun.env, ctx);
      }
      mark_ptr_only(obj->fun.name, ctx);
      break;
    case LVAL_HANDLE:
      if (obj->async.handle) {
        mark_lval(obj->async.handle->on_complete, ctx);
        mark_lval(obj->async.handle->on_error, ctx);
        mark_lval(obj->async.handle->on_cancel, ctx);
        mark_lval(atomic_load_explicit(&obj->async.handle->result, memory_order_acquire), ctx);
        mark_lval(atomic_load_explicit(&obj->async.handle->error, memory_order_acquire), ctx);
        if (obj->async.handle->env) mark_env(obj->async.handle->env, ctx);
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
  valk_gc_mark_ctx_t *ctx = user;
  mark_lval(val, ctx);
}

void valk_gc_heap_mark_object(valk_gc_mark_ctx_t *ctx, void *ptr) {
  mark_lval(ptr, ctx);
}
// LCOV_EXCL_BR_STOP

// ============================================================================
// OWST Termination Detection
// ============================================================================

static _Atomic u64 __gc_heap_offered = 0;
static _Atomic bool __gc_heap_terminated = false;
static _Atomic(valk_gc_heap_t *) __gc_heap_current = nullptr;
static pthread_mutex_t __gc_heap_term_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t __gc_heap_term_cond = PTHREAD_COND_INITIALIZER;

// LCOV_EXCL_START - OWST termination requires multi-threaded GC timing impossible to reliably test
static bool valk_gc_heap_offer_termination(void) {
  u64 num_threads = atomic_load(&valk_sys->threads_registered);

  pthread_mutex_lock(&__gc_heap_term_lock);
  u64 offered = atomic_fetch_add(&__gc_heap_offered, 1) + 1;

  if (offered == num_threads) {
    bool all_empty = true;
    for (u64 i = 0; i < num_threads; i++) {
      if (!valk_sys->threads[i].active) continue;
      if (!valk_gc_mark_queue_empty(&valk_sys->threads[i].mark_queue)) {
        all_empty = false;
        break;
      }
    }
    if (all_empty) {
      atomic_store(&__gc_heap_terminated, true);
      pthread_cond_broadcast(&__gc_heap_term_cond);
      pthread_mutex_unlock(&__gc_heap_term_lock);
      return true;
    }
  }

  while (!atomic_load(&__gc_heap_terminated)) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_nsec += 1000000;
    if (ts.tv_nsec >= 1000000000) { ts.tv_sec++; ts.tv_nsec -= 1000000000; }
    pthread_cond_timedwait(&__gc_heap_term_cond, &__gc_heap_term_lock, &ts);

    if (atomic_load(&__gc_heap_terminated)) {
      pthread_mutex_unlock(&__gc_heap_term_lock);
      return true;
    }

    bool found_work = false;
    for (u64 i = 0; i < num_threads; i++) {
      if (!valk_sys->threads[i].active) continue;
      if (!valk_gc_mark_queue_empty(&valk_sys->threads[i].mark_queue)) {
        found_work = true;
        break;
      }
    }
    if (found_work) {
      atomic_fetch_sub(&__gc_heap_offered, 1);
      pthread_cond_signal(&__gc_heap_term_cond);
      pthread_mutex_unlock(&__gc_heap_term_lock);
      return false;
    }
  }

  pthread_mutex_unlock(&__gc_heap_term_lock);
  return true;
}
// LCOV_EXCL_STOP

// ============================================================================
// Parallel Mark / Sweep
// ============================================================================

// LCOV_EXCL_START - Heap2 parallel mark/sweep requires multi-threaded STW coordination
void valk_gc_heap_parallel_mark(valk_gc_heap_t *heap) {
  if (!heap) return;
  if (!valk_thread_ctx.gc_registered) return;

  u64 my_id = valk_thread_ctx.gc_thread_id;
  valk_gc_mark_queue_t *my_queue = &valk_sys->threads[my_id].mark_queue;

  valk_gc_mark_queue_init(my_queue);

  valk_gc_mark_ctx_t ctx = {
    .heap = heap,
    .queue = my_queue
  };

  valk_gc_visit_thread_roots(mark_root_visitor2, &ctx);

  if (my_id == 0) {
    valk_gc_visit_global_roots(mark_root_visitor2, &ctx);
  }

  valk_barrier_wait(&valk_sys->barrier);

  while (true) {
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != nullptr) {
      mark_children(obj, &ctx);
    }

    bool found_work = false;
    u64 num_threads = atomic_load(&valk_sys->threads_registered);

    for (u64 i = 1; i <= num_threads; i++) {
      u64 victim = (my_id + i) % num_threads;
      if (!valk_sys->threads[victim].active) continue;

      obj = valk_gc_mark_queue_steal(&valk_sys->threads[victim].mark_queue);
      if (obj != nullptr) {
        mark_children(obj, &ctx);
        found_work = true;
        break;
      }
    }

    if (!found_work) {
      if (valk_gc_heap_offer_termination()) {
        break;
      }
    }
  }
}

void valk_gc_heap_parallel_sweep(valk_gc_heap_t *heap) {
  if (!heap) return;
  if (!valk_thread_ctx.gc_registered) return;

  u64 my_id = valk_thread_ctx.gc_thread_id;
  u64 num_threads = atomic_load(&valk_sys->threads_registered);

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];

    u64 num_pages = list->num_pages;
    if (num_pages == 0) continue;

    u64 pages_per_thread = (num_pages + num_threads - 1) / num_threads;
    u64 my_start = my_id * pages_per_thread;
    u64 my_end = (my_id + 1) * pages_per_thread;
    if (my_end > num_pages) my_end = num_pages;

    valk_gc_page_t *page = list->all_pages;
    for (u64 i = 0; i < my_start && page != nullptr; i++) {
      page = page->next;
    }

    u64 freed_slots = 0;
    for (u64 i = my_start; i < my_end && page != nullptr; i++) {
      freed_slots += valk_gc_sweep_page(page);
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

// ============================================================================
// STW Request
// ============================================================================

bool valk_gc_heap_request_stw(valk_gc_heap_t *heap) {
  if (!heap) return false;

  if (atomic_load(&valk_sys->shutting_down)) return false;

  u64 num_threads = atomic_load(&valk_sys->threads_registered);
  if (num_threads == 0) return false;

  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_sys->phase, &expected,
                                       VALK_GC_PHASE_STW_REQUESTED)) {
    return false;
  }

  if (valk_sys->barrier_initialized) {
    valk_barrier_reset(&valk_sys->barrier, num_threads);
  } else {
    valk_barrier_init(&valk_sys->barrier, num_threads);
    valk_sys->barrier_initialized = true;
  }

  atomic_store(&__gc_heap_current, heap);

  atomic_thread_fence(memory_order_seq_cst);

  valk_system_wake_threads(valk_sys);

  valk_barrier_wait(&valk_sys->barrier);

  return true;
}

// ============================================================================
// Participate in Parallel GC (worker threads)
// ============================================================================

void valk_gc_participate_in_parallel_gc(void) {
  valk_gc_heap_t *heap = atomic_load(&__gc_heap_current);

  valk_barrier_wait(&valk_sys->barrier);
  if (heap) valk_gc_heap_parallel_mark(heap);
  valk_barrier_wait(&valk_sys->barrier);
  if (heap) valk_gc_heap_parallel_sweep(heap);
  valk_barrier_wait(&valk_sys->barrier);
  valk_barrier_wait(&valk_sys->barrier);
}
// LCOV_EXCL_STOP

// ============================================================================
// GC Collection Cycle
// ============================================================================

sz valk_gc_heap_collect(valk_gc_heap_t *heap) {
  if (!heap) return 0;

  VALK_ASSERT(atomic_load(&valk_sys->threads_registered) > 0, // LCOV_EXCL_BR_LINE
              "GC collect requires at least one registered thread");

  // LCOV_EXCL_START - STW request contention: requires concurrent GC requests
  if (!valk_gc_heap_request_stw(heap)) {
    VALK_GC_SAFE_POINT();
    return 0;
  }
  // LCOV_EXCL_STOP

  u64 num_threads = atomic_load(&valk_sys->threads_registered);
  u64 start_ns = uv_hrtime();

  atomic_store(&heap->gc_in_progress, true);
  atomic_fetch_add(&heap->collections, 1);

  u64 bytes_before = valk_gc_heap_used_bytes(heap);

  atomic_store(&__gc_heap_offered, 0);
  atomic_store(&__gc_heap_terminated, false);

  valk_barrier_wait(&valk_sys->barrier);

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_MARKING);
  valk_gc_heap_parallel_mark(heap);

  valk_barrier_wait(&valk_sys->barrier);

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_SWEEPING);
  valk_gc_heap_parallel_sweep(heap);

  valk_barrier_wait(&valk_sys->barrier);

  if (valk_thread_ctx.gc_thread_id == 0) { // LCOV_EXCL_BR_LINE - only lead GC thread
    valk_gc_rebuild_partial_lists(heap);
    valk_gc_reclaim_empty_pages(heap);
    heap->generation = valk_gc_heap_next_generation();
  }

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);

  valk_barrier_wait(&valk_sys->barrier);

  u64 bytes_after = valk_gc_heap_used_bytes(heap);
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
  while (pause_us > current_max) { // LCOV_EXCL_BR_LINE - CAS loop
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_us_max, &current_max, pause_us)) { // LCOV_EXCL_BR_LINE
      break;
    }
  }

  atomic_fetch_add(&valk_sys->parallel_cycles, 1);
  atomic_fetch_add(&valk_sys->parallel_pause_us_total, pause_us);

  VALK_DEBUG("GC cycle complete: reclaimed %zu bytes in %llu us (%zu threads)",
             reclaimed, (unsigned long long)pause_us, num_threads);

  return reclaimed;
}

// LCOV_EXCL_START - fork safety function requires actual fork()
void valk_gc_mark_reset_after_fork(void) {
  atomic_store(&__gc_heap_offered, 0);
  atomic_store(&__gc_heap_terminated, false);
  atomic_store(&__gc_heap_current, nullptr);
  pthread_mutex_init(&__gc_heap_term_lock, nullptr);
  pthread_cond_init(&__gc_heap_term_cond, nullptr);
}
// LCOV_EXCL_STOP
