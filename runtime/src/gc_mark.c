#include "gc.h"
#include "parser.h"
#include "conc_map.h"
#include "dict.h"
#include "memory.h"
#include "async_handle.h"
#include "eval_internal.h"
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

// LCOV_EXCL_START - Heap2 mark internals only reachable from parallel GC cycle
static bool mark_ptr_only(void *ptr, valk_gc_mark_ctx_t *ctx) {
  if (ptr == nullptr) return false;

  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(ctx->heap, ptr, &loc)) {
    return ctx->solo ? valk_gc_page_try_mark_solo(loc.page, loc.slot)
                     : valk_gc_page_try_mark(loc.page, loc.slot);
  } else {
    return valk_gc_mark_large_object(ctx->heap, ptr);
  }
}
static void mark_lval(valk_lval_t *lval, valk_gc_mark_ctx_t *ctx) {
  if (lval == nullptr) return;

  valk_gc_ptr_location_t loc;
  bool in_heap = valk_gc_ptr_to_location(ctx->heap, lval, &loc);

  if (in_heap) {
    // Inside the heap, ONLY the mark bit protects a slot — flags don't.
    // Builtin lvals are allocated on the GC heap and flagged IMMORTAL
    // (put_builtin_impl); honoring the flag here left every builtin
    // unmarked and the sweeper freed them all at the first collection.
    // The heap-resident "immortals" still need their children traced:
    // a builtin's fun.name string is a heap allocation too.
    bool first = ctx->solo ? valk_gc_page_try_mark_solo(loc.page, loc.slot)
                           : valk_gc_page_try_mark(loc.page, loc.slot);
    if (!first) return;
    // Leaves don't need a queue round-trip. Pushing them only to pop them
    // again and fall through mark_children's switch was roughly half of all
    // queue traffic, because half of a typical live set is numbers.
    switch (LVAL_TYPE(lval)) {
      case LVAL_NUM:
      case LVAL_NIL:
        return;
      case LVAL_SYM:
      case LVAL_STR:
      case LVAL_ERR:
        mark_ptr_only(lval->str, ctx);
        return;
      default:
        valk_gc_mark_queue_push(ctx->queue, lval);
        return;
    }
  }

  // True immortals (image buffers, singletons, num cache, static storage)
  // live outside the heap; nothing to mark and children are covered by the
  // frozen-env walk.
  if (lval->flags & LVAL_FLAG_IMMORTAL) return;

  if (!valk_gc_mark_large_object(ctx->heap, lval)) {
    mark_children(lval, ctx);
  }
}

static void mark_env_block_cb(void *ptr, void *ctx) {
  mark_ptr_only(ptr, (valk_gc_mark_ctx_t *)ctx);
}
static void mark_env_value_cb(valk_lval_t *val, void *ctx) {
  mark_lval(val, (valk_gc_mark_ctx_t *)ctx);
}

static void mark_env(valk_lenv_t *env, valk_gc_mark_ctx_t *ctx) {
  while (env != nullptr) {
    valk_gc_ptr_location_t loc;
    if (valk_gc_ptr_to_location(ctx->heap, env, &loc)) {
      // Heap env: the mark bit dedups the walk. Whoever marks it first
      // walks its contents AND the rest of the parent chain, so a lost
      // race here means the whole subtree is already covered.
      bool first = ctx->solo ? valk_gc_page_try_mark_solo(loc.page, loc.slot)
                             : valk_gc_page_try_mark(loc.page, loc.slot);
      if (!first) return;
    } else if (!(atomic_load(&env->flags) & LENV_FLAG_FROZEN)) {
      // Env block outside the GC heap and not frozen (malloc-mode tests,
      // foreign envs): stop. There is no mark bit for dedup, and walking
      // would recurse forever on cyclic closures (fun in env whose
      // fun.env is that env). Mutable envs that bind GC-heap values must
      // live in the GC heap — eval on event-loop threads runs under the
      // scratch discipline (see __run_task_in_scratch and the pipe read
      // callbacks) to uphold this.
      return;
    }
    // Frozen image env (immortal memory): its bindings MUST be walked.
    // Image loading resolves builtin stubs against the runtime registry
    // and patches RUNTIME GC-HEAP builtin lvals into the immortal image
    // buffer (img_apply_stub_map). Skipping frozen envs orphans every
    // builtin function lval: they are collected at the first cycle and
    // all interpreted applications afterwards fail with "Cannot call
    // non-function: UNDEFINED" (AOT-compiled direct calls keep working,
    // which made AOT binaries limp convincingly instead of crashing).
    // No recursion hazard: frozen bindings are immortal lvals (skipped
    // by mark_lval) or heap lvals (deduped by their mark bits). The walk
    // is deduped by the heap ancestors through which chains reach it.
    if (env->cmap) {
      // Concurrent (shared global) env: mark the map's tables, keys, values.
      valk_cmap_gc_mark((valk_cmap_t *)env->cmap, mark_env_block_cb,
                        mark_env_value_cb, ctx);
    }
    mark_ptr_only(env->symbols.items, ctx);
    mark_ptr_only(env->vals.items, ctx);
    // Interned keys are permanent intern-table allocations, not GC objects.
    // Marking them is not just pointless: mark_ptr_only falls through to
    // valk_gc_mark_large_object, which takes heap->large_lock and walks the
    // large-object list for every key on every mark.
    if (!(atomic_load(&env->flags) & LENV_FLAG_KEYS_INTERNED)) {
      for (u64 i = 0; i < env->symbols.count; i++) {
        mark_ptr_only(env->symbols.items[i], ctx);
      }
    }
    for (u64 i = 0; i < env->vals.count; i++) {
      mark_lval(env->vals.items[i], ctx);
    }
    env = env->parent;
  }
}

static void mark_children(valk_lval_t *obj, valk_gc_mark_ctx_t *ctx) {
  while (obj != nullptr) {
    switch (LVAL_TYPE(obj)) {
      case LVAL_CONS:
        mark_lval(obj->cons.head, ctx);
        obj = obj->cons.tail;
        if (obj == nullptr) return;
        {
          valk_gc_ptr_location_t loc;
          if (valk_gc_ptr_to_location(ctx->heap, obj, &loc)) {
            bool first = ctx->solo
                             ? valk_gc_page_try_mark_solo(loc.page, loc.slot)
                             : valk_gc_page_try_mark(loc.page, loc.slot);
            // Walk the spine in place rather than enqueueing every tail: a
            // list of N cells used to cost N pushes and N pops. If someone
            // else already marked the tail, the rest of the spine is theirs.
            if (!first) return;
            continue;
          }
          if (valk_gc_mark_large_object(ctx->heap, obj))
            return;
        }
        continue;
      case LVAL_FUN:
        if (obj->fun.builtin == nullptr) {
          mark_lval(obj->fun.formals, ctx);
          mark_lval(obj->fun.body, ctx);
          if (obj->fun.env) mark_env(obj->fun.env, ctx);
        }
        mark_ptr_only(obj->fun.name, ctx);
        return;
      case LVAL_HANDLE:
        if (obj->async.handle) {
          mark_lval(obj->async.handle->on_complete, ctx);
          mark_lval(obj->async.handle->on_error, ctx);
          mark_lval(obj->async.handle->on_cancel, ctx);
          mark_lval(atomic_load_explicit(&obj->async.handle->result, memory_order_acquire), ctx);
          mark_lval(atomic_load_explicit(&obj->async.handle->error, memory_order_acquire), ctx);
          if (obj->async.handle->env) mark_env(obj->async.handle->env, ctx);
        }
        return;
      case LVAL_SYM:
      case LVAL_STR:
      case LVAL_ERR:
        mark_ptr_only(obj->str, ctx);
        return;
      case LVAL_REF:
        mark_ptr_only(obj->ref.type, ctx);
        if (obj->ref.mark)
          obj->ref.mark(obj->ref.ptr, ctx);
        return;
      case LVAL_DICT: {
        valk_dict_t *d = obj->dict.data;
        if (d) {
          mark_ptr_only(d, ctx);
          valk_dict_cell_t *cells = dict_cells(d);
          u32 *buckets = dict_buckets(d);
          for (u32 b = 0; b < d->num_buckets; b++) {
            u32 ci = buckets[b];
            while (ci != DICT_EMPTY) {
              if (cells[ci].value != nullptr)
                mark_lval(cells[ci].value, ctx);
              ci = cells[ci].next;
            }
          }
        }
        return;
      }
      default:
        return;
    }
  }
}

static void mark_one_eval_stack(valk_eval_stack_t *stack, valk_gc_mark_ctx_t *ctx) {
  for (u64 i = 0; i < stack->count; i++) {
    valk_cont_frame_t *frame = &stack->frames[i];
    if (frame->env) mark_env(frame->env, ctx);
    switch (frame->kind) {
      case CONT_EVAL_ARGS:
        mark_lval(frame->eval_args.func, ctx);
        mark_lval(frame->eval_args.remaining, ctx);
        break;
      case CONT_COLLECT_ARG:
        mark_lval(frame->collect_arg.func, ctx);
        mark_lval(frame->collect_arg.remaining, ctx);
        for (u64 j = 0; j < frame->collect_arg.count; j++) {
          mark_lval(frame->collect_arg.args[j], ctx);
        }
        break;
      case CONT_IF_BRANCH:
        mark_lval(frame->if_branch.true_branch, ctx);
        mark_lval(frame->if_branch.false_branch, ctx);
        break;
      case CONT_DO_NEXT:
        mark_lval(frame->do_next.remaining, ctx);
        break;
      case CONT_SELECT_CHECK:
        mark_lval(frame->select_check.result_expr, ctx);
        mark_lval(frame->select_check.remaining, ctx);
        mark_lval(frame->select_check.original_args, ctx);
        break;
      case CONT_BODY_NEXT:
        mark_lval(frame->body_next.remaining, ctx);
        if (frame->body_next.call_env) mark_env(frame->body_next.call_env, ctx);
        break;
      case CONT_CTX_DEADLINE:
        mark_lval(frame->ctx_deadline.body, ctx);
        break;
      case CONT_CTX_WITH:
        mark_lval(frame->ctx_with.value_expr, ctx);
        mark_lval(frame->ctx_with.body, ctx);
        break;
      default:
        break;
    }
  }
}

static void mark_eval_stack_roots(valk_gc_mark_ctx_t *ctx) {
  valk_thread_context_t *tc = &valk_thread_ctx;

  mark_lval(tc->eval_expr, ctx);
  mark_lval(tc->eval_value, ctx);
  if (tc->eval_env) mark_env(tc->eval_env, ctx);

  for (u32 i = 0; i < tc->eval_stack_depth; i++) {
    valk_eval_stack_t *stack = (valk_eval_stack_t *)tc->eval_stacks[i];
    if (stack) mark_one_eval_stack(stack, ctx);
    if (tc->saved_eval_envs[i]) mark_env(tc->saved_eval_envs[i], ctx);
  }

  // Call envs held only by native (AOT/JIT) frames — pushed by compiled
  // function prologues and the interpreter's call-env construction.
  for (sz i = 0; i < tc->env_root_stack_count; i++) {
    if (tc->env_root_stack[i]) mark_env(tc->env_root_stack[i], ctx);
  }
}

static void mark_root_visitor2(valk_lval_t *val, void *user) {
  valk_gc_mark_ctx_t *ctx = user;
  mark_lval(val, ctx);
}

// Remembered-set entries are immortal lvals whose CONTENTS reference the GC
// heap (e.g., image dicts grown at runtime). mark_lval would skip them, so
// trace their children directly.
static void mark_remembered_visitor(valk_lval_t *val, void *user) {
  valk_gc_mark_ctx_t *ctx = user;
  mark_children(val, ctx);
}

void valk_gc_heap_mark_object(valk_gc_mark_ctx_t *ctx, void *ptr) {
  mark_lval(ptr, ctx);
}

void valk_gc_heap_mark_raw(valk_gc_mark_ctx_t *ctx, void *ptr) {
  mark_ptr_only(ptr, ctx);
}
// LCOV_EXCL_STOP
// LCOV_EXCL_BR_STOP

// ============================================================================
// OWST Termination Detection
// ============================================================================

static _Atomic u64 __gc_heap_offered = 0;
static _Atomic bool __gc_heap_terminated = false;
static _Atomic(valk_gc_heap_t *) __gc_heap_current = nullptr;
static pthread_mutex_t __gc_heap_term_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t __gc_heap_term_cond = PTHREAD_COND_INITIALIZER;

// Cycle-frozen participant set, written by the coordinator under
// thread_mutex in valk_gc_heap_request_stw. OWST termination and sweep
// partitioning are only correct against a constant participant count;
// threads_registered is live and moves when threads register mid-cycle.
static _Atomic u64 __gc_cycle_participants = 0;
static _Atomic u64 __gc_cycle_scan_max = 0;

// LCOV_EXCL_START - OWST termination requires multi-threaded GC timing impossible to reliably test
static bool valk_gc_heap_offer_termination(void) {
  u64 num_threads = atomic_load(&__gc_cycle_participants);
  u64 max_idx = atomic_load(&__gc_cycle_scan_max);

  pthread_mutex_lock(&__gc_heap_term_lock);
  u64 offered = atomic_fetch_add(&__gc_heap_offered, 1) + 1;

  if (offered == num_threads) {
    bool all_empty = true;
    for (u64 i = 0; i < max_idx; i++) {
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
    for (u64 i = 0; i < max_idx; i++) {
      if (!valk_sys->threads[i].active) continue;
      if (!valk_gc_mark_queue_empty(&valk_sys->threads[i].mark_queue)) {
        found_work = true;
        break;
      }
    }
    if (found_work) {  // LCOV_EXCL_BR_LINE - work-refound timing
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

  valk_gc_mark_queue_reset(my_queue);

  const bool solo = atomic_load(&__gc_cycle_participants) <= 1;

  valk_gc_mark_ctx_t ctx = {
    .heap = heap,
    .queue = my_queue,
    .solo = solo
  };

  valk_gc_visit_thread_roots(mark_root_visitor2, &ctx);
  mark_eval_stack_roots(&ctx);

  if (valk_thread_ctx.gc_cycle_rank == 0) {
    valk_gc_visit_global_roots(mark_root_visitor2, &ctx);

    // The macro env may be a standalone heap env referenced only by a
    // static C global (AOT binaries point it at the runtime-built builtin
    // registry). visit_global_roots marks its VALUES via the visitor, but
    // the env block and its symbols/vals ARRAYS are heap allocations too —
    // without a full mark_env walk they are swept at the first collection
    // and every macro-expansion lookup afterwards reads recycled memory.
    {
      extern valk_lenv_t *valk_macro_env(void);
      valk_lenv_t *menv = valk_macro_env();
      if (menv) mark_env(menv, &ctx);
    }

    valk_gc_visit_remembered(mark_remembered_visitor, &ctx);

    pthread_mutex_lock(&valk_sys->thread_mutex);
    for (u64 i = 0; i < VALK_GC_MAX_THREADS; i++) {
      if (valk_sys->threads[i].active && valk_sys->threads[i].ctx != nullptr) {
        valk_thread_context_t *tc = valk_sys->threads[i].ctx;
        valk_lenv_t *root_env = atomic_load(&tc->root_env);
        if (root_env != nullptr) {
          mark_env(root_env, &ctx);
        }
      }
    }
    pthread_mutex_unlock(&valk_sys->thread_mutex);
  }

  valk_barrier_wait(&valk_sys->barrier);

  if (solo) {
    // Nobody can steal from us and nobody else can finish work on our behalf,
    // so drain to empty and skip both the fencing pop and the whole
    // steal/termination protocol.
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop_solo(my_queue)) != nullptr) {
      mark_children(obj, &ctx);
    }
    return;
  }

  while (true) {
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != nullptr) {
      mark_children(obj, &ctx);
    }

    bool found_work = false;
    u64 max_idx = atomic_load(&__gc_cycle_scan_max);

    for (u64 i = 1; i < max_idx; i++) {
      u64 victim = (my_id + i) % max_idx;
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

  // Partitioning MUST use the cycle-frozen rank and participant count. A
  // rank recomputed from live `active` flags shifts when a thread registers
  // mid-cycle, making two sweepers claim the same pages (concurrent bitmap
  // writes, double-freed slots); a live participant count leaves the tail
  // partition unswept (unbounded heap growth).
  u64 my_rank = valk_thread_ctx.gc_cycle_rank;
  u64 num_threads = atomic_load(&__gc_cycle_participants);

  for (u8 c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    valk_gc_page_list_t *list = &heap->classes[c];

    u64 num_pages = list->num_pages;
    if (num_pages == 0) continue;

    u64 pages_per_thread = (num_pages + num_threads - 1) / num_threads;
    u64 my_start = my_rank * pages_per_thread;
    u64 my_end = (my_rank + 1) * pages_per_thread;
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

  if (my_rank == 0) {
    valk_gc_sweep_large_objects(heap);
  }
}

// ============================================================================
// STW Request
// ============================================================================

bool valk_gc_heap_request_stw(valk_gc_heap_t *heap) {
  if (!heap) return false;

  if (atomic_load(&valk_sys->shutting_down)) return false;

  pthread_mutex_lock(&valk_sys->thread_mutex);

  u64 num_threads = atomic_load(&valk_sys->threads_registered);
  if (num_threads == 0) {
    pthread_mutex_unlock(&valk_sys->thread_mutex);
    return false;
  }

  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_sys->phase, &expected,
                                       VALK_GC_PHASE_PREPARING)) {
    pthread_mutex_unlock(&valk_sys->thread_mutex);
    return false;
  }

  if (valk_sys->barrier_initialized) {
    valk_barrier_reset(&valk_sys->barrier, num_threads);
  } else {
    valk_barrier_init(&valk_sys->barrier, num_threads);
    valk_sys->barrier_initialized = true;
  }

  atomic_store(&__gc_heap_current, heap);

  // Freeze the participant set for this cycle. Everything cycle-scoped
  // (barrier membership, OWST termination count, steal/scan bounds, sweep
  // partitioning) derives from these frozen values — never from live
  // registry state, which changes when threads register mid-cycle.
  u64 epoch = atomic_load(&valk_sys->stw_epoch) + 1;
  atomic_store(&valk_sys->stw_epoch, epoch);
  atomic_store(&__gc_cycle_participants, num_threads);
  atomic_store(&__gc_cycle_scan_max, valk_sys->next_fresh_idx);

  atomic_store_explicit(&valk_sys->phase,
                        VALK_GC_PHASE_STW_REQUESTED,
                        memory_order_release);

  u64 rank = 0;
  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (valk_sys->threads[i].active && valk_sys->threads[i].ctx != nullptr) {
      valk_thread_context_t *tc = valk_sys->threads[i].ctx;
      tc->gc_cycle_rank = rank++;
      atomic_store(&tc->stw_epoch, epoch);
      atomic_fetch_or_explicit(&tc->safepoint_flags, VALK_SP_STW,
                                memory_order_release);
    }
  }

  pthread_mutex_unlock(&valk_sys->thread_mutex);

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

  VALK_ASSERT(atomic_load(&valk_sys->threads_registered) > 0,
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

  {
    static _Atomic u64 __gc_lead_claimed = 0;
    u64 expected = 0;
    if (atomic_compare_exchange_strong(&__gc_lead_claimed, &expected, 1)) {
      valk_gc_rebuild_partial_lists(heap);
      valk_gc_reclaim_empty_pages(heap);
      heap->generation = valk_gc_heap_next_generation();
      atomic_store(&__gc_lead_claimed, 0);
    }
  }

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);

  valk_barrier_wait(&valk_sys->barrier);

  u64 bytes_after = valk_gc_heap_used_bytes(heap);
  u64 reclaimed = 0;
  if (bytes_before > bytes_after) {
    reclaimed = bytes_before - bytes_after;
  }

  heap->live_after_gc = bytes_after;

  atomic_fetch_add(&heap->bytes_reclaimed_total, reclaimed);
  atomic_store(&heap->gc_in_progress, false);

  u64 end_ns = uv_hrtime();
  u64 pause_ns = end_ns - start_ns;
  u64 pause_us = pause_ns / 1000;
  heap->last_gc_time_us = end_ns / 1000;

  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_ns_total, pause_ns);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);
  atomic_store(&heap->runtime_metrics.last_heap_before_gc, bytes_before);
  atomic_store(&heap->runtime_metrics.last_reclaimed, reclaimed);

  u64 current_max = atomic_load(&heap->runtime_metrics.pause_ns_max);
  while (pause_ns > current_max) { // LCOV_EXCL_BR_LINE - CAS loop
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_ns_max, &current_max, pause_ns)) { // LCOV_EXCL_BR_LINE
      break;
    }
  }

  // LCOV_EXCL_START - GC pause histogram: bucket timing is non-deterministic, untestable
  if (pause_us < 1000)
    atomic_fetch_add(&heap->runtime_metrics.pause_0_1ms, 1);
  else if (pause_us < 5000)
    atomic_fetch_add(&heap->runtime_metrics.pause_1_5ms, 1);
  else if (pause_us < 10000)
    atomic_fetch_add(&heap->runtime_metrics.pause_5_10ms, 1);
  else if (pause_us < 16000)
    atomic_fetch_add(&heap->runtime_metrics.pause_10_16ms, 1);
  else
    atomic_fetch_add(&heap->runtime_metrics.pause_16ms_plus, 1);

  if (pause_us > 50000) {
    u64 cycles = atomic_load(&heap->runtime_metrics.cycles_total);
    fprintf(stderr, "[gc] slow cycle #%llu: %llu.%03llums (reclaimed %llu bytes, %llu -> %llu)\n",
            (unsigned long long)cycles,
            (unsigned long long)(pause_us / 1000),
            (unsigned long long)(pause_us % 1000),
            (unsigned long long)reclaimed,
            (unsigned long long)bytes_before,
            (unsigned long long)bytes_after);
  }
  // LCOV_EXCL_STOP

  atomic_fetch_add(&valk_sys->parallel_cycles, 1);
  atomic_fetch_add(&valk_sys->parallel_pause_ns_total, pause_ns);

  // Do NOT clear VALK_SP_STW here (this is the coordinator clearing the
  // flag it set on itself via request_stw). A new cycle started by another
  // thread between this cycle reaching IDLE and this line also sets the
  // flag — clearing wiped that cycle's flag while its coordinator had
  // already counted us as a participant, deadlocking its barrier (caught
  // live: one thread flags=0/2 at the current epoch, 24/25 at the
  // barrier). The stale self-flag is absorbed at the next safepoint: the
  // STW branch clears it and returns as soon as it sees phase IDLE.

  VALK_DEBUG("GC cycle complete: reclaimed %zu bytes in %llu ns (%zu threads)",
             reclaimed, (unsigned long long)pause_ns, num_threads);

  return reclaimed;
}

// LCOV_EXCL_START - fork safety function requires actual fork()
void valk_gc_mark_reset_after_fork(void) {
  atomic_store(&__gc_heap_offered, 0);
  atomic_store(&__gc_heap_terminated, false);
  atomic_store(&__gc_heap_current, nullptr);
  atomic_store(&__gc_cycle_participants, 0);
  atomic_store(&__gc_cycle_scan_max, 0);
  pthread_mutex_init(&__gc_heap_term_lock, nullptr);
  pthread_cond_init(&__gc_heap_term_cond, nullptr);
}
// LCOV_EXCL_STOP
