#include "gc.h"
#include "parser.h"
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
    return valk_gc_page_try_mark(loc.page, loc.slot);
  } else {
    return valk_gc_mark_large_object(ctx->heap, ptr);
  }
}
static void mark_lval(valk_lval_t *lval, valk_gc_mark_ctx_t *ctx);

// Conservative mark: takes an arbitrary uintptr_t found on the C stack
// (or in any uninspected memory) and decides whether it points at a
// valid heap-allocated lval slot. If yes, marks it AND enqueues it so
// the worker loop processes its children — same recursive coverage as
// mark_lval, but starting from a raw address with no type info.
//
// Validation pipeline (each layer rejects most non-pointers cheaply):
//   1. NULL / non-canonical address — reject
//   2. Outside heap virtual reservation — reject (one bounds check)
//   3. Not slot-aligned — reject (interior pointers ignored)
//   4. Slot's alloc-bitmap bit is 0 (slot was freed) — reject
//   5. Already marked — return false (no enqueue, already covered)
//   6. Otherwise: atomic-set mark, push to mark queue
//
// Large objects are handled by the same path that mark_lval uses: if
// ptr_to_location says "not in main heap", try the large-object list.
// Large-object lookup matches `data == ptr` exactly (no interior ptrs);
// fine for this use because AOT-emitted lval pointers always point at
// the lval header, not into its body.
//
// Marked LCOV_EXCL because deterministic test coverage of conservative
// scanning would require careful stack-layout choreography; the
// integration test is "LSP under typing load doesn't SIGSEGV in
// valk_lenv_get / valk_evacuate_value".
static bool mark_conservative(void *ptr, valk_gc_mark_ctx_t *ctx) {
  if (ptr == nullptr) return false;
  uintptr_t p = (uintptr_t)ptr;
  // Reject obvious non-pointers (kernel space, low memory). On x86_64 a
  // canonical user pointer is in [0x10000, 0x7fffffffffff]. Tighter
  // checks happen inside ptr_to_location.
  if (p < 0x10000 || p >= 0x800000000000ULL) return false;

  valk_gc_ptr_location_t loc;
  if (valk_gc_ptr_to_location(ctx->heap, ptr, &loc)) {
    // ptr_to_location accepts any address inside the slot region. We
    // require exact slot-base alignment so we don't mark on interior
    // pointers (e.g., ptr+8 from some random integer that happens to
    // land mid-slot). For valk_lval_t* the AOT/interpreter always
    // hold pointers at the slot base.
    void *slot_base = valk_gc_page_slot_ptr(loc.page, loc.slot);
    if (slot_base != ptr) return false;
    // Check alloc bitmap so we don't mark a swept slot.
    if (!valk_gc_page_is_allocated(loc.page, loc.slot)) return false;
    if (!valk_gc_page_try_mark(loc.page, loc.slot)) return false;
    // Newly marked — enqueue so worker drains children. Conservative
    // entry treats every marked slot as a possible lval; the worker
    // will dispatch on its actual LVAL_TYPE in mark_children.
    valk_gc_mark_queue_push(ctx->queue, (valk_lval_t *)ptr);
    return true;
  }
  return valk_gc_mark_large_object(ctx->heap, ptr);
}

// Walk the live portion of a thread's native C stack and conservatively
// mark every aligned uintptr_t that points at a heap-allocated lval
// slot. Called once per registered thread per mark phase, while every
// thread is parked at the STW barrier (so stack snapshots are stable).
//
// The stack range is [native_stack_top, native_stack_base) on
// x86_64/aarch64 (stack grows down). top is captured at safepoint
// entry by valk_gc_safe_point_slow / valk_gc_heap_collect; base is
// captured once on thread register.
//
// Granularity: 8-byte aligned. Lvals are at minimum 16-byte aligned
// (size class 0), but we step by 8 to catch lvals that happen to land
// at +8 offsets (uncommon but possible if the stack frame layout puts
// them there). Cost is one mark_conservative call per pointer-shaped
// 8-byte word in the live stack region.
//
// What this catches that precise root-tracking does not:
//   - LLVM SSA values held in register-spill slots during AOT calls
//   - Formal parameters in fast-variant compiled functions
//   - C-local valk_lval_t* in any builtin or runtime helper
//   - Anything held across an apply_func_iter's nested call chain
// In short: replaces the entire VALK_GC_ROOT machinery + AOT IR-level
// root insertion with one runtime stack walk per GC cycle.
static void scan_thread_native_stack(valk_thread_context_t *tc,
                                     valk_gc_mark_ctx_t *ctx) {
  if (!tc) return;
  // Test-only opt-out for tests that exercise precise mark/sweep
  // semantics. Production never sets this.
  if (tc->gc_disable_stack_scan) return;
  void *top  = atomic_load_explicit(&tc->native_stack_top,
                                    memory_order_acquire);
  void *base = tc->native_stack_base;
  if (!top || !base) return;
  // Sanity: top must be below base on a downward-growing stack.
  if ((uintptr_t)top >= (uintptr_t)base) return;

  // Align the start address up to 8-byte boundary in case the captured
  // frame address isn't (it usually is, since pthread frames are
  // 16-byte aligned and __builtin_frame_address returns an 8-aligned
  // address by ABI).
  uintptr_t start = ((uintptr_t)top + 7) & ~(uintptr_t)7;
  uintptr_t end   = (uintptr_t)base & ~(uintptr_t)7;

  for (uintptr_t addr = start; addr < end; addr += sizeof(void *)) {
    void *candidate = *(void **)addr;
    mark_conservative(candidate, ctx);
  }
}

// Public wrapper exposed via gc.h for use by LVAL_REF.mark callbacks.
// LVAL_REF wrapping shared resources (CHM, etc.) implements a mark hook
// that needs to recursively mark valk values held by the resource;
// this is the safe entry point.
void valk_gc_mark_visit(valk_lval_t *lval, void *ctx) {
  mark_lval(lval, (valk_gc_mark_ctx_t *)ctx);
}

static void mark_lval(valk_lval_t *lval, valk_gc_mark_ctx_t *ctx) {
  if (lval == nullptr) return;
  // Immortal lvals (image buffers, singletons, num cache) live outside the
  // GC heap and reference only other immortals, so there's nothing to mark.
  if (lval->flags & LVAL_FLAG_IMMORTAL) return;

  valk_gc_ptr_location_t loc;
  bool in_heap = valk_gc_ptr_to_location(ctx->heap, lval, &loc);

  if (in_heap) {
    if (!valk_gc_page_try_mark(loc.page, loc.slot)) return;
    valk_gc_mark_queue_push(ctx->queue, lval);
  } else if (!valk_gc_mark_large_object(ctx->heap, lval)) {
    mark_children(lval, ctx);
  }
}

static void mark_env(valk_lenv_t *env, valk_gc_mark_ctx_t *ctx) {
  while (env != nullptr) {
    if (!mark_ptr_only(env, ctx)) {
      return;
    }
    mark_ptr_only(env->symbols.items, ctx);
    mark_ptr_only(env->vals.items, ctx);
    for (u64 i = 0; i < env->symbols.count; i++) {
      // env->symbols.items[i] is char* (the strdup'd sym name buffer);
      // mark_ptr_only suffices — no children to recurse.
      mark_ptr_only(env->symbols.items[i], ctx);
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
            if (valk_gc_page_try_mark(loc.page, loc.slot))
              valk_gc_mark_queue_push(ctx->queue, obj);
            return;
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

  // For every nested eval level, walk:
  //   - the level's continuation-frame stack (every payload lval),
  //   - the saved outer eval_expr/value/env snapshotted on entry to
  //     that level so the outer eval's state stays live across nested
  //     eval calls.
  for (u32 i = 0; i < tc->eval_stack_depth; i++) {
    valk_eval_stack_t *stack = (valk_eval_stack_t *)tc->eval_stacks[i];
    if (stack) mark_one_eval_stack(stack, ctx);
    if (tc->saved_eval_exprs[i]) mark_lval(tc->saved_eval_exprs[i], ctx);
    if (tc->saved_eval_values[i]) mark_lval(tc->saved_eval_values[i], ctx);
    if (tc->saved_eval_envs[i]) mark_env(tc->saved_eval_envs[i], ctx);
  }
}

static void mark_root_visitor2(valk_lval_t *val, void *user) {
  valk_gc_mark_ctx_t *ctx = user;
  mark_lval(val, ctx);
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

// LCOV_EXCL_START - OWST termination requires multi-threaded GC timing impossible to reliably test
static bool valk_gc_heap_offer_termination(void) {
  u64 num_threads = atomic_load(&valk_sys->threads_registered);
  u64 max_idx = valk_sys->next_fresh_idx;

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

  valk_gc_mark_queue_reset(my_queue);

  valk_gc_mark_ctx_t ctx = {
    .heap = heap,
    .queue = my_queue
  };

  // Eval-state precise roots: walked from valk_thread_ctx.eval_expr/
  // eval_value/eval_env + every nested level's saved snapshots and
  // continuation-frame payloads.
  mark_eval_stack_roots(&ctx);

  // Conservative scan of THIS thread's native C stack. Discovers
  // everything else: AOT-held formals/SSA spills, register-spilled C
  // locals, hand-written-C lvals held without manual rooting,
  // anything sitting in a stack frame at safepoint entry. Each thread
  // scans its own stack in parallel; cache-friendly, no cross-thread
  // reads. The captured native_stack_top is set by safe_point_slow
  // (or by valk_gc_heap_collect for the initiator) right before the
  // STW barrier, so the snapshot is stable while mark runs.
  scan_thread_native_stack(&valk_thread_ctx, &ctx);

  if (my_id == 0) {
    valk_gc_visit_global_roots(mark_root_visitor2, &ctx);

    for (u64 i = 0; i < VALK_GC_MAX_THREADS; i++) {
      if (valk_sys->threads[i].active && valk_sys->threads[i].ctx != nullptr) {
        valk_thread_context_t *tc = valk_sys->threads[i].ctx;
        if (tc->root_env != nullptr) {
          mark_env(tc->root_env, &ctx);
        }
      }
    }
  }

  valk_barrier_wait(&valk_sys->barrier);

  while (true) {
    valk_lval_t *obj;
    while ((obj = valk_gc_mark_queue_pop(my_queue)) != nullptr) {
      mark_children(obj, &ctx);
    }

    bool found_work = false;
    u64 max_idx = valk_sys->next_fresh_idx;

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

  u64 raw_id = valk_thread_ctx.gc_thread_id;
  u64 num_threads = atomic_load(&valk_sys->threads_registered);

  u64 my_rank = 0;
  for (u64 i = 0; i < raw_id; i++) {
    if (valk_sys->threads[i].active) my_rank++;
  }

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

  if (raw_id == 0) {
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

  atomic_store_explicit(&valk_sys->phase,
                        VALK_GC_PHASE_STW_REQUESTED,
                        memory_order_release);

  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (valk_sys->threads[i].active && valk_sys->threads[i].ctx != nullptr) {
      valk_thread_context_t *tc = valk_sys->threads[i].ctx;
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

  // The initiator thread does NOT enter valk_gc_safe_point_slow, so it
  // must capture its own deepest live frame for the conservative scanner
  // here, before parking at the barrier below. Mirrors the snapshot
  // taken by safe_point_slow for every other thread.
  atomic_store_explicit(&valk_thread_ctx.native_stack_top,
                        __builtin_frame_address(0),
                        memory_order_release);

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

  atomic_fetch_and(&valk_thread_ctx.safepoint_flags, ~(u32)VALK_SP_STW);

  VALK_DEBUG("GC cycle complete: reclaimed %zu bytes in %llu ns (%zu threads)",
             reclaimed, (unsigned long long)pause_ns, num_threads);

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
