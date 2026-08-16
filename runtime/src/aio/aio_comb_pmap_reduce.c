#include "aio_combinators_internal.h"

typedef struct {
  valk_async_handle_t *handle;
  valk_aio_system_t *sys;
  valk_handle_t *item_handles;
  u64 total;
  _Atomic(u64) next;
  _Atomic(u64) folded;
  _Atomic(u64) refs;
  _Atomic(u32) rr;
  valk_handle_t fn_handle;
  valk_handle_t reduce_handle;
  valk_handle_t acc_handle;
} valk_pmr_ctx_t;

typedef struct {
  valk_pmr_ctx_t *ctx;
  u64 index;
} valk_pmr_compute_task_t;

typedef struct {
  valk_pmr_ctx_t *ctx;
  valk_handle_t result_handle;
} valk_pmr_fold_task_t;

static void __pmr_compute(void *arg);

// LCOV_EXCL_BR_START - free: branch edges depend on which path drops the last ref
static void __pmr_free(valk_pmr_ctx_t *ctx) {
  valk_handle_release(&valk_sys->handle_table, ctx->fn_handle);
  valk_handle_release(&valk_sys->handle_table, ctx->reduce_handle);
  valk_handle_release(&valk_sys->handle_table, ctx->acc_handle);
  u64 start = atomic_load_explicit(&ctx->next, memory_order_acquire);
  if (start > ctx->total) start = ctx->total;
  for (u64 i = start; i < ctx->total; i++)
    valk_handle_release(&valk_sys->handle_table, ctx->item_handles[i]);
  free(ctx->item_handles);
  free(ctx);
}

static void __pmr_release(valk_pmr_ctx_t *ctx) {
  if (atomic_fetch_sub(&ctx->refs, 1) == 1) __pmr_free(ctx);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_START - cleanup callback: runs non-deterministically on handle destruction
static void __pmr_on_cleanup(void *arg) {
  valk_pmr_ctx_t *ctx = (valk_pmr_ctx_t *)arg;
  if (!ctx) return;
  __pmr_release(ctx);
}
// LCOV_EXCL_STOP

static void __pmr_dispatch_next(valk_pmr_ctx_t *ctx) {
  u64 idx = atomic_fetch_add(&ctx->next, 1);
  if (idx >= ctx->total) return;

  atomic_fetch_add(&ctx->refs, 1);
  valk_pmr_compute_task_t *task = malloc(sizeof(valk_pmr_compute_task_t));
  if (!task) { // LCOV_EXCL_BR_LINE
    valk_handle_release(&valk_sys->handle_table, ctx->item_handles[idx]); // LCOV_EXCL_LINE
    valk_async_handle_fail(ctx->handle, // LCOV_EXCL_LINE
        valk_lval_err("aio/pmap-reduce: failed to allocate task")); // LCOV_EXCL_LINE
    __pmr_release(ctx); // LCOV_EXCL_LINE
    return; // LCOV_EXCL_LINE
  }
  task->ctx = ctx;
  task->index = idx;

  u32 num_loops = ctx->sys->num_loops;
  u32 loop_idx = num_loops > 1
      ? 1 + (atomic_fetch_add(&ctx->rr, 1) % (num_loops - 1))
      : 0;
  valk_aio_loop_t *loop = &ctx->sys->loops[loop_idx];
  if (!valk_aio_loop_enqueue_task(loop, __pmr_compute, task)) { // LCOV_EXCL_BR_LINE
    valk_handle_release(&valk_sys->handle_table, ctx->item_handles[idx]); // LCOV_EXCL_LINE
    free(task); // LCOV_EXCL_LINE
    valk_async_handle_fail(ctx->handle, // LCOV_EXCL_LINE
        valk_lval_err("aio/pmap-reduce: task queue full")); // LCOV_EXCL_LINE
    __pmr_release(ctx); // LCOV_EXCL_LINE
  }
}

static void __pmr_fold(void *arg) {
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE - GC coordination

  valk_pmr_fold_task_t *task = (valk_pmr_fold_task_t *)arg;
  valk_pmr_ctx_t *ctx = task->ctx;

  // LCOV_EXCL_START - race: handle terminal before fold runs (sibling failed)
  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->handle))) {
    valk_handle_release(&valk_sys->handle_table, task->result_handle);
    free(task);
    __pmr_release(ctx);
    return;
  }
  // LCOV_EXCL_STOP

  valk_lval_t *reduce_fn = valk_handle_resolve(&valk_sys->handle_table, ctx->reduce_handle);
  valk_lval_t *acc = valk_handle_resolve(&valk_sys->handle_table, ctx->acc_handle);
  valk_lval_t *result = valk_handle_resolve(&valk_sys->handle_table, task->result_handle);
  VALK_GC_ROOT(reduce_fn);
  VALK_GC_ROOT(acc);
  VALK_GC_ROOT(result);

  valk_lval_t *args = valk_lval_cons(acc, valk_lval_cons(result, valk_lval_nil()));
  VALK_GC_ROOT(args);

  valk_mem_arena_t *scratch = valk_thread_ctx.scratch;
  valk_lval_t *new_acc;
  if (scratch) { // LCOV_EXCL_BR_LINE - scratch always present in test environment
    VALK_WITH_ALLOC((void *)scratch) {
      new_acc = valk_lval_eval_call(reduce_fn->fun.env, reduce_fn, args);
    }
  } else {
    new_acc = valk_lval_eval_call(reduce_fn->fun.env, reduce_fn, args); // LCOV_EXCL_LINE
  }
  VALK_GC_ROOT(new_acc);

  valk_handle_release(&valk_sys->handle_table, task->result_handle);

  if (LVAL_TYPE(new_acc) == LVAL_ERR) {
    valk_lval_t *heap_err = valk_evacuate_to_heap(new_acc);
    if (scratch) valk_mem_arena_reset(scratch); // LCOV_EXCL_BR_LINE
    valk_async_handle_fail(ctx->handle, heap_err);
    free(task);
    __pmr_release(ctx);
    return;
  }

  valk_lval_t *heap_acc = valk_evacuate_to_heap(new_acc);
  if (scratch) valk_mem_arena_reset(scratch); // LCOV_EXCL_BR_LINE - scratch always present
  valk_handle_t new_acc_handle = valk_handle_create(&valk_sys->handle_table, heap_acc);
  valk_handle_release(&valk_sys->handle_table, ctx->acc_handle);
  ctx->acc_handle = new_acc_handle;

  u64 folded = atomic_fetch_add(&ctx->folded, 1) + 1;
  if (folded == ctx->total) {
    valk_async_handle_complete(ctx->handle, heap_acc);
  } else {
    __pmr_dispatch_next(ctx);
  }

  free(task);
  __pmr_release(ctx);
}

static void __pmr_compute(void *arg) {
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE - GC coordination

  valk_pmr_compute_task_t *task = (valk_pmr_compute_task_t *)arg;
  valk_pmr_ctx_t *ctx = task->ctx;

  // LCOV_EXCL_START - race: handle terminal before compute runs (sibling failed)
  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->handle))) {
    valk_handle_release(&valk_sys->handle_table, ctx->item_handles[task->index]);
    free(task);
    __pmr_release(ctx);
    return;
  }
  // LCOV_EXCL_STOP

  valk_lval_t *fn = valk_handle_resolve(&valk_sys->handle_table, ctx->fn_handle);
  valk_lval_t *arg_val = valk_handle_resolve(&valk_sys->handle_table,
                                             ctx->item_handles[task->index]);
  VALK_GC_ROOT(fn);
  VALK_GC_ROOT(arg_val);

  valk_lval_t *args = valk_lval_cons(arg_val, valk_lval_nil());
  VALK_GC_ROOT(args);

  valk_mem_arena_t *scratch = valk_thread_ctx.scratch;
  valk_lval_t *result;
  if (scratch) { // LCOV_EXCL_BR_LINE - scratch always present in test environment
    VALK_WITH_ALLOC((void *)scratch) {
      result = valk_lval_eval_call(fn->fun.env, fn, args);
    }
  } else {
    result = valk_lval_eval_call(fn->fun.env, fn, args); // LCOV_EXCL_LINE
  }
  VALK_GC_ROOT(result);

  valk_handle_release(&valk_sys->handle_table, ctx->item_handles[task->index]);

  if (LVAL_TYPE(result) == LVAL_ERR) {
    valk_lval_t *heap_err = valk_evacuate_to_heap(result);
    if (scratch) valk_mem_arena_reset(scratch); // LCOV_EXCL_BR_LINE
    valk_async_handle_fail(ctx->handle, heap_err);
    free(task);
    __pmr_release(ctx);
    return;
  }

  valk_lval_t *heap_result = valk_evacuate_to_heap(result);
  if (scratch) valk_mem_arena_reset(scratch); // LCOV_EXCL_BR_LINE - scratch always present

  valk_pmr_fold_task_t *fold_task = malloc(sizeof(valk_pmr_fold_task_t));
  if (!fold_task) { // LCOV_EXCL_BR_LINE
    valk_async_handle_fail(ctx->handle, // LCOV_EXCL_LINE
        valk_lval_err("aio/pmap-reduce: failed to allocate fold task")); // LCOV_EXCL_LINE
    free(task); // LCOV_EXCL_LINE
    __pmr_release(ctx); // LCOV_EXCL_LINE
    return; // LCOV_EXCL_LINE
  }
  fold_task->ctx = ctx;
  fold_task->result_handle = valk_handle_create(&valk_sys->handle_table, heap_result);

  valk_aio_loop_t *fold_loop = &ctx->sys->loops[0];
  if (!valk_aio_loop_enqueue_task(fold_loop, __pmr_fold, fold_task)) { // LCOV_EXCL_BR_LINE
    valk_handle_release(&valk_sys->handle_table, fold_task->result_handle); // LCOV_EXCL_LINE
    free(fold_task); // LCOV_EXCL_LINE
    valk_async_handle_fail(ctx->handle, // LCOV_EXCL_LINE
        valk_lval_err("aio/pmap-reduce: fold queue full")); // LCOV_EXCL_LINE
    free(task); // LCOV_EXCL_LINE
    __pmr_release(ctx); // LCOV_EXCL_LINE
    return; // LCOV_EXCL_LINE
  }

  free(task);
} // LCOV_EXCL_BR_LINE

static valk_lval_t *valk_builtin_aio_pmap_reduce(valk_lenv_t *e, valk_lval_t *a) {
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 5);

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *fn_arg = valk_lval_list_nth(a, 1);
  valk_lval_t *reduce_arg = valk_lval_list_nth(a, 2);
  valk_lval_t *init_arg = valk_lval_list_nth(a, 3);
  valk_lval_t *list_arg = valk_lval_list_nth(a, 4);

  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
  LVAL_ASSERT_TYPE(a, fn_arg, LVAL_FUN);
  LVAL_ASSERT_TYPE(a, reduce_arg, LVAL_FUN);
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  u64 count = 0;
  valk_lval_t *iter = list_arg;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) { // LCOV_EXCL_BR_LINE
      return valk_lval_err("aio/pmap-reduce: expected a list as fifth argument"); // LCOV_EXCL_LINE
    }
    count++;
    iter = valk_lval_tail(iter);
  }

  valk_async_handle_t *handle = valk_async_handle_new(sys, e);
  if (!handle) { // LCOV_EXCL_BR_LINE
    return valk_lval_err("aio/pmap-reduce: failed to allocate handle"); // LCOV_EXCL_LINE
  }

  if (count == 0) {
    valk_async_handle_complete(handle, init_arg);
    return valk_lval_handle(handle);
  }

  atomic_store_explicit(&handle->status, VALK_ASYNC_RUNNING, memory_order_release);

  valk_pmr_ctx_t *ctx = malloc(sizeof(valk_pmr_ctx_t));
  if (!ctx) { // LCOV_EXCL_BR_LINE
    return valk_lval_err("aio/pmap-reduce: failed to allocate context"); // LCOV_EXCL_LINE
  }
  ctx->handle = handle;
  ctx->sys = sys;
  ctx->total = count;
  ctx->item_handles = calloc(count, sizeof(valk_handle_t));
  if (!ctx->item_handles) { // LCOV_EXCL_BR_LINE
    free(ctx); // LCOV_EXCL_LINE
    return valk_lval_err("aio/pmap-reduce: failed to allocate item array"); // LCOV_EXCL_LINE
  }
  atomic_store(&ctx->next, 0);
  atomic_store(&ctx->folded, 0);
  atomic_store(&ctx->refs, 1);
  atomic_store(&ctx->rr, 0);

  valk_lval_t *heap_fn = valk_evacuate_to_heap(fn_arg);
  ctx->fn_handle = valk_handle_create(&valk_sys->handle_table, heap_fn);
  valk_lval_t *heap_reduce = valk_evacuate_to_heap(reduce_arg);
  ctx->reduce_handle = valk_handle_create(&valk_sys->handle_table, heap_reduce);
  valk_lval_t *heap_init = valk_evacuate_to_heap(init_arg);
  ctx->acc_handle = valk_handle_create(&valk_sys->handle_table, heap_init);

  iter = list_arg;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *heap_item = valk_evacuate_to_heap(valk_lval_head(iter));
    ctx->item_handles[i] = valk_handle_create(&valk_sys->handle_table, heap_item);
    iter = valk_lval_tail(iter);
  }

  valk_async_handle_on_cleanup(handle, __pmr_on_cleanup, ctx);

  u32 num_loops = sys->num_loops;
  u64 window = num_loops > 1 ? (u64)(num_loops - 1) * 2 : 2;
  if (window > count) window = count;
  for (u64 i = 0; i < window; i++) {
    __pmr_dispatch_next(ctx);
  }

  return valk_lval_handle(handle);
}

void valk_register_comb_pmap_reduce(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/pmap-reduce", valk_builtin_aio_pmap_reduce);
}
