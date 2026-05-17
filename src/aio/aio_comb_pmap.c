#include "aio_combinators_internal.h"

typedef struct {
  valk_async_handle_t *pmap_handle;
  valk_handle_t *result_handles;
  _Atomic(bool) *result_ready;
  u64 total;
  _Atomic(u64) completed;
  _Atomic(u64) finished;
  valk_handle_t fn_handle;
  _Atomic(bool) fn_released;
} valk_pmap_ctx_t;

typedef struct {
  valk_pmap_ctx_t *pmap_ctx;
  valk_handle_t fn_handle;
  valk_handle_t arg_handle;
  u64 index;
} valk_pmap_task_t;

// LCOV_EXCL_BR_START - cleanup: branch edges depend on which path triggers free (worker completion vs error vs cancel)
static void valk_pmap_ctx_free(valk_pmap_ctx_t *ctx) {
  if (!ctx) return;
  if (!atomic_exchange(&ctx->fn_released, true))
    valk_handle_release(&valk_sys->handle_table, ctx->fn_handle);
  if (ctx->result_handles) {
    for (u64 i = 0; i < ctx->total; i++) {
      if (atomic_load_explicit(&ctx->result_ready[i], memory_order_acquire))
        valk_handle_release(&valk_sys->handle_table, ctx->result_handles[i]);
    }
    free(ctx->result_handles);
    free(ctx->result_ready);
  }
  free(ctx);
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_START - cleanup callback: runs non-deterministically on handle destruction
static void valk_pmap_ctx_cleanup(void *ctx) {
  valk_pmap_ctx_t *pmap_ctx = (valk_pmap_ctx_t *)ctx;
  if (!pmap_ctx) return;
  u64 done = atomic_load_explicit(&pmap_ctx->finished, memory_order_acquire);
  if (done >= pmap_ctx->total) {
    valk_pmap_ctx_free(pmap_ctx);
  }
}
// LCOV_EXCL_STOP

static void __pmap_worker(void *arg) {
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE - GC coordination

  valk_pmap_task_t *task = (valk_pmap_task_t *)arg;
  valk_pmap_ctx_t *ctx = task->pmap_ctx;

  // LCOV_EXCL_START - race: requires pmap handle to be terminal before worker starts (another worker failed)
  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->pmap_handle))) {
    valk_handle_release(&valk_sys->handle_table, task->arg_handle);
    free(task);
    u64 fin = atomic_fetch_add(&ctx->finished, 1) + 1;
    if (fin >= ctx->total) valk_pmap_ctx_free(ctx);
    return;
  }
  // LCOV_EXCL_STOP

  // fn and arg_val stay GC-reachable via the handle table (walked by
  // valk_handle_table_visit) until released. `args` is walked via
  // eval_calling_args during the eval_call. After eval_call, `result`
  // is parked in eval_value across the handle_release + evacuate path.
  valk_lval_t *fn = valk_handle_resolve(&valk_sys->handle_table, task->fn_handle);
  valk_lval_t *arg_val = valk_handle_resolve(&valk_sys->handle_table, task->arg_handle);

  valk_lval_t *args = valk_lval_cons(arg_val, valk_lval_nil());

  valk_mem_arena_t *scratch = valk_thread_ctx.scratch;
  valk_lval_t *result;
  if (scratch) { // LCOV_EXCL_BR_LINE - scratch always present in test environment
    VALK_WITH_ALLOC((void *)scratch) {
      result = valk_lval_eval_call(fn->fun.env, fn, args);
    }
  } else {
    result = valk_lval_eval_call(fn->fun.env, fn, args); // LCOV_EXCL_LINE
  }
  valk_thread_ctx.eval_value = result;

  valk_handle_release(&valk_sys->handle_table, task->arg_handle);

  // LCOV_EXCL_BR_START - error path: requires worker fn to return error, transition race
  if (LVAL_TYPE(result) == LVAL_ERR) {
    valk_lval_t *heap_err = valk_evacuate_to_heap(result);
    if (scratch) valk_mem_arena_reset(scratch);

    valk_async_handle_fail(ctx->pmap_handle, heap_err);
    free(task);
    u64 fin = atomic_fetch_add(&ctx->finished, 1) + 1;
    if (fin >= ctx->total) valk_pmap_ctx_free(ctx);
    return;
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t *heap_result = valk_evacuate_to_heap(result);
  valk_thread_ctx.eval_value = heap_result;
  if (scratch) valk_mem_arena_reset(scratch); // LCOV_EXCL_BR_LINE - scratch always present
  ctx->result_handles[task->index] =
      valk_handle_create(&valk_sys->handle_table, heap_result);
  valk_thread_ctx.eval_value = NULL;
  atomic_store_explicit(&ctx->result_ready[task->index], true, memory_order_release);
  u64 new_completed = atomic_fetch_add(&ctx->completed, 1) + 1;

  if (new_completed == ctx->total) { // LCOV_EXCL_BR_LINE - completion: only one worker hits total
    valk_lval_t *result_list;
    VALK_WITH_ALLOC((void *)valk_thread_ctx.heap) {
      result_list = valk_lval_nil();
      for (u64 i = ctx->total; i > 0; i--) {
        valk_lval_t *val = valk_handle_resolve(&valk_sys->handle_table,
                                                ctx->result_handles[i - 1]);
        result_list = valk_lval_cons(val, result_list);
        valk_handle_release(&valk_sys->handle_table, ctx->result_handles[i - 1]);
        atomic_store_explicit(&ctx->result_ready[i - 1], false, memory_order_release);
      }
    }
    valk_lval_t *heap_list = valk_evacuate_to_heap(result_list);
    valk_async_handle_complete(ctx->pmap_handle, heap_list);
  }

  free(task);
  u64 fin = atomic_fetch_add(&ctx->finished, 1) + 1;
  if (fin >= ctx->total) valk_pmap_ctx_free(ctx); // LCOV_EXCL_BR_LINE - last-worker cleanup
} // LCOV_EXCL_BR_LINE

static valk_lval_t *valk_builtin_aio_pmap(valk_lenv_t *e, valk_lval_t *a) {
  // LCOV_EXCL_BR_START - arg validation
  LVAL_ASSERT_COUNT_EQ(a, a, 3);

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *fn_arg = valk_lval_list_nth(a, 1);
  valk_lval_t *list_arg = valk_lval_list_nth(a, 2);

  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
  LVAL_ASSERT_TYPE(a, fn_arg, LVAL_FUN);
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  u64 count = 0;
  valk_lval_t *iter = list_arg;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) { // LCOV_EXCL_BR_LINE - list type already validated by caller
      return valk_lval_err("aio/pmap: expected a list as third argument"); // LCOV_EXCL_LINE
    }
    count++;
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    valk_async_handle_t *handle = valk_async_handle_new(sys, e);
    valk_async_handle_complete(handle, valk_lval_nil());
    return valk_lval_handle(handle);
  }

  valk_async_handle_t *pmap_handle = valk_async_handle_new(sys, e);
  if (!pmap_handle) { // LCOV_EXCL_BR_LINE
    return valk_lval_err("aio/pmap: failed to allocate handle"); // LCOV_EXCL_LINE
  }
  atomic_store_explicit(&pmap_handle->status, VALK_ASYNC_RUNNING, memory_order_release);

  valk_pmap_ctx_t *ctx = malloc(sizeof(valk_pmap_ctx_t));
  if (!ctx) { // LCOV_EXCL_BR_LINE
    return valk_lval_err("aio/pmap: failed to allocate context"); // LCOV_EXCL_LINE
  }
  ctx->pmap_handle = pmap_handle;
  ctx->result_handles = calloc(count, sizeof(valk_handle_t));
  ctx->result_ready = calloc(count, sizeof(_Atomic(bool)));
  if (!ctx->result_handles || !ctx->result_ready) { // LCOV_EXCL_BR_LINE
    free(ctx->result_handles); // LCOV_EXCL_LINE
    free(ctx->result_ready); // LCOV_EXCL_LINE
    free(ctx); // LCOV_EXCL_LINE
    return valk_lval_err("aio/pmap: failed to allocate result arrays"); // LCOV_EXCL_LINE
  }
  ctx->total = count;
  atomic_store(&ctx->completed, 0);
  atomic_store(&ctx->finished, 0);
  atomic_store(&ctx->fn_released, false);

  valk_lval_t *heap_fn = valk_evacuate_to_heap(fn_arg);
  ctx->fn_handle = valk_handle_create(&valk_sys->handle_table, heap_fn);

  valk_async_handle_on_cleanup(pmap_handle, valk_pmap_ctx_cleanup, ctx);

  valk_handle_t fn_handle = ctx->fn_handle;

  u32 num_loops = sys->num_loops;
  iter = list_arg;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *item = valk_lval_head(iter);

    valk_lval_t *heap_item = valk_evacuate_to_heap(item);
    valk_handle_t arg_handle = valk_handle_create(&valk_sys->handle_table, heap_item);

    valk_pmap_task_t *task = malloc(sizeof(valk_pmap_task_t));
    if (!task) { // LCOV_EXCL_BR_LINE
      valk_handle_release(&valk_sys->handle_table, arg_handle); // LCOV_EXCL_LINE
      valk_async_handle_fail(pmap_handle, // LCOV_EXCL_LINE
          valk_lval_err("aio/pmap: failed to allocate task")); // LCOV_EXCL_LINE
      return valk_lval_handle(pmap_handle); // LCOV_EXCL_LINE
    }
    task->pmap_ctx = ctx;
    task->fn_handle = fn_handle;
    task->arg_handle = arg_handle;
    task->index = i;

    valk_aio_loop_t *loop = &sys->loops[i % num_loops];
    if (!valk_aio_loop_enqueue_task(loop, __pmap_worker, task)) { // LCOV_EXCL_BR_LINE
      valk_handle_release(&valk_sys->handle_table, arg_handle); // LCOV_EXCL_LINE
      free(task); // LCOV_EXCL_LINE
      valk_async_handle_fail(pmap_handle, // LCOV_EXCL_LINE
          valk_lval_err("aio/pmap: task queue full")); // LCOV_EXCL_LINE
      return valk_lval_handle(pmap_handle); // LCOV_EXCL_LINE
    }

    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(pmap_handle);
}

void valk_register_comb_pmap(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/pmap", valk_builtin_aio_pmap);
}
