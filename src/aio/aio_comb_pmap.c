#include "aio_combinators_internal.h"

typedef struct {
  valk_async_handle_t *pmap_handle;
  valk_handle_t *result_handles;
  _Atomic(bool) *result_ready;
  u64 total;
  _Atomic(u64) completed;
  valk_handle_t fn_handle;
  bool fn_released;
} valk_pmap_ctx_t;

typedef struct {
  valk_pmap_ctx_t *pmap_ctx;
  valk_handle_t fn_handle;
  valk_handle_t arg_handle;
  u64 index;
} valk_pmap_task_t;

static void valk_pmap_ctx_cleanup(void *ctx) {
  valk_pmap_ctx_t *pmap_ctx = (valk_pmap_ctx_t *)ctx;
  if (!pmap_ctx) return; // LCOV_EXCL_LINE
  if (!pmap_ctx->fn_released) {
    valk_handle_release(&valk_sys->handle_table, pmap_ctx->fn_handle);
    pmap_ctx->fn_released = true;
  }
  if (pmap_ctx->result_handles) {
    for (u64 i = 0; i < pmap_ctx->total; i++) {
      if (atomic_load_explicit(&pmap_ctx->result_ready[i], memory_order_acquire))
        valk_handle_release(&valk_sys->handle_table, pmap_ctx->result_handles[i]);
    }
    free(pmap_ctx->result_handles);
    free(pmap_ctx->result_ready);
  }
  free(pmap_ctx);
}

static void __pmap_worker(void *arg) {
  VALK_GC_SAFE_POINT();

  valk_pmap_task_t *task = (valk_pmap_task_t *)arg;
  valk_pmap_ctx_t *ctx = task->pmap_ctx;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->pmap_handle))) {
    valk_handle_release(&valk_sys->handle_table, task->arg_handle);
    free(task);
    return;
  }

  valk_lval_t *fn = valk_handle_resolve(&valk_sys->handle_table, task->fn_handle);
  valk_lval_t *arg_val = valk_handle_resolve(&valk_sys->handle_table, task->arg_handle);
  VALK_GC_ROOT(fn);
  VALK_GC_ROOT(arg_val);

  valk_lval_t *args = valk_lval_cons(arg_val, valk_lval_nil());
  VALK_GC_ROOT(args);

  valk_mem_arena_t *scratch = valk_thread_ctx.scratch;
  valk_lval_t *result;
  if (scratch) {
    VALK_WITH_ALLOC((void *)scratch) {
      result = valk_lval_eval_call(fn->fun.env, fn, args);
    }
  } else {
    result = valk_lval_eval_call(fn->fun.env, fn, args); // LCOV_EXCL_LINE
  }
  VALK_GC_ROOT(result);

  valk_handle_release(&valk_sys->handle_table, task->arg_handle);

  if (LVAL_TYPE(result) == LVAL_ERR) {
    valk_lval_t *heap_err = valk_evacuate_to_heap(result);
    if (scratch) valk_mem_arena_reset(scratch);

    if (!valk_async_handle_try_transition(ctx->pmap_handle,
        VALK_ASYNC_RUNNING, VALK_ASYNC_FAILED)) {
      free(task);
      return;
    }
    atomic_store_explicit(&ctx->pmap_handle->error, heap_err, memory_order_release);
    valk_async_handle_finish(ctx->pmap_handle);
    free(task);
    return;
  }

  valk_lval_t *heap_result = valk_evacuate_to_heap(result);
  if (scratch) valk_mem_arena_reset(scratch);
  ctx->result_handles[task->index] =
      valk_handle_create(&valk_sys->handle_table, heap_result);
  atomic_store_explicit(&ctx->result_ready[task->index], true, memory_order_release);
  u64 new_completed = atomic_fetch_add(&ctx->completed, 1) + 1;

  if (new_completed == ctx->total) {
    if (!valk_async_handle_try_transition(ctx->pmap_handle,
        VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
      free(task); // LCOV_EXCL_LINE
      return; // LCOV_EXCL_LINE
    }

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
    atomic_store_explicit(&ctx->pmap_handle->result, result_list, memory_order_release);
    valk_async_handle_finish(ctx->pmap_handle);
  }

  free(task);
}

static valk_lval_t *valk_builtin_aio_pmap(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 3);

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *fn_arg = valk_lval_list_nth(a, 1);
  valk_lval_t *list_arg = valk_lval_list_nth(a, 2);

  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
  LVAL_ASSERT_TYPE(a, fn_arg, LVAL_FUN);

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  u64 count = 0;
  valk_lval_t *iter = list_arg;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/pmap: expected a list as third argument");
    }
    count++;
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    valk_async_handle_t *handle = valk_async_handle_new(sys, e);
    atomic_store_explicit(&handle->result, valk_lval_nil(), memory_order_release);
    valk_async_handle_try_transition(handle, VALK_ASYNC_PENDING, VALK_ASYNC_COMPLETED);
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
  ctx->total = count;
  atomic_store(&ctx->completed, 0);
  ctx->fn_released = false;

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
    task->pmap_ctx = ctx;
    task->fn_handle = fn_handle;
    task->arg_handle = arg_handle;
    task->index = i;

    valk_aio_loop_t *loop = &sys->loops[i % num_loops];
    valk_aio_loop_enqueue_task(loop, __pmap_worker, task);

    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(pmap_handle);
}

void valk_register_comb_pmap(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/pmap", valk_builtin_aio_pmap);
}
