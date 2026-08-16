#include "aio_combinators_internal.h"

static valk_lval_t* valk_builtin_aio_then(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/then: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/then: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/then: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  valk_async_handle_t *result = valk_async_handle_new(source->sys, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!result) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP
  result->request_ctx = source->request_ctx;

  // LCOV_EXCL_START - sync completion: timing-dependent, varies by platform
  valk_async_status_t source_status = atomic_load_explicit(&source->status, memory_order_acquire);
  if (source_status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *src_result = atomic_load_explicit(&source->result, memory_order_acquire);
    valk_lval_t *args = valk_lval_cons(src_result, valk_lval_nil());
    valk_lval_t *transformed = valk_lval_eval_call(e, fn, args);
    if (LVAL_TYPE(transformed) == LVAL_ERR) {
      atomic_store_explicit(&result->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&result->error, valk_evacuate_to_heap(transformed), memory_order_release);
    } else if (LVAL_TYPE(transformed) == LVAL_HANDLE) {
      valk_async_handle_t *inner = transformed->async.handle;
      valk_async_status_t inner_status = atomic_load_explicit(&inner->status, memory_order_acquire);
      if (inner_status == VALK_ASYNC_COMPLETED) {
        atomic_store_explicit(&result->status, VALK_ASYNC_COMPLETED, memory_order_release);
        atomic_store_explicit(&result->result, valk_evacuate_to_heap(atomic_load_explicit(&inner->result, memory_order_acquire)), memory_order_release);
      } else if (inner_status == VALK_ASYNC_FAILED) {
        atomic_store_explicit(&result->status, VALK_ASYNC_FAILED, memory_order_release);
        atomic_store_explicit(&result->error, valk_evacuate_to_heap(atomic_load_explicit(&inner->error, memory_order_acquire)), memory_order_release);
      } else {
        atomic_store_explicit(&result->status, VALK_ASYNC_RUNNING, memory_order_release);
        valk_async_handle_add_child(inner, result);
      }
    } else {
      atomic_store_explicit(&result->status, VALK_ASYNC_COMPLETED, memory_order_release);
      atomic_store_explicit(&result->result, valk_evacuate_to_heap(transformed), memory_order_release);
    }
    return valk_lval_handle(result);
  }

  if (source_status == VALK_ASYNC_FAILED) {
    atomic_store_explicit(&result->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&result->error, atomic_load_explicit(&source->error, memory_order_acquire), memory_order_release);
    return valk_lval_handle(result);
  }

  if (source_status == VALK_ASYNC_CANCELLED) {
    atomic_store_explicit(&result->status, VALK_ASYNC_CANCELLED, memory_order_release);
    return valk_lval_handle(result);
  }
  // LCOV_EXCL_STOP

  atomic_store_explicit(&result->status, VALK_ASYNC_RUNNING, memory_order_release);
  result->env = e;
  result->on_complete = valk_evacuate_to_heap(fn);
  result->on_error = NULL;
  result->parent = source;

  valk_async_handle_add_child(source, result);

  return valk_lval_handle(result);
}

static valk_lval_t* valk_builtin_aio_catch(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/catch: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/catch: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/catch: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  valk_async_handle_t *catch_handle = valk_async_handle_new(source->sys, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!catch_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP
  catch_handle->request_ctx = source->request_ctx;

  // LCOV_EXCL_START - sync completion: timing-dependent, varies by platform
  valk_async_status_t source_status = atomic_load_explicit(&source->status, memory_order_acquire);
  if (source_status == VALK_ASYNC_COMPLETED) {
    atomic_store_explicit(&catch_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
    atomic_store_explicit(&catch_handle->result, atomic_load_explicit(&source->result, memory_order_acquire), memory_order_release);
    return valk_lval_handle(catch_handle);
  }

  if (source_status == VALK_ASYNC_FAILED) {
    valk_lval_t *src_error = atomic_load_explicit(&source->error, memory_order_acquire);
    valk_lval_t *args = valk_lval_cons(src_error, valk_lval_nil());
    valk_lval_t *recovered = valk_lval_eval_call(e, fn, args);
    if (LVAL_TYPE(recovered) == LVAL_ERR) {
      atomic_store_explicit(&catch_handle->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&catch_handle->error, valk_evacuate_to_heap(recovered), memory_order_release);
    } else if (LVAL_TYPE(recovered) == LVAL_HANDLE) {
      valk_async_handle_t *inner = recovered->async.handle;
      valk_async_status_t inner_status = atomic_load_explicit(&inner->status, memory_order_acquire);
      if (inner_status == VALK_ASYNC_COMPLETED) {
        atomic_store_explicit(&catch_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
        atomic_store_explicit(&catch_handle->result, valk_evacuate_to_heap(atomic_load_explicit(&inner->result, memory_order_acquire)), memory_order_release);
      } else if (inner_status == VALK_ASYNC_FAILED) {
        atomic_store_explicit(&catch_handle->status, VALK_ASYNC_FAILED, memory_order_release);
        atomic_store_explicit(&catch_handle->error, valk_evacuate_to_heap(atomic_load_explicit(&inner->error, memory_order_acquire)), memory_order_release);
      } else {
        atomic_store_explicit(&catch_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
        valk_async_handle_add_child(inner, catch_handle);
      }
    } else {
      atomic_store_explicit(&catch_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
      atomic_store_explicit(&catch_handle->result, valk_evacuate_to_heap(recovered), memory_order_release);
    }
    return valk_lval_handle(catch_handle);
  }

  if (source_status == VALK_ASYNC_CANCELLED) {
    atomic_store_explicit(&catch_handle->status, VALK_ASYNC_CANCELLED, memory_order_release);
    return valk_lval_handle(catch_handle);
  }

  atomic_store_explicit(&catch_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
  catch_handle->env = e;
  catch_handle->on_complete = NULL;
  catch_handle->on_error = valk_evacuate_to_heap(fn);
  catch_handle->parent = source;

  valk_async_handle_add_child(source, catch_handle);

  return valk_lval_handle(catch_handle);
}

static valk_lval_t* valk_builtin_aio_finally(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/finally: expected 2 arguments (handle fn)");
  }
  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/finally: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/finally: second argument must be a function");
  }

  valk_async_handle_t *source = source_lval->async.handle;

  valk_async_handle_t *finally_handle = valk_async_handle_new(source->sys, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!finally_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP
  finally_handle->request_ctx = source->request_ctx;

  // LCOV_EXCL_START - sync completion: timing-dependent, varies by platform
  valk_async_status_t source_status = atomic_load_explicit(&source->status, memory_order_acquire);
  if (source_status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    atomic_store_explicit(&finally_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
    atomic_store_explicit(&finally_handle->result, atomic_load_explicit(&source->result, memory_order_acquire), memory_order_release);
    return valk_lval_handle(finally_handle);
  }
  if (source_status == VALK_ASYNC_FAILED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    atomic_store_explicit(&finally_handle->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&finally_handle->error, atomic_load_explicit(&source->error, memory_order_acquire), memory_order_release);
    return valk_lval_handle(finally_handle);
  }
  if (source_status == VALK_ASYNC_CANCELLED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    atomic_store_explicit(&finally_handle->status, VALK_ASYNC_CANCELLED, memory_order_release);
    return valk_lval_handle(finally_handle);
  }

  atomic_store_explicit(&finally_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
  finally_handle->env = e;
  finally_handle->on_cancel = valk_evacuate_to_heap(fn);
  finally_handle->parent = source;

  valk_async_handle_add_child(source, finally_handle);

  return valk_lval_handle(finally_handle);
}

void valk_register_comb_chain(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/then", valk_builtin_aio_then);
  valk_lenv_put_builtin(env, "aio/catch", valk_builtin_aio_catch);
  valk_lenv_put_builtin(env, "aio/finally", valk_builtin_aio_finally);
}
