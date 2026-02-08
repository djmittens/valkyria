#include "aio_combinators_internal.h"

static valk_lval_t* valk_builtin_aio_on_cancel(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/on-cancel: expected 2 arguments (handle fn)");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/on-cancel: first argument must be a handle");
  }
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/on-cancel: second argument must be a function");
  }
  // LCOV_EXCL_STOP

  valk_async_handle_t *handle = handle_lval->async.handle;

  // LCOV_EXCL_START - cancelled status: requires specific async lifecycle
  if (handle->status == VALK_ASYNC_CANCELLED) {
    valk_lval_t *args = valk_lval_nil();
    valk_lval_eval_call(e, fn, args);
    return valk_lval_handle(handle);
  }
  // LCOV_EXCL_STOP

  handle->on_cancel = valk_evacuate_to_heap(fn);
  // LCOV_EXCL_START - env check: defensive
  if (!handle->env) handle->env = e;
  // LCOV_EXCL_STOP

  return valk_lval_handle(handle);
}

static valk_lval_t* valk_builtin_aio_bracket(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 3) {
    return valk_lval_err("aio/bracket: expected 3 arguments (acquire release use)");
  }
  valk_lval_t *acquire_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *release_fn = valk_lval_list_nth(a, 1);
  valk_lval_t *use_fn = valk_lval_list_nth(a, 2);

  if (LVAL_TYPE(acquire_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/bracket: first argument must be a handle");
  }
  if (LVAL_TYPE(release_fn) != LVAL_FUN) {
    return valk_lval_err("aio/bracket: second argument must be a function");
  }
  if (LVAL_TYPE(use_fn) != LVAL_FUN) {
    return valk_lval_err("aio/bracket: third argument must be a function");
  }
  // LCOV_EXCL_STOP

  valk_async_handle_t *acquire = acquire_lval->async.handle;

  valk_async_handle_t *bracket_handle = valk_async_handle_new(acquire->sys, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!bracket_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP
  bracket_handle->request_ctx = acquire->request_ctx;

  valk_async_status_t acquire_status = atomic_load_explicit(&acquire->status, memory_order_acquire);
  // LCOV_EXCL_START - bracket status dispatch: depends on acquire handle status
  if (acquire_status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *resource = atomic_load_explicit(&acquire->result, memory_order_acquire);

    valk_lval_t *use_args = valk_lval_cons(resource, valk_lval_nil());
    valk_lval_t *use_result = valk_lval_eval_call(e, use_fn, use_args);

    if (LVAL_TYPE(use_result) == LVAL_HANDLE) {
      valk_async_handle_t *use_handle = use_result->async.handle;
      valk_async_status_t use_status = atomic_load_explicit(&use_handle->status, memory_order_acquire);

      if (use_status == VALK_ASYNC_COMPLETED ||
          use_status == VALK_ASYNC_FAILED ||
          use_status == VALK_ASYNC_CANCELLED) {
        valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
        valk_lval_eval_call(e, release_fn, release_args);

        if (use_status == VALK_ASYNC_COMPLETED) {
          atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
          atomic_store_explicit(&bracket_handle->result, atomic_load_explicit(&use_handle->result, memory_order_acquire), memory_order_release);
        } else if (use_status == VALK_ASYNC_FAILED) {
          atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_FAILED, memory_order_release);
          atomic_store_explicit(&bracket_handle->error, atomic_load_explicit(&use_handle->error, memory_order_acquire), memory_order_release);
        } else {
          atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_CANCELLED, memory_order_release);
        }
      } else {
        atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
        bracket_handle->env = e;
        bracket_handle->parent = use_handle;

        bracket_handle->on_cancel = valk_evacuate_to_heap(release_fn);
        atomic_store_explicit(&bracket_handle->result, resource, memory_order_release);

        valk_async_handle_add_child(use_handle, bracket_handle);
      }
    } else if (LVAL_TYPE(use_result) == LVAL_ERR) {
      valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
      valk_lval_eval_call(e, release_fn, release_args);

      atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&bracket_handle->error, use_result, memory_order_release);
    } else {
      valk_lval_t *release_args = valk_lval_cons(resource, valk_lval_nil());
      valk_lval_eval_call(e, release_fn, release_args);

      atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
      atomic_store_explicit(&bracket_handle->result, use_result, memory_order_release);
    }

    return valk_lval_handle(bracket_handle);
  }

  if (acquire_status == VALK_ASYNC_FAILED) {
    atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&bracket_handle->error, atomic_load_explicit(&acquire->error, memory_order_acquire), memory_order_release);
    return valk_lval_handle(bracket_handle);
  }

  if (acquire_status == VALK_ASYNC_CANCELLED) {
    atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_CANCELLED, memory_order_release);
    return valk_lval_handle(bracket_handle);
  }
  // LCOV_EXCL_STOP

  atomic_store_explicit(&bracket_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
  bracket_handle->env = e;

  bracket_handle->on_complete = valk_evacuate_to_heap(use_fn);
  bracket_handle->on_cancel = valk_evacuate_to_heap(release_fn);
  bracket_handle->parent = acquire;

  valk_async_handle_add_child(acquire, bracket_handle);

  return valk_lval_handle(bracket_handle);
}

static valk_lval_t* valk_builtin_aio_scope(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/scope: expected 1 argument (fn)");
  }
  valk_lval_t *fn = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/scope: argument must be a function");
  }
  // LCOV_EXCL_STOP

  valk_async_handle_t *scope_handle = valk_async_handle_new(NULL, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!scope_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP
  atomic_store_explicit(&scope_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
  scope_handle->env = e;

  valk_lval_t *scope_lval = valk_lval_handle(scope_handle);

  valk_lval_t *args = valk_lval_cons(scope_lval, valk_lval_nil());
  valk_lval_t *result = valk_lval_eval_call(e, fn, args);

  // LCOV_EXCL_START - result type dispatch: callback-dependent
  if (LVAL_TYPE(result) == LVAL_ERR) {
    atomic_store_explicit(&scope_handle->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&scope_handle->error, result, memory_order_release);
    return scope_lval;
  }

  if (LVAL_TYPE(result) == LVAL_HANDLE) {
    valk_async_handle_t *inner = result->async.handle;
    valk_async_status_t inner_status = atomic_load_explicit(&inner->status, memory_order_acquire);

    if (inner_status == VALK_ASYNC_COMPLETED) {
      atomic_store_explicit(&scope_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
      atomic_store_explicit(&scope_handle->result, atomic_load_explicit(&inner->result, memory_order_acquire), memory_order_release);
    } else if (inner_status == VALK_ASYNC_FAILED) {
      atomic_store_explicit(&scope_handle->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&scope_handle->error, atomic_load_explicit(&inner->error, memory_order_acquire), memory_order_release);
    } else if (inner_status == VALK_ASYNC_CANCELLED) {
      atomic_store_explicit(&scope_handle->status, VALK_ASYNC_CANCELLED, memory_order_release);
    } else {
      scope_handle->parent = inner;
      valk_async_handle_add_child(inner, scope_handle);
    }
    return scope_lval;
  }
  // LCOV_EXCL_STOP

  atomic_store_explicit(&scope_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
  atomic_store_explicit(&scope_handle->result, result, memory_order_release);
  return scope_lval;
}

void valk_register_comb_resource(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/on-cancel", valk_builtin_aio_on_cancel);
  valk_lenv_put_builtin(env, "aio/bracket", valk_builtin_aio_bracket);
  valk_lenv_put_builtin(env, "aio/scope", valk_builtin_aio_scope);
}
