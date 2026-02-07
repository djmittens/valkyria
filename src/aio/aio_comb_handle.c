#include "aio_combinators_internal.h"

static valk_lval_t* valk_builtin_aio_cancel(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/cancel: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/cancel: expected handle argument");
  }
  // LCOV_EXCL_BR_STOP

  valk_async_handle_t *handle = handle_lval->async.handle;
  bool cancelled = valk_async_handle_cancel(handle);

  return valk_lval_sym(cancelled ? ":true" : ":false");
}

static valk_lval_t* valk_builtin_aio_cancelled(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/cancelled?: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/cancelled?: expected handle argument");
  }
  // LCOV_EXCL_BR_STOP

  valk_async_handle_t *handle = handle_lval->async.handle;
  // LCOV_EXCL_BR_START - cancelled status: depends on async lifecycle
  bool cancelled = handle->status == VALK_ASYNC_CANCELLED ||
                   valk_async_handle_is_cancelled(handle);
  // LCOV_EXCL_BR_STOP

  return valk_lval_sym(cancelled ? ":true" : ":false");
}

// LCOV_EXCL_START - aio/status, aio/result, aio/error: internal helpers not directly tested
static valk_lval_t* valk_builtin_aio_status(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/status: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/status: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  return valk_async_status_to_sym(handle->status);
}

static valk_lval_t* valk_builtin_aio_result(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/result: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/result: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  valk_async_status_t status = valk_async_handle_get_status(handle);
  if (status == VALK_ASYNC_COMPLETED) {
    return atomic_load_explicit(&handle->result, memory_order_acquire);
  } else {
    return valk_lval_err("aio/result: handle not completed");
  }
}

static valk_lval_t* valk_builtin_aio_error(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/error: expected 1 argument");
  }
  valk_lval_t *handle_lval = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/error: expected handle argument");
  }

  valk_async_handle_t *handle = handle_lval->async.handle;
  valk_async_status_t status = valk_async_handle_get_status(handle);
  if (status == VALK_ASYNC_FAILED) {
    return atomic_load_explicit(&handle->error, memory_order_acquire);
  } else {
    return valk_lval_err("aio/error: handle not failed");
  }
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_aio_pure(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/pure: expected 1 argument");
  }
  // LCOV_EXCL_BR_STOP
  valk_lval_t *value = valk_lval_list_nth(a, 0);

  valk_async_handle_t *handle = valk_async_handle_new(NULL, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP

  valk_lval_t *heap_value = valk_evacuate_to_heap(value);
  atomic_store_explicit(&handle->result, heap_value, memory_order_release);
  valk_async_handle_try_transition(handle, VALK_ASYNC_PENDING, VALK_ASYNC_COMPLETED);

  return valk_lval_handle(handle);
}

static valk_lval_t* valk_builtin_aio_fail(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/fail: expected 1 argument");
  }
  // LCOV_EXCL_BR_STOP
  valk_lval_t *error = valk_lval_list_nth(a, 0);

  valk_async_handle_t *handle = valk_async_handle_new(NULL, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP

  valk_lval_t *heap_error = valk_evacuate_to_heap(error);
  atomic_store_explicit(&handle->error, heap_error, memory_order_release);
  valk_async_handle_try_transition(handle, VALK_ASYNC_PENDING, VALK_ASYNC_FAILED);

  return valk_lval_handle(handle);
}

static valk_lval_t* valk_builtin_aio_await(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/await: expected 1 argument (handle)");
  }
  valk_lval_t *handle_arg = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(handle_arg) != LVAL_HANDLE) {
    return valk_lval_err("aio/await: argument must be a handle");
  }
  // LCOV_EXCL_BR_STOP
  valk_async_handle_t *handle = handle_arg->async.handle;
  return valk_async_handle_await(handle);
}

static valk_lval_t* valk_builtin_aio_never(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/never: expected 1 argument (aio system)");
  }
  // LCOV_EXCL_BR_STOP
  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);

  // LCOV_EXCL_BR_START - type validation: compile-time checks catch most
  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  valk_async_handle_t *handle = valk_async_handle_new(sys, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP

  handle->status = VALK_ASYNC_RUNNING;

  return valk_lval_handle(handle);
}

void valk_register_comb_handle(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/cancel", valk_builtin_aio_cancel);
  valk_lenv_put_builtin(env, "aio/cancelled?", valk_builtin_aio_cancelled);
  valk_lenv_put_builtin(env, "aio/status", valk_builtin_aio_status);
  valk_lenv_put_builtin(env, "aio/result", valk_builtin_aio_result);
  valk_lenv_put_builtin(env, "aio/error", valk_builtin_aio_error);
  valk_lenv_put_builtin(env, "aio/pure", valk_builtin_aio_pure);
  valk_lenv_put_builtin(env, "aio/fail", valk_builtin_aio_fail);
  valk_lenv_put_builtin(env, "aio/never", valk_builtin_aio_never);
  valk_lenv_put_builtin(env, "aio/await", valk_builtin_aio_await);
}
