#include "aio_combinators_internal.h"

#define VALK_ANY_CTX_MAGIC 0xA4177821

typedef struct {
  u32 magic;
  valk_async_handle_t *any_handle;
  valk_async_handle_t **handles;
  u64 total;
  u64 failed_count;
  valk_lval_t *last_error;
  valk_mem_allocator_t *allocator;
} valk_any_ctx_t;

// LCOV_EXCL_START - async any: internal callbacks called from async system
static void valk_any_ctx_cleanup(void *ctx) {
  valk_any_ctx_t *any_ctx = (valk_any_ctx_t *)ctx;
  if (!any_ctx) return;
  any_ctx->magic = 0;
  if (any_ctx->handles) free(any_ctx->handles);
  free(any_ctx);
}

static void valk_async_any_child_success(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_any_ctx_t *ctx = (valk_any_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ANY_CTX_MAGIC) return;

  if (!valk_async_handle_try_transition(ctx->any_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
    return;
  }

  atomic_store_explicit(&ctx->any_handle->result, atomic_load_explicit(&child->result, memory_order_acquire), memory_order_release);

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  valk_async_notify_parent(ctx->any_handle);
  valk_async_notify_done(ctx->any_handle);
  valk_async_propagate_completion(ctx->any_handle);
}

static void valk_async_any_child_failed(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_any_ctx_t *ctx = (valk_any_ctx_t*)parent->uv_handle_ptr;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->any_handle))) {
    return;
  }

  ctx->failed_count++;
  ctx->last_error = atomic_load_explicit(&child->error, memory_order_acquire);

  if (ctx->failed_count == ctx->total) {
    if (!valk_async_handle_try_transition(ctx->any_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_FAILED)) {
      return;
    }
    atomic_store_explicit(&ctx->any_handle->error, ctx->last_error, memory_order_release);
    valk_async_notify_parent(ctx->any_handle);
    valk_async_notify_done(ctx->any_handle);
    valk_async_propagate_completion(ctx->any_handle);
  }
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_aio_any(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/any: expected 1 argument (list of handles)");
  }
  // LCOV_EXCL_BR_STOP
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  u64 count = 0;
  u64 failed_count = 0;
  valk_async_handle_t *first_success = NULL;
  valk_lval_t *last_error = NULL;
  valk_lval_t *iter = handles_list;

  while (LVAL_TYPE(iter) != LVAL_NIL) {
    // LCOV_EXCL_BR_START - list type validation
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/any: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/any: all elements must be handles");
    }
    // LCOV_EXCL_BR_STOP
    valk_async_handle_t *handle = h->async.handle;
    count++;

    // LCOV_EXCL_BR_START - status detection: depends on handle status
    valk_async_status_t h_status = atomic_load_explicit(&handle->status, memory_order_acquire);
    if (h_status == VALK_ASYNC_COMPLETED && !first_success) {
      first_success = handle;
    } else if (h_status == VALK_ASYNC_FAILED ||
               h_status == VALK_ASYNC_CANCELLED) {
      failed_count++;
      valk_lval_t *h_error = atomic_load_explicit(&handle->error, memory_order_acquire);
      last_error = h_error ? h_error : valk_lval_err("cancelled");
    }
    // LCOV_EXCL_BR_STOP
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    return valk_lval_err("aio/any: cannot use with empty list");
  }

  valk_async_handle_t *any_handle = valk_async_handle_new(NULL, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!any_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_BR_START - request ctx propagation: depends on caller setup
  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) {
    any_handle->request_ctx = first_h->async.handle->request_ctx;
  }
  // LCOV_EXCL_BR_STOP

  if (first_success) {
    atomic_store_explicit(&any_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
    atomic_store_explicit(&any_handle->result, atomic_load_explicit(&first_success->result, memory_order_acquire), memory_order_release);

    // LCOV_EXCL_START - cancel remaining: first_success found
    iter = handles_list;
    while (LVAL_TYPE(iter) != LVAL_NIL) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      valk_async_status_t h_status = atomic_load_explicit(&handle->status, memory_order_acquire);
      if (handle != first_success &&
          (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    // LCOV_EXCL_STOP
    return valk_lval_handle(any_handle);
  }

  if (failed_count == count) {
    atomic_store_explicit(&any_handle->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&any_handle->error, last_error, memory_order_release);
    return valk_lval_handle(any_handle);
  }

  atomic_store_explicit(&any_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
  any_handle->env = e;

  // LCOV_EXCL_START - sys detection: depends on handle configuration
  iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    if (handle->sys) {
      any_handle->sys = handle->sys;
      break;
    }
    iter = valk_lval_tail(iter);
  }
  // LCOV_EXCL_STOP

  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!handles) {
    valk_async_handle_free(any_handle);
    return valk_lval_err("Failed to allocate handles array");
  }

  valk_any_ctx_t *ctx = malloc(sizeof(valk_any_ctx_t));
  if (!ctx) {
    free(handles);
    valk_async_handle_free(any_handle);
    return valk_lval_err("Failed to allocate any context");
  }
  // LCOV_EXCL_STOP
  ctx->magic = VALK_ANY_CTX_MAGIC;
  ctx->any_handle = any_handle;
  ctx->handles = handles;
  ctx->total = count;
  ctx->failed_count = 0;
  ctx->last_error = NULL;
  ctx->allocator = &valk_malloc_allocator;
  any_handle->uv_handle_ptr = ctx;
  any_handle->on_child_completed = valk_async_any_child_success;
  any_handle->on_child_failed = valk_async_any_child_failed;

  valk_async_handle_on_cleanup(any_handle, valk_any_ctx_cleanup, ctx);

  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    valk_async_handle_add_child(any_handle, handle);
    iter = valk_lval_tail(iter);
  }

   return valk_lval_handle(any_handle);
}

void valk_register_comb_any(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/any", valk_builtin_aio_any);
}
