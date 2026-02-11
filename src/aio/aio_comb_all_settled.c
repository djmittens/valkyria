#include "aio_combinators_internal.h"

#define VALK_ALL_SETTLED_CTX_MAGIC 0xA11C5E7D
#define VALK_ALL_SETTLED_CTX_MAGIC_EARLY 0xA11C5E7D

typedef struct {
  u32 magic;
  valk_async_handle_t *all_settled_handle;
  valk_lval_t **results;
  valk_async_handle_t **handles;
  u64 total;
  _Atomic(u64) completed;
  valk_mem_allocator_t *allocator;
} valk_all_settled_ctx_t;

static void valk_all_settled_ctx_cleanup(void *ctx) {
  valk_all_settled_ctx_t *as_ctx = (valk_all_settled_ctx_t *)ctx;
  if (!as_ctx) return;
  as_ctx->magic = 0;
  if (as_ctx->results) free(as_ctx->results);
  if (as_ctx->handles) free(as_ctx->handles);
  free(as_ctx);
}

static void valk_async_all_settled_child_completed(valk_async_handle_t *child);

static inline valk_all_settled_ctx_t* valk_async_get_all_settled_ctx(valk_async_handle_t *handle) {
  if (!handle || !handle->parent) return NULL;
  valk_async_handle_t *parent = handle->parent;
  if (!parent->uv_handle_ptr) return NULL;
  valk_all_settled_ctx_t *ctx = (valk_all_settled_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ALL_SETTLED_CTX_MAGIC) return NULL;
  return ctx;
}

static inline i64 valk_async_all_settled_find_index(valk_all_settled_ctx_t *ctx, valk_async_handle_t *child) {
  for (u64 i = 0; i < ctx->total; i++) {
    if (ctx->handles[i] == child) return (i64)i;
  }
  return -1;
}

static void valk_async_all_settled_child_completed(valk_async_handle_t *child) {
  valk_all_settled_ctx_t *ctx = valk_async_get_all_settled_ctx(child);
  if (!ctx) return;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->all_settled_handle))) {
    return;
  }

  i64 idx = valk_async_all_settled_find_index(ctx, child);
  if (idx < 0) return;

  valk_async_status_t child_status = valk_async_handle_get_status(child);
  valk_lval_t *result_obj;

  if (child_status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *value = atomic_load_explicit(&child->result, memory_order_acquire);
    valk_lval_t *items[] = {
      valk_lval_sym(":status"), valk_lval_sym(":ok"),
      valk_lval_sym(":value"), value
    };
    result_obj = valk_lval_qlist(items, 4);
  } else if (child_status == VALK_ASYNC_FAILED) {
    valk_lval_t *error = atomic_load_explicit(&child->error, memory_order_acquire);
    valk_lval_t *items[] = {
      valk_lval_sym(":status"), valk_lval_sym(":error"),
      valk_lval_sym(":error"), error
    };
    result_obj = valk_lval_qlist(items, 4);
  } else if (child_status == VALK_ASYNC_CANCELLED) {
    valk_lval_t *items[] = {
      valk_lval_sym(":status"), valk_lval_sym(":error"),
      valk_lval_sym(":error"), valk_lval_err("cancelled")
    };
    result_obj = valk_lval_qlist(items, 4);
  } else {
    return;
  }

  ctx->results[idx] = result_obj;
  u64 new_completed = atomic_fetch_add(&ctx->completed, 1) + 1;

  if (new_completed == ctx->total) {
    if (!valk_async_handle_try_transition(ctx->all_settled_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
      return;
    }

    valk_lval_t *result_list = valk_lval_nil();
    for (u64 i = ctx->total; i > 0; i--) {
      result_list = valk_lval_cons(ctx->results[i-1], result_list);
    }

    valk_lval_t *heap_result = valk_evacuate_to_heap(result_list);
    atomic_store_explicit(&ctx->all_settled_handle->result, heap_result, memory_order_release);

    valk_async_handle_finish(ctx->all_settled_handle);
  }
}

static valk_lval_t* valk_builtin_aio_all_settled(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/all-settled: expected 1 argument (list of handles)");
  }
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  u64 count = 0;
  valk_lval_t *iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/all-settled: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/all-settled: all elements must be handles");
    }
    count++;
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    valk_async_handle_t *result = valk_async_handle_new(NULL, e);
    result->status = VALK_ASYNC_COMPLETED;
    result->result = valk_lval_nil();
    return valk_lval_handle(result);
  }

  valk_async_handle_t *as_handle = valk_async_handle_new(NULL, e);
  // LCOV_EXCL_START - OOM: handle allocation failure
  if (!as_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_BR_START - request ctx propagation: depends on caller setup
  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) {
    as_handle->request_ctx = first_h->async.handle->request_ctx;
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t **results = calloc(count, sizeof(valk_lval_t*));
  // LCOV_EXCL_START - OOM: calloc failure
  if (!results) {
    valk_async_handle_free(as_handle);
    return valk_lval_err("Failed to allocate results array");
  }
  // LCOV_EXCL_STOP

  atomic_store_explicit(&as_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
  as_handle->env = e;

  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  // LCOV_EXCL_START - OOM: calloc/malloc failure
  if (!handles) {
    free(results);
    valk_async_handle_free(as_handle);
    return valk_lval_err("Failed to allocate handles array");
  }

  valk_all_settled_ctx_t *ctx = malloc(sizeof(valk_all_settled_ctx_t));
  if (!ctx) {
    free(results);
    free(handles);
    valk_async_handle_free(as_handle);
    return valk_lval_err("Failed to allocate all-settled context");
  }
  // LCOV_EXCL_STOP
  ctx->magic = VALK_ALL_SETTLED_CTX_MAGIC;
  ctx->all_settled_handle = as_handle;
  ctx->results = results;
  ctx->handles = handles;
  ctx->total = count;
  atomic_store(&ctx->completed, 0);
  ctx->allocator = &valk_malloc_allocator;
  as_handle->uv_handle_ptr = ctx;
  as_handle->on_child_completed = valk_async_all_settled_child_completed;
  as_handle->on_child_failed = valk_async_all_settled_child_completed;

  valk_async_handle_on_cleanup(as_handle, valk_all_settled_ctx_cleanup, ctx);

  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    if (!as_handle->sys && handle->sys) {
      as_handle->sys = handle->sys;
    }
    valk_async_handle_add_child(as_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(as_handle);
}

void valk_register_comb_all_settled(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/all-settled", valk_builtin_aio_all_settled);
}
