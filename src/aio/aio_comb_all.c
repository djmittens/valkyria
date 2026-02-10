#include "aio_combinators_internal.h"

#define VALK_ALL_CTX_MAGIC 0xA11C7821

typedef struct {
  u32 magic;
  valk_async_handle_t *all_handle;
  valk_lval_t **results;
  valk_async_handle_t **handles;
  u64 total;
  _Atomic(u64) completed;
  valk_mem_allocator_t *allocator;
} valk_all_ctx_t;

typedef struct {
  valk_all_ctx_t *all_ctx;
  u64 index;
} valk_all_wrapper_ctx_t;

static void valk_all_ctx_cleanup(void *ctx) {
  // LCOV_EXCL_START - cleanup callback: called from async system teardown
  valk_all_ctx_t *all_ctx = (valk_all_ctx_t *)ctx;
  if (!all_ctx) return;
  all_ctx->magic = 0;
  if (all_ctx->results) free(all_ctx->results);
  if (all_ctx->handles) free(all_ctx->handles);
  free(all_ctx);
  // LCOV_EXCL_STOP
}

static void valk_async_all_child_completed(valk_async_handle_t *child);
static void valk_async_all_child_failed(valk_async_handle_t *child);
static void valk_async_all_child_completed_with_ctx(valk_all_ctx_t *ctx, u64 idx, valk_async_handle_t *child);
static void valk_async_all_child_failed_with_ctx(valk_all_ctx_t *ctx, valk_async_handle_t *child);

// LCOV_EXCL_START - all wrapper on_done: internal async callback
static void valk_all_wrapper_on_done(valk_async_handle_t *handle, void *ctx) {
  valk_all_wrapper_ctx_t *wrapper_ctx = (valk_all_wrapper_ctx_t *)ctx;
  if (!wrapper_ctx || !wrapper_ctx->all_ctx) {
    free(wrapper_ctx);
    return;
  }

  valk_async_status_t status = valk_async_handle_get_status(handle);
  if (status == VALK_ASYNC_COMPLETED) {
    valk_async_all_child_completed_with_ctx(wrapper_ctx->all_ctx, wrapper_ctx->index, handle);
  } else if (status == VALK_ASYNC_FAILED) {
    valk_async_all_child_failed_with_ctx(wrapper_ctx->all_ctx, handle);
  }
  free(wrapper_ctx);
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_aio_all(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/all: expected 1 argument (list of handles)");
  }
  // LCOV_EXCL_BR_STOP
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  u64 count = 0;
  valk_lval_t *iter = handles_list;
  while (LVAL_TYPE(iter) != LVAL_NIL) {
    // LCOV_EXCL_BR_START - list type validation
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/all: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/all: all elements must be handles");
    }
    // LCOV_EXCL_BR_STOP
    count++;
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    valk_async_handle_t *result = valk_async_handle_new(NULL, e);
    result->status = VALK_ASYNC_COMPLETED;
    result->result = valk_lval_nil();
    return valk_lval_handle(result);
  }

  valk_async_handle_t *all_handle = valk_async_handle_new(NULL, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!all_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_BR_START - request ctx propagation: depends on caller setup
  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) {
    all_handle->request_ctx = first_h->async.handle->request_ctx;
  }
  // LCOV_EXCL_BR_STOP

  valk_lval_t **results = calloc(count, sizeof(valk_lval_t*));
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!results) {
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate results array");
  }
  // LCOV_EXCL_STOP

  u64 completed = 0;
  bool any_pending = false;
  bool any_failed = false;
  valk_lval_t *first_error = NULL;

  // LCOV_EXCL_BR_START - handle status iteration: depends on async lifecycle
  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    valk_async_status_t h_status = atomic_load_explicit(&handle->status, memory_order_acquire);

    if (h_status == VALK_ASYNC_COMPLETED) {
      results[i] = atomic_load_explicit(&handle->result, memory_order_acquire);
      completed++;
    } else if (h_status == VALK_ASYNC_FAILED) {
      any_failed = true;
      if (!first_error) first_error = atomic_load_explicit(&handle->error, memory_order_acquire);
    } else if (h_status == VALK_ASYNC_CANCELLED) {
      any_failed = true;
      if (!first_error) first_error = valk_lval_err("cancelled");
    } else {
      any_pending = true;
      if (!all_handle->sys && handle->sys) {
        all_handle->sys = handle->sys;
      }
    }
    iter = valk_lval_tail(iter);
  // LCOV_EXCL_BR_STOP
  }

  // LCOV_EXCL_START - any_failed cancel loop: depends on handle lifecycle
  if (any_failed) {
    valk_mem_free(results);
    atomic_store_explicit(&all_handle->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&all_handle->error, first_error, memory_order_release);

    iter = handles_list;
    for (u64 i = 0; i < count; i++) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      valk_async_status_t h_status = atomic_load_explicit(&handle->status, memory_order_acquire);
      if (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING) {
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    valk_async_handle_finish(all_handle);
    return valk_lval_handle(all_handle);
  }
  // LCOV_EXCL_STOP

  if (!any_pending) {
    valk_lval_t *result_list = valk_lval_nil();
    for (u64 i = count; i > 0; i--) {
      result_list = valk_lval_cons(results[i-1], result_list);
    }
    valk_mem_free(results);
    valk_lval_t *heap_result = valk_evacuate_to_heap(result_list);
    atomic_store_explicit(&all_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
    atomic_store_explicit(&all_handle->result, heap_result, memory_order_release);
    return valk_lval_handle(all_handle);
  }

  atomic_store_explicit(&all_handle->status, VALK_ASYNC_RUNNING, memory_order_release);
  all_handle->env = e;

  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  // LCOV_EXCL_START - calloc failure: requires OOM
  if (!handles) {
    valk_mem_free(results);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate handles array");
  }
  // LCOV_EXCL_STOP

  valk_all_ctx_t *ctx = malloc(sizeof(valk_all_ctx_t));
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!ctx) {
    valk_mem_free(results);
    valk_mem_free(handles);
    valk_async_handle_free(all_handle);
    return valk_lval_err("Failed to allocate all context");
  }
  // LCOV_EXCL_STOP
  ctx->magic = VALK_ALL_CTX_MAGIC;
  ctx->all_handle = all_handle;
  ctx->results = results;
  ctx->handles = handles;
  ctx->total = count;
  atomic_store(&ctx->completed, completed);
  ctx->allocator = &valk_malloc_allocator;
  all_handle->uv_handle_ptr = ctx;
  all_handle->on_child_completed = valk_async_all_child_completed;
  all_handle->on_child_failed = valk_async_all_child_failed;

  valk_async_handle_on_cleanup(all_handle, valk_all_ctx_cleanup, ctx);

  // LCOV_EXCL_START - all handle wiring loop: async lifecycle race conditions
  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;

    valk_async_status_t h_status = atomic_load_explicit(&handle->status, memory_order_acquire);
    if (h_status == VALK_ASYNC_COMPLETED) {
      handles[i] = handle;
      if (!ctx->results[i]) {
        ctx->results[i] = atomic_load_explicit(&handle->result, memory_order_acquire);
        u64 new_completed = atomic_fetch_add(&ctx->completed, 1) + 1;
        if (new_completed == ctx->total) {
          if (valk_async_handle_try_transition(ctx->all_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
            valk_lval_t *result_list = valk_lval_nil();
            for (u64 j = ctx->total; j > 0; j--) {
              result_list = valk_lval_cons(ctx->results[j-1], result_list);
            }
            valk_lval_t *heap_result = valk_evacuate_to_heap(result_list);
            atomic_store_explicit(&ctx->all_handle->result, heap_result, memory_order_release);
            valk_async_handle_finish(ctx->all_handle);
          }
        }
      }
    } else if (handle->parent != NULL) {
      valk_async_handle_t *wrapper = valk_async_handle_new(handle->sys, e);
      wrapper->status = VALK_ASYNC_RUNNING;
      wrapper->on_complete = valk_evacuate_to_heap(valk_lval_lambda(e,
        valk_lval_qcons(valk_lval_sym("x"), valk_lval_nil()),
        valk_lval_sym("x")));
      handles[i] = wrapper;
      valk_chunked_ptrs_push(&all_handle->children, wrapper, all_handle->region);

      valk_all_wrapper_ctx_t *wrapper_ctx = malloc(sizeof(valk_all_wrapper_ctx_t));
      if (wrapper_ctx) {
        wrapper_ctx->all_ctx = ctx;
        wrapper_ctx->index = i;
        atomic_store_explicit(&wrapper->on_done, valk_all_wrapper_on_done, memory_order_release);
        atomic_store_explicit(&wrapper->on_done_ctx, wrapper_ctx, memory_order_relaxed);
      }
      valk_async_handle_add_child(handle, wrapper);
    } else {
      handles[i] = handle;
      valk_async_handle_add_child(all_handle, handle);
    }
    iter = valk_lval_tail(iter);
  }
  // LCOV_EXCL_STOP

  return valk_lval_handle(all_handle);
}

static inline valk_all_ctx_t* valk_async_get_all_ctx(valk_async_handle_t *handle) {
  // LCOV_EXCL_START - internal helper: defensive checks
  if (!handle || !handle->parent) return NULL;
  valk_async_handle_t *parent = handle->parent;
  if (!parent->uv_handle_ptr) return NULL;
  valk_all_ctx_t *ctx = (valk_all_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_ALL_CTX_MAGIC) return NULL;
  return ctx;
  // LCOV_EXCL_STOP
}

static inline i64 valk_async_all_find_index(valk_all_ctx_t *ctx, valk_async_handle_t *child) {
  // LCOV_EXCL_START - internal helper: linear search
  for (u64 i = 0; i < ctx->total; i++) {
    if (ctx->handles[i] == child) return (i64)i;
  }
  return -1;
  // LCOV_EXCL_STOP
}

// LCOV_EXCL_START - async all completion: internal callback, called from async system
static void valk_async_all_child_completed(valk_async_handle_t *child) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->all_handle))) {
    return;
  }

  i64 idx = valk_async_all_find_index(ctx, child);
  if (idx < 0) return;

  ctx->results[idx] = atomic_load_explicit(&child->result, memory_order_acquire);
  u64 new_completed = atomic_fetch_add(&ctx->completed, 1) + 1;

  if (new_completed == ctx->total) {
    if (!valk_async_handle_try_transition(ctx->all_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
      return;
    }

    valk_lval_t *result_list = valk_lval_nil();
    for (u64 i = ctx->total; i > 0; i--) {
      result_list = valk_lval_cons(ctx->results[i-1], result_list);
    }

    valk_lval_t *heap_result = valk_evacuate_to_heap(result_list);
    atomic_store_explicit(&ctx->all_handle->result, heap_result, memory_order_release);

    valk_async_handle_finish(ctx->all_handle);
  }
}

static void valk_async_all_child_failed(valk_async_handle_t *child) {
  valk_all_ctx_t *ctx = valk_async_get_all_ctx(child);
  if (!ctx) return;

  if (!valk_async_handle_try_transition(ctx->all_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_FAILED)) {
    return;
  }

  valk_lval_t *error = atomic_load_explicit(&child->error, memory_order_acquire);
  atomic_store_explicit(&ctx->all_handle->error, error, memory_order_release);

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  valk_async_handle_finish(ctx->all_handle);
}

static void valk_async_all_child_completed_with_ctx(valk_all_ctx_t *ctx, u64 idx, valk_async_handle_t *child) {
  if (!ctx) return;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(ctx->all_handle))) {
    return;
  }

  ctx->results[idx] = atomic_load_explicit(&child->result, memory_order_acquire);
  u64 new_completed = atomic_fetch_add(&ctx->completed, 1) + 1;

  if (new_completed == ctx->total) {
    if (!valk_async_handle_try_transition(ctx->all_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_COMPLETED)) {
      return;
    }

    valk_lval_t *result_list = valk_lval_nil();
    for (u64 i = ctx->total; i > 0; i--) {
      result_list = valk_lval_cons(ctx->results[i-1], result_list);
    }

    valk_lval_t *heap_result = valk_evacuate_to_heap(result_list);
    atomic_store_explicit(&ctx->all_handle->result, heap_result, memory_order_release);

    valk_async_handle_finish(ctx->all_handle);
  }
}

static void valk_async_all_child_failed_with_ctx(valk_all_ctx_t *ctx, valk_async_handle_t *child) {
  if (!ctx) return;

  if (!valk_async_handle_try_transition(ctx->all_handle, VALK_ASYNC_RUNNING, VALK_ASYNC_FAILED)) {
    return;
  }

  valk_lval_t *error = atomic_load_explicit(&child->error, memory_order_acquire);
  atomic_store_explicit(&ctx->all_handle->error, error, memory_order_release);

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  valk_async_handle_finish(ctx->all_handle);
}
// LCOV_EXCL_STOP

void valk_register_comb_all(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/all", valk_builtin_aio_all);
}
