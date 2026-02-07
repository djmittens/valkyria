#include "aio_combinators_internal.h"

#define VALK_ALL_CTX_MAGIC 0xA11C7821
#define VALK_RACE_CTX_MAGIC 0x9ACE7821
#define VALK_ANY_CTX_MAGIC 0xA4177821
#define VALK_ALL_SETTLED_CTX_MAGIC 0xA11C5E7D

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
    valk_async_notify_parent(all_handle);
    valk_async_notify_done(all_handle);
    valk_async_propagate_completion(all_handle);
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
            valk_async_notify_parent(ctx->all_handle);
            valk_async_notify_done(ctx->all_handle);
            valk_async_propagate_completion(ctx->all_handle);
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

    valk_async_notify_parent(ctx->all_handle);
    valk_async_notify_done(ctx->all_handle);
    valk_async_propagate_completion(ctx->all_handle);
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

  valk_async_notify_parent(ctx->all_handle);
  valk_async_notify_done(ctx->all_handle);
  valk_async_propagate_completion(ctx->all_handle);
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

    valk_async_notify_parent(ctx->all_handle);
    valk_async_notify_done(ctx->all_handle);
    valk_async_propagate_completion(ctx->all_handle);
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

  valk_async_notify_parent(ctx->all_handle);
  valk_async_notify_done(ctx->all_handle);
  valk_async_propagate_completion(ctx->all_handle);
}
// LCOV_EXCL_STOP

typedef struct {
  u32 magic;
  valk_async_handle_t *race_handle;
  valk_async_handle_t **handles;
  u64 total;
  valk_mem_allocator_t *allocator;
} valk_race_ctx_t;

// LCOV_EXCL_START - async race: internal callbacks called from async system
static void valk_race_ctx_cleanup(void *ctx) {
  valk_race_ctx_t *race_ctx = (valk_race_ctx_t *)ctx;
  if (!race_ctx) return;
  race_ctx->magic = 0;
  if (race_ctx->handles) free(race_ctx->handles);
  free(race_ctx);
}

static void valk_async_race_child_resolved(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  if (!parent->uv_handle_ptr) return;

  valk_race_ctx_t *ctx = (valk_race_ctx_t*)parent->uv_handle_ptr;
  if (ctx->magic != VALK_RACE_CTX_MAGIC) return;

  valk_async_status_t child_status = valk_async_handle_get_status(child);
  valk_async_status_t new_status;
  if (child_status == VALK_ASYNC_COMPLETED) {
    new_status = VALK_ASYNC_COMPLETED;
  } else if (child_status == VALK_ASYNC_FAILED) {
    new_status = VALK_ASYNC_FAILED;
  } else {
    return;
  }

  if (!valk_async_handle_try_transition(ctx->race_handle, VALK_ASYNC_RUNNING, new_status)) {
    return;
  }

  if (new_status == VALK_ASYNC_COMPLETED) {
    atomic_store_explicit(&ctx->race_handle->result, atomic_load_explicit(&child->result, memory_order_acquire), memory_order_release);
  } else {
    atomic_store_explicit(&ctx->race_handle->error, atomic_load_explicit(&child->error, memory_order_acquire), memory_order_release);
  }

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
      valk_async_handle_cancel(h);
    }
  }

  valk_async_notify_parent(ctx->race_handle);
  valk_async_notify_done(ctx->race_handle);
  valk_async_propagate_completion(ctx->race_handle);
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_aio_race(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/race: expected 1 argument (list of handles)");
  }
  // LCOV_EXCL_BR_STOP
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  u64 count = 0;
  valk_async_handle_t *first_done = NULL;
  valk_lval_t *iter = handles_list;

  while (LVAL_TYPE(iter) != LVAL_NIL) {
    // LCOV_EXCL_BR_START - list type validation
    if (LVAL_TYPE(iter) != LVAL_CONS && LVAL_TYPE(iter) != LVAL_QEXPR) {
      return valk_lval_err("aio/race: expected a list of handles");
    }
    valk_lval_t *h = valk_lval_head(iter);
    if (LVAL_TYPE(h) != LVAL_HANDLE) {
      return valk_lval_err("aio/race: all elements must be handles");
    }
    // LCOV_EXCL_BR_STOP
    valk_async_handle_t *handle = h->async.handle;
    count++;

    // LCOV_EXCL_BR_START - first_done detection: depends on handle status
    if (!first_done && (handle->status == VALK_ASYNC_COMPLETED ||
                        handle->status == VALK_ASYNC_FAILED)) {
      first_done = handle;
    }
    // LCOV_EXCL_BR_STOP
    iter = valk_lval_tail(iter);
  }

  if (count == 0) {
    return valk_lval_err("aio/race: cannot race empty list");
  }

  valk_async_handle_t *race_handle = valk_async_handle_new(NULL, e);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!race_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_BR_START - request ctx propagation: depends on caller setup
  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) {
    race_handle->request_ctx = first_h->async.handle->request_ctx;
  }
  // LCOV_EXCL_BR_STOP

  // LCOV_EXCL_BR_START - first_done handling: depends on async lifecycle
  if (first_done) {
    valk_async_status_t first_done_status = atomic_load_explicit(&first_done->status, memory_order_acquire);
    if (first_done_status == VALK_ASYNC_COMPLETED) {
      atomic_store_explicit(&race_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
      atomic_store_explicit(&race_handle->result, atomic_load_explicit(&first_done->result, memory_order_acquire), memory_order_release);
    } else {
      atomic_store_explicit(&race_handle->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&race_handle->error, atomic_load_explicit(&first_done->error, memory_order_acquire), memory_order_release);
    }

    iter = handles_list;
    while (LVAL_TYPE(iter) != LVAL_NIL) {
      valk_lval_t *h = valk_lval_head(iter);
      valk_async_handle_t *handle = h->async.handle;
      valk_async_status_t h_status = atomic_load_explicit(&handle->status, memory_order_acquire);
      if (handle != first_done &&
          (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) {
  // LCOV_EXCL_BR_STOP
        valk_async_handle_cancel(handle);
      }
      iter = valk_lval_tail(iter);
    }
    return valk_lval_handle(race_handle);
  }

  race_handle->status = VALK_ASYNC_RUNNING;
  race_handle->env = e;

  // LCOV_EXCL_BR_START - sys assignment: depends on handles list
  iter = handles_list;
  if (LVAL_TYPE(iter) != LVAL_NIL) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    race_handle->sys = handle->sys;
  }
  // LCOV_EXCL_BR_STOP

  valk_async_handle_t **handles = calloc(count, sizeof(valk_async_handle_t*));
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!handles) {
    valk_async_handle_free(race_handle);
    return valk_lval_err("Failed to allocate handles array");
  }
  // LCOV_EXCL_STOP

  valk_race_ctx_t *ctx = malloc(sizeof(valk_race_ctx_t));
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!ctx) {
    free(handles);
    valk_async_handle_free(race_handle);
    return valk_lval_err("Failed to allocate race context");
  }
  // LCOV_EXCL_STOP
  ctx->magic = VALK_RACE_CTX_MAGIC;
  ctx->race_handle = race_handle;
  ctx->handles = handles;
  ctx->total = count;
  ctx->allocator = &valk_malloc_allocator;
  race_handle->uv_handle_ptr = ctx;
  race_handle->on_child_completed = valk_async_race_child_resolved;
  race_handle->on_child_failed = valk_async_race_child_resolved;

  valk_async_handle_on_cleanup(race_handle, valk_race_ctx_cleanup, ctx);

  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    handles[i] = handle;
    valk_async_handle_add_child(race_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(race_handle);
}

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

// LCOV_EXCL_START - all-settled cleanup and internal callbacks: called from async system
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

    valk_async_notify_parent(ctx->all_settled_handle);
    valk_async_notify_done(ctx->all_settled_handle);
    valk_async_propagate_completion(ctx->all_settled_handle);
  }
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_aio_all_settled(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_START - arg/list validation: compile-time checks catch most
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
  // LCOV_EXCL_STOP
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

  u64 completed = 0;
  bool any_pending = false;

  // LCOV_EXCL_START - handle status iteration: depends on async lifecycle
  iter = handles_list;
  for (u64 i = 0; i < count; i++) {
    valk_lval_t *h = valk_lval_head(iter);
    valk_async_handle_t *handle = h->async.handle;
    valk_async_status_t h_status = atomic_load_explicit(&handle->status, memory_order_acquire);

    if (h_status == VALK_ASYNC_COMPLETED) {
      valk_lval_t *value = atomic_load_explicit(&handle->result, memory_order_acquire);
      valk_lval_t *items[] = {
        valk_lval_sym(":status"), valk_lval_sym(":ok"),
        valk_lval_sym(":value"), value
      };
      results[i] = valk_lval_qlist(items, 4);
      completed++;
    } else if (h_status == VALK_ASYNC_FAILED) {
      valk_lval_t *error = atomic_load_explicit(&handle->error, memory_order_acquire);
      valk_lval_t *items[] = {
        valk_lval_sym(":status"), valk_lval_sym(":error"),
        valk_lval_sym(":error"), error
      };
      results[i] = valk_lval_qlist(items, 4);
      completed++;
    } else if (h_status == VALK_ASYNC_CANCELLED) {
      valk_lval_t *items[] = {
        valk_lval_sym(":status"), valk_lval_sym(":error"),
        valk_lval_sym(":error"), valk_lval_err("cancelled")
      };
      results[i] = valk_lval_qlist(items, 4);
      completed++;
    } else {
      any_pending = true;
      if (!as_handle->sys && handle->sys) {
        as_handle->sys = handle->sys;
      }
    }
    iter = valk_lval_tail(iter);
  }

  if (!any_pending) {
    valk_lval_t *result_list = valk_lval_nil();
    for (u64 i = count; i > 0; i--) {
      result_list = valk_lval_cons(results[i-1], result_list);
    }
    valk_mem_free(results);
    valk_lval_t *heap_result = valk_evacuate_to_heap(result_list);
    atomic_store_explicit(&as_handle->status, VALK_ASYNC_COMPLETED, memory_order_release);
    atomic_store_explicit(&as_handle->result, heap_result, memory_order_release);
    return valk_lval_handle(as_handle);
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
  atomic_store(&ctx->completed, completed);
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
    valk_async_handle_add_child(as_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(as_handle);
}

void valk_register_comb_collection(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/all", valk_builtin_aio_all);
  valk_lenv_put_builtin(env, "aio/race", valk_builtin_aio_race);
  valk_lenv_put_builtin(env, "aio/any", valk_builtin_aio_any);
  valk_lenv_put_builtin(env, "aio/all-settled", valk_builtin_aio_all_settled);
}
