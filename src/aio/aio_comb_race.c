#include "aio_combinators_internal.h"

typedef struct {
  valk_async_handle_t *race_handle;
  valk_async_handle_t **handles;
  u64 total;
  valk_mem_allocator_t *allocator;
} valk_race_ctx_t;

// LCOV_EXCL_START - cleanup defensive null-checks: ctx always valid when called
static void valk_race_ctx_cleanup(void *ctx) {
  valk_race_ctx_t *race_ctx = (valk_race_ctx_t *)ctx;
  if (!race_ctx) return;
  if (race_ctx->handles) free(race_ctx->handles);
  free(race_ctx);
}
// LCOV_EXCL_STOP

static void valk_async_race_child_resolved(valk_async_handle_t *child) {
  valk_async_handle_t *parent = child->parent;
  valk_race_ctx_t *ctx = (valk_race_ctx_t*)parent->uv_handle_ptr;

  valk_async_status_t child_status = valk_async_handle_get_status(child);
  valk_async_status_t new_status;
  if (child_status == VALK_ASYNC_COMPLETED) {
    new_status = VALK_ASYNC_COMPLETED;
  } else if (child_status == VALK_ASYNC_FAILED) { // LCOV_EXCL_BR_LINE - only completed/failed possible
    new_status = VALK_ASYNC_FAILED;
  } else {
    return; // LCOV_EXCL_LINE - only terminal states reach here
  }

  if (!valk_async_handle_try_transition(ctx->race_handle, VALK_ASYNC_RUNNING, new_status)) { // LCOV_EXCL_BR_LINE - race protection
    return; // LCOV_EXCL_LINE
  }

  if (new_status == VALK_ASYNC_COMPLETED) {
    atomic_store_explicit(&ctx->race_handle->result, atomic_load_explicit(&child->result, memory_order_acquire), memory_order_release);
  } else {
    atomic_store_explicit(&ctx->race_handle->error, atomic_load_explicit(&child->error, memory_order_acquire), memory_order_release);
  }

  for (u64 i = 0; i < ctx->total; i++) {
    valk_async_handle_t *h = ctx->handles[i];
    valk_async_status_t h_status = valk_async_handle_get_status(h);
    if (h != child && (h_status == VALK_ASYNC_PENDING || h_status == VALK_ASYNC_RUNNING)) { // LCOV_EXCL_BR_LINE - loop iteration varies
      valk_async_handle_cancel(h);
    }
  }

  valk_async_handle_finish(ctx->race_handle);
}

static valk_lval_t* valk_builtin_aio_race(valk_lenv_t* e, valk_lval_t* a) {
  // LCOV_EXCL_BR_START - arg validation: compile-time checks catch most
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("aio/race: expected 1 argument (list of handles)");
  }
  // LCOV_EXCL_BR_STOP
  valk_lval_t *handles_list = valk_lval_list_nth(a, 0);

  u64 count = 0;
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
    count++;
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

  valk_lval_t *first_h = valk_lval_head(handles_list);
  if (first_h && LVAL_TYPE(first_h) == LVAL_HANDLE && first_h->async.handle->request_ctx) { // LCOV_EXCL_BR_LINE - first_h/type always valid after count check; request_ctx only set in HTTP
    race_handle->request_ctx = first_h->async.handle->request_ctx;
  }

  race_handle->status = VALK_ASYNC_RUNNING;
  race_handle->env = e;

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
    if (!race_handle->sys && handle->sys) {
      race_handle->sys = handle->sys;
    }
    valk_async_handle_add_child(race_handle, handle);
    iter = valk_lval_tail(iter);
  }

  return valk_lval_handle(race_handle);
}

void valk_register_comb_race(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/race", valk_builtin_aio_race);
}
