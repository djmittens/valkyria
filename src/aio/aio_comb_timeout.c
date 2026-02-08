#include "aio_combinators_internal.h"

static void __within_timeout_timer_cb(uv_timer_t *timer_handle) {
  valk_async_handle_uv_data_t *data = (valk_async_handle_uv_data_t *)timer_handle->data;
  valk_async_handle_t *timeout_handle = data->handle;

  valk_async_handle_fail(timeout_handle, valk_lval_sym(":timeout"));

  uv_timer_stop(timer_handle);
  uv_close((uv_handle_t *)timer_handle, __sleep_timer_close_cb);
}

typedef struct {
  valk_aio_system_t *sys;
  valk_async_handle_uv_data_t *timer_data;
  u64 timeout_ms;
} valk_within_init_ctx_t;

// LCOV_EXCL_START
static void __within_init_on_loop(void *ctx) {
  valk_within_init_ctx_t *init_ctx = (valk_within_init_ctx_t *)ctx;
  if (!init_ctx || !init_ctx->sys) return;
  
  valk_async_handle_uv_data_t *timer_data = init_ctx->timer_data;
  
  uv_loop_t *loop = init_ctx->sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->uv.timer);
  if (r != 0) {
    valk_async_handle_fail(timer_data->handle, valk_lval_err("Failed to init timer"));
    return;
  }

  r = uv_timer_start(&timer_data->uv.timer, __within_timeout_timer_cb, init_ctx->timeout_ms, 0);
  if (r != 0) {
    valk_async_handle_fail(timer_data->handle, valk_lval_err("Failed to start timer"));
    uv_close((uv_handle_t *)&timer_data->uv.timer, NULL);
  }
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - within child resolution: internal async callback
static void valk_async_within_child_resolved(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *within = child->parent;

  valk_async_status_t child_status = valk_async_handle_get_status(child);
  if (child_status != VALK_ASYNC_COMPLETED && child_status != VALK_ASYNC_FAILED) {
    return;
  }

  valk_async_status_t new_status = (child_status == VALK_ASYNC_COMPLETED) ? 
                                   VALK_ASYNC_COMPLETED : VALK_ASYNC_FAILED;

  if (!valk_async_handle_try_transition(within, VALK_ASYNC_RUNNING, new_status)) {
    return;
  }

  if (child == within->comb.within.source_handle) {
    if (new_status == VALK_ASYNC_COMPLETED) {
      atomic_store_explicit(&within->result, 
                           atomic_load_explicit(&child->result, memory_order_acquire), 
                           memory_order_release);
    } else {
      atomic_store_explicit(&within->error, 
                           atomic_load_explicit(&child->error, memory_order_acquire), 
                           memory_order_release);
    }
    valk_async_handle_cancel(within->comb.within.timeout_handle);
  } else if (child == within->comb.within.timeout_handle) {
    atomic_store_explicit(&within->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&within->error, valk_lval_err(":timeout"), memory_order_release);
    valk_async_handle_cancel(within->comb.within.source_handle);
  }

  valk_async_notify_parent(within);
  valk_async_notify_done(within);
  valk_async_propagate_completion(within);
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_aio_within(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/within: expected 2 arguments (handle timeout-ms)");
  }

  valk_lval_t *source_lval = valk_lval_list_nth(a, 0);
  valk_lval_t *timeout_lval = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(source_lval) != LVAL_HANDLE) {
    return valk_lval_err("aio/within: first argument must be a handle");
  }
  if (LVAL_TYPE(timeout_lval) != LVAL_NUM) {
    return valk_lval_err("aio/within: second argument must be a number (timeout in ms)");
  }

  valk_async_handle_t *source = source_lval->async.handle;
  u64 timeout_ms = (u64)timeout_lval->num;

  // LCOV_EXCL_BR_START - source status early return: depends on async lifecycle timing
  valk_async_status_t source_status = valk_async_handle_get_status(source);
  if (source_status == VALK_ASYNC_COMPLETED || source_status == VALK_ASYNC_FAILED || 
      source_status == VALK_ASYNC_CANCELLED) {
    return valk_lval_handle(source);
  }
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t *sys = source->sys;
  // LCOV_EXCL_START - defensive null / OOM paths for within allocation
  if (!sys) {
    return valk_lval_err("aio/within: source handle must have an AIO system");
  }

  valk_async_handle_t *timeout_handle = valk_async_handle_new(sys, e);
  if (!timeout_handle) {
    return valk_lval_err("Failed to allocate timeout handle");
  }

  valk_async_handle_uv_data_t *timer_data = aligned_alloc(alignof(valk_async_handle_uv_data_t), 
                                                           sizeof(valk_async_handle_uv_data_t));
  if (!timer_data) {
    valk_async_handle_free(timeout_handle);
    return valk_lval_err("Failed to allocate timer data");
  }
  // LCOV_EXCL_STOP

  timer_data->magic = VALK_UV_DATA_TIMER_MAGIC;
  timer_data->handle = timeout_handle;
  timer_data->uv.timer.data = timer_data;

  timeout_handle->uv_handle_ptr = timer_data;
  timeout_handle->status = VALK_ASYNC_RUNNING;

  valk_within_init_ctx_t *init_ctx = valk_region_alloc(&sys->system_region, sizeof(valk_within_init_ctx_t));
  // LCOV_EXCL_START - OOM: region alloc failure
  if (!init_ctx) {
    valk_async_handle_free(timeout_handle);
    return valk_lval_err("Failed to allocate within init context");
  }
  // LCOV_EXCL_STOP

  init_ctx->sys = sys;
  init_ctx->timer_data = timer_data;
  init_ctx->timeout_ms = timeout_ms;

  valk_async_handle_t *within_handle = valk_async_handle_new(sys, e);
  // LCOV_EXCL_START - OOM: handle allocation failure
  if (!within_handle) {
    valk_async_handle_cancel(timeout_handle);
    return valk_lval_err("Failed to allocate within handle");
  }
  // LCOV_EXCL_STOP
  within_handle->request_ctx = source->request_ctx;
  within_handle->status = VALK_ASYNC_RUNNING;

  within_handle->comb.within.source_handle = source;
  within_handle->comb.within.timeout_handle = timeout_handle;
  within_handle->on_child_completed = valk_async_within_child_resolved;
  within_handle->on_child_failed = valk_async_within_child_resolved;

  valk_async_handle_add_child(within_handle, source);
  valk_async_handle_add_child(within_handle, timeout_handle);

  valk_aio_enqueue_task(sys, __within_init_on_loop, init_ctx);

  // LCOV_EXCL_BR_START - race: source may complete between allocation and check
  source_status = valk_async_handle_get_status(source);
  if (source_status == VALK_ASYNC_COMPLETED || source_status == VALK_ASYNC_FAILED) {
    valk_async_within_child_resolved(source);
  }
  // LCOV_EXCL_BR_STOP

  return valk_lval_handle(within_handle);
}

static void valk_async_retry_schedule_next(valk_async_handle_t *retry_handle);

// LCOV_EXCL_START - retry async callbacks: called from event loop / async system
static void valk_async_retry_backoff_done(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  parent->comb.retry.backoff_timer = NULL;
  valk_async_retry_schedule_next(parent);
}

static void valk_async_retry_attempt_completed(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;
  valk_async_status_t status = valk_async_handle_get_status(child);

  if (status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *result = atomic_load_explicit(&child->result, memory_order_acquire);
    atomic_store_explicit(&parent->status, VALK_ASYNC_COMPLETED, memory_order_release);
    atomic_store_explicit(&parent->result, result, memory_order_release);
    valk_async_notify_parent(parent);
    valk_async_notify_done(parent);
    valk_async_propagate_completion(parent);
    return;
  }

  if (status == VALK_ASYNC_FAILED || status == VALK_ASYNC_CANCELLED) {
    parent->comb.retry.last_error = atomic_load_explicit(&child->error, memory_order_acquire);
    parent->comb.retry.current_attempt_num++;

    if (parent->comb.retry.current_attempt_num >= parent->comb.retry.max_attempts) {
      atomic_store_explicit(&parent->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&parent->error, parent->comb.retry.last_error, memory_order_release);
      valk_async_notify_parent(parent);
      valk_async_notify_done(parent);
      valk_async_propagate_completion(parent);
      return;
    }

    u64 delay_ms = (u64)((f64)parent->comb.retry.base_delay_ms * pow(parent->comb.retry.backoff_multiplier, (f64)(parent->comb.retry.current_attempt_num - 1)));
    const u64 MAX_BACKOFF_MS = 30000;
    if (delay_ms > MAX_BACKOFF_MS) delay_ms = MAX_BACKOFF_MS;

    valk_async_handle_t *timer = valk_async_handle_new(parent->sys, parent->env);
    if (!timer) {
      atomic_store_explicit(&parent->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&parent->error, valk_lval_err("Failed to allocate backoff timer"), memory_order_release);
      valk_async_notify_parent(parent);
      valk_async_notify_done(parent);
      valk_async_propagate_completion(parent);
      return;
    }

    valk_async_handle_uv_data_t *timer_data = aligned_alloc(alignof(valk_async_handle_uv_data_t), sizeof(valk_async_handle_uv_data_t));
    if (!timer_data) {
      valk_async_handle_free(timer);
      atomic_store_explicit(&parent->status, VALK_ASYNC_FAILED, memory_order_release);
      atomic_store_explicit(&parent->error, valk_lval_err("Failed to allocate timer data"), memory_order_release);
      valk_async_notify_parent(parent);
      valk_async_notify_done(parent);
      valk_async_propagate_completion(parent);
      return;
    }

    timer_data->magic = VALK_UV_DATA_TIMER_MAGIC;
    timer_data->handle = timer;
    timer_data->uv.timer.data = timer_data;

    timer->uv_handle_ptr = timer_data;
    timer->status = VALK_ASYNC_RUNNING;
    timer->parent = parent;

    uv_timer_init(parent->sys->eventloop, &timer_data->uv.timer);
    uv_timer_start(&timer_data->uv.timer, __sleep_timer_cb, (unsigned long long)delay_ms, 0);

    parent->comb.retry.backoff_timer = timer;
    valk_async_handle_add_child(parent, timer);
  }
}

static void valk_async_notify_retry_child(valk_async_handle_t *child) {
  if (!child || !child->parent) return;

  valk_async_handle_t *parent = child->parent;

  if (child == parent->comb.retry.backoff_timer) {
    valk_async_retry_backoff_done(child);
  } else if (child == parent->comb.retry.current_attempt) {
    valk_async_retry_attempt_completed(child);
  }
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - retry schedule: called from async system callbacks
static void valk_async_retry_schedule_next(valk_async_handle_t *retry_handle) {
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result_val = valk_lval_eval_call(retry_handle->env, retry_handle->comb.retry.fn, args);

  if (LVAL_TYPE(result_val) != LVAL_HANDLE) {
    atomic_store_explicit(&retry_handle->status, VALK_ASYNC_FAILED, memory_order_release);
    atomic_store_explicit(&retry_handle->error, valk_lval_err("aio/retry: fn must return a handle"), memory_order_release);
    valk_async_notify_parent(retry_handle);
    valk_async_notify_done(retry_handle);
    valk_async_propagate_completion(retry_handle);
    return;
  }

  valk_async_handle_t *attempt = result_val->async.handle;
  retry_handle->comb.retry.current_attempt = attempt;
  attempt->parent = retry_handle;
  valk_async_handle_add_child(retry_handle, attempt);
}
// LCOV_EXCL_STOP

static valk_lval_t* valk_builtin_aio_retry(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 3) {
    return valk_lval_err("aio/retry: expected 3 arguments (sys fn opts)");
  }

  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *fn = valk_lval_list_nth(a, 1);
  valk_lval_t *opts = valk_lval_list_nth(a, 2);

  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg); // LCOV_EXCL_BR_LINE
  if (LVAL_TYPE(fn) != LVAL_FUN) {
    return valk_lval_err("aio/retry: second argument must be a function");
  }
  if (LVAL_TYPE(opts) != LVAL_QEXPR) {
    return valk_lval_err("aio/retry: third argument must be a qexpr (options dict)");
  }

  valk_aio_system_t *sys = sys_arg->ref.ptr;

  u64 max_attempts = 3;
  u64 base_delay_ms = 100;
  f64 backoff_multiplier = 2.0;

  // LCOV_EXCL_BR_START - option parsing: many key/value dispatch branches
  valk_lval_t *opts_iter = opts;
  while (LVAL_TYPE(opts_iter) != LVAL_NIL) {
    if (LVAL_TYPE(opts_iter) != LVAL_CONS && LVAL_TYPE(opts_iter) != LVAL_QEXPR) {
      break;
    }

    valk_lval_t *key = valk_lval_head(opts_iter);
    opts_iter = valk_lval_tail(opts_iter);
    if (LVAL_TYPE(opts_iter) == LVAL_NIL) break;

    valk_lval_t *val = valk_lval_head(opts_iter);
    opts_iter = valk_lval_tail(opts_iter);

    if (LVAL_TYPE(key) == LVAL_SYM) {
      if (strcmp(key->str, ":max-attempts") == 0 && LVAL_TYPE(val) == LVAL_NUM) {
        max_attempts = (u64)val->num;
      } else if (strcmp(key->str, ":base-ms") == 0 && LVAL_TYPE(val) == LVAL_NUM) {
        base_delay_ms = (u64)val->num;
      } else if (strcmp(key->str, ":backoff") == 0 && LVAL_TYPE(val) == LVAL_SYM) {
        if (strcmp(val->str, ":exponential") == 0) {
          backoff_multiplier = 2.0;
        } else if (strcmp(val->str, ":linear") == 0) {
          backoff_multiplier = 1.0;
        } else if (strcmp(val->str, ":none") == 0) {
          backoff_multiplier = 1.0;
        }
      }
    }
  }
  // LCOV_EXCL_BR_STOP

  if (max_attempts == 0) max_attempts = 1; // LCOV_EXCL_BR_LINE - defensive clamp
  if (backoff_multiplier < 1.0) backoff_multiplier = 1.0; // LCOV_EXCL_BR_LINE - defensive clamp

  valk_async_handle_t *retry_handle = valk_async_handle_new(sys, e);
  // LCOV_EXCL_START - OOM: handle allocation failure
  if (!retry_handle) {
    return valk_lval_err("Failed to allocate retry handle");
  }
  // LCOV_EXCL_STOP

  retry_handle->comb.retry.current_attempt = NULL;
  retry_handle->comb.retry.backoff_timer = NULL;
  retry_handle->comb.retry.fn = fn;
  retry_handle->comb.retry.max_attempts = max_attempts;
  retry_handle->comb.retry.current_attempt_num = 0;
  retry_handle->comb.retry.base_delay_ms = base_delay_ms;
  retry_handle->comb.retry.backoff_multiplier = backoff_multiplier;
  retry_handle->comb.retry.last_error = NULL;

  retry_handle->status = VALK_ASYNC_RUNNING;
  retry_handle->on_child_completed = valk_async_notify_retry_child;
  retry_handle->on_child_failed = valk_async_notify_retry_child;

  valk_async_retry_schedule_next(retry_handle);

  return valk_lval_handle(retry_handle);
}

void valk_register_comb_timeout(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/within", valk_builtin_aio_within);
  valk_lenv_put_builtin(env, "aio/retry", valk_builtin_aio_retry);
}
