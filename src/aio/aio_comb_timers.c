#include "aio_combinators_internal.h"

extern void valk_async_handle_on_resource_cleanup(valk_async_handle_t *handle, void (*fn)(void *data, void *ctx), void *data, void *ctx);

#include "aio_async.h"

static void __schedule_timer_close_cb(uv_handle_t *handle) {
  valk_schedule_timer_t *timer_data = (valk_schedule_timer_t *)handle->data;
  if (timer_data) { // LCOV_EXCL_BR_LINE - timer_data always set before uv_timer_start
    timer_data->async_handle = NULL;
  }
}

static u64 g_interval_id = 1;

static void __interval_timer_close_cb(uv_handle_t *handle) {
  valk_interval_timer_t *timer_data = (valk_interval_timer_t *)handle->data;
  if (!timer_data) return; // LCOV_EXCL_BR_LINE - timer_data always set before uv_timer_start

  if (timer_data->callback) { // LCOV_EXCL_BR_LINE - callback always set at init
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
  }
}

// LCOV_EXCL_START - cleanup function: defensive checks for timer state
static void __interval_cleanup(void *data, void *ctx) {
  UNUSED(ctx);
  valk_interval_timer_t *timer_data = (valk_interval_timer_t *)data;
  if (!timer_data || timer_data->stopped) return;
  timer_data->stopped = true;
  if (!timer_data->timer.loop) return;
  if (uv_is_closing((uv_handle_t *)&timer_data->timer)) return;
  uv_timer_stop(&timer_data->timer);
  uv_close((uv_handle_t *)&timer_data->timer, __interval_timer_close_cb);
  if (timer_data->async_handle) {
    timer_data->async_handle->uv_handle_ptr = NULL;
  }
}
// LCOV_EXCL_STOP

static void __interval_timer_cb(uv_timer_t *handle) {
  VALK_GC_SAFE_POINT();

  if (uv_is_closing((uv_handle_t *)handle)) return; // LCOV_EXCL_BR_LINE - callback only fires when active

  valk_interval_timer_t *timer_data = (valk_interval_timer_t *)handle->data;
  if (!timer_data || timer_data->stopped) return; // LCOV_EXCL_BR_LINE - timer_data always set; stopped checked before start

  bool cancelled = false;
  if (timer_data->async_handle) { // LCOV_EXCL_BR_LINE - async_handle always set at init
    valk_async_status_t status = valk_async_handle_get_status(timer_data->async_handle);
    cancelled = (status == VALK_ASYNC_CANCELLED);
  }

  // LCOV_EXCL_START - cancel detection during tick: race with cleanup stopping timer first
  if (cancelled) {
    timer_data->stopped = true;
    uv_timer_stop(handle);
    if (!uv_is_closing((uv_handle_t *)handle)) {
      uv_close((uv_handle_t *)handle, __interval_timer_close_cb);
    }
    if (timer_data->async_handle) {
      timer_data->async_handle->uv_handle_ptr = NULL;
    }
    return;
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START - callback resolved via handle table; GC can't collect while handle table holds ref
  valk_lval_t *callback = valk_handle_resolve(&valk_sys->handle_table, timer_data->callback_handle);
  if (!callback) {
    timer_data->stopped = true;
    uv_timer_stop(handle);
    if (!uv_is_closing((uv_handle_t *)handle)) {
      uv_close((uv_handle_t *)handle, __interval_timer_close_cb);
    }
    if (timer_data->async_handle) {
      timer_data->async_handle->uv_handle_ptr = NULL;
      valk_async_handle_complete(timer_data->async_handle, valk_lval_nil());
    }
    return;
  }
  // LCOV_EXCL_STOP
  valk_lval_t *args = valk_lval_nil();
  valk_lval_t *result = valk_lval_eval_call(callback->fun.env, callback, args);

  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_WARN("aio/interval callback returned error: %s", result->str);
  }

  if (LVAL_TYPE(result) == LVAL_SYM && strcmp(result->str, ":stop") == 0) {
    timer_data->stopped = true;
    uv_timer_stop(handle);
    if (!uv_is_closing((uv_handle_t *)handle)) { // LCOV_EXCL_BR_LINE - just stopped, not closing
      uv_close((uv_handle_t *)handle, __interval_timer_close_cb);
    }
    if (timer_data->async_handle) { // LCOV_EXCL_BR_LINE - always set
      timer_data->async_handle->uv_handle_ptr = NULL;
      valk_async_handle_complete(timer_data->async_handle, valk_lval_nil());
    }
  }
}

typedef struct {
  valk_aio_system_t *sys;
  valk_interval_timer_t *timer_data;
  u64 interval_ms;
} valk_interval_init_ctx_t;

static void __interval_init_on_loop(void *ctx) {
  valk_interval_init_ctx_t *init_ctx = (valk_interval_init_ctx_t *)ctx;
  if (!init_ctx || !init_ctx->sys) return; // LCOV_EXCL_BR_LINE - init_ctx always valid from region alloc
  
  valk_interval_timer_t *timer_data = init_ctx->timer_data;

  if (timer_data->stopped) return; // LCOV_EXCL_BR_LINE - race between cleanup and init
  
  uv_loop_t *loop = init_ctx->sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->timer);
  // LCOV_EXCL_START - uv_timer_init rarely fails
  if (r != 0) {
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
    return;
  }
  // LCOV_EXCL_STOP

  r = uv_timer_start(&timer_data->timer, __interval_timer_cb, init_ctx->interval_ms, init_ctx->interval_ms);
  // LCOV_EXCL_START - uv_timer_start rarely fails
  if (r != 0) {
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
    uv_close((uv_handle_t *)&timer_data->timer, NULL);
  }
  // LCOV_EXCL_STOP
}

extern valk_lval_t* valk_lval_copy(valk_lval_t* lval);

valk_lval_t* valk_aio_interval(valk_aio_system_t* sys, u64 interval_ms,
                                valk_lval_t* callback, valk_lenv_t* env) {
  UNUSED(env);
  if (!sys || !sys->eventloop) { // LCOV_EXCL_BR_LINE - sys always valid after LVAL_ASSERT_AIO_SYSTEM
    return valk_lval_err("aio/interval: invalid AIO system"); // LCOV_EXCL_LINE
  }

  valk_interval_timer_t *timer_data = valk_region_alloc(&sys->system_region, sizeof(valk_interval_timer_t));
  // LCOV_EXCL_START - region alloc failure: requires OOM
  if (!timer_data) {
    return valk_lval_err("Failed to allocate interval timer");
  }
  // LCOV_EXCL_STOP
  memset(timer_data, 0, sizeof(valk_interval_timer_t));

  valk_async_handle_t *async_handle = valk_async_handle_new(sys, env);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!async_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP
  async_handle->status = VALK_ASYNC_RUNNING;

  valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);
  
  timer_data->magic = VALK_INTERVAL_TIMER_MAGIC;
  timer_data->callback = heap_callback;
  timer_data->callback_handle = valk_handle_create(&valk_sys->handle_table, heap_callback);
  timer_data->interval_id = __atomic_fetch_add(&g_interval_id, 1, __ATOMIC_RELAXED);
  timer_data->stopped = false;
  timer_data->async_handle = async_handle;
  timer_data->timer.data = timer_data;

  async_handle->uv_handle_ptr = timer_data;

  valk_async_handle_on_resource_cleanup(async_handle, __interval_cleanup, timer_data, NULL);
  VALK_ASSERT_HAS_CLEANUP(async_handle);

  valk_interval_init_ctx_t *init_ctx = valk_region_alloc(&sys->system_region, sizeof(valk_interval_init_ctx_t));
  // LCOV_EXCL_START - region alloc failure: requires OOM
  if (!init_ctx) {
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
    return valk_lval_err("Failed to allocate interval init context");
  }
  // LCOV_EXCL_STOP
  
  init_ctx->sys = sys;
  init_ctx->timer_data = timer_data;
  init_ctx->interval_ms = interval_ms;
  
  valk_aio_enqueue_task(sys, __interval_init_on_loop, init_ctx);

  return valk_lval_handle(async_handle);
}

// LCOV_EXCL_START - cleanup function: defensive checks for timer state
static void __schedule_cleanup(void *data, void *ctx) {
  UNUSED(ctx);
  valk_schedule_timer_t *timer_data = (valk_schedule_timer_t *)data;
  if (!timer_data) return;
  if (!timer_data->timer.loop) return;
  if (uv_is_closing((uv_handle_t *)&timer_data->timer)) return;
  if (uv_is_active((uv_handle_t *)&timer_data->timer)) {
    uv_timer_stop(&timer_data->timer);
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
    uv_close((uv_handle_t *)&timer_data->timer, __schedule_timer_close_cb);
    if (timer_data->async_handle) {
      timer_data->async_handle->uv_handle_ptr = NULL;
    }
  }
}
// LCOV_EXCL_STOP

static void __schedule_timer_cb(uv_timer_t *handle) {
  VALK_GC_SAFE_POINT();
  
  valk_schedule_timer_t *timer_data = (valk_schedule_timer_t *)handle->data;
  
  bool cancelled = false;
  if (timer_data->async_handle) { // LCOV_EXCL_BR_LINE - always set at init
    valk_async_status_t status = valk_async_handle_get_status(timer_data->async_handle);
    cancelled = (status == VALK_ASYNC_CANCELLED);
  }
  
  valk_lval_t *cb_result = valk_lval_nil();
  if (!cancelled) { // LCOV_EXCL_BR_LINE - schedule cancel: race between cancel and one-shot timer fire
    valk_lval_t *callback = valk_handle_resolve(&valk_sys->handle_table, timer_data->callback_handle);
    if (callback) { // LCOV_EXCL_BR_LINE - handle table holds ref, GC can't collect
      valk_lval_t *args = valk_lval_nil();
      cb_result = valk_lval_eval_call(callback->fun.env, callback, args);
      if (LVAL_TYPE(cb_result) == LVAL_ERR) {
        VALK_WARN("aio/schedule callback returned error: %s", cb_result->str);
      }
    }
  }

  valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
  uv_timer_stop(handle);
  if (!uv_is_closing((uv_handle_t *)handle)) { // LCOV_EXCL_BR_LINE - just stopped, not closing
    uv_close((uv_handle_t *)handle, __schedule_timer_close_cb);
  }

  if (timer_data->async_handle) { // LCOV_EXCL_BR_LINE - always set at init
    timer_data->async_handle->uv_handle_ptr = NULL;
    valk_async_handle_complete(timer_data->async_handle, cb_result);
  }
}

typedef struct {
  valk_aio_system_t *sys;
  valk_schedule_timer_t *timer_data;
  u64 delay_ms;
} valk_schedule_init_ctx_t;

static void __schedule_init_on_loop(void *ctx) {
  valk_schedule_init_ctx_t *init_ctx = (valk_schedule_init_ctx_t *)ctx;
  if (!init_ctx || !init_ctx->sys) return; // LCOV_EXCL_BR_LINE - init_ctx always valid from region alloc
  
  valk_schedule_timer_t *timer_data = init_ctx->timer_data;

  if (timer_data->async_handle && // LCOV_EXCL_BR_LINE - race between cancel and init
      valk_async_handle_is_terminal(valk_async_handle_get_status(timer_data->async_handle))) return;
  
  uv_loop_t *loop = init_ctx->sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->timer);
  // LCOV_EXCL_START - uv_timer_init rarely fails
  if (r != 0) {
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
    return;
  }
  // LCOV_EXCL_STOP

  r = uv_timer_start(&timer_data->timer, __schedule_timer_cb, init_ctx->delay_ms, 0);
  // LCOV_EXCL_START - uv_timer_start rarely fails
  if (r != 0) {
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
    uv_close((uv_handle_t *)&timer_data->timer, NULL);
  }
  // LCOV_EXCL_STOP
}

static _Atomic(u64) g_schedule_id = 0;

extern valk_async_handle_t* valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern valk_lval_t *valk_lval_handle(valk_async_handle_t *handle);

valk_lval_t* valk_aio_schedule(valk_aio_system_t* sys, u64 delay_ms,
                                valk_lval_t* callback, valk_lenv_t* env) {
  if (!sys || !sys->eventloop) { // LCOV_EXCL_BR_LINE - sys always valid after LVAL_ASSERT_AIO_SYSTEM
    return valk_lval_err("aio/schedule: invalid AIO system"); // LCOV_EXCL_LINE
  }

  u64 schedule_id = atomic_fetch_add(&g_schedule_id, 1);

  valk_schedule_timer_t *timer_data = valk_region_alloc(&sys->system_region, sizeof(valk_schedule_timer_t));
  // LCOV_EXCL_START - region alloc failure: requires OOM
  if (!timer_data) {
    return valk_lval_err("Failed to allocate timer");
  }
  // LCOV_EXCL_STOP
  memset(timer_data, 0, sizeof(valk_schedule_timer_t));

  valk_async_handle_t *async_handle = valk_async_handle_new(sys, env);
  // LCOV_EXCL_START - allocation failure: requires OOM
  if (!async_handle) {
    return valk_lval_err("Failed to allocate async handle");
  }
  // LCOV_EXCL_STOP
  async_handle->status = VALK_ASYNC_RUNNING;

  valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);

  timer_data->callback = heap_callback;
  timer_data->callback_handle = valk_handle_create(&valk_sys->handle_table, heap_callback);
  timer_data->timer.data = timer_data;
  timer_data->schedule_id = schedule_id;
  timer_data->async_handle = async_handle;

  valk_async_handle_on_resource_cleanup(async_handle, __schedule_cleanup, timer_data, NULL);
  VALK_ASSERT_HAS_CLEANUP(async_handle);

  valk_schedule_init_ctx_t *init_ctx = valk_region_alloc(&sys->system_region, sizeof(valk_schedule_init_ctx_t));
  // LCOV_EXCL_START - region alloc failure: requires OOM
  if (!init_ctx) {
    valk_handle_release(&valk_sys->handle_table, timer_data->callback_handle);
    return valk_lval_err("Failed to allocate schedule init context");
  }
  // LCOV_EXCL_STOP
  
  init_ctx->sys = sys;
  init_ctx->timer_data = timer_data;
  init_ctx->delay_ms = delay_ms;
  
  valk_aio_enqueue_task(sys, __schedule_init_on_loop, init_ctx);

  return valk_lval_handle(async_handle);
}

typedef struct {
  valk_aio_system_t *sys;
  valk_async_handle_uv_data_t *timer_data;
  u64 delay_ms;
} valk_sleep_init_ctx_t;

// LCOV_EXCL_START - cleanup function: defensive checks for timer state
static void __sleep_cleanup(void *data, void *ctx) {
  UNUSED(ctx);
  valk_async_handle_uv_data_t *timer_data = (valk_async_handle_uv_data_t *)data;
  if (!timer_data) return;
  if (!timer_data->uv.timer.loop) return;
  if (uv_is_closing((uv_handle_t *)&timer_data->uv.timer)) return;
  if (uv_is_active((uv_handle_t *)&timer_data->uv.timer)) {
    uv_timer_stop(&timer_data->uv.timer);
  }
  uv_close((uv_handle_t *)&timer_data->uv.timer, __sleep_timer_close_cb);
}
// LCOV_EXCL_STOP

static void __sleep_init_on_loop(void *ctx) {
  valk_sleep_init_ctx_t *init_ctx = (valk_sleep_init_ctx_t *)ctx;
  if (!init_ctx || !init_ctx->sys) return; // LCOV_EXCL_BR_LINE - init_ctx always valid from region alloc
  
  valk_async_handle_uv_data_t *timer_data = init_ctx->timer_data;

  if (valk_async_handle_is_terminal(valk_async_handle_get_status(timer_data->handle))) { // LCOV_EXCL_BR_LINE - race between cancel and init
    free(timer_data); // LCOV_EXCL_LINE
    return; // LCOV_EXCL_LINE
  }
  
  uv_loop_t *loop = init_ctx->sys->eventloop;
  int r = uv_timer_init(loop, &timer_data->uv.timer);
  // LCOV_EXCL_START - uv_timer_init rarely fails
  if (r != 0) {
    valk_async_handle_fail(timer_data->handle, valk_lval_err("Failed to init timer"));
    return;
  }
  // LCOV_EXCL_STOP

  r = uv_timer_start(&timer_data->uv.timer, __sleep_timer_cb, init_ctx->delay_ms, 0);
  // LCOV_EXCL_START - uv_timer_start rarely fails
  if (r != 0) {
    valk_async_handle_fail(timer_data->handle, valk_lval_err("Failed to start timer"));
    uv_close((uv_handle_t *)&timer_data->uv.timer, NULL);
  }
  // LCOV_EXCL_STOP
}



static valk_lval_t* valk_builtin_aio_sleep(valk_lenv_t* e, valk_lval_t* a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("aio/sleep: expected 2 arguments (sys ms)");
  }
  valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
  valk_lval_t *ms_arg = valk_lval_list_nth(a, 1);

  LVAL_ASSERT_AIO_SYSTEM(a, sys_arg);
  if (LVAL_TYPE(ms_arg) != LVAL_NUM) {
    return valk_lval_err("aio/sleep: second argument must be a number");
  }

  valk_request_ctx_t *req_ctx = valk_thread_ctx.request_ctx;
  // LCOV_EXCL_BR_START - request_ctx deadline: only set in HTTP request handling
  if (req_ctx && valk_request_ctx_deadline_exceeded(req_ctx)) {
    return valk_lval_err(":deadline-exceeded");
  }
  // LCOV_EXCL_BR_STOP

  valk_aio_system_t *sys = sys_arg->ref.ptr;
  u64 delay_ms = (u64)ms_arg->num;

  // LCOV_EXCL_BR_START - request_ctx deadline: only set in HTTP request handling
  if (req_ctx && valk_request_ctx_has_deadline(req_ctx)) {
    u64 remaining_ms = valk_request_ctx_remaining_ms(req_ctx);
    if (delay_ms > remaining_ms) {
      delay_ms = remaining_ms;
    }
  }
  // LCOV_EXCL_BR_STOP

  valk_async_handle_t *async_handle = valk_async_handle_new(sys, e);
  async_handle->request_ctx = req_ctx;

  valk_async_handle_uv_data_t *timer_data = aligned_alloc(alignof(valk_async_handle_uv_data_t), sizeof(valk_async_handle_uv_data_t));
  memset(timer_data, 0, sizeof(valk_async_handle_uv_data_t));
  timer_data->magic = VALK_UV_DATA_TIMER_MAGIC;
  timer_data->handle = async_handle;
  timer_data->uv.timer.data = timer_data;

  async_handle->uv_handle_ptr = timer_data;
  async_handle->status = VALK_ASYNC_RUNNING;

  valk_async_handle_on_resource_cleanup(async_handle, __sleep_cleanup, timer_data, NULL);
  VALK_ASSERT_HAS_CLEANUP(async_handle);

  valk_sleep_init_ctx_t *init_ctx = valk_region_alloc(&sys->system_region, sizeof(valk_sleep_init_ctx_t));
  // LCOV_EXCL_START - region alloc failure: requires OOM
  if (!init_ctx) {
    valk_async_handle_fail(async_handle, valk_lval_err("Failed to allocate sleep init context"));
    return valk_lval_handle(async_handle);
  }
  // LCOV_EXCL_STOP

  init_ctx->sys = sys;
  init_ctx->timer_data = timer_data;
  init_ctx->delay_ms = delay_ms;

  valk_aio_enqueue_task(sys, __sleep_init_on_loop, init_ctx);

  VALK_INFO("aio/sleep started: %llu ms, handle id=%llu", (unsigned long long)delay_ms, (unsigned long long)async_handle->id);

  return valk_lval_handle(async_handle);
}

void valk_register_comb_timers(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "aio/sleep", valk_builtin_aio_sleep);
}
