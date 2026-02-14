#include "aio_internal.h"
#include "aio_http2_session.h"
#include "aio_request_ctx.h"

extern u64 g_async_handle_id;

extern void valk_http2_continue_pending_send(valk_aio_handle_t *conn);

extern void valk_async_propagate_completion(valk_async_handle_t *source);
extern void valk_async_notify_parent(valk_async_handle_t *child);

void valk_async_handle_run_resource_cleanups(valk_async_handle_t *handle);

// LCOV_EXCL_BR_START - async callback defensive null checks
void valk_http_async_done_callback(valk_async_handle_t *handle, void *ctx) {
  if (!ctx) return;
  valk_http_async_ctx_t *http = (valk_http_async_ctx_t*)ctx;

  valk_aio_handle_t *conn = http->conn;
  valk_mem_arena_t *arena = http->arena;
  nghttp2_session *session = (nghttp2_session*)http->session;
  i32 stream_id = http->stream_id;

  if (!conn || conn->http.state == VALK_CONN_CLOSING ||
      conn->http.state == VALK_CONN_CLOSED || !conn->http.session) {
    VALK_INFO("Async handle %llu: connection closed, skipping HTTP response for stream %d",
              handle->id, stream_id);
    return;
  }

  if (http->stream_response) {
    VALK_DEBUG("Async handle %llu: stream response already sent for stream %d, skipping",
               handle->id, stream_id);
    return;
  }

  valk_async_status_t done_status = valk_async_handle_get_status(handle);
  if (done_status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *result = atomic_load_explicit(&handle->result, memory_order_acquire);
    if (LVAL_TYPE(result) == LVAL_SYM && strcmp(result->str, ":closed") == 0) {
      return;
    }
    if (LVAL_TYPE(result) == LVAL_ERR) {
      VALK_WARN("Handle completed with error for stream %d: %s", stream_id, result->str);
      VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
        valk_lval_t* error_items[] = {
          valk_lval_sym(":status"), valk_lval_str("500"),
          valk_lval_sym(":body"), valk_lval_str(result->str)
        };
        valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
        valk_http2_send_response(session, stream_id, error_resp, arena);
      }
    } else {
      VALK_INFO("Sending async response for stream %d", stream_id);
      valk_http2_send_response(session, stream_id, result, arena);
    }
    valk_http2_continue_pending_send(conn);
  } else if (done_status == VALK_ASYNC_FAILED) {
    valk_lval_t *err_val = atomic_load_explicit(&handle->error, memory_order_acquire);
    valk_lval_t *err = err_val ? err_val : valk_lval_err("Async operation failed");
    VALK_WARN("Handle failed for stream %d: %s",
              stream_id, LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown");
    VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
      const char *err_msg = LVAL_TYPE(err) == LVAL_ERR ? err->str : "Async operation failed";
      valk_lval_t* error_items[] = {
        valk_lval_sym(":status"), valk_lval_str("500"),
        valk_lval_sym(":body"), valk_lval_str(err_msg)
      };
      valk_lval_t* error_resp = valk_lval_qlist(error_items, 4);
      valk_http2_send_response(session, stream_id, error_resp, arena);
    }
    valk_http2_continue_pending_send(conn);
  }
  // LCOV_EXCL_BR_STOP
}

// LCOV_EXCL_START - standalone async context: used for non-HTTP async ops
void valk_standalone_async_done_callback(valk_async_handle_t *handle, void *ctx) {
  UNUSED(handle);
  if (!ctx) return;
  valk_standalone_async_ctx_t *standalone = (valk_standalone_async_ctx_t*)ctx;

  if (valk_arena_ref_valid(standalone->arena_ref) && standalone->sys && standalone->sys->httpStreamArenas) {
    VALK_DEBUG("Releasing standalone async arena back to pool");
    valk_arena_ref_release(&standalone->arena_ref, standalone->sys->httpStreamArenas);
  }
}

valk_standalone_async_ctx_t* valk_standalone_async_ctx_new(valk_aio_system_t *sys) {
  if (!sys || !sys->httpStreamArenas) return nullptr;

  valk_slab_item_t *arena_item = valk_slab_aquire(sys->httpStreamArenas);
  if (!arena_item) {
    VALK_WARN("Standalone async: failed to acquire arena from pool");
    return nullptr;
  }

  valk_mem_arena_t *arena = (valk_mem_arena_t *)arena_item->data;
  valk_mem_arena_init(arena, sys->config.arena_size);

  valk_standalone_async_ctx_t *ctx = valk_region_alloc(&sys->system_region, sizeof(valk_standalone_async_ctx_t));
  if (!ctx) {
    valk_slab_release(sys->httpStreamArenas, arena_item);
    return nullptr;
  }

  ctx->arena = arena;
  ctx->arena_ref = (valk_arena_ref_t){.slab_item = arena_item, .slot = UINT32_MAX};
  ctx->sys = sys;

  VALK_DEBUG("Allocated standalone async arena from pool");
  return ctx;
}
// LCOV_EXCL_STOP

void valk_async_notify_done(valk_async_handle_t *handle) {
  valk_async_done_fn on_done = atomic_exchange_explicit(&handle->on_done, nullptr, memory_order_acq_rel);
  if (on_done) {
    void *ctx = atomic_exchange_explicit(&handle->on_done_ctx, nullptr, memory_order_relaxed);
    on_done(handle, ctx);
  }
}

valk_async_handle_t* valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env) {
  return valk_async_handle_new_in_region(sys, env, nullptr);
}

valk_async_handle_t* valk_async_handle_new_in_region(valk_aio_system_t *sys, valk_lenv_t *env, valk_region_t *region) {
  if (!region && sys) { // LCOV_EXCL_BR_LINE - region provided directly only from internal callers
    region = &sys->system_region;
  }

  valk_async_handle_t *handle;
  if (region) {
    handle = valk_region_alloc(region, sizeof(valk_async_handle_t));
  } else {
    handle = malloc(sizeof(valk_async_handle_t));
  }
  if (!handle) return nullptr; // LCOV_EXCL_BR_LINE - OOM

  memset(handle, 0, sizeof(valk_async_handle_t));
  handle->id = __atomic_fetch_add(&g_async_handle_id, 1, __ATOMIC_RELAXED);
  atomic_store_explicit(&handle->status, VALK_ASYNC_PENDING, memory_order_release);
  atomic_store_explicit(&handle->cancel_requested, 0, memory_order_release);
  handle->refcount = 1;
  handle->sys = sys;
  handle->env = env;
  handle->region = region;

  return handle;
}

void valk_async_handle_free(valk_async_handle_t *handle) {
  if (!handle) return;
  if (handle->region) return;
  valk_chunked_ptrs_free(&handle->children);
  free(handle);
}

valk_async_handle_t *valk_async_handle_ref(valk_async_handle_t *handle) {
  if (!handle) return nullptr;
  atomic_fetch_add_explicit(&handle->refcount, 1, memory_order_relaxed);
  return handle;
}

void valk_async_handle_unref(valk_async_handle_t *handle) {
  if (!handle) return;

  u32 old = atomic_fetch_sub_explicit(&handle->refcount, 1, memory_order_acq_rel);
  if (old != 1) return;

  if (handle->cleanup_fn) {
    handle->cleanup_fn(handle->cleanup_ctx);
  }

  valk_async_handle_run_resource_cleanups(handle);

  u32 count = valk_chunked_ptrs_count(&handle->children);
  for (u32 i = 0; i < count; i++) {
    valk_async_handle_unref(valk_chunked_ptrs_get(&handle->children, i));
  }

  valk_async_handle_free(handle);
}

u32 valk_async_handle_refcount(valk_async_handle_t *handle) {
  if (!handle) return 0;
  return atomic_load_explicit(&handle->refcount, memory_order_relaxed);
}

void valk_async_handle_on_cleanup(valk_async_handle_t *handle,
                                   valk_async_cleanup_fn fn, void *ctx) {
  if (!handle || !fn) return;
  handle->cleanup_fn = fn;
  handle->cleanup_ctx = ctx;
}

void valk_async_handle_run_resource_cleanups(valk_async_handle_t *handle) {
  if (!handle || !handle->resource_cleanup_count) return; // LCOV_EXCL_BR_LINE - defensive null check
  for (i32 i = (i32)handle->resource_cleanup_count - 1; i >= 0; i--) {
    valk_async_cleanup_entry_t *entry = &handle->resource_cleanups[i];
    entry->fn(entry->data, entry->ctx);
  }
  handle->resource_cleanup_count = 0;
  free(handle->resource_cleanups);
  handle->resource_cleanups = nullptr;
  handle->resource_cleanup_capacity = 0;
}

// LCOV_EXCL_BR_START - defensive null/capacity checks
void valk_async_handle_on_resource_cleanup(valk_async_handle_t *handle,
                                           void (*fn)(void *data, void *ctx),
                                           void *data, void *ctx) {
  if (!handle || !fn) return;
  if (handle->resource_cleanup_count == handle->resource_cleanup_capacity) {
    u16 new_cap = handle->resource_cleanup_capacity ? handle->resource_cleanup_capacity * 2 : 2;
    valk_async_cleanup_entry_t *new_arr = realloc(handle->resource_cleanups,
                                                  new_cap * sizeof(valk_async_cleanup_entry_t));
    if (!new_arr) return; // LCOV_EXCL_BR_LINE - OOM
    handle->resource_cleanups = new_arr;
    handle->resource_cleanup_capacity = new_cap;
  }
  handle->resource_cleanups[handle->resource_cleanup_count++] = (valk_async_cleanup_entry_t){
    .fn = fn, .data = data, .ctx = ctx
  };
}
// LCOV_EXCL_BR_STOP

void valk_async_handle_finish(valk_async_handle_t *handle) {
  valk_async_notify_parent(handle);
  valk_async_notify_done(handle);
  valk_async_propagate_completion(handle);
  valk_async_handle_run_resource_cleanups(handle);
}

// LCOV_EXCL_BR_START - CAS transition fallback branches
static bool __reach_terminal(valk_async_handle_t *handle, valk_async_status_t new_status) {
  bool transitioned = valk_async_handle_try_transition(handle, VALK_ASYNC_PENDING, new_status);
  if (!transitioned) {
    transitioned = valk_async_handle_try_transition(handle, VALK_ASYNC_RUNNING, new_status);
  }
  if (!transitioned) return false;
// LCOV_EXCL_BR_STOP

  valk_async_handle_finish(handle);
  return true;
}

void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result) {
  if (!handle) return;

  valk_async_status_t current = valk_async_handle_get_status(handle);
  if (valk_async_handle_is_terminal(current)) return;

  atomic_store_explicit(&handle->result, result, memory_order_release);
  __reach_terminal(handle, VALK_ASYNC_COMPLETED);
}

void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error) {
  if (!handle) return;

  valk_async_status_t current = valk_async_handle_get_status(handle);
  if (valk_async_handle_is_terminal(current)) return;

  atomic_store_explicit(&handle->error, error, memory_order_release);
  __reach_terminal(handle, VALK_ASYNC_FAILED);
}

// LCOV_EXCL_START - cancel task: runs on event loop thread, requires live UV timers and GC coordination
static void valk_async_cancel_task(void *ctx) {
  VALK_GC_SAFE_POINT();

  valk_async_handle_t *handle = (valk_async_handle_t *)ctx;
  if (!handle) return;

  if (!__reach_terminal(handle, VALK_ASYNC_CANCELLED)) return;

  atomic_store_explicit(&handle->cancel_requested, 1, memory_order_release);

  if (handle->uv_handle_ptr) {
    u32 *magic_ptr = (u32*)handle->uv_handle_ptr;
    if (*magic_ptr == VALK_UV_DATA_TIMER_MAGIC) {
      valk_async_handle_uv_data_t *uv_data = handle->uv_handle_ptr;
      if (uv_data->uv.timer.loop &&
          uv_is_active((uv_handle_t*)&uv_data->uv.timer) &&
          !uv_is_closing((uv_handle_t*)&uv_data->uv.timer)) {
        uv_timer_stop(&uv_data->uv.timer);
      }
    } else if (*magic_ptr == VALK_INTERVAL_TIMER_MAGIC) {
      valk_interval_timer_t *timer_data = (valk_interval_timer_t*)handle->uv_handle_ptr;
      timer_data->stopped = true;
      if (timer_data->timer.loop &&
          uv_is_active((uv_handle_t*)&timer_data->timer) &&
          !uv_is_closing((uv_handle_t*)&timer_data->timer)) {
        uv_timer_stop(&timer_data->timer);
      }
    }
  }

  if (handle->on_cancel && handle->env) {
    valk_mem_allocator_t *alloc = handle->region ? (valk_mem_allocator_t*)handle->region : nullptr;
    if (!alloc && handle->sys) {
      alloc = (valk_mem_allocator_t*)&handle->sys->system_region;
    }
    if (!alloc) alloc = &valk_malloc_allocator;
    VALK_WITH_ALLOC(alloc) {
      valk_lval_t *args = valk_lval_nil();
      valk_lval_eval_call(handle->env, handle->on_cancel, args);
    }
  }

  valk_aio_system_t *sys = handle->sys;
  if (sys) {
    u32 count = valk_chunked_ptrs_count(&handle->children);
    for (u32 i = 0; i < count; i++) {
      valk_aio_enqueue_task(sys, valk_async_cancel_task, valk_chunked_ptrs_get(&handle->children, i));
    }
  }
}
// LCOV_EXCL_STOP

bool valk_async_handle_cancel(valk_async_handle_t *handle) {
  if (!handle) return false;

  valk_async_status_t status = valk_async_handle_get_status(handle);
  if (valk_async_handle_is_terminal(status)) {
    return false;
  }

  atomic_store_explicit(&handle->cancel_requested, 1, memory_order_release);

  valk_aio_system_t *sys = handle->sys;
  if (sys) {
    if (uv_thread_self() == sys->loopThread) {
      valk_async_cancel_task(handle);
    } else {
      valk_aio_enqueue_task(sys, valk_async_cancel_task, handle);
    }
  } else {
    valk_async_cancel_task(handle);
  }

  return true;
}

void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child) {
  if (!parent || !child) return;
  child->parent = parent;
  if (parent->request_ctx && !child->request_ctx) {
    child->request_ctx = parent->request_ctx;
  }
  valk_chunked_ptrs_push(&parent->children, child, parent->region);
  
  valk_async_status_t parent_status = valk_async_handle_get_status(parent);
  if (valk_async_handle_is_terminal(parent_status)) {
    valk_async_propagate_completion(parent);
  }
  
  valk_async_status_t child_status = valk_async_handle_get_status(child);
  if (valk_async_handle_is_terminal(child_status)) {
    valk_async_notify_parent(child);
  }
}

static void valk_async_propagate_context_impl(valk_async_handle_t *handle, valk_region_t *region, valk_lenv_t *env, valk_request_ctx_t *request_ctx, valk_aio_system_t *expected_sys) {
  if (!handle) return;

  if (expected_sys && handle->sys && handle->sys != expected_sys) {
    return;
  }

  if (!handle->region) {
    handle->region = region;
  }
  if (!handle->env && env) {
    handle->env = env;
  }
  if (!handle->request_ctx && request_ctx) {
    handle->request_ctx = request_ctx;
  }

  u32 count = valk_chunked_ptrs_count(&handle->children);
  for (u32 i = 0; i < count; i++) {
    valk_async_propagate_context_impl(valk_chunked_ptrs_get(&handle->children, i), region, env, request_ctx, expected_sys);
  }
}

void valk_async_propagate_region(valk_async_handle_t *handle, valk_region_t *region, valk_lenv_t *env) {
  valk_request_ctx_t *request_ctx = handle ? handle->request_ctx : nullptr;
  valk_async_propagate_context_impl(handle, region, env, request_ctx, handle ? handle->sys : nullptr);
}

void valk_async_propagate_context(valk_async_handle_t *handle, valk_region_t *region, valk_lenv_t *env, valk_request_ctx_t *request_ctx) {
  valk_async_propagate_context_impl(handle, region, env, request_ctx, handle ? handle->sys : nullptr);
}

valk_lval_t* valk_async_status_to_sym(valk_async_status_t status) {
  switch (status) {
    case VALK_ASYNC_PENDING:   return valk_lval_sym(":pending");
    case VALK_ASYNC_RUNNING:   return valk_lval_sym(":running");
    case VALK_ASYNC_COMPLETED: return valk_lval_sym(":completed");
    case VALK_ASYNC_FAILED:    return valk_lval_sym(":failed");
    case VALK_ASYNC_CANCELLED: return valk_lval_sym(":cancelled");
    default:                   return valk_lval_sym(":unknown");
  }
}

valk_lval_t *valk_lval_handle(valk_async_handle_t *handle) {
  valk_lval_t *res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_HANDLE | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  res->origin_allocator = valk_thread_ctx.allocator;
  res->gc_next = nullptr;
  res->async.handle = handle;
  return res;
}

extern valk_lval_t *valk_lval_err(const char *fmt, ...);

valk_lval_t *valk_async_handle_await_timeout(valk_async_handle_t *handle, u32 timeout_ms) {
  if (!handle) return valk_lval_err("await: null handle");
  
  valk_aio_system_t *sys = handle->sys;
  bool on_loop_thread = sys && uv_thread_self() == sys->loopThread;
  
  if (!sys || !sys->eventloop || !on_loop_thread) { // LCOV_EXCL_BR_LINE - on_loop_thread true only from HTTP handler callbacks
    u64 start = 0;
    if (timeout_ms > 0) {
      struct timespec ts;
      clock_gettime(CLOCK_MONOTONIC, &ts);
      start = ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
    }
    
    while (!valk_async_handle_is_terminal(valk_async_handle_get_status(handle))) {
      VALK_GC_SAFE_POINT();
      uv_sleep(1);
      
      if (timeout_ms > 0) {
        struct timespec ts;
        clock_gettime(CLOCK_MONOTONIC, &ts);
        u64 now = ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
        if (now - start > timeout_ms) {
          return valk_lval_err("await: timeout");
        }
      }
    }
  // LCOV_EXCL_START - on-loop-thread await: only reachable from HTTP handler callbacks on event loop thread
  } else {
    u64 start = 0;
    if (timeout_ms > 0) {
      struct timespec ts;
      clock_gettime(CLOCK_MONOTONIC, &ts);
      start = ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
    }
    
    while (!valk_async_handle_is_terminal(valk_async_handle_get_status(handle))) {
      uv_run(sys->eventloop, UV_RUN_ONCE);
      
      if (timeout_ms > 0) {
        struct timespec ts;
        clock_gettime(CLOCK_MONOTONIC, &ts);
        u64 now = ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
        if (now - start > timeout_ms) {
          return valk_lval_err("await: timeout");
        }
      }
    }
  }
  // LCOV_EXCL_STOP
  
  valk_async_status_t status = valk_async_handle_get_status(handle);
  if (status == VALK_ASYNC_COMPLETED) {
    return atomic_load_explicit(&handle->result, memory_order_acquire);
  } else if (status == VALK_ASYNC_FAILED) {
    valk_lval_t *err = atomic_load_explicit(&handle->error, memory_order_acquire);
    return err ? err : valk_lval_err("async operation failed");
  } else {
    return valk_lval_err("async operation cancelled");
  }
}

valk_lval_t *valk_async_handle_await(valk_async_handle_t *handle) {
  return valk_async_handle_await_timeout(handle, 0);
}
