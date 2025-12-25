#include "aio_internal.h"
#include "aio_http2_session.h"

extern uint64_t g_async_handle_id;

extern void valk_http2_continue_pending_send(valk_aio_handle_t *conn);

extern void valk_async_propagate_completion(valk_async_handle_t *source);
extern void valk_async_notify_all_parent(valk_async_handle_t *child);
extern void valk_async_notify_race_parent(valk_async_handle_t *child);
extern void valk_async_notify_any_parent(valk_async_handle_t *child);

bool valk_http_async_is_closed_callback(void *ctx) {
  if (!ctx) return false;
  valk_http_async_ctx_t *http = (valk_http_async_ctx_t*)ctx;
  if (!http->conn) return false;

  valk_aio_handle_t *conn = http->conn;
  return conn->http.state == VALK_CONN_CLOSING ||
         conn->http.state == VALK_CONN_CLOSED ||
         !conn->http.session;
}

void valk_http_async_done_callback(valk_async_handle_t *handle, void *ctx) {
  if (!ctx) return;
  valk_http_async_ctx_t *http = (valk_http_async_ctx_t*)ctx;

  valk_aio_handle_t *conn = http->conn;
  valk_mem_arena_t *arena = http->arena;
  nghttp2_session *session = (nghttp2_session*)http->session;
  int32_t stream_id = http->stream_id;

  if (!conn || conn->http.state == VALK_CONN_CLOSING ||
      conn->http.state == VALK_CONN_CLOSED || !conn->http.session) {
    VALK_INFO("Async handle %lu: connection closed, skipping HTTP response for stream %d",
              handle->id, stream_id);
    goto cleanup;
  }

  valk_http2_server_request_t *stream_req =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (!stream_req) {
    VALK_INFO("Async handle %lu: stream %d no longer exists, skipping HTTP response",
              handle->id, stream_id);
    goto cleanup;
  }

  if (arena && stream_req->stream_arena != arena) {
    VALK_INFO("Async handle %lu: stream %d arena mismatch, skipping", handle->id, stream_id);
    goto cleanup;
  }

  if (arena && http->arena_slab_item) {
    stream_req->arena_slab_item = http->arena_slab_item;
    stream_req->arena_slot = http->arena_slot;
    http->arena_slab_item = NULL;
  }

  if (handle->status == VALK_ASYNC_COMPLETED) {
    valk_lval_t *result = handle->result;
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
  } else if (handle->status == VALK_ASYNC_FAILED) {
    valk_lval_t *err = handle->error ? handle->error : valk_lval_err("Async operation failed");
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

cleanup:
  free(http);
}

// LCOV_EXCL_START - standalone async context: used for non-HTTP async ops
void valk_standalone_async_done_callback(valk_async_handle_t *handle, void *ctx) {
  UNUSED(handle);
  if (!ctx) return;
  valk_standalone_async_ctx_t *standalone = (valk_standalone_async_ctx_t*)ctx;

  if (standalone->arena_slab_item && standalone->sys && standalone->sys->httpStreamArenas) {
    VALK_DEBUG("Releasing standalone async arena back to pool");
    valk_slab_release(standalone->sys->httpStreamArenas, standalone->arena_slab_item);
  }

  free(standalone);
}

valk_standalone_async_ctx_t* valk_standalone_async_ctx_new(valk_aio_system_t *sys) {
  if (!sys || !sys->httpStreamArenas) return NULL;

  valk_slab_item_t *arena_item = valk_slab_aquire(sys->httpStreamArenas);
  if (!arena_item) {
    VALK_WARN("Standalone async: failed to acquire arena from pool");
    return NULL;
  }

  valk_mem_arena_t *arena = (valk_mem_arena_t *)arena_item->data;
  valk_mem_arena_init(arena, sys->config.arena_size);

  valk_standalone_async_ctx_t *ctx = malloc(sizeof(valk_standalone_async_ctx_t));
  if (!ctx) {
    valk_slab_release(sys->httpStreamArenas, arena_item);
    return NULL;
  }
// LCOV_EXCL_STOP

  ctx->arena = arena;
  ctx->arena_slab_item = arena_item;
  ctx->sys = sys;

  VALK_DEBUG("Allocated standalone async arena from pool");
  return ctx;
}

void valk_async_notify_done(valk_async_handle_t *handle) {
  if (handle->on_done) {
    handle->on_done(handle, handle->on_done_ctx);
    handle->on_done = NULL;
    handle->on_done_ctx = NULL;
  }
}

bool valk_async_is_resource_closed(valk_async_handle_t *handle) {
  if (!handle) return false;
  if (handle->is_closed) {
    return handle->is_closed(handle->is_closed_ctx);
  }
  return false;
}

valk_async_handle_t* valk_async_handle_new(uv_loop_t *loop, valk_lenv_t *env) {
  valk_async_handle_t *handle = malloc(sizeof(valk_async_handle_t));
  if (!handle) return NULL;

  memset(handle, 0, sizeof(valk_async_handle_t));
  handle->id = __atomic_fetch_add(&g_async_handle_id, 1, __ATOMIC_RELAXED);
  handle->status = VALK_ASYNC_PENDING;
  __atomic_store_n(&handle->cancel_requested, 0, __ATOMIC_RELAXED);
  handle->loop = loop;
  handle->env = env;
  
  handle->allocator = valk_thread_ctx.allocator;

  return handle;
}

void valk_async_handle_free(valk_async_handle_t *handle) {
  if (!handle) return;

  if (handle->children.items) {
    free(handle->children.items);
  }

  free(handle);
}

void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result) {
  VALK_DEBUG("valk_async_handle_complete: handle=%p, id=%lu", (void*)handle, handle ? handle->id : 0);
  if (!handle) return;
  if (handle->status != VALK_ASYNC_PENDING && handle->status != VALK_ASYNC_RUNNING) {
    VALK_DEBUG("  handle already in terminal state: %d", handle->status);
    return;
  }

  if (valk_async_is_resource_closed(handle)) {
    VALK_INFO("Async handle %lu: resource closed during completion, aborting", handle->id);
    handle->status = VALK_ASYNC_CANCELLED;
    return;
  }

  handle->status = VALK_ASYNC_COMPLETED;
  handle->result = result;

  valk_async_notify_all_parent(handle);
  valk_async_notify_race_parent(handle);
  valk_async_notify_any_parent(handle);
  valk_async_notify_done(handle);
  valk_async_propagate_completion(handle);
}

void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error) {
  if (!handle) return;
  if (handle->status != VALK_ASYNC_PENDING && handle->status != VALK_ASYNC_RUNNING) {
    return;
  }

  if (valk_async_is_resource_closed(handle)) {
    VALK_INFO("Async handle %lu: resource closed during failure, aborting", handle->id);
    handle->status = VALK_ASYNC_CANCELLED;
    return;
  }

  handle->status = VALK_ASYNC_FAILED;
  handle->error = error;

  valk_async_notify_all_parent(handle);
  valk_async_notify_race_parent(handle);
  valk_async_notify_any_parent(handle);
  valk_async_notify_done(handle);
  valk_async_propagate_completion(handle);
}

bool valk_async_handle_cancel(valk_async_handle_t *handle) {
  if (!handle) return false;
  if (handle->status != VALK_ASYNC_PENDING && handle->status != VALK_ASYNC_RUNNING) {
    return false;
  }

  __atomic_store_n(&handle->cancel_requested, 1, __ATOMIC_RELEASE);

  if (handle->status == VALK_ASYNC_RUNNING && handle->uv_handle_ptr) {
    valk_async_handle_uv_data_t *uv_data = handle->uv_handle_ptr;
    uv_timer_stop(&uv_data->uv.timer);
  }

  handle->status = VALK_ASYNC_CANCELLED;

  if (handle->on_cancel && handle->env) {
    valk_mem_allocator_t *alloc = handle->allocator;
    bool needs_arena = !alloc || 
                       alloc->type == VALK_ALLOC_MALLOC ||
                       alloc->type == VALK_ALLOC_GC_HEAP ||
                       alloc->type == VALK_ALLOC_NULL;
    // LCOV_EXCL_START - fallback arena allocation rarely triggered
    if (needs_arena) {
      valk_aio_system_t *sys = g_last_started_aio_system;
      if (sys) {
        valk_standalone_async_ctx_t *standalone = valk_standalone_async_ctx_new(sys);
        if (standalone) {
          alloc = (valk_mem_allocator_t*)standalone->arena;
          handle->allocator = alloc;
          valk_async_handle_t *root = handle;
          while (root->parent) root = root->parent;
          if (!root->on_done) {
            root->on_done = valk_standalone_async_done_callback;
            root->on_done_ctx = standalone;
          }
        }
      }
    }
    // LCOV_EXCL_STOP
    if (!alloc || alloc->type != VALK_ALLOC_ARENA) alloc = &valk_malloc_allocator;
    VALK_WITH_ALLOC(alloc) {
      valk_lval_t *args = valk_lval_nil();
      valk_lval_eval_call(handle->env, handle->on_cancel, args);
    }
  }

  for (size_t i = 0; i < handle->children.count; i++) {
    valk_async_handle_cancel(handle->children.items[i]);
  }

  return true;
}

void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child) {
  if (!parent || !child) return;

  child->parent = parent;

  if (parent->children.count >= parent->children.capacity) {
    size_t new_cap = parent->children.capacity == 0 ? 4 : parent->children.capacity * 2;
    valk_async_handle_t **new_items = realloc(parent->children.items,
                                               new_cap * sizeof(valk_async_handle_t*));
    if (!new_items) return;
    parent->children.items = new_items;
    parent->children.capacity = new_cap;
  }

  parent->children.items[parent->children.count++] = child;
}

static void valk_async_propagate_allocator_impl(valk_async_handle_t *handle, valk_mem_allocator_t *allocator, valk_lenv_t *env, void *expected_loop) {
  if (!handle) return;

  if (expected_loop && handle->loop && handle->loop != expected_loop) {
    return;
  }

  if (!handle->allocator) {
    handle->allocator = allocator;
  }
  if (!handle->env && env) {
    handle->env = env;
  }

  for (size_t i = 0; i < handle->children.count; i++) {
    valk_async_propagate_allocator_impl(handle->children.items[i], allocator, env, expected_loop);
  }
}

void valk_async_propagate_allocator(valk_async_handle_t *handle, valk_mem_allocator_t *allocator, valk_lenv_t *env) {
  valk_async_propagate_allocator_impl(handle, allocator, env, handle ? handle->loop : NULL);
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
  res->gc_next = NULL;
  res->async.handle = handle;
  return res;
}
