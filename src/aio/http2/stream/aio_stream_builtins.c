#include "aio_stream_body.h"

#include <string.h>

#include "aio_internal.h"
#include "aio_http2_session.h"
#include "common.h"
#include "gc.h"
#include "log.h"
#include "parser.h"

void valk_http2_flush_pending(valk_aio_handle_t *conn);
extern valk_async_handle_t *valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);

// LCOV_EXCL_START - defensive validation already covered by LVAL_TYPE check
static valk_stream_body_t *get_stream_body(valk_lval_t *ref) {
  if (!ref || LVAL_TYPE(ref) != LVAL_REF) {
    return nullptr;
  }
  if (!ref->ref.type) {
    return nullptr;
  }
  if (strcmp(ref->ref.type, "stream_body") != 0) {
    return nullptr;
  }
  return (valk_stream_body_t *)ref->ref.ptr;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - ref cleanup callback invoked only when lval_ref is freed by GC
static void stream_body_cleanup(void *ptr) {
  valk_stream_body_t *body = (valk_stream_body_t *)ptr;
  if (body) {
    valk_stream_body_free(body);
  }
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - requires full HTTP/2 server integration with valid request context
static valk_lval_t *valk_builtin_stream_open(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  u64 argc = valk_lval_list_count(a);
  if (argc < 1 || argc > 2) {
    return valk_lval_err("stream/open: expected 1-2 arguments (request [headers]), got %llu",
                         (unsigned long long)argc);
  }

  valk_lval_t *req_ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(req_ref) != LVAL_REF || strcmp(req_ref->ref.type, "http_request") != 0) {
    return valk_lval_err("stream/open: first argument must be http request");
  }

  valk_http2_server_request_t *req = (valk_http2_server_request_t *)req_ref->ref.ptr;
  valk_aio_handle_t *conn = req->conn;
  i32 stream_id = req->stream_id;
  nghttp2_session *session = conn->http.session;

  if (!session || !conn) {
    return valk_lval_err("stream/open: invalid HTTP request");
  }

  const char *content_type = "application/octet-stream";
  const char *status = "200";
  const char *cache_control = nullptr;

  if (argc == 2) {
    valk_lval_t *headers = valk_lval_list_nth(a, 1);
    if (LVAL_TYPE(headers) == LVAL_QEXPR || LVAL_TYPE(headers) == LVAL_CONS) {
      valk_lval_t *ct = valk_http2_qexpr_get(headers, ":content-type");
      if (ct && LVAL_TYPE(ct) == LVAL_STR) {
        content_type = ct->str;
      }
      valk_lval_t *st = valk_http2_qexpr_get(headers, ":status");
      if (st && LVAL_TYPE(st) == LVAL_STR) {
        status = st->str;
      }
      valk_lval_t *cc = valk_http2_qexpr_get(headers, ":cache-control");
      if (cc && LVAL_TYPE(cc) == LVAL_STR) {
        cache_control = cc->str;
      }
    }
  }

  nghttp2_data_provider2 data_prd;
  valk_mem_arena_t *stream_arena = req->stream_arena;
  valk_stream_body_t *body = valk_stream_body_new(conn, session, stream_id, &data_prd, stream_arena);
  if (!body) {
    return valk_lval_err("stream/open: failed to create stream body");
  }

  valk_stream_body_register(body);

  nghttp2_nv headers[4];
  u64 header_count = 2;

  headers[0] = (nghttp2_nv){
    (u8 *)":status", (u8 *)status,
    sizeof(":status") - 1, strlen(status),
    NGHTTP2_NV_FLAG_NONE
  };
  headers[1] = (nghttp2_nv){
    (u8 *)"content-type", (u8 *)content_type,
    sizeof("content-type") - 1, strlen(content_type),
    NGHTTP2_NV_FLAG_NONE
  };

  if (cache_control) {
    headers[header_count++] = (nghttp2_nv){
      (u8 *)"cache-control", (u8 *)cache_control,
      sizeof("cache-control") - 1, strlen(cache_control),
      NGHTTP2_NV_FLAG_NONE
    };
  }

  int rv = nghttp2_submit_response2(session, stream_id, headers, header_count, &data_prd);
  if (rv != 0) {
    valk_stream_body_close(body);
    return valk_lval_err("stream/open: failed to submit response: %s", nghttp2_strerror(rv));
  }

  valk_http2_flush_pending(conn);

  VALK_DEBUG("stream: opened body id=%llu for http2_stream=%d",
             (unsigned long long)body->id, stream_id);

  return valk_lval_ref("stream_body", body, stream_body_cleanup);
}
// LCOV_EXCL_STOP

static valk_lval_t *valk_builtin_stream_write(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("stream/write: expected 2 arguments (body data), got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *data_arg = valk_lval_list_nth(a, 1);

  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/write: first argument must be stream body handle");
  }

  if (LVAL_TYPE(data_arg) != LVAL_STR) {
    return valk_lval_err("stream/write: second argument must be a string");
  }

  const char *data = data_arg->str;
  u64 data_len = strlen(data);

  int rv = valk_stream_body_write(body, data, data_len);

  if (rv == -2) {
    return valk_lval_err("stream/write: queue full (backpressure)");
  } else if (rv < 0) {
    return valk_lval_err("stream/write: failed with code %d", rv);
  }

  return valk_lval_num((long)data_len);
}

static valk_lval_t *valk_builtin_stream_writable(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("stream/writable?: expected 1 argument, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body || body->state != VALK_STREAM_OPEN) {
    return valk_lval_num(0);
  }

  bool writable = valk_stream_body_writable(body);
  return valk_lval_num(writable ? 1 : 0);
}

static valk_lval_t *valk_builtin_stream_close(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("stream/close: expected 1 argument, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/close: argument must be stream body handle");
  }

  VALK_DEBUG("stream: closing body id=%llu", (unsigned long long)body->id);
  valk_stream_body_close(body);

  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_stream_on_drain(valk_lenv_t *e, valk_lval_t *a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("stream/on-drain: expected 2 arguments, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *callback = valk_lval_list_nth(a, 1);

  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/on-drain: first argument must be stream body handle");
  }
  if (LVAL_TYPE(callback) != LVAL_FUN) {
    return valk_lval_err("stream/on-drain: second argument must be a function");
  }

  if (body->lisp_on_drain_handle.generation > 0) {
    valk_handle_release(&valk_global_handle_table, body->lisp_on_drain_handle);
  }
  valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);
  body->lisp_on_drain_handle = valk_handle_create(&valk_global_handle_table, heap_callback);
  body->callback_env = e;

  VALK_DEBUG("stream: registered on-drain callback for body id=%llu",
             (unsigned long long)body->id);

  return body_ref;
}

static valk_lval_t *valk_builtin_stream_set_timeout(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("stream/set-timeout: expected 2 arguments, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *timeout_arg = valk_lval_list_nth(a, 1);

  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/set-timeout: first argument must be stream body handle");
  }

  if (LVAL_TYPE(timeout_arg) != LVAL_NUM) {
    return valk_lval_err("stream/set-timeout: second argument must be a number (milliseconds)");
  }

  u64 timeout_ms = (u64)timeout_arg->num;
  valk_stream_body_set_idle_timeout(body, timeout_ms);

  return body_ref;
}

static valk_lval_t *valk_builtin_stream_cancel(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("stream/cancel: expected 1 argument, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/cancel: argument must be stream body handle");
  }

  int rv = valk_stream_body_cancel(body, 0x8);
  if (rv < 0) { // LCOV_EXCL_BR_LINE - defensive: cancel only fails if body is null, already checked above
    return valk_lval_err("stream/cancel: failed to cancel stream");
  }

  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_stream_id(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("stream/id: expected 1 argument, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/id: argument must be stream body handle");
  }

  return valk_lval_num((long)body->id);
}

static valk_lval_t *valk_builtin_stream_on_close(valk_lenv_t *e, valk_lval_t *a) {
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("stream/on-close: expected 2 arguments, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *callback = valk_lval_list_nth(a, 1);

  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/on-close: first argument must be stream body handle");
  }
  if (LVAL_TYPE(callback) != LVAL_FUN) {
    return valk_lval_err("stream/on-close: second argument must be a function");
  }

  if (body->lisp_on_close_handle.generation > 0) {
    valk_handle_release(&valk_global_handle_table, body->lisp_on_close_handle);
  }
  valk_lval_t *heap_callback = valk_evacuate_to_heap(callback);
  body->lisp_on_close_handle = valk_handle_create(&valk_global_handle_table, heap_callback);
  body->callback_env = e;

  VALK_DEBUG("stream: registered on-close callback for body id=%llu",
             (unsigned long long)body->id);

  return body_ref;
}

static valk_lval_t *valk_builtin_stream_closed(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("stream/closed: expected 1 argument, got %llu",
                         (unsigned long long)valk_lval_list_count(a));
  }

  valk_lval_t *body_ref = valk_lval_list_nth(a, 0);
  valk_stream_body_t *body = get_stream_body(body_ref);
  if (!body) {
    return valk_lval_err("stream/closed: argument must be stream body handle");
  }

  if (atomic_load(&body->state) == VALK_STREAM_CLOSED) {
    valk_async_handle_t *handle = valk_async_handle_new(NULL, NULL);
    handle->status = VALK_ASYNC_COMPLETED;
    atomic_store_explicit(&handle->result, valk_lval_sym(":closed"), memory_order_release);
    return valk_lval_handle(handle);
  }

  if (body->closed_handle) {
    return valk_lval_handle(body->closed_handle);
  }

  valk_async_handle_t *handle = valk_async_handle_new(body->conn ? body->conn->sys : NULL, NULL);
  body->closed_handle = handle;

  VALK_DEBUG("stream: created closed future for body id=%llu",
             (unsigned long long)body->id);

  return valk_lval_handle(handle);
}

void valk_register_stream_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "stream/open", valk_builtin_stream_open);
  valk_lenv_put_builtin(env, "stream/write", valk_builtin_stream_write);
  valk_lenv_put_builtin(env, "stream/writable?", valk_builtin_stream_writable);
  valk_lenv_put_builtin(env, "stream/close", valk_builtin_stream_close);
  valk_lenv_put_builtin(env, "stream/on-drain", valk_builtin_stream_on_drain);
  valk_lenv_put_builtin(env, "stream/on-close", valk_builtin_stream_on_close);
  valk_lenv_put_builtin(env, "stream/set-timeout", valk_builtin_stream_set_timeout);
  valk_lenv_put_builtin(env, "stream/cancel", valk_builtin_stream_cancel);
  valk_lenv_put_builtin(env, "stream/id", valk_builtin_stream_id);
  valk_lenv_put_builtin(env, "stream/closed", valk_builtin_stream_closed);

  VALK_DEBUG("stream: registered builtins");
}
