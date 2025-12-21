#include "aio_sse.h"

#include <string.h>

#include "aio.h"
#include "common.h"
#include "log.h"
#include "memory.h"
#include "parser.h"

// ============================================================================
// External Declarations
// ============================================================================

// Forward declaration from aio_uv.c
typedef struct {
  nghttp2_session *session;
  int32_t stream_id;
  valk_aio_handle_t *conn;
  void *req;  // valk_http2_server_request_t*
  valk_lenv_t *env;
} valk_http_request_ctx_t;

extern valk_http_request_ctx_t *valk_http_get_request_ctx(void);
extern void valk_http_set_status_code(int status_code);

// Forward declaration from aio_sse.c
extern void valk_http2_flush_pending(valk_aio_handle_t *conn);

// ============================================================================
// Helper Functions
// ============================================================================

// Extract valk_sse_stream_t* from LVAL_REF
static valk_sse_stream_t *get_sse_stream(valk_lval_t *ref) {
  if (!ref || LVAL_TYPE(ref) != LVAL_REF) {
    return NULL;
  }
  if (strcmp(ref->ref.type, "sse_stream") != 0) {
    return NULL;
  }
  return (valk_sse_stream_t *)ref->ref.ptr;
}

// Cleanup function for LVAL_REF
static void sse_stream_cleanup(void *ptr) {
  valk_sse_stream_t *stream = (valk_sse_stream_t *)ptr;
  if (stream) {
    valk_sse_stream_close(stream);
  }
}

// ============================================================================
// Builtin: sse/open
// ============================================================================

// Usage: (sse/open) -> stream-handle
// Must be called within HTTP request handler context
static valk_lval_t *valk_builtin_sse_open(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  // Validate no arguments
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("sse/open: expected 0 arguments, got %zu",
                         valk_lval_list_count(a));
  }

  // Must be in HTTP request context
  valk_http_request_ctx_t *ctx = valk_http_get_request_ctx();
  if (!ctx) {
    return valk_lval_err("sse/open must be called within HTTP request handler");
  }

  // Extract HTTP/2 context
  nghttp2_session *session = ctx->session;
  int32_t stream_id = ctx->stream_id;
  valk_aio_handle_t *conn = ctx->conn;

  if (!session || !conn) {
    return valk_lval_err("sse/open: invalid HTTP request context");
  }

  // Create SSE stream with data provider
  nghttp2_data_provider2 data_prd;
  valk_sse_stream_t *stream = valk_sse_stream_new(conn, session, stream_id, &data_prd);
  if (!stream) {
    return valk_lval_err("sse/open: failed to create SSE stream");
  }

  // Register stream with connection for cleanup on connection close
  valk_sse_stream_register(stream);

  // Submit HTTP/2 response headers
  nghttp2_nv headers[] = {
    {
      (uint8_t *)":status",   (uint8_t *)"200",     sizeof(":status") - 1,
      sizeof("200") - 1, NGHTTP2_NV_FLAG_NONE,
    },
    {
      (uint8_t *)"content-type",   (uint8_t *)"text/event-stream",     sizeof("content-type") - 1,
      sizeof("text/event-stream") - 1, NGHTTP2_NV_FLAG_NONE,
    },
    {
      (uint8_t *)"cache-control",   (uint8_t *)"no-cache",     sizeof("cache-control") - 1,
      sizeof("no-cache") - 1, NGHTTP2_NV_FLAG_NONE,
    },
    {
      (uint8_t *)"connection",   (uint8_t *)"keep-alive",     sizeof("connection") - 1,
      sizeof("keep-alive") - 1, NGHTTP2_NV_FLAG_NONE,
    },
  };

  int rv = nghttp2_submit_response2(session, stream_id, headers, 4, &data_prd);
  if (rv != 0) {
    valk_sse_stream_close(stream);
    return valk_lval_err("sse/open: failed to submit response: %s", nghttp2_strerror(rv));
  }

  // Set status code for metrics tracking when stream eventually closes
  // SSE streams stay open indefinitely, so this ensures the 200 response
  // is counted when the connection finally closes
  valk_http_set_status_code(200);

  // Flush pending data to client
  valk_http2_flush_pending(conn);

  VALK_DEBUG("SSE: opened stream id=%lu for http2_stream=%d", stream->id, stream_id);

  // Return handle as LVAL_REF
  return valk_lval_ref("sse_stream", stream, sse_stream_cleanup);
}

// ============================================================================
// Builtin: sse/send
// ============================================================================

// Usage: (sse/send stream data) -> data-length or error
// Usage: (sse/send stream event-type data) -> data-length or error
static valk_lval_t *valk_builtin_sse_send(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  // Validate 2-3 arguments
  size_t argc = valk_lval_list_count(a);
  if (argc < 2 || argc > 3) {
    return valk_lval_err("sse/send: expected 2-3 arguments, got %zu", argc);
  }

  // Extract stream from first argument
  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(stream_ref) != LVAL_REF) {
    return valk_lval_err("sse/send: first argument must be SSE stream handle");
  }

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/send: first argument must be SSE stream handle");
  }

  const char *event_type = NULL;
  const char *data = NULL;
  size_t data_len = 0;

  if (argc == 3) {
    // (sse/send stream event-type data)
    valk_lval_t *event_arg = valk_lval_list_nth(a, 1);
    valk_lval_t *data_arg = valk_lval_list_nth(a, 2);

    if (LVAL_TYPE(event_arg) != LVAL_STR) {
      return valk_lval_err("sse/send: event-type must be a string");
    }
    if (LVAL_TYPE(data_arg) != LVAL_STR) {
      return valk_lval_err("sse/send: data must be a string");
    }

    event_type = event_arg->str;
    data = data_arg->str;
    data_len = strlen(data);
  } else {
    // (sse/send stream data)
    valk_lval_t *data_arg = valk_lval_list_nth(a, 1);

    if (LVAL_TYPE(data_arg) != LVAL_STR) {
      return valk_lval_err("sse/send: data must be a string");
    }

    data = data_arg->str;
    data_len = strlen(data);
  }

  // Send event (event_type=NULL means "message" event)
  int rv = valk_sse_send_event(stream, event_type, data, data_len, 0);

  if (rv == -2) {
    return valk_lval_err("sse/send: queue full (backpressure)");
  } else if (rv < 0) {
    return valk_lval_err("sse/send: failed with code %d", rv);
  }

  // Return data length on success
  return valk_lval_num((long)data_len);
}

// ============================================================================
// Builtin: sse/close
// ============================================================================

// Usage: (sse/close stream) -> nil
static valk_lval_t *valk_builtin_sse_close(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  // Validate 1 argument
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("sse/close: expected 1 argument, got %zu",
                         valk_lval_list_count(a));
  }

  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(stream_ref) != LVAL_REF) {
    return valk_lval_err("sse/close: argument must be SSE stream handle");
  }

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/close: argument must be SSE stream handle");
  }

  VALK_DEBUG("SSE: closing stream id=%lu", stream->id);
  valk_sse_stream_close(stream);

  return valk_lval_nil();
}

// ============================================================================
// Builtin: sse/writable?
// ============================================================================

// Usage: (sse/writable? stream) -> true/false
static valk_lval_t *valk_builtin_sse_writable(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  // Validate 1 argument
  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("sse/writable?: expected 1 argument, got %zu",
                         valk_lval_list_count(a));
  }

  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  if (LVAL_TYPE(stream_ref) != LVAL_REF) {
    return valk_lval_err("sse/writable?: argument must be SSE stream handle");
  }

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/writable?: argument must be SSE stream handle");
  }

  bool writable = valk_sse_is_writable(stream);
  return valk_lval_sym(writable ? "true" : "false");
}

// ============================================================================
// Builtin: sse/on-drain
// ============================================================================

// Usage: (sse/on-drain stream callback) -> stream
// Callback called when queue drains below threshold
static valk_lval_t *valk_builtin_sse_on_drain(valk_lenv_t *e, valk_lval_t *a) {
  // Validate 2 arguments
  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("sse/on-drain: expected 2 arguments, got %zu",
                         valk_lval_list_count(a));
  }

  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *callback = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(stream_ref) != LVAL_REF) {
    return valk_lval_err("sse/on-drain: first argument must be SSE stream handle");
  }
  if (LVAL_TYPE(callback) != LVAL_FUN) {
    return valk_lval_err("sse/on-drain: second argument must be a function");
  }

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/on-drain: first argument must be SSE stream handle");
  }

  // Copy callback to GC heap for persistence
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    stream->lisp_on_drain = valk_lval_copy(callback);
    stream->callback_env = e;
  }

  VALK_DEBUG("SSE: registered on-drain callback for stream id=%lu", stream->id);

  // Return stream ref for chaining
  return stream_ref;
}

// ============================================================================
// Builtin: sse/set-timeout
// ============================================================================

// Usage: (sse/set-timeout stream timeout-ms) -> stream
static valk_lval_t *valk_builtin_sse_set_timeout(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 2) {
    return valk_lval_err("sse/set-timeout: expected 2 arguments, got %zu",
                         valk_lval_list_count(a));
  }

  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *timeout_arg = valk_lval_list_nth(a, 1);

  if (LVAL_TYPE(stream_ref) != LVAL_REF) {
    return valk_lval_err("sse/set-timeout: first argument must be SSE stream handle");
  }

  if (LVAL_TYPE(timeout_arg) != LVAL_NUM) {
    return valk_lval_err("sse/set-timeout: second argument must be a number (milliseconds)");
  }

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/set-timeout: first argument must be SSE stream handle");
  }

  uint64_t timeout_ms = (uint64_t)timeout_arg->num;
  valk_sse_set_idle_timeout(stream, timeout_ms);

  return stream_ref;
}

// ============================================================================
// Builtin: sse/cancel
// ============================================================================

// Usage: (sse/cancel stream) -> nil
static valk_lval_t *valk_builtin_sse_cancel(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("sse/cancel: expected 1 argument, got %zu",
                         valk_lval_list_count(a));
  }

  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(stream_ref) != LVAL_REF) {
    return valk_lval_err("sse/cancel: argument must be SSE stream handle");
  }

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/cancel: argument must be SSE stream handle");
  }

  // Cancel with NGHTTP2_CANCEL error code
  int rv = valk_sse_stream_cancel(stream, 0x8);  // NGHTTP2_CANCEL = 0x8
  if (rv < 0) {
    return valk_lval_err("sse/cancel: failed to cancel stream");
  }

  return valk_lval_nil();
}

// ============================================================================
// Builtin: sse/stream-id
// ============================================================================

// Usage: (sse/stream-id stream) -> id
static valk_lval_t *valk_builtin_sse_stream_id(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("sse/stream-id: expected 1 argument, got %zu",
                         valk_lval_list_count(a));
  }

  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(stream_ref) != LVAL_REF) {
    return valk_lval_err("sse/stream-id: argument must be SSE stream handle");
  }

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/stream-id: argument must be SSE stream handle");
  }

  return valk_lval_num((long)stream->id);
}

// ============================================================================
// Builtin: sse/cancel-by-id
// ============================================================================

// Usage: (sse/cancel-by-id id) -> true/false
static valk_lval_t *valk_builtin_sse_cancel_by_id(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 1) {
    return valk_lval_err("sse/cancel-by-id: expected 1 argument, got %zu",
                         valk_lval_list_count(a));
  }

  valk_lval_t *id_arg = valk_lval_list_nth(a, 0);

  if (LVAL_TYPE(id_arg) != LVAL_NUM) {
    return valk_lval_err("sse/cancel-by-id: argument must be a stream ID (number)");
  }

  uint64_t id = (uint64_t)id_arg->num;
  valk_sse_manager_t *mgr = valk_sse_get_manager();

  valk_sse_stream_t *stream = valk_sse_manager_find_by_id(mgr, id);
  if (!stream) {
    return valk_lval_sym("false");
  }

  valk_sse_stream_cancel(stream, 0x8);  // NGHTTP2_CANCEL
  return valk_lval_sym("true");
}

// ============================================================================
// Builtin: sse/shutdown-all
// ============================================================================

// Usage: (sse/shutdown-all) -> count
// Usage: (sse/shutdown-all drain-timeout-ms) -> count
static valk_lval_t *valk_builtin_sse_shutdown_all(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  size_t argc = valk_lval_list_count(a);
  if (argc > 1) {
    return valk_lval_err("sse/shutdown-all: expected 0-1 arguments, got %zu", argc);
  }

  uint64_t drain_timeout_ms = 0;
  if (argc == 1) {
    valk_lval_t *timeout_arg = valk_lval_list_nth(a, 0);
    if (LVAL_TYPE(timeout_arg) != LVAL_NUM) {
      return valk_lval_err("sse/shutdown-all: argument must be a number (milliseconds)");
    }
    drain_timeout_ms = (uint64_t)timeout_arg->num;
  }

  valk_sse_manager_t *mgr = valk_sse_get_manager();

  if (drain_timeout_ms == 0) {
    // Immediate close
    size_t closed = valk_sse_manager_force_close_all(mgr);
    return valk_lval_num((long)closed);
  } else {
    // Graceful shutdown
    valk_sse_manager_graceful_shutdown(mgr, drain_timeout_ms);
    return valk_lval_num((long)mgr->stream_count);
  }
}

// ============================================================================
// Builtin: sse/stream-count
// ============================================================================

// Usage: (sse/stream-count) -> count
static valk_lval_t *valk_builtin_sse_stream_count(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("sse/stream-count: expected 0 arguments, got %zu",
                         valk_lval_list_count(a));
  }

  valk_sse_manager_t *mgr = valk_sse_get_manager();
  return valk_lval_num((long)mgr->stream_count);
}

// ============================================================================
// Registration Function
// ============================================================================

void valk_register_sse_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "sse/open", valk_builtin_sse_open);
  valk_lenv_put_builtin(env, "sse/send", valk_builtin_sse_send);
  valk_lenv_put_builtin(env, "sse/close", valk_builtin_sse_close);
  valk_lenv_put_builtin(env, "sse/writable?", valk_builtin_sse_writable);
  valk_lenv_put_builtin(env, "sse/on-drain", valk_builtin_sse_on_drain);

  // Timeout management
  valk_lenv_put_builtin(env, "sse/set-timeout", valk_builtin_sse_set_timeout);

  // Stream cancellation
  valk_lenv_put_builtin(env, "sse/cancel", valk_builtin_sse_cancel);
  valk_lenv_put_builtin(env, "sse/stream-id", valk_builtin_sse_stream_id);
  valk_lenv_put_builtin(env, "sse/cancel-by-id", valk_builtin_sse_cancel_by_id);

  // Global stream management
  valk_lenv_put_builtin(env, "sse/shutdown-all", valk_builtin_sse_shutdown_all);
  valk_lenv_put_builtin(env, "sse/stream-count", valk_builtin_sse_stream_count);

  VALK_DEBUG("SSE: registered builtins");
}
