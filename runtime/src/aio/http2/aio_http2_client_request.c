// HTTP/2 client request orchestration: the one-shot connect->send->complete
// pipeline behind http2/client-request, client-post and client-stream.
// Split from aio_http2_client.c (transport + nghttp2 callbacks).
#include "aio_http2_client.h"
#include "gc.h"
#include <stdatomic.h>

extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern valk_async_handle_t *valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);

valk_async_handle_t *valk_http2_request_send_full(valk_http2_request_t *req,
                                                  valk_aio_http2_client *client,
                                                  valk_async_done_fn on_done,
                                                  void *on_done_ctx,
                                                  bool streaming,
                                                  valk_handle_t on_data);

static _Atomic u64 g_client_request_id = 0;

typedef struct {
  valk_aio_system_t *sys;
  valk_handle_t headers_handle;
  char *host;
  int port;
  char *path;
  char *method;
  char *body;
  valk_aio_http2_client *client;
  valk_mem_arena_t *arena;
  u64 request_id;
  valk_async_handle_t *async_handle;
  bool streaming;
  valk_handle_t stream_cb;
} valk_http2_client_request_ctx_t;

static char *__client_arena_strdup(const char *s) {
  u64 len = strlen(s);
  char *dup = valk_mem_alloc(len + 1);
  memcpy(dup, s, len + 1);
  return dup;
}

static void __http2_client_request_response_done(valk_async_handle_t *handle, void *ctx_ptr);

static void __http2_client_request_connect_done(valk_async_handle_t *handle, void *ctx_ptr) {
  VALK_GC_SAFE_POINT();
  
  valk_http2_client_request_ctx_t *ctx = ctx_ptr;
  valk_async_status_t status = valk_async_handle_get_status(handle);

  VALK_INFO("http2/client-request[%llu]: connect_done status=%d", 
            (unsigned long long)ctx->request_id, status);
  // LCOV_EXCL_BR_START connection failure paths in async callback
  if (status != VALK_ASYNC_COMPLETED) {
    valk_lval_t *err_val = atomic_load_explicit(&handle->error, memory_order_acquire);
    valk_lval_t *err = err_val ? err_val : valk_lval_err("Connection failed");
    VALK_ERROR("http2/client-request[%llu]: connection failed: %s", 
               (unsigned long long)ctx->request_id,
               LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown");
    valk_async_handle_fail(ctx->async_handle, err);
    goto cleanup;
  }

  valk_lval_t *result = atomic_load_explicit(&handle->result, memory_order_acquire);
  if (!result || LVAL_TYPE(result) != LVAL_REF) {
    VALK_ERROR("http2/client-request[%llu]: invalid connect result", 
               (unsigned long long)ctx->request_id);
    valk_async_handle_fail(ctx->async_handle, valk_lval_err("Invalid connect result"));
    goto cleanup;
  }
  // LCOV_EXCL_BR_STOP

  ctx->client = result->ref.ptr;
  VALK_INFO("http2/client-request[%llu]: connected to %s:%d", 
            (unsigned long long)ctx->request_id, ctx->host, ctx->port);

  u64 arena_bytes = sizeof(valk_mem_arena_t) + (8 * 1024 * 1024) + (64 * 1024);
  valk_mem_arena_t *arena = malloc(arena_bytes);
  valk_mem_arena_init(arena, arena_bytes - sizeof(*arena));
  ctx->arena = arena;

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    memset(req, 0, sizeof(*req));
    req->allocator = (valk_mem_allocator_t *)arena;
    req->method = __client_arena_strdup(ctx->method ? ctx->method : "GET");
    req->scheme = __client_arena_strdup("https");
    req->authority = __client_arena_strdup(ctx->host);
    req->path = __client_arena_strdup(ctx->path);
    if (ctx->body) {
      req->bodyLen = strlen(ctx->body);
      req->body = (u8 *)__client_arena_strdup(ctx->body);
      req->bodyCapacity = req->bodyLen + 1;
    }
    da_init(&req->headers); // LCOV_EXCL_BR_LINE da_init macro

    valk_lval_t *headers = valk_handle_resolve(&valk_sys->handle_table, ctx->headers_handle);
    // LCOV_EXCL_BR_START header parsing defensive checks
    if (headers && LVAL_TYPE(headers) == LVAL_QEXPR) {
      for (u64 i = 0; i < valk_lval_list_count(headers); i++) {
        valk_lval_t *pair = valk_lval_list_nth(headers, i);
        if (LVAL_TYPE(pair) == LVAL_QEXPR && valk_lval_list_count(pair) >= 2) {
          valk_lval_t *name_val = valk_lval_list_nth(pair, 0);
          valk_lval_t *value_val = valk_lval_list_nth(pair, 1);
          if (LVAL_TYPE(name_val) == LVAL_STR && LVAL_TYPE(value_val) == LVAL_STR) {
            struct valk_http2_header_t hdr;
            hdr.name = (u8 *)__client_arena_strdup(name_val->str);
            hdr.value = (u8 *)__client_arena_strdup(value_val->str);
            hdr.nameLen = strlen(name_val->str);
            hdr.valueLen = strlen(value_val->str);
            da_add(&req->headers, hdr);
          }
        }
      }
    }
    // LCOV_EXCL_BR_STOP
  }

  valk_http2_request_send_full(req, ctx->client,
                               __http2_client_request_response_done, ctx,
                               ctx->streaming, ctx->stream_cb);
  return;

cleanup:
  if (ctx->streaming) {
    valk_handle_release(&valk_sys->handle_table, ctx->stream_cb);
  }
  valk_handle_release(&valk_sys->handle_table, ctx->headers_handle);
  free(ctx->host);
  free(ctx->path);
  free(ctx->method);
  free(ctx->body);
  free(ctx);
}

static void __http2_client_request_response_done(valk_async_handle_t *handle, void *ctx_ptr) {
  VALK_GC_SAFE_POINT();
  
  valk_http2_client_request_ctx_t *ctx = ctx_ptr;
  valk_async_status_t status = valk_async_handle_get_status(handle);

  VALK_INFO("http2/client-request[%llu]: response_done status=%d", 
            (unsigned long long)ctx->request_id, status);

  // LCOV_EXCL_BR_START response callback defensive paths
  if (status != VALK_ASYNC_COMPLETED) {
    valk_lval_t *err_val = atomic_load_explicit(&handle->error, memory_order_acquire);
    valk_lval_t *err = err_val ? err_val : valk_lval_err("Request failed");
    VALK_ERROR("http2/client-request[%llu]: request failed: %s",
               (unsigned long long)ctx->request_id,
               LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown");
    valk_async_handle_fail(ctx->async_handle, err);
  } else {
    valk_lval_t *result = atomic_load_explicit(&handle->result, memory_order_acquire);
    VALK_INFO("http2/client-request[%llu]: completing with result", 
              (unsigned long long)ctx->request_id);
    valk_async_handle_complete(ctx->async_handle, result);
  }
  // LCOV_EXCL_BR_STOP
  valk_handle_release(&valk_sys->handle_table, ctx->headers_handle);
  free(ctx->host);
  free(ctx->path);
  free(ctx->method);
  free(ctx->body);
  if (ctx->arena) { // LCOV_EXCL_BR_LINE defensive null check
    free(ctx->arena);
  }
  free(ctx);
}

static valk_lval_t *__client_request_start(valk_lenv_t *e,
                                           valk_aio_system_t *sys,
                                           const char *method,
                                           const char *host, int port,
                                           const char *path,
                                           valk_lval_t *headers,
                                           const char *body,
                                           valk_lval_t *stream_cb) {
  u64 req_id = atomic_fetch_add(&g_client_request_id, 1);
  VALK_INFO("http2/client-request[%llu]: %s %s:%d%s (with %zu headers)",
            (unsigned long long)req_id, method, host, port, path,
            headers ? valk_lval_list_count(headers) : 0);

  valk_async_handle_t *async_handle = valk_async_handle_new(sys, e);

  valk_http2_client_request_ctx_t *ctx = malloc(sizeof(valk_http2_client_request_ctx_t));
  ctx->sys = sys;
  ctx->host = strdup(host);
  ctx->port = port;
  ctx->path = strdup(path);
  ctx->method = strdup(method);
  ctx->body = body ? strdup(body) : nullptr;
  ctx->client = nullptr;
  ctx->arena = nullptr;
  ctx->request_id = req_id;
  ctx->async_handle = async_handle;
  if (stream_cb) {
    valk_lval_t *heap_cb = valk_evacuate_to_heap(stream_cb);
    ctx->streaming = true;
    ctx->stream_cb = valk_handle_create(&valk_sys->handle_table, heap_cb);
  } else {
    ctx->streaming = false;
    ctx->stream_cb = (valk_handle_t){0, 0};
  }

  valk_lval_t *heap_headers = headers ? valk_evacuate_to_heap(headers) : nullptr;
  ctx->headers_handle = heap_headers 
    ? valk_handle_create(&valk_sys->handle_table, heap_headers)
    : (valk_handle_t){0, 0};

  VALK_INFO("http2/client-request[%llu]: async_handle=%p created", 
            (unsigned long long)req_id, (void*)async_handle);

  valk_async_handle_t *connect_handle = valk_aio_http2_connect_host_with_done(
      sys, host, port, host, __http2_client_request_connect_done, ctx);

  VALK_INFO("http2/client-request[%llu]: connect_handle=%p created", 
            (unsigned long long)req_id, (void*)connect_handle);

  return valk_lval_handle(async_handle);
}

valk_lval_t *valk_http2_client_request_full_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *method,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *headers,
                                             const char *body) {
  return __client_request_start(e, sys, method, host, port, path, headers,
                                body, nullptr);
}

// Streaming GET: response body chunks are delivered to on_data as they
// arrive (SSE consumption); the handle completes on stream close.
valk_lval_t *valk_http2_client_stream_impl(valk_lenv_t *e,
                                           valk_aio_system_t *sys,
                                           const char *host, int port,
                                           const char *path,
                                           valk_lval_t *on_data) {
  return __client_request_start(e, sys, "GET", host, port, path, nullptr,
                                nullptr, on_data);
}

valk_lval_t *valk_http2_client_request_with_headers_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *headers) {
  return valk_http2_client_request_full_impl(e, sys, "GET", host, port, path,
                                             headers, nullptr);
}

valk_lval_t *valk_http2_client_request_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path) {
  return valk_http2_client_request_full_impl(e, sys, "GET", host, port, path,
                                             nullptr, nullptr);
}


