#include "aio_http2_client.h"
#include "aio_http2_conn.h"
#include "aio_http2_session.h"
#include "aio_ssl.h"
#include "gc.h"
#include <stdatomic.h>

static inline valk_lval_t *__load_callback_atomic(valk_lval_t **callback_ptr) {
  valk_lval_t *callback = atomic_load_explicit((_Atomic(valk_lval_t *)*)callback_ptr, memory_order_acquire);
  if (!callback) return nullptr;
  while (LVAL_TYPE(callback) == LVAL_FORWARD) {
    callback = callback->forward;
  }
  atomic_store_explicit((_Atomic(valk_lval_t *)*)callback_ptr, callback, memory_order_release);
  return callback;
}

extern void valk_uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task);
extern valk_async_handle_t *valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern valk_lval_t *valk_lval_ref(const char *type, void *ptr, void (*free)(void *));

#ifdef VALK_METRICS_ENABLED
extern valk_gauge_v2_t* client_connections_active;
#endif

static inline const valk_io_tcp_ops_t *__tcp_ops(valk_aio_handle_t *conn) {
  return conn->sys ? conn->sys->ops->tcp : nullptr;
}

static inline valk_io_tcp_t *__conn_tcp(valk_aio_handle_t *conn) {
  return &conn->uv.tcp;
}

static inline bool __vtable_is_closing(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return true;
  return tcp->is_closing(__conn_tcp(conn));
}

static inline void __vtable_close(valk_aio_handle_t *conn, valk_io_close_cb cb) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return;
  tcp->close(__conn_tcp(conn), cb);
}

static inline int __vtable_init(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->init(conn->sys, __conn_tcp(conn));
}

static inline int __vtable_nodelay(valk_aio_handle_t *conn, int enable) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->nodelay(__conn_tcp(conn), enable);
}

static void __vtable_alloc_cb(valk_io_tcp_t *tcp, u64 suggested, void **buf, u64 *buflen) {
  UNUSED(suggested);
  valk_aio_handle_t *conn = tcp->user_data;
  *buf = nullptr;
  *buflen = 0;
  
  if (conn && conn->magic == VALK_AIO_HANDLE_MAGIC && conn->kind == VALK_HNDL_HTTP_CONN) {
    if (conn->http.io.read_buf) {
      *buf = (char *)valk_conn_io_read_buf_data(&conn->http.io);
      *buflen = valk_conn_io_read_buf_size(&conn->http.io);
      return;
    }
    
    if (!valk_conn_io_read_buf_acquire(&conn->http.io, conn->sys->tcpBufferSlab)) {
      VALK_WARN("TCP buffer slab exhausted for read buffer");
      return;
    }
    
    *buf = (char *)valk_conn_io_read_buf_data(&conn->http.io);
    *buflen = valk_conn_io_read_buf_size(&conn->http.io);
    return;
  }
  
  VALK_ERROR("Cannot allocate TCP buffer: no valid connection handle");
}

static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf) {
  valk_aio_handle_t *conn = tcp->user_data;
  valk_http2_conn_tcp_read_impl(conn, nread, buf);
}

static inline int __vtable_read_start(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->read_start(__conn_tcp(conn), __vtable_alloc_cb, __vtable_read_cb);
}

static void __http2_connect_impl(valk_aio_handle_t *conn, int status);

static void __vtable_connect_cb(valk_io_tcp_t *tcp, int status) {
  valk_aio_handle_t *conn = tcp->user_data;
  __http2_connect_impl(conn, status);
}

static inline int __vtable_connect(valk_aio_handle_t *conn, const char *ip, int port) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->connect(__conn_tcp(conn), ip, port, __vtable_connect_cb);
}

typedef struct {
  valk_aio_http2_client *client;
  valk_async_handle_t *handle;
} __client_connect_ctx_t;

static int __http_client_on_frame_recv_callback(nghttp2_session *session,
                                                const nghttp2_frame *frame,
                                                void *user_data) {
  UNUSED(session);
  UNUSED(user_data);

  VALK_TRACE("on_recv callback");

  switch (frame->hd.type) {
    case NGHTTP2_HEADERS:
      break;
    case NGHTTP2_RST_STREAM:
      VALK_INFO("C <--- S (RST_STREAM) stream=%d error=%d", frame->hd.stream_id,
               frame->rst_stream.error_code);
      break;
    case NGHTTP2_GOAWAY:
      VALK_INFO("C <--- S (GOAWAY) %d", frame->hd.stream_id);
      VALK_INFO("Client received GOAWAY");
      break;
  }

  return 0;
}

typedef struct {
  u64 streamid;
  valk_http2_request_t *req;
  valk_http2_response_t *res;
  valk_async_handle_t *handle;
} __http2_client_req_res_t;

static void __valk_http2_response_body_free(void *ptr) {
  if (!ptr) return;
  valk_http2_response_t *res = ptr;
  if (res->body) {
    free(res->body);
    res->body = nullptr;
  }
}

static int __http_client_on_stream_close_callback(nghttp2_session *session,
                                                  i32 stream_id,
                                                  u32 error_code,
                                                  void *user_data) {
  UNUSED(user_data);
  VALK_INFO("Client stream close: stream_id=%d, error_code=%u", stream_id, error_code);
  __http2_client_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (reqres) {
    if (error_code != NGHTTP2_NO_ERROR) {
      char errmsg[256];
      snprintf(errmsg, sizeof(errmsg), "HTTP/2 stream error: %s (code=%u)",
               nghttp2_http2_strerror(error_code), error_code);
      valk_async_handle_fail(reqres->handle, valk_lval_err("%s", errmsg));
    } else {
      valk_lval_t *result = valk_lval_ref("success", reqres->res, __valk_http2_response_body_free);
      valk_async_handle_complete(reqres->handle, result);
      reqres->res = nullptr;
    }
    free(reqres);
  }
  return 0;
}

static int __http_on_data_chunk_recv_callback(nghttp2_session *session,
                                              u8 flags, i32 stream_id,
                                              const u8 *data, size_t len,
                                              void *user_data) {
  (void)flags;
  (void)user_data;

  __http2_client_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);

  if (reqres) {
    VALK_INFO("C <--- S (DATA chunk) len=%lu", (unsigned long)len);
    u64 offset = reqres->res->bodyLen;
    VALK_ASSERT((offset + len) < reqres->res->bodyCapacity,
                "Response was too big %llu > %llu", (unsigned long long)(offset + len),
                (unsigned long long)reqres->res->bodyCapacity);
    memcpy((char *)reqres->res->body + offset, data, len);
    reqres->res->bodyLen = offset + len;
    ((char *)reqres->res->body)[reqres->res->bodyLen] = '\0';
  }

  return 0;
}

static void __http2_connect_impl(valk_aio_handle_t *conn, int status) {
  __client_connect_ctx_t *ctx = conn->http.connectReq.data;
  valk_aio_http2_client *client = ctx->client;
  valk_async_handle_t *handle = ctx->handle;

  if (status < 0) {
    VALK_ERROR("Client Connection err: %d", status);
    valk_async_handle_fail(handle, valk_lval_err("Client connection error: %d", status));
    
    if (client->connection && !__vtable_is_closing(client->connection)) {
      valk_conn_transition(client->connection, VALK_CONN_EVT_ERROR);
      __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    
    free(ctx);
    return;
  }

#ifdef VALK_METRICS_ENABLED
  if (!client_connections_active) {
    valk_label_set_v2_t client_labels = {
      .labels = {{"role", "client"}},
      .count = 1
    };
    client_connections_active = valk_gauge_get_or_create("http_connections_active",
      nullptr, &client_labels);
  }
  valk_gauge_v2_inc(client_connections_active);
#endif

  if (!valk_http2_conn_write_buf_acquire(client->connection)) {
    VALK_ERROR("Failed to acquire write buffer for client handshake");
    valk_async_handle_fail(handle, valk_lval_err("TCP buffer exhausted during client connect"));
    if (client->connection && !__vtable_is_closing(client->connection)) {
      valk_conn_transition(client->connection, VALK_CONN_EVT_ERROR);
      __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    free(ctx);
    return;
  }

  static nghttp2_session_callbacks *callbacks = nullptr;
  if (!callbacks) {
    nghttp2_session_callbacks_new(&callbacks);
    nghttp2_session_callbacks_set_on_header_callback(
        callbacks, valk_http2_client_on_header_cb);
    nghttp2_session_callbacks_set_on_frame_recv_callback(
        callbacks, __http_client_on_frame_recv_callback);
    nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
        callbacks, __http_on_data_chunk_recv_callback);
    nghttp2_session_callbacks_set_on_stream_close_callback(
        callbacks, __http_client_on_stream_close_callback);
  }

  nghttp2_session_client_new3(&client->connection->http.session, callbacks, client,
                              nullptr, valk_aio_nghttp2_mem());

  valk_http2_send_client_connection_header(client->connection->http.session, client->sys);

  valk_aio_ssl_client_init(&client->ssl_ctx);
  SSL_CTX_set_alpn_protos(client->ssl_ctx, (const unsigned char *)"\x02h2", 3);

  if (valk_aio_ssl_connect(&client->connection->http.io.ssl, client->ssl_ctx) != 0) {
    VALK_ERROR("Failed to initialize SSL for client connection");
    valk_async_handle_fail(handle, valk_lval_err("SSL initialization failed"));
    if (client->connection && !__vtable_is_closing(client->connection)) {
      valk_conn_transition(client->connection, VALK_CONN_EVT_ERROR);
      __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    free(ctx);
    return;
  }
  const char *sni = (client->hostname[0] != '\0') ? client->hostname : "localhost";
  SSL_set_tlsext_host_name(client->connection->http.io.ssl.ssl, sni);

  u8 *write_buf = valk_http2_conn_write_buf_data(client->connection);
  u64 write_available = valk_http2_conn_write_buf_available(client->connection);
  valk_buffer_t Out = {
      .items = write_buf + client->connection->http.io.write_pos, 
      .count = 0, 
      .capacity = write_available};

  valk_aio_ssl_handshake(&client->connection->http.io.ssl, &Out);

  if (Out.count > 0) {
    client->connection->http.io.write_pos += Out.count;
    valk_http2_conn_write_buf_flush(client->connection);
  }

  if (SSL_is_init_finished(client->connection->http.io.ssl.ssl)) {
    valk_http2_continue_pending_send(client->connection);
  }

  __vtable_read_start(client->connection);

  valk_lval_t *client_ref = valk_lval_ref("http2_client", client, nullptr);
  valk_async_handle_complete(handle, client_ref);
  free(ctx);
}

static void __aio_client_connect_cb(valk_aio_system_t *sys,
                                    valk_aio_task_new *task) {
  int r;
  __client_connect_ctx_t *ctx = task->arg;
  valk_aio_http2_client *client = ctx->client;
  valk_async_handle_t *handle = ctx->handle;

  valk_slab_item_t *slab_item = valk_slab_aquire(sys->handleSlab);
  if (!slab_item) {
    VALK_ERROR("Handle slab exhausted during client connect");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    free(ctx->client);
    free(ctx);
    return;
  }
  client->connection = (valk_aio_handle_t *)slab_item->data;
  memset(client->connection, 0, sizeof(valk_aio_handle_t));
  client->connection->magic = VALK_AIO_HANDLE_MAGIC;
  client->connection->kind = VALK_HNDL_HTTP_CONN;
  client->connection->sys = sys;
  client->connection->onClose = valk_http2_conn_on_disconnect;

  valk_conn_init_state(client->connection);
  client->connection->http.io.buf_size = HTTP_SLAB_ITEM_SIZE;

  valk_dll_insert_after(&sys->liveHandles, client->connection);

  r = __vtable_init(client->connection);
  client->connection->uv.tcp.uv.data = client->connection;
  client->connection->uv.tcp.user_data = client->connection;

  if (r) {
    VALK_ERROR("TcpInit err: %d", r);
    valk_async_handle_fail(handle, valk_lval_err("TCP init error: %d", r));
    valk_dll_pop(client->connection);
    valk_slab_release_ptr(sys->handleSlab, client->connection);
    free(ctx->client);
    free(ctx);
    return;
  }

  __vtable_nodelay(client->connection, 1);

  client->connection->http.connectReq.data = ctx;
  r = __vtable_connect(client->connection, client->interface, client->port);
  if (r) {
    VALK_ERROR("Connect err: %d", r);
    valk_async_handle_fail(handle, valk_lval_err("Connect error: %d", r));
    valk_conn_transition(client->connection, VALK_CONN_EVT_ERROR);
    __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    free(ctx->client);
    free(ctx);
  }
}

valk_async_handle_t *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                                  const char *ip, const int port,
                                                  const char *hostname) {
  valk_async_handle_t *handle = valk_async_handle_new(sys, nullptr);
  if (!handle) {
    return nullptr;
  }

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }

  if (!task) {
    VALK_ERROR("Handle slab exhausted in http2_connect");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    return handle;
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  valk_aio_http2_client *client = malloc(sizeof(valk_aio_http2_client));
  if (!client) {
    VALK_ERROR("Failed to allocate client");
    valk_async_handle_fail(handle, valk_lval_err("Failed to allocate client"));
    valk_mem_allocator_free(task->allocator, task);
    return handle;
  }
  memset(client, 0, sizeof(valk_aio_http2_client));

  strncpy(client->interface, ip, sizeof(client->interface) - 1);
  client->interface[sizeof(client->interface) - 1] = '\0';
  if (hostname) {
    strncpy(client->hostname, hostname, sizeof(client->hostname) - 1);
    client->hostname[sizeof(client->hostname) - 1] = '\0';
  } else {
    client->hostname[0] = '\0';
  }
  client->sys = sys;
  client->port = port;

  __client_connect_ctx_t *ctx = malloc(sizeof(__client_connect_ctx_t));
  ctx->client = client;
  ctx->handle = handle;

  task->arg = ctx;
  task->handle = handle;
  task->callback = __aio_client_connect_cb;

  VALK_DEBUG("Initializing client %p", (void *)client);
  valk_uv_exec_task(sys, task);

  return handle;
}

valk_async_handle_t *valk_aio_http2_connect(valk_aio_system_t *sys,
                                             const char *interface, const int port,
                                             const char *certfile) {
  UNUSED(certfile);
  return valk_aio_http2_connect_host(sys, interface, port, "localhost");
}

typedef struct {
  valk_aio_http2_client *client;
  valk_http2_request_t *req;
  valk_async_handle_t *handle;
} __request_send_ctx_t;

static void __valk_aio_http2_request_send_cb(valk_aio_system_t *sys,
                                             struct valk_aio_task_new *task) {
  UNUSED(sys);
  __request_send_ctx_t *ctx = task->arg;

  valk_aio_http2_client *client = ctx->client;
  valk_aio_handle_t *conn = client->connection;
  valk_async_handle_t *handle = ctx->handle;

  if (conn->http.state == VALK_CONN_CLOSING || conn->http.state == VALK_CONN_CLOSED) {
    valk_async_handle_fail(handle, valk_lval_err("Client connection closing"));
    free(ctx);
    return;
  }

  VALK_INFO("Client ready: %s:%d", client->interface, client->port);
  VALK_DEBUG("req: %s%s", ctx->req->authority, ctx->req->path);

  __http2_client_req_res_t *reqres = malloc(sizeof(__http2_client_req_res_t));
  reqres->req = ctx->req;
  reqres->handle = handle;

  valk_mem_allocator_t *alloc = ctx->req->allocator;
  valk_http2_response_t *res;
  VALK_WITH_ALLOC(alloc) {
    res = valk_mem_alloc(sizeof(valk_http2_response_t));
    memset(res, 0, sizeof(valk_http2_response_t));
    res->allocator = alloc;
    res->headers.items = valk_mem_alloc(sizeof(struct valk_http2_header_t) * 8);
    res->headers.count = 0;
    res->headers.capacity = 8;
  }
  u64 client_response_limit = 64 * 1024 * 1024;
  res->body = malloc(client_response_limit);
  res->bodyLen = 0;
  res->bodyCapacity = client_response_limit;

  reqres->res = res;

  VALK_WITH_ALLOC(alloc) {
    const u64 NUM_PSEUDO_HEADERS = 4;
    u64 hdrCount = ctx->req->headers.count + NUM_PSEUDO_HEADERS;
    struct valk_http2_header_t *phds = ctx->req->headers.items;

    nghttp2_nv hdrs[hdrCount];

    hdrs[0].name = (u8 *)":method";
    hdrs[0].value = (u8 *)ctx->req->method;
    hdrs[0].namelen = sizeof(":method") - 1;
    hdrs[0].valuelen = strlen(ctx->req->method);
    hdrs[0].flags = NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[1].name = (u8 *)":scheme";
    hdrs[1].value = (u8 *)ctx->req->scheme;
    hdrs[1].namelen = sizeof(":scheme") - 1;
    hdrs[1].valuelen = strlen(ctx->req->scheme);
    hdrs[1].flags = NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[2].name = (u8 *)":authority";
    hdrs[2].value = (u8 *)ctx->req->authority;
    hdrs[2].namelen = sizeof(":authority") - 1;
    hdrs[2].valuelen = strlen(ctx->req->authority);
    hdrs[2].flags = NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[3].name = (u8 *)":path";
    hdrs[3].value = (u8 *)ctx->req->path;
    hdrs[3].namelen = sizeof(":path") - 1;
    hdrs[3].valuelen = strlen(ctx->req->path);
    hdrs[3].flags = NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    for (u64 i = 0; i < ctx->req->headers.count; ++i) {
      hdrs[NUM_PSEUDO_HEADERS + i].name = phds[i].name;
      hdrs[NUM_PSEUDO_HEADERS + i].value = phds[i].value;
      hdrs[NUM_PSEUDO_HEADERS + i].namelen = phds[i].nameLen;
      hdrs[NUM_PSEUDO_HEADERS + i].valuelen = phds[i].valueLen;
      hdrs[NUM_PSEUDO_HEADERS + i].flags =
          NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;
    }

    reqres->streamid = nghttp2_submit_request2(conn->http.session, nullptr, hdrs,
                                               hdrCount, nullptr, reqres);

    if (reqres->streamid < 0) {
      VALK_ERROR("Could not submit HTTP request: %s",
                 nghttp2_strerror(reqres->streamid));
      valk_async_handle_fail(handle, valk_lval_err("Could not submit HTTP request"));

      free(reqres);
      free(ctx);
      return;
    }

    res->stream_id = reqres->streamid;
    VALK_INFO("Submitted request stream_id=%ld", reqres->streamid);
  }

  if (SSL_is_init_finished(client->connection->http.io.ssl.ssl)) {
    valk_http2_continue_pending_send(conn);
  }

  free(ctx);
}

valk_async_handle_t *valk_aio_http2_request_send(valk_http2_request_t *req,
                                                  valk_aio_http2_client *client) {
  valk_async_handle_t *handle = valk_async_handle_new(client->sys, nullptr);
  if (!handle) {
    return nullptr;
  }

  valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)client->sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }

  if (!task) {
    VALK_ERROR("Handle slab exhausted in request_send");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    return handle;
  }
  task->allocator = (valk_mem_allocator_t *)client->sys->handleSlab;

  __request_send_ctx_t *ctx = malloc(sizeof(__request_send_ctx_t));
  ctx->client = client;
  ctx->req = req;
  ctx->handle = handle;

  task->arg = ctx;
  task->handle = handle;
  task->callback = __valk_aio_http2_request_send_cb;

  valk_uv_exec_task(client->sys, task);
  return handle;
}

static _Atomic u64 g_client_request_id = 0;

typedef struct {
  valk_aio_system_t *sys;
  valk_lval_t *callback;
  char *host;
  int port;
  char *path;
  valk_aio_http2_client *client;
  valk_lval_t *headers;
  valk_mem_arena_t *arena;
  u64 request_id;
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

  if (status != VALK_ASYNC_COMPLETED) {
    valk_lval_t *err = handle->error ? handle->error : valk_lval_err("Connection failed");
    VALK_ERROR("http2/client-request[%llu]: connection failed: %s", 
               (unsigned long long)ctx->request_id,
               LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown");
    valk_lval_t *cb = __load_callback_atomic(&ctx->callback);
    if (cb) {
      valk_lval_t *args = valk_lval_cons(err, valk_lval_nil());
      valk_lval_eval_call(cb->fun.env, cb, args);
    }
    goto cleanup;
  }

  valk_lval_t *result = handle->result;
  if (!result || LVAL_TYPE(result) != LVAL_REF) {
    VALK_ERROR("http2/client-request[%llu]: invalid connect result", 
               (unsigned long long)ctx->request_id);
    valk_lval_t *cb = __load_callback_atomic(&ctx->callback);
    if (cb) {
      valk_lval_t *err = valk_lval_err("Invalid connect result");
      valk_lval_t *args = valk_lval_cons(err, valk_lval_nil());
      valk_lval_eval_call(cb->fun.env, cb, args);
    }
    goto cleanup;
  }

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
    req->method = __client_arena_strdup("GET");
    req->scheme = __client_arena_strdup("https");
    req->authority = __client_arena_strdup(ctx->host);
    req->path = __client_arena_strdup(ctx->path);
    da_init(&req->headers);

    if (ctx->headers && LVAL_TYPE(ctx->headers) == LVAL_QEXPR) {
      for (u64 i = 0; i < valk_lval_list_count(ctx->headers); i++) {
        valk_lval_t *pair = valk_lval_list_nth(ctx->headers, i);
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
  }

  valk_async_handle_t *request_handle = valk_aio_http2_request_send(req, ctx->client);
  request_handle->on_done = __http2_client_request_response_done;
  request_handle->on_done_ctx = ctx;
  return;

cleanup:
  valk_gc_remove_global_root(&ctx->callback);
  if (ctx->headers) {
    valk_gc_remove_global_root(&ctx->headers);
  }
  free(ctx->host);
  free(ctx->path);
  free(ctx);
}

static void __http2_client_request_response_done(valk_async_handle_t *handle, void *ctx_ptr) {
  VALK_GC_SAFE_POINT();
  
  valk_http2_client_request_ctx_t *ctx = ctx_ptr;
  valk_async_status_t status = valk_async_handle_get_status(handle);

  VALK_INFO("http2/client-request[%llu]: response_done status=%d", 
            (unsigned long long)ctx->request_id, status);

  valk_lval_t *cb = __load_callback_atomic(&ctx->callback);
  if (status != VALK_ASYNC_COMPLETED) {
    valk_lval_t *err = handle->error ? handle->error : valk_lval_err("Request failed");
    VALK_ERROR("http2/client-request[%llu]: request failed: %s",
               (unsigned long long)ctx->request_id,
               LVAL_TYPE(err) == LVAL_ERR ? err->str : "unknown");
    if (cb) {
      valk_lval_t *args = valk_lval_cons(err, valk_lval_nil());
      VALK_INFO("http2/client-request[%llu]: calling error callback", 
                (unsigned long long)ctx->request_id);
      valk_lval_eval_call(cb->fun.env, cb, args);
    } else {
      VALK_ERROR("http2/client-request[%llu]: NO CALLBACK",
                 (unsigned long long)ctx->request_id);
    }
  } else {
    valk_lval_t *result = handle->result;
    if (cb) {
      valk_lval_t *args = valk_lval_cons(result, valk_lval_nil());
      VALK_INFO("http2/client-request[%llu]: calling success callback", 
                (unsigned long long)ctx->request_id);
      valk_lval_eval_call(cb->fun.env, cb, args);
    } else {
      VALK_ERROR("http2/client-request[%llu]: NO CALLBACK",
                 (unsigned long long)ctx->request_id);
    }
  }

  valk_gc_remove_global_root(&ctx->callback);
  if (ctx->headers) {
    valk_gc_remove_global_root(&ctx->headers);
  }
  free(ctx->host);
  free(ctx->path);
  if (ctx->arena) {
    free(ctx->arena);
  }
  free(ctx);
}

valk_lval_t *valk_http2_client_request_with_headers_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *headers,
                                             valk_lval_t *callback) {
  UNUSED(e);
  u64 req_id = atomic_fetch_add(&g_client_request_id, 1);
  VALK_INFO("http2/client-request[%llu]: %s:%d%s (with %zu headers)", 
            (unsigned long long)req_id, host, port, path,
            headers ? valk_lval_list_count(headers) : 0);

  valk_http2_client_request_ctx_t *ctx = malloc(sizeof(valk_http2_client_request_ctx_t));
  ctx->sys = sys;
  ctx->host = strdup(host);
  ctx->port = port;
  ctx->path = strdup(path);
  ctx->client = nullptr;
  ctx->arena = nullptr;
  ctx->request_id = req_id;

  ctx->callback = callback;
  ctx->headers = headers;
  
  valk_gc_add_global_root(&ctx->callback);
  if (ctx->headers) {
    valk_gc_add_global_root(&ctx->headers);
  }

  VALK_INFO("http2/client-request[%llu]: callback=%p rooted", 
            (unsigned long long)req_id, (void*)callback);

  valk_async_handle_t *connect_handle = valk_aio_http2_connect_host(sys, host, port, host);
  connect_handle->on_done = __http2_client_request_connect_done;
  connect_handle->on_done_ctx = ctx;

  VALK_INFO("http2/client-request[%llu]: connect_handle=%p created", 
            (unsigned long long)req_id, (void*)connect_handle);

  return valk_lval_nil();
}

valk_lval_t *valk_http2_client_request_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *callback) {
  return valk_http2_client_request_with_headers_impl(e, sys, host, port, path, nullptr, callback);
}
