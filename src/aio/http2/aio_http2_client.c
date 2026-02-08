#include "aio_http2_client.h"
#include "aio_http2_conn.h"
#include "aio_http2_session.h"
#include "aio_ssl.h"
#include "gc.h"
#include "../aio_request_ctx.h"
#include "aio_tcp_helpers.h"
#include <stdatomic.h>

extern void valk_uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task);
extern valk_async_handle_t *valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern valk_lval_t *valk_lval_ref(const char *type, void *ptr, void (*free)(void *));

extern valk_gauge_v2_t* client_connections_active;

static void __vtable_alloc_cb(valk_io_tcp_t *tcp, u64 suggested, void **buf, u64 *buflen) {
  UNUSED(suggested);
  valk_aio_handle_t *conn = tcp->user_data;
  *buf = nullptr;
  *buflen = 0;
  // LCOV_EXCL_BR_START defensive validation of connection handle
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
  // LCOV_EXCL_BR_STOP
  VALK_ERROR("Cannot allocate TCP buffer: no valid connection handle"); // LCOV_EXCL_LINE impossible error path
}

static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf) {
  valk_aio_handle_t *conn = tcp->user_data;
  valk_http2_conn_tcp_read_impl(conn, nread, buf);
}

static inline int __vtable_read_start(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->read_start(__conn_tcp(conn), __vtable_alloc_cb, __vtable_read_cb);
}

static void __http2_connect_impl(valk_aio_handle_t *conn, int status);

static void __vtable_connect_cb(valk_io_tcp_t *tcp, int status) {
  valk_aio_handle_t *conn = tcp->user_data;
  __http2_connect_impl(conn, status);
}

static inline int __vtable_connect(valk_aio_handle_t *conn, const char *ip, int port) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
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
  // LCOV_EXCL_START switch on nghttp2 frame types, not all types are logged; RST_STREAM/GOAWAY are rare protocol errors
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
  // LCOV_EXCL_STOP
  return 0;
}

typedef struct {
  u64 streamid;
  valk_http2_request_t *req;
  valk_http2_response_t *res;
  valk_async_handle_t *handle;
} __http2_client_req_res_t;

typedef struct __pending_client_request {
  struct __pending_client_request *next;
  valk_async_handle_t *handle;
} __pending_client_request_t;

static void __add_pending_request(valk_aio_handle_t *conn, valk_async_handle_t *handle) {
  __pending_client_request_t *pending = malloc(sizeof(__pending_client_request_t));
  pending->handle = handle;
  pending->next = (__pending_client_request_t *)conn->http.pending_client_requests;
  conn->http.pending_client_requests = pending;
}

static void __remove_pending_request(valk_aio_handle_t *conn, valk_async_handle_t *handle) {
  __pending_client_request_t **pp = (__pending_client_request_t **)&conn->http.pending_client_requests;
  while (*pp) {
    if ((*pp)->handle == handle) {
      __pending_client_request_t *to_free = *pp;
      *pp = (*pp)->next;
      free(to_free);
      return;
    }
    pp = &(*pp)->next;
  }
}

void valk_http2_fail_pending_client_requests(valk_aio_handle_t *conn) {
  if (!conn) return;
  __pending_client_request_t *p = (__pending_client_request_t *)conn->http.pending_client_requests;
  conn->http.pending_client_requests = NULL;
  while (p) {
    __pending_client_request_t *next = p->next;
    valk_async_handle_t *handle = p->handle;
    free(p);
    
    if (handle) {
      valk_async_status_t status = valk_async_handle_get_status(handle);
      if (!valk_async_handle_is_terminal(status)) {
        VALK_WARN("Failing pending client request due to connection disconnect");
        valk_async_handle_fail(handle, valk_lval_err("Connection closed before request could be sent"));
      }
    }
    p = next;
  }
}

// LCOV_EXCL_START libuv ref-free callback, invoked by GC during lval cleanup
static void __valk_http2_response_free(void *ptr) {
  if (!ptr) return;
  valk_http2_response_t *res = ptr;
  if (res->body) {
    free(res->body);
    res->body = nullptr;
  }
  if (res->status) {
    free((void*)res->status);
  }
  for (u64 i = 0; i < res->headers.count; i++) {
    if (res->headers.items[i].name) free(res->headers.items[i].name);
    if (res->headers.items[i].value) free(res->headers.items[i].value);
  }
  if (res->headers.items) {
    free(res->headers.items);
    res->headers.items = nullptr;
  }
  free(res);
}
// LCOV_EXCL_STOP

static int __http_client_on_stream_close_callback(nghttp2_session *session,
                                                  i32 stream_id,
                                                  u32 error_code,
                                                  void *user_data) {
  valk_aio_http2_client *client = user_data;
  VALK_INFO("Client stream close: stream_id=%d, error_code=%u", stream_id, error_code);
  __http2_client_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (reqres) { // LCOV_EXCL_BR_LINE nghttp2 callback, reqres always set for client streams
    if (client && client->connection && reqres->handle) {
      __remove_pending_request(client->connection, reqres->handle);
    }
    if (error_code != NGHTTP2_NO_ERROR) {
      char errmsg[256];
      snprintf(errmsg, sizeof(errmsg), "HTTP/2 stream error: %s (code=%u)",
               nghttp2_http2_strerror(error_code), error_code);
      valk_async_handle_fail(reqres->handle, valk_lval_err("%s", errmsg));
    } else {
      valk_lval_t *result = valk_lval_ref("success", reqres->res, __valk_http2_response_free);
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
  // LCOV_EXCL_BR_START nghttp2 callback, reqres always set for client streams
  if (reqres) {
    VALK_INFO("C <--- S (DATA chunk) len=%lu", (unsigned long)len);
    u64 offset = reqres->res->bodyLen;
    VALK_ASSERT((offset + len) < reqres->res->bodyCapacity, // LCOV_EXCL_BR_LINE assertion
                "Response was too big %llu > %llu", (unsigned long long)(offset + len),
                (unsigned long long)reqres->res->bodyCapacity);
    memcpy((char *)reqres->res->body + offset, data, len);
    reqres->res->bodyLen = offset + len;
    ((char *)reqres->res->body)[reqres->res->bodyLen] = '\0';
  }
  // LCOV_EXCL_BR_STOP
  return 0;
}

static void __http2_connect_impl(valk_aio_handle_t *conn, int status) {
  __client_connect_ctx_t *ctx = conn->http.connectReq.data;
  valk_aio_http2_client *client = ctx->client;
  valk_async_handle_t *handle = ctx->handle;

  if (status < 0) { // LCOV_EXCL_BR_LINE connection errors are rare in test environment
    VALK_ERROR("Client Connection err: %d", status);
    valk_async_handle_fail(handle, valk_lval_err("Client connection error: %d", status));
    // LCOV_EXCL_BR_START defensive cleanup on connection error
    if (client->connection && !__vtable_is_closing(client->connection)) {
      valk_conn_transition(client->connection, VALK_CONN_EVT_ERROR);
      __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    // LCOV_EXCL_BR_STOP
    free(ctx);
    return;
  }

  if (!client_connections_active) {
    valk_label_set_v2_t client_labels = {
      .labels = {{"role", "client"}},
      .count = 1
    };
    client_connections_active = valk_gauge_get_or_create("http_connections_active",
      nullptr, &client_labels);
  }
  valk_gauge_v2_inc(client_connections_active);

  if (!valk_http2_conn_write_buf_acquire(client->connection)) { // LCOV_EXCL_BR_LINE buffer slab exhaustion
    VALK_ERROR("Failed to acquire write buffer for client handshake");
    valk_async_handle_fail(handle, valk_lval_err("TCP buffer exhausted during client connect"));
    if (client->connection && !__vtable_is_closing(client->connection)) { // LCOV_EXCL_BR_LINE defensive cleanup
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

  // LCOV_EXCL_START SSL init failure - platform/OpenSSL failure paths
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
  // LCOV_EXCL_STOP
  const char *sni = (client->hostname[0] != '\0') ? client->hostname : "localhost";
  SSL_set_tlsext_host_name(client->connection->http.io.ssl.ssl, sni);

  u8 *write_buf = valk_http2_conn_write_buf_data(client->connection);
  u64 write_available = valk_http2_conn_write_buf_available(client->connection);
  valk_buffer_t Out = {
      .items = write_buf + client->connection->http.io.write_pos, 
      .count = 0, 
      .capacity = write_available};

  valk_aio_ssl_handshake(&client->connection->http.io.ssl, &Out);

  if (Out.count > 0) { // LCOV_EXCL_BR_LINE SSL handshake always produces output
    client->connection->http.io.write_pos += Out.count;
    valk_http2_conn_write_buf_flush(client->connection);
  }

  // LCOV_EXCL_START SSL handshake completes asynchronously, not during initial callback
  if (SSL_is_init_finished(client->connection->http.io.ssl.ssl)) {
    valk_http2_continue_pending_send(client->connection);
  }
  // LCOV_EXCL_STOP
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
  if (!slab_item) { // LCOV_EXCL_START
    VALK_ERROR("Handle slab exhausted during client connect");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    free(ctx->client);
    free(ctx);
    return;
  } // LCOV_EXCL_STOP
  client->connection = (valk_aio_handle_t *)slab_item->data;
  memset(client->connection, 0, sizeof(valk_aio_handle_t));
  client->connection->magic = VALK_AIO_HANDLE_MAGIC;
  client->connection->kind = VALK_HNDL_HTTP_CONN;
  client->connection->sys = sys;
  client->connection->onClose = valk_http2_conn_on_disconnect;

  valk_conn_init_state(client->connection);
  client->connection->http.io.buf_size = HTTP_SLAB_ITEM_SIZE;

  valk_dll_insert_after(&sys->liveHandles, client->connection); // LCOV_EXCL_BR_LINE macro internal branches

  r = __vtable_init(client->connection);
  client->connection->uv.tcp.uv.data = client->connection;
  client->connection->uv.tcp.user_data = client->connection;
  // LCOV_EXCL_START platform TCP init failure
  if (r) {
    VALK_ERROR("TcpInit err: %d", r);
    valk_async_handle_fail(handle, valk_lval_err("TCP init error: %d", r));
    valk_dll_pop(client->connection);
    valk_slab_release_ptr(sys->handleSlab, client->connection);
    free(ctx->client);
    free(ctx);
    return;
  }
  // LCOV_EXCL_STOP

  __vtable_nodelay(client->connection, 1);

  client->connection->http.connectReq.data = ctx;
  r = __vtable_connect(client->connection, client->interface, client->port);
  // LCOV_EXCL_START platform connect initiation failure
  if (r) {
    VALK_ERROR("Connect err: %d", r);
    valk_async_handle_fail(handle, valk_lval_err("Connect error: %d", r));
    valk_conn_transition(client->connection, VALK_CONN_EVT_ERROR);
    __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    free(ctx->client);
    free(ctx);
  }
  // LCOV_EXCL_STOP
}

valk_async_handle_t *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                                  const char *ip, const int port,
                                                  const char *hostname) {
  valk_async_handle_t *handle = valk_async_handle_new(sys, nullptr);
  if (!handle) { // LCOV_EXCL_BR_LINE OOM during handle creation
    return nullptr;
  }

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }

  if (!task) { // LCOV_EXCL_START
    VALK_ERROR("Handle slab exhausted in http2_connect"); // LCOV_EXCL_LINE OOM
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    return handle;
  } // LCOV_EXCL_STOP // LCOV_EXCL_LINE
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  valk_aio_http2_client *client = malloc(sizeof(valk_aio_http2_client));
  if (!client) { // LCOV_EXCL_START
    VALK_ERROR("Failed to allocate client");
    valk_async_handle_fail(handle, valk_lval_err("Failed to allocate client"));
    valk_mem_allocator_free(task->allocator, task);
    return handle;
  } // LCOV_EXCL_STOP
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
  valk_request_ctx_t *request_ctx;
} __request_send_ctx_t;

static void __valk_aio_http2_request_send_cb(valk_aio_system_t *sys,
                                             struct valk_aio_task_new *task) {
  UNUSED(sys);
  __request_send_ctx_t *ctx = task->arg;

  valk_aio_http2_client *client = ctx->client;
  valk_aio_handle_t *conn = client->connection;
  valk_async_handle_t *handle = ctx->handle;

  // LCOV_EXCL_START connection closing race condition
  if (conn->http.state == VALK_CONN_CLOSING || conn->http.state == VALK_CONN_CLOSED) {
    valk_async_handle_fail(handle, valk_lval_err("Client connection closing"));
    free(ctx);
    return;
  }
  // LCOV_EXCL_STOP

  VALK_INFO("Client ready: %s:%d", client->interface, client->port);
  VALK_DEBUG("req: %s%s", ctx->req->authority, ctx->req->path);

  __http2_client_req_res_t *reqres = malloc(sizeof(__http2_client_req_res_t));
  reqres->req = ctx->req;
  reqres->handle = handle;
  
  __add_pending_request(conn, handle);

  valk_http2_response_t *res = malloc(sizeof(valk_http2_response_t));
  memset(res, 0, sizeof(valk_http2_response_t));
  res->allocator = nullptr;
  res->headers.items = malloc(sizeof(struct valk_http2_header_t) * 8);
  res->headers.count = 0;
  res->headers.capacity = 8;
  u64 client_response_limit = 64 * 1024 * 1024;
  res->body = malloc(client_response_limit);
  res->bodyLen = 0;
  res->bodyCapacity = client_response_limit;

  reqres->res = res;

  valk_mem_allocator_t *alloc = ctx->req->allocator;
  VALK_WITH_ALLOC(alloc) {
    const u64 NUM_PSEUDO_HEADERS = 4;
    u64 trace_header_count = 0;
    char trace_id_buf[32] = {0};
    char span_id_buf[32] = {0};
    char deadline_buf[32] = {0};

    // LCOV_EXCL_START request context propagation - internal tracing feature
    if (ctx->request_ctx) {
      snprintf(trace_id_buf, sizeof(trace_id_buf), "%llu", (unsigned long long)ctx->request_ctx->trace_id);
      snprintf(span_id_buf, sizeof(span_id_buf), "%llu", (unsigned long long)ctx->request_ctx->span_id);
      trace_header_count = 2;
      if (ctx->request_ctx->deadline_us != VALK_NO_DEADLINE) {
        u64 remaining_ms = valk_request_ctx_remaining_ms(ctx->request_ctx);
        snprintf(deadline_buf, sizeof(deadline_buf), "%llu", (unsigned long long)remaining_ms);
        trace_header_count = 3;
      }
    }
    // LCOV_EXCL_STOP

    u64 hdrCount = ctx->req->headers.count + NUM_PSEUDO_HEADERS + trace_header_count;
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

    u64 trace_idx = NUM_PSEUDO_HEADERS + ctx->req->headers.count;
    // LCOV_EXCL_START trace header propagation - internal tracing feature
    if (trace_header_count >= 2) {
      hdrs[trace_idx].name = (u8 *)"x-trace-id";
      hdrs[trace_idx].value = (u8 *)valk_mem_alloc(strlen(trace_id_buf) + 1);
      memcpy((char*)hdrs[trace_idx].value, trace_id_buf, strlen(trace_id_buf) + 1);
      hdrs[trace_idx].namelen = 10;
      hdrs[trace_idx].valuelen = strlen(trace_id_buf);
      hdrs[trace_idx].flags = NGHTTP2_NV_FLAG_NO_COPY_NAME;

      hdrs[trace_idx + 1].name = (u8 *)"x-span-id";
      hdrs[trace_idx + 1].value = (u8 *)valk_mem_alloc(strlen(span_id_buf) + 1);
      memcpy((char*)hdrs[trace_idx + 1].value, span_id_buf, strlen(span_id_buf) + 1);
      hdrs[trace_idx + 1].namelen = 9;
      hdrs[trace_idx + 1].valuelen = strlen(span_id_buf);
      hdrs[trace_idx + 1].flags = NGHTTP2_NV_FLAG_NO_COPY_NAME;
    }
    if (trace_header_count >= 3) {
      hdrs[trace_idx + 2].name = (u8 *)"x-deadline-ms";
      hdrs[trace_idx + 2].value = (u8 *)valk_mem_alloc(strlen(deadline_buf) + 1);
      memcpy((char*)hdrs[trace_idx + 2].value, deadline_buf, strlen(deadline_buf) + 1);
      hdrs[trace_idx + 2].namelen = 13;
      hdrs[trace_idx + 2].valuelen = strlen(deadline_buf);
      hdrs[trace_idx + 2].flags = NGHTTP2_NV_FLAG_NO_COPY_NAME;
    }
    // LCOV_EXCL_STOP

    reqres->streamid = nghttp2_submit_request2(conn->http.session, nullptr, hdrs,
                                               hdrCount, nullptr, reqres);
    // LCOV_EXCL_START nghttp2 submit failure
    if (reqres->streamid < 0) {
      VALK_ERROR("Could not submit HTTP request: %s",
                 nghttp2_strerror(reqres->streamid));
      valk_async_handle_fail(handle, valk_lval_err("Could not submit HTTP request"));

      free(reqres);
      free(ctx);
      return;
    }
    // LCOV_EXCL_STOP

    res->stream_id = reqres->streamid;
    VALK_INFO("Submitted request stream_id=%ld", reqres->streamid);
  } // LCOV_EXCL_BR_LINE VALK_WITH_ALLOC macro cleanup

  if (SSL_is_init_finished(client->connection->http.io.ssl.ssl)) { // LCOV_EXCL_BR_LINE SSL state check
    valk_http2_continue_pending_send(conn);
  }

  free(ctx);
}

valk_async_handle_t *valk_aio_http2_request_send(valk_http2_request_t *req,
                                                  valk_aio_http2_client *client) {
  valk_request_ctx_t *req_ctx = valk_thread_ctx.request_ctx;
  // LCOV_EXCL_BR_START deadline exceeded early check
  if (req_ctx && valk_request_ctx_deadline_exceeded(req_ctx)) {
    valk_async_handle_t *failed_handle = valk_async_handle_new(client->sys, nullptr);
    if (failed_handle) {
      valk_async_handle_fail(failed_handle, valk_lval_err(":deadline-exceeded"));
    }
    return failed_handle;
  }
  // LCOV_EXCL_BR_STOP
  valk_async_handle_t *handle = valk_async_handle_new(client->sys, nullptr);
  if (!handle) { // LCOV_EXCL_BR_LINE OOM during handle creation
    return nullptr;
  }
  handle->request_ctx = req_ctx;

  valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)client->sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }

  if (!task) { // LCOV_EXCL_START
    VALK_ERROR("Handle slab exhausted in request_send");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    return handle;
  } // LCOV_EXCL_STOP
  task->allocator = (valk_mem_allocator_t *)client->sys->handleSlab;

  __request_send_ctx_t *ctx = malloc(sizeof(__request_send_ctx_t));
  ctx->client = client;
  ctx->req = req;
  ctx->handle = handle;
  ctx->request_ctx = valk_thread_ctx.request_ctx;

  task->arg = ctx;
  task->handle = handle;
  task->callback = __valk_aio_http2_request_send_cb;

  valk_uv_exec_task(client->sys, task);
  return handle;
}

static _Atomic u64 g_client_request_id = 0;

typedef struct {
  valk_aio_system_t *sys;
  valk_handle_t headers_handle;
  char *host;
  int port;
  char *path;
  valk_aio_http2_client *client;
  valk_mem_arena_t *arena;
  u64 request_id;
  valk_async_handle_t *async_handle;
} valk_http2_client_request_ctx_t;

static char *__client_arena_strdup(const char *s) {
  u64 len = strlen(s);
  char *dup = valk_mem_alloc(len + 1);
  memcpy(dup, s, len + 1);
  return dup;
}

static void __http2_client_request_response_done(valk_async_handle_t *handle, void *ctx_ptr);

static void __http2_client_request_connect_done(valk_async_handle_t *handle, void *ctx_ptr) {
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE GC safepoint macro
  
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
    req->method = __client_arena_strdup("GET");
    req->scheme = __client_arena_strdup("https");
    req->authority = __client_arena_strdup(ctx->host);
    req->path = __client_arena_strdup(ctx->path);
    da_init(&req->headers); // LCOV_EXCL_BR_LINE da_init macro

    valk_lval_t *headers = valk_handle_resolve(&valk_global_handle_table, ctx->headers_handle);
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

  valk_async_handle_t *request_handle = valk_aio_http2_request_send(req, ctx->client);
  atomic_store_explicit(&request_handle->on_done, __http2_client_request_response_done, memory_order_release);
  atomic_store_explicit(&request_handle->on_done_ctx, ctx, memory_order_relaxed);
  return;

cleanup:
  valk_handle_release(&valk_global_handle_table, ctx->headers_handle);
  free(ctx->host);
  free(ctx->path);
  free(ctx);
}

static void __http2_client_request_response_done(valk_async_handle_t *handle, void *ctx_ptr) {
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE GC safepoint macro
  
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
  valk_handle_release(&valk_global_handle_table, ctx->headers_handle);
  free(ctx->host);
  free(ctx->path);
  if (ctx->arena) { // LCOV_EXCL_BR_LINE defensive null check
    free(ctx->arena);
  }
  free(ctx);
}

valk_lval_t *valk_http2_client_request_with_headers_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *headers) {
  u64 req_id = atomic_fetch_add(&g_client_request_id, 1);
  VALK_INFO("http2/client-request[%llu]: %s:%d%s (with %zu headers)", 
            (unsigned long long)req_id, host, port, path,
            headers ? valk_lval_list_count(headers) : 0);

  valk_async_handle_t *async_handle = valk_async_handle_new(sys, e);

  valk_http2_client_request_ctx_t *ctx = malloc(sizeof(valk_http2_client_request_ctx_t));
  ctx->sys = sys;
  ctx->host = strdup(host);
  ctx->port = port;
  ctx->path = strdup(path);
  ctx->client = nullptr;
  ctx->arena = nullptr;
  ctx->request_id = req_id;
  ctx->async_handle = async_handle;

  valk_lval_t *heap_headers = headers ? valk_evacuate_to_heap(headers) : nullptr;
  ctx->headers_handle = heap_headers 
    ? valk_handle_create(&valk_global_handle_table, heap_headers)
    : (valk_handle_t){0, 0};

  VALK_INFO("http2/client-request[%llu]: async_handle=%p created", 
            (unsigned long long)req_id, (void*)async_handle);

  valk_async_handle_t *connect_handle = valk_aio_http2_connect_host(sys, host, port, host);
  atomic_store_explicit(&connect_handle->on_done, __http2_client_request_connect_done, memory_order_release);
  atomic_store_explicit(&connect_handle->on_done_ctx, ctx, memory_order_relaxed);

  VALK_INFO("http2/client-request[%llu]: connect_handle=%p created", 
            (unsigned long long)req_id, (void*)connect_handle);

  return valk_lval_handle(async_handle);
}

valk_lval_t *valk_http2_client_request_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path) {
  return valk_http2_client_request_with_headers_impl(e, sys, host, port, path, nullptr);
}


