#include "aio_http2_client.h"
#include "aio_http2_conn.h"
#include "aio_http2_session.h"
#include "aio_ssl.h"
#include "gc.h"

extern void valk_uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task);

#ifdef VALK_METRICS_ENABLED
extern valk_gauge_v2_t* client_connections_active;
#endif

static inline const valk_io_tcp_ops_t *__tcp_ops(valk_aio_handle_t *conn) {
  return conn->sys ? conn->sys->ops->tcp : NULL;
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
  *buf = NULL;
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

static void __valk_http2_response_free(valk_arc_box *box) {
  if (!box || !box->item) return;
  valk_http2_response_t *res = (valk_http2_response_t *)box->item;
  if (res->body) {
    free(res->body);
    res->body = NULL;
  }
  if (res->headers.items) {
    for (u64 i = 0; i < res->headers.count; i++) {
      if (res->headers.items[i].name) free((void*)res->headers.items[i].name);
      if (res->headers.items[i].value) free((void*)res->headers.items[i].value);
    }
    free(res->headers.items);
    res->headers.items = NULL;
  }
}

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

static int __http_client_on_stream_close_callback(nghttp2_session *session,
                                                  i32 stream_id,
                                                  u32 error_code,
                                                  void *user_data) {
  UNUSED(user_data);
  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (reqres) {
    if (error_code != NGHTTP2_NO_ERROR) {
      char errmsg[256];
      snprintf(errmsg, sizeof(errmsg), "HTTP/2 stream error: %s (code=%u)",
               nghttp2_http2_strerror(error_code), error_code);
      valk_arc_box *err = valk_arc_box_err(errmsg);
      valk_promise_respond(&reqres->promise, err);
      valk_arc_release(err);
    } else {
      valk_arc_box *box = reqres->res_box;
      valk_promise_respond(&reqres->promise, box);
    }
    valk_mem_free(reqres);
  }
  return 0;
}

static int __http_on_data_chunk_recv_callback(nghttp2_session *session,
                                              u8 flags, i32 stream_id,
                                              const u8 *data, size_t len,
                                              void *user_data) {
  (void)flags;
  (void)user_data;

  __http2_req_res_t *reqres =
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
  valk_arc_box *box = conn->http.connectReq.data;
  valk_aio_http2_client *client = box->item;
  valk_arc_retain(box);

  if (status < 0) {
    fprintf(stderr, "Client Connection err: %d\n", status);
    valk_arc_box *err = valk_arc_box_err("Client Connection err");
    valk_promise_respond(&client->_promise, err);
    valk_arc_release(err);
    
    if (client->connection && !__vtable_is_closing(client->connection)) {
      client->connection->http.state = VALK_CONN_CLOSING;
      __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    
    valk_arc_release(box);
    return;
  }

#ifdef VALK_METRICS_ENABLED
  if (!client_connections_active) {
    valk_label_set_v2_t client_labels = {
      .labels = {{"role", "client"}},
      .count = 1
    };
    client_connections_active = valk_gauge_get_or_create("http_connections_active",
      NULL, &client_labels);
  }
  valk_gauge_v2_inc(client_connections_active);
#endif

  if (!valk_http2_conn_write_buf_acquire(client->connection)) {
    VALK_ERROR("Failed to acquire write buffer for client handshake");
    valk_arc_box *err = valk_arc_box_err("TCP buffer exhausted during client connect");
    valk_promise_respond(&client->_promise, err);
    valk_arc_release(err);
    if (client->connection && !__vtable_is_closing(client->connection)) {
      client->connection->http.state = VALK_CONN_CLOSING;
      __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    valk_arc_release(box);
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
    valk_arc_box *err = valk_arc_box_err("SSL initialization failed for client connection");
    valk_promise_respond(&client->_promise, err);
    valk_arc_release(err);
    if (client->connection && !__vtable_is_closing(client->connection)) {
      client->connection->http.state = VALK_CONN_CLOSING;
      __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    valk_arc_release(box);
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

  valk_promise_respond(&client->_promise, box);
  valk_arc_release(box);
}

static void __aio_client_connect_cb(valk_aio_system_t *sys,
                                    valk_aio_task_new *task) {
  int r;

  valk_arc_box *box = task->arg;
  valk_aio_http2_client *client = box->item;

  valk_slab_item_t *slab_item = valk_slab_aquire(sys->handleSlab);
  if (!slab_item) {
    VALK_ERROR("Handle slab exhausted during client connect");
    valk_arc_box *err = valk_arc_box_err("Handle slab exhausted during client connect");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }
  client->connection = (valk_aio_handle_t *)slab_item->data;
  memset(client->connection, 0, sizeof(valk_aio_handle_t));
  client->connection->magic = VALK_AIO_HANDLE_MAGIC;
  client->connection->kind = VALK_HNDL_HTTP_CONN;
  client->connection->sys = sys;
  client->connection->onClose = valk_http2_conn_on_disconnect;

  client->connection->http.state = VALK_CONN_INIT;
  client->connection->http.io.buf_size = HTTP_SLAB_ITEM_SIZE;

  valk_dll_insert_after(&sys->liveHandles, client->connection);

  r = __vtable_init(client->connection);
  client->connection->uv.tcp.uv.data = client->connection;
  client->connection->uv.tcp.user_data = client->connection;

  if (r) {
    fprintf(stderr, "TcpInit err: %d \n", r);
    valk_arc_box *err = valk_arc_box_err("TcpInit err");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_dll_pop(client->connection);
    valk_slab_release_ptr(sys->handleSlab, client->connection);
    return;
  }

  __vtable_nodelay(client->connection, 1);

  client->connection->http.connectReq.data = box;
  client->_promise = task->promise;
  r = __vtable_connect(client->connection, client->interface, client->port);
  if (r) {
    fprintf(stderr, "Connect err: %d\n", r);
    valk_arc_box *err = valk_arc_box_err("Connect err");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    client->connection->http.state = VALK_CONN_CLOSING;
    __vtable_close(client->connection, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
  }
}

static void __valk_aio_http2_client_free(valk_arc_box *box) {
  valk_aio_http2_client *client = box->item;
  SSL_CTX_free(client->ssl_ctx);
  valk_mem_allocator_free(box->allocator, box);
}

valk_future *valk_aio_http2_connect_host(valk_aio_system_t *sys,
                                         const char *ip, const int port,
                                         const char *hostname) {

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }

  valk_future *res = valk_future_new();
  if (!task) {
    VALK_ERROR("Handle slab exhausted in http2_connect");
    valk_arc_box *err = valk_arc_box_err("Handle slab exhausted");
    valk_promise p = {.item = res};
    valk_arc_retain(res);
    valk_promise_respond(&p, err);
    valk_arc_release(err);
    return res;
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, sizeof(valk_aio_http2_client));
  box->free = __valk_aio_http2_client_free;

  task->arg = box;
  memset(box->item, 0, sizeof(valk_aio_http2_client));

  valk_aio_http2_client *client = box->item;
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

  task->promise.item = res;
  valk_arc_retain(res);
  task->callback = __aio_client_connect_cb;

  VALK_DEBUG("Initializing client %p", (void *)client);
  valk_uv_exec_task(sys, task);

  return res;
}

valk_future *valk_aio_http2_connect(valk_aio_system_t *sys,
                                    const char *interface, const int port,
                                    const char *certfile) {
  UNUSED(certfile);
  return valk_aio_http2_connect_host(sys, interface, port, "localhost");
}

static void __valk_aio_http2_request_send_cb(valk_aio_system_t *sys,
                                             struct valk_aio_task_new *task) {
  UNUSED(sys);
  __valk_request_client_pair_t *pair = task->arg;

  valk_aio_http2_client *client = pair->client;
  valk_aio_handle_t *conn = client->connection;

  if (conn->http.state == VALK_CONN_CLOSING || conn->http.state == VALK_CONN_CLOSED) {
    valk_arc_box *err = valk_arc_box_err("Client connection closing");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    return;
  }

  VALK_INFO("Client ready: %s:%d", client->interface, client->port);
  VALK_DEBUG("req: %s%s", pair->req->authority, pair->req->path);

  VALK_DEBUG("Constructing request on client %p", (void *)client);

  __http2_req_res_t *reqres = valk_mem_alloc(sizeof(__http2_req_res_t));
  reqres->req = pair->req;
  reqres->promise = task->promise;

  valk_arc_box *box =
      valk_arc_box_new(VALK_SUC, sizeof(valk_http2_response_t));
  box->free = __valk_http2_response_free;

  reqres->res_box = box;
  reqres->res = box->item;
  memset(reqres->res, 0, sizeof(valk_http2_response_t));
  da_init(&reqres->res->headers);

  u64 client_response_limit = 64 * 1024 * 1024;
  reqres->res->body = valk_mem_alloc(client_response_limit);
  reqres->res->bodyLen = 0;
  reqres->res->bodyCapacity = client_response_limit;

  VALK_TRACE("Box: %p, item: %p", (void*)box, reqres->res);

  VALK_WITH_ALLOC(pair->req->allocator) {
    const u64 NUM_PSEUDO_HEADERS = 4;
    u64 hdrCount = pair->req->headers.count + NUM_PSEUDO_HEADERS;
    struct valk_http2_header_t *phds = pair->req->headers.items;

    nghttp2_nv hdrs[hdrCount];

    hdrs[0].name = (u8 *)":method";
    hdrs[0].value = (u8 *)pair->req->method;
    hdrs[0].namelen = sizeof(":method") - 1;
    hdrs[0].valuelen = strlen(pair->req->method);
    hdrs[0].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[1].name = (u8 *)":scheme";
    hdrs[1].value = (u8 *)pair->req->scheme;
    hdrs[1].namelen = sizeof(":scheme") - 1;
    hdrs[1].valuelen = strlen(pair->req->scheme);
    hdrs[1].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[2].name = (u8 *)":authority";
    hdrs[2].value = (u8 *)pair->req->authority;
    hdrs[2].namelen = sizeof(":authority") - 1;
    hdrs[2].valuelen = strlen(pair->req->authority);
    hdrs[2].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    hdrs[3].name = (u8 *)":path";
    hdrs[3].value = (u8 *)pair->req->path;
    hdrs[3].namelen = sizeof(":path") - 1;
    hdrs[3].valuelen = strlen(pair->req->path);
    hdrs[3].flags =
        NGHTTP2_NV_FLAG_NO_COPY_NAME | NGHTTP2_NV_FLAG_NO_COPY_VALUE;

    for (u64 i = 0; i < pair->req->headers.count; ++i) {
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
      valk_arc_box *err = valk_arc_box_err("Could not submit HTTP request");
      valk_promise_respond(&task->promise, err);
      valk_arc_release(err);
      return;
    }

    reqres->res->stream_id = reqres->streamid;
    VALK_INFO("Submitted request stream_id=%ld", reqres->streamid);
  }

  if (SSL_is_init_finished(client->connection->http.io.ssl.ssl)) {
    valk_http2_continue_pending_send(conn);
  }
}

valk_future *valk_aio_http2_request_send(valk_http2_request_t *req,
                                         valk_aio_http2_client *client) {
  valk_future *res;
  valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)client->sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }

  if (!task) {
    VALK_ERROR("Handle slab exhausted in request_send");
    res = valk_future_new();
    valk_arc_box *err = valk_arc_box_err("Handle slab exhausted");
    valk_promise p = {.item = res};
    valk_arc_retain(res);
    valk_promise_respond(&p, err);
    valk_arc_release(err);
    return res;
  }
  task->allocator = (valk_mem_allocator_t *)client->sys->handleSlab;

  VALK_WITH_ALLOC(req->allocator) {
    res = valk_future_new();
    __valk_request_client_pair_t *pair =
        valk_mem_alloc(sizeof(__valk_request_client_pair_t));

    pair->client = client;
    pair->req = req;

    task->arg = pair;
    task->promise.item = res;
    valk_arc_retain(res);
    task->callback = __valk_aio_http2_request_send_cb;
  }
  valk_uv_exec_task(client->sys, task);
  return res;
}

typedef struct {
  valk_aio_system_t *sys;
  valk_lval_t *callback;
  valk_lenv_t *env;
  char *host;
  int port;
  char *path;
  valk_future *connect_future;
  valk_arc_box *client_box;
  valk_lval_t *headers;
} valk_http2_client_request_ctx_t;

static char *__client_arena_strdup(const char *s) {
  u64 len = strlen(s);
  char *dup = valk_mem_alloc(len + 1);
  memcpy(dup, s, len + 1);
  return dup;
}

static void __http2_client_request_response_cb(void *arg, valk_arc_box *result);

static void __http2_client_request_connect_cb(void *arg, valk_arc_box *result) {
  VALK_GC_SAFE_POINT();
  
  valk_http2_client_request_ctx_t *ctx = arg;

  if (result->type != VALK_SUC) {
    const char *errmsg = result->item ? (const char *)result->item : "unknown error";
    VALK_ERROR("http2/client-request: connection failed: %s", errmsg);
    if (ctx->callback && ctx->env) {
      valk_lval_t *err = valk_lval_err("Connection failed: %s", errmsg);
      valk_lval_t *args = valk_lval_cons(err, valk_lval_nil());
      valk_lval_eval_call(ctx->env, ctx->callback, args);
    }
    free(ctx->host);
    free(ctx->path);
    valk_arc_release(ctx->connect_future);
    free(ctx);
    return;
  }

  ctx->client_box = result;
  valk_arc_retain(result);
  valk_aio_http2_client *client = result->item;

  VALK_INFO("http2/client-request: connected to %s:%d", ctx->host, ctx->port);

  u64 arena_bytes = sizeof(valk_mem_arena_t) + (8 * 1024 * 1024) + (64 * 1024);
  valk_mem_arena_t *arena = malloc(arena_bytes);
  valk_mem_arena_init(arena, arena_bytes - sizeof(*arena));

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

  valk_future *response_future = valk_aio_http2_request_send(req, client);

  struct valk_future_and_then *response_cb = malloc(sizeof(struct valk_future_and_then));
  response_cb->arg = ctx;
  response_cb->cb = __http2_client_request_response_cb;
  valk_future_and_then(response_future, response_cb);
}

static void __http2_client_request_response_cb(void *arg, valk_arc_box *result) {
  VALK_GC_SAFE_POINT();
  
  valk_http2_client_request_ctx_t *ctx = arg;

  VALK_INFO("http2/client-request: response received");

  if (result->type != VALK_SUC) {
    const char *errmsg = result->item ? (const char *)result->item : "unknown error";
    VALK_ERROR("http2/client-request: request failed: %s", errmsg);
    if (ctx->callback && ctx->env) {
      valk_lval_t *err = valk_lval_err("Request failed: %s", errmsg);
      valk_lval_t *args = valk_lval_cons(err, valk_lval_nil());
      valk_lval_eval_call(ctx->env, ctx->callback, args);
    }
  } else {
    valk_http2_response_t *response = result->item;

    valk_lval_t *resp_ref = valk_lval_ref("success", response, NULL);
    valk_arc_retain(result);

    if (ctx->callback && ctx->env) {
      valk_lval_t *args = valk_lval_cons(resp_ref, valk_lval_nil());
      VALK_INFO("http2/client-request: calling callback with status %s",
                response->status ? response->status : "null");
      valk_lval_eval_call(ctx->env, ctx->callback, args);
    }
  }

  free(ctx->host);
  free(ctx->path);
  if (ctx->connect_future) {
    valk_arc_release(ctx->connect_future);
  }
  if (ctx->client_box) {
    valk_arc_release(ctx->client_box);
  }
  free(ctx);
}

valk_lval_t *valk_http2_client_request_with_headers_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *headers,
                                             valk_lval_t *callback) {
  VALK_INFO("http2/client-request: %s:%d%s (with %zu headers)", host, port, path,
            headers ? valk_lval_list_count(headers) : 0);

  valk_http2_client_request_ctx_t *ctx = malloc(sizeof(valk_http2_client_request_ctx_t));
  ctx->sys = sys;
  ctx->host = strdup(host);
  ctx->port = port;
  ctx->path = strdup(path);
  ctx->client_box = NULL;

  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    ctx->callback = valk_lval_copy(callback);
    ctx->headers = headers ? valk_lval_copy(headers) : NULL;
  }
  ctx->env = e;

  valk_future *connect_future = valk_aio_http2_connect_host(sys, host, port, host);
  ctx->connect_future = connect_future;
  valk_arc_retain(connect_future);

  struct valk_future_and_then *connect_cb = malloc(sizeof(struct valk_future_and_then));
  connect_cb->arg = ctx;
  connect_cb->cb = __http2_client_request_connect_cb;
  valk_future_and_then(connect_future, connect_cb);

  return valk_lval_nil();
}

valk_lval_t *valk_http2_client_request_impl(valk_lenv_t *e,
                                             valk_aio_system_t *sys,
                                             const char *host, int port,
                                             const char *path,
                                             valk_lval_t *callback) {
  return valk_http2_client_request_with_headers_impl(e, sys, host, port, path, NULL, callback);
}
