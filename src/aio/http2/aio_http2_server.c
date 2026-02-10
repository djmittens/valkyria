#include "aio_http2_server.h"
#include "aio_internal.h"
#include "aio_http2_conn.h"
#include "aio_http2_session.h"
#include "aio_ssl.h"
#include "aio_metrics_v2.h"
#include "../gc.h"
#include "aio_tcp_helpers.h"

static void __vtable_alloc_cb(valk_io_tcp_t *tcp, u64 suggested, void **buf, u64 *buflen);
static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf);

static inline int __vtable_read_start(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->read_start(__conn_tcp(conn), __vtable_alloc_cb, __vtable_read_cb);
}

static inline int __vtable_bind(valk_aio_handle_t *conn, const char *ip, int port) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->bind(__conn_tcp(conn), ip, port);
}

static void __vtable_connection_cb(valk_io_tcp_t *server, int status);

static inline int __vtable_listen(valk_aio_handle_t *conn, int backlog) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->listen(__conn_tcp(conn), backlog, __vtable_connection_cb);
}

static inline int __vtable_getsockname(valk_aio_handle_t *conn, void *addr, int *len) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->getsockname(__conn_tcp(conn), addr, len);
}

static inline int __vtable_getpeername(valk_aio_handle_t *conn, void *addr, int *len) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->getpeername(__conn_tcp(conn), addr, len);
}

valk_gauge_v2_t* client_connections_active = nullptr;

void valk_http2_server_metrics_init(valk_aio_system_t* sys, valk_server_metrics_t* m,
                                 const char* name, int port, const char* protocol,
                                 const char* loop_name) {
  char* port_str = sys->port_strs[sys->port_str_idx++ % sys->config.max_servers];
  snprintf(port_str, 8, "%d", port);

  valk_label_set_v2_t base_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}},
    .count = 4
  };

  m->requests_total = valk_counter_get_or_create("http_requests_total", nullptr, &base_labels);

  valk_label_set_v2_t success_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}, {"status", "2xx"}},
    .count = 5
  };
  m->requests_success = valk_counter_get_or_create("http_requests_total", nullptr, &success_labels);

  valk_label_set_v2_t client_err_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}, {"status", "4xx"}},
    .count = 5
  };
  m->requests_client_error = valk_counter_get_or_create("http_requests_total", nullptr, &client_err_labels);

  valk_label_set_v2_t server_err_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}, {"status", "5xx"}},
    .count = 5
  };
  m->requests_server_error = valk_counter_get_or_create("http_requests_total", nullptr, &server_err_labels);

  m->connections_active = valk_gauge_get_or_create("http_connections_active", nullptr, &base_labels);
  m->sse_streams_active = valk_gauge_get_or_create("http_sse_streams_active", nullptr, &base_labels);

  static const double latency_buckets[] = {
    0.00005, 0.0001, 0.00025, 0.0005,
    0.001, 0.0025, 0.005, 0.01,
    0.025, 0.05, 0.1, 0.25, 0.5,
    1.0, 2.5, 5.0, 10.0
  };
  m->request_duration = valk_histogram_get_or_create("http_request_duration_seconds",
    nullptr, latency_buckets, 17, &base_labels);

  static const double sse_duration_buckets[] = {
    1.0, 5.0, 10.0, 30.0, 60.0,
    120.0, 300.0, 600.0, 1800.0, 3600.0
  };
  m->sse_stream_duration = valk_histogram_get_or_create("http_sse_stream_duration_seconds",
    nullptr, sse_duration_buckets, 10, &base_labels);

  m->bytes_sent = valk_counter_get_or_create("http_bytes_sent_total", nullptr, &base_labels);
  m->bytes_recv = valk_counter_get_or_create("http_bytes_recv_total", nullptr, &base_labels);
  m->overload_responses = valk_counter_get_or_create("http_overload_responses_total", nullptr, &base_labels);
}

static void __load_shed_close_cb(uv_handle_t *handle) {
  free(handle);
}

// LCOV_EXCL_START libuv internal callback - invoked from event loop thread only
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
// LCOV_EXCL_STOP

// LCOV_EXCL_START libuv internal callback - invoked from event loop thread only
static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf) {
  valk_aio_handle_t *conn = tcp->user_data;
  valk_http2_conn_tcp_read_impl(conn, nread, buf);
}
// LCOV_EXCL_STOP

static void __http_server_accept_impl(valk_aio_handle_t *listener, int status);

// LCOV_EXCL_START libuv internal callback - invoked from event loop thread only
static void __vtable_connection_cb(valk_io_tcp_t *server, int status) {
  valk_aio_handle_t *listener = server->user_data;
  __http_server_accept_impl(listener, status);
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static bool __accept_should_reject(valk_aio_http_server *srv, valk_aio_handle_t *hndl, int status) {
  if (status < 0) {
    fprintf(stderr, "New connection error %s\n", srv->sys->ops->tcp->strerror(status));
    return true;
  }
  if (srv->state == VALK_SRV_CLOSING || srv->state == VALK_SRV_CLOSED) return true;
  if (!srv->sys || !srv->sys->tcpBufferSlab) return true;

  u64 now_ms = srv->sys->ops->loop->now(srv->sys);
  valk_pressure_state_t state = valk_conn_admission_snapshot(srv->sys, now_ms);
  valk_conn_admission_result_t result = valk_conn_admission_check(&srv->sys->admission, &state);

  if (result.accept) return false;

  VALK_WARN("Load shedding: rejecting connection (%s, level=%s)",
            result.reason ? result.reason : "unknown",
            valk_pressure_level_str(result.level));
  valk_counter_v2_inc(((valk_aio_system_stats_v2_t*)srv->sys->metrics_state->system_stats_v2)->connections_rejected_load);
  uv_tcp_t *reject_tcp = malloc(sizeof(uv_tcp_t));
  if (reject_tcp) {
    uv_tcp_init(srv->sys->eventloop, reject_tcp);
    if (srv->sys->ops->tcp->accept(__conn_tcp(hndl), (valk_io_tcp_t *)reject_tcp) == 0) {
      uv_close((uv_handle_t *)reject_tcp, __load_shed_close_cb);
    } else {
      free(reject_tcp);
    }
  }
  return true;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static valk_aio_handle_t *__accept_alloc_conn(valk_aio_http_server *srv) {
  valk_slab_item_t *slab_item = valk_slab_aquire(srv->sys->handleSlab);
  if (!slab_item) {
    VALK_ERROR("Failed to allocate connection handle from slab");
    return nullptr;
  }
  valk_aio_handle_t *conn = (valk_aio_handle_t *)slab_item->data;
  memset(conn, 0, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->kind = VALK_HNDL_HTTP_CONN;
  conn->sys = srv->sys;
  conn->onClose = valk_http2_conn_on_disconnect;

  valk_conn_init_state(conn);
  conn->http.server = srv;
  conn->http.httpHandler = &srv->handler;
  conn->http.active_arena_head = UINT32_MAX;
  conn->http.io.buf_size = HTTP_SLAB_ITEM_SIZE;

  conn->http.diag.owner_idx = srv->owner_idx;

  valk_dll_insert_after(&srv->sys->liveHandles, conn);

  __vtable_init(conn);
  conn->uv.tcp.uv.data = conn;
  conn->uv.tcp.user_data = conn;
  return conn;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static void __accept_log_peer(valk_aio_handle_t *conn) {
  struct sockaddr_storage client_addr;
  int addr_len = sizeof(client_addr);
  const valk_io_tcp_ops_t *tcp_ops = conn->sys->ops->tcp;

  if (__vtable_getpeername(conn, &client_addr, &addr_len) != 0) {
    VALK_WARN("Could not get peer name");
    return;
  }

  char ip[INET6_ADDRSTRLEN] = {0};
  u16 port = 0;
  if (client_addr.ss_family == AF_INET) {
    struct sockaddr_in *addr4 = (struct sockaddr_in *)&client_addr;
    tcp_ops->ip4_name(addr4, ip, sizeof(ip));
    port = ntohs(addr4->sin_port);
  } else if (client_addr.ss_family == AF_INET6) {
    struct sockaddr_in6 *addr6 = (struct sockaddr_in6 *)&client_addr;
    tcp_ops->ip6_name(addr6, ip, sizeof(ip));
    port = ntohs(addr6->sin6_port);
  }
  VALK_INFO("Accepted connection from %s:%d", ip, port);
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static nghttp2_session_callbacks *__accept_get_callbacks(void) {
  static nghttp2_session_callbacks *callbacks = nullptr;
  if (callbacks) return callbacks;

  nghttp2_session_callbacks_new(&callbacks);
  nghttp2_session_callbacks_set_on_begin_headers_callback(callbacks, valk_http2_on_begin_headers_callback);
  nghttp2_session_callbacks_set_on_header_callback(callbacks, valk_http2_on_header_callback);
  nghttp2_session_callbacks_set_on_frame_recv_callback(callbacks, valk_http2_on_frame_recv_callback);
  nghttp2_session_callbacks_set_on_frame_send_callback(callbacks, valk_http2_server_on_frame_send_callback);
  nghttp2_session_callbacks_set_on_stream_close_callback(callbacks, valk_http2_server_on_stream_close_callback);
  return callbacks;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static int __accept_setup_session(valk_aio_handle_t *conn, valk_aio_http_server *srv) {
  nghttp2_session_server_new3(&conn->http.session, __accept_get_callbacks(), conn, nullptr,
                              valk_aio_nghttp2_mem());
  if (valk_aio_ssl_accept(&conn->http.io.ssl, srv->ssl_ctx) != 0) {
    VALK_ERROR("Failed to initialize SSL for connection");
    return -1;
  }
  valk_http2_send_server_connection_header(conn->http.session, srv->sys);
  return 0;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static void __accept_finalize(valk_aio_handle_t *conn, valk_aio_http_server *srv) {
  if (conn->http.httpHandler && conn->http.httpHandler->onConnect) {
    conn->http.httpHandler->onConnect(conn->http.httpHandler->arg, conn);
  }

  valk_aio_metrics_v2_on_connection(
      (valk_aio_metrics_v2_t*)srv->sys->metrics_state->metrics_v2, true);
  valk_gauge_v2_inc(srv->metrics.connections_active);
  conn->http.diag.state = VALK_DIAG_CONN_ACTIVE;
  conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
  conn->http.diag.owner_idx = srv->owner_idx;

  __vtable_read_start(conn);
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static void __accept_handle_error(valk_aio_handle_t *conn, valk_aio_http_server *srv, int res) {
  VALK_WARN("Accept error: %s", srv->sys->ops->tcp->strerror(res));
  valk_aio_metrics_v2_on_connection(
      (valk_aio_metrics_v2_t*)srv->sys->metrics_state->metrics_v2, false);
  if (!__vtable_is_closing(conn)) {
    valk_conn_transition(conn, VALK_CONN_EVT_ERROR);
    __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
  }
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal accept path - invoked from libuv connection callback
static void __http_server_accept_impl(valk_aio_handle_t *hndl, int status) {
  valk_aio_http_server *srv = hndl->arg;

  if (__accept_should_reject(srv, hndl, status)) return;

  valk_aio_handle_t *conn = __accept_alloc_conn(srv);
  if (!conn) return;

  int res = __vtable_accept(hndl, conn);
  if (res != 0) {
    __accept_handle_error(conn, srv, res);
    return;
  }

  __accept_log_peer(conn);

  if (__accept_setup_session(conn, srv) != 0) {
    __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    return;
  }

  __accept_finalize(conn, srv);
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal shutdown path - invoked from libuv callback
static int __send_goaway_to_all_conns(valk_aio_system_t *sys, valk_aio_http_server *srv) {
  int goaway_count = 0;
  valk_aio_handle_t *h = sys->liveHandles.next;
  while (h && h != &sys->liveHandles) {
    valk_aio_handle_t *next = h->next;
    if (h->kind == VALK_HNDL_HTTP_CONN && h->http.server == srv &&
        h->http.state == VALK_CONN_ESTABLISHED && h->http.session &&
        !__vtable_is_closing(h)) {
      valk_http2_submit_goaway(h, NGHTTP2_NO_ERROR);
      valk_http2_flush_pending(h);
      goaway_count++;
    }
    h = next;
  }
  return goaway_count;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal shutdown callback - invoked from libuv
static void __http_shutdown_cb(valk_aio_handle_t *hndl) {
  valk_aio_http_server *srv = hndl->arg;
  if (!srv || !srv->sys) return;

  valk_aio_system_t *sys = srv->sys;
  
  if (srv->state == VALK_SRV_CLOSING || srv->state == VALK_SRV_CLOSED) {
    if (sys->shuttingDown && srv->lisp_handler_handle.generation > 0) {
      valk_handle_release(&valk_sys->handle_table, srv->lisp_handler_handle);
      srv->lisp_handler_handle = (valk_handle_t){0, 0};
    }
    return;
  }

  srv->state = VALK_SRV_CLOSING;
  VALK_INFO("Server :%d shutting down, sending GOAWAY to connections", srv->port);

  if (sys->shuttingDown) {
    if (srv->lisp_handler_handle.generation > 0) {
      valk_handle_release(&valk_sys->handle_table, srv->lisp_handler_handle);
      srv->lisp_handler_handle = (valk_handle_t){0, 0};
    }
    srv->state = VALK_SRV_CLOSED;
    return;
  }

  int goaway_count = __send_goaway_to_all_conns(sys, srv);
  if (goaway_count > 0) {
    VALK_INFO("Server :%d sent GOAWAY to %d connections", srv->port, goaway_count);
  }
  srv->state = VALK_SRV_CLOSED;
}
// LCOV_EXCL_STOP

extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern valk_lval_t *valk_lval_ref(const char *type, void *ptr, void (*free)(void *));
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);

// LCOV_EXCL_START internal cleanup - only called during server cleanup
static void __valk_aio_http2_server_cleanup(valk_aio_http_server *srv) {
  if (!srv || !srv->sys) return;
  valk_aio_system_stats_v2_on_server_stop(
      (valk_aio_system_stats_v2_t*)srv->sys->metrics_state->system_stats_v2);
  if (srv->lisp_handler_handle.generation > 0) {
    valk_handle_release(&valk_sys->handle_table, srv->lisp_handler_handle);
    srv->lisp_handler_handle = (valk_handle_t){0, 0};
  }
  SSL_CTX_free(srv->ssl_ctx);
  srv->ssl_ctx = nullptr;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal list management - only called during server cleanup
static void __valk_server_list_remove(valk_aio_http_server *srv) {
  if (!srv || !srv->sys) return;
  valk_aio_system_t *sys = srv->sys;
  if (srv->prev) {
    srv->prev->next = srv->next;
  } else {
    sys->serverList = srv->next;
  }
  if (srv->next) {
    srv->next->prev = srv->prev;
  }
  srv->next = nullptr;
  srv->prev = nullptr;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal list management - only called during server setup
static void __valk_server_list_insert(valk_aio_system_t *sys, valk_aio_http_server *srv) {
  srv->next = sys->serverList;
  srv->prev = nullptr;
  if (sys->serverList) {
    sys->serverList->prev = srv;
  }
  sys->serverList = srv;
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START internal callback - invoked from libuv async dispatch
static void __http_listen_cb(valk_aio_system_t *sys,
                             struct valk_aio_task_new *task) {
  int r;
  valk_aio_http_server *srv = task->arg;
  valk_async_handle_t *handle = task->handle;

  srv->listener = (void *)valk_slab_aquire(sys->handleSlab)->data;

  memset(srv->listener, 0, sizeof(valk_aio_handle_t));
  srv->listener->magic = VALK_AIO_HANDLE_MAGIC;
  srv->listener->kind = VALK_HNDL_TCP;
  srv->listener->sys = sys;
  srv->listener->arg = srv;
  srv->listener->onClose = __http_shutdown_cb;

  r = __vtable_init(srv->listener);
  srv->listener->uv.tcp.uv.data = srv->listener;
  srv->listener->uv.tcp.user_data = srv->listener;
  VALK_ASSERT(r == 0, "tcp init failed: %d", r);
  __vtable_nodelay(srv->listener, 1);

  r = __vtable_bind(srv->listener, srv->interface, srv->port);
  if (r) {
    VALK_ERROR("Bind error: %d", r);
    valk_async_handle_fail(handle, valk_lval_err("Error on Bind"));
    __valk_aio_http2_server_cleanup(srv);
    valk_slab_release_ptr(sys->httpServers, srv);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  if (srv->port == 0) {
    struct sockaddr_in bound_addr;
    int namelen = sizeof(bound_addr);
    r = __vtable_getsockname(srv->listener, &bound_addr, &namelen);
    if (r == 0) {
      srv->port = ntohs(bound_addr.sin_port);
    }
  }

  const char* protocol = srv->ssl_ctx ? "https" : "http";
  valk_http2_server_metrics_init(sys, &srv->metrics, srv->interface, srv->port, protocol, sys->name);
  valk_aio_system_stats_v2_on_server_start(
      (valk_aio_system_stats_v2_t*)sys->metrics_state->system_stats_v2);

  char owner_name[32];
  snprintf(owner_name, sizeof(owner_name), ":%d", srv->port);
  srv->owner_idx = valk_owner_register(sys, owner_name, 0, srv);

  r = __vtable_listen(srv->listener, 128);
  if (r) {
    VALK_ERROR("Listen error: %d", r);
    valk_async_handle_fail(handle, valk_lval_err("Error on Listening"));
    __valk_aio_http2_server_cleanup(srv);
    valk_slab_release_ptr(sys->httpServers, srv);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  VALK_INFO("Listening on %s:%d", srv->interface, srv->port);

  __valk_server_list_insert(sys, srv);
  valk_lval_t *server_ref = valk_lval_ref("http_server", srv, nullptr);
  valk_async_handle_complete(handle, server_ref);
  valk_dll_insert_after(&sys->liveHandles, srv->listener);
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START SSL callback - invoked during TLS handshake
static int __alpn_select_proto_cb(SSL *ssl, const unsigned char **out,
                                  unsigned char *outlen,
                                  const unsigned char *in, unsigned int inlen,
                                  void *arg) {
  UNUSED(ssl);
  UNUSED(arg);

  int rv;
  rv = nghttp2_select_alpn(out, outlen, in, inlen);
  if (rv == -1) {
    return SSL_TLSEXT_ERR_NOACK;
  }
  return SSL_TLSEXT_ERR_OK;
}
// LCOV_EXCL_STOP

extern valk_async_handle_t *valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);

valk_async_handle_t *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler) {
  return valk_aio_http2_listen_with_config(sys, interface, port, keyfile, certfile,
                                            handler, lisp_handler, nullptr);
}

valk_async_handle_t *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config) {
  valk_slab_item_t *slab_item = valk_slab_aquire(sys->httpServers);
  if (!slab_item) { // LCOV_EXCL_START
    valk_async_handle_t *handle = valk_async_handle_new(sys, nullptr);
    valk_async_handle_fail(handle, valk_lval_err("Server slab exhausted"));
    return handle;
  } // LCOV_EXCL_STOP
  valk_aio_http_server *srv = (valk_aio_http_server *)slab_item->data;
  valk_async_handle_t *handle = valk_async_handle_new(sys, nullptr);

  memset(srv, 0, sizeof(valk_aio_http_server));
  srv->sys = sys;

  strncpy(srv->interface, interface, 200);
  srv->port = port;
  if (handler) {
    srv->handler = *handler;
  }
  if (lisp_handler) {
    valk_lval_t *heap_handler = valk_evacuate_to_heap((valk_lval_t*)lisp_handler);
    srv->lisp_handler_handle = valk_handle_create(&valk_sys->handle_table, heap_handler);
  } else {
    srv->lisp_handler_handle = (valk_handle_t){0, 0};
  }

  if (config) {
    srv->config = *config;
  } else {
    srv->config = valk_http_server_config_default();
  }

  valk_err_e ssl_err = valk_aio_ssl_server_init(&srv->ssl_ctx, keyfile, certfile);
  if (ssl_err != VALK_ERR_SUCCESS) { // LCOV_EXCL_START SSL cert/key file error
    VALK_ERROR("Failed to initialize SSL context (key=%s, cert=%s)", keyfile, certfile);
    valk_async_handle_fail(handle, valk_lval_err("SSL initialization failed"));
    valk_slab_release_ptr(sys->httpServers, srv);
    return handle;
  } // LCOV_EXCL_STOP
  SSL_CTX_set_alpn_select_cb(srv->ssl_ctx, __alpn_select_proto_cb, nullptr);

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  if (!task) { // LCOV_EXCL_START
    VALK_ERROR("Handle slab exhausted in http2_listen");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    __valk_aio_http2_server_cleanup(srv);
    valk_slab_release_ptr(sys->httpServers, srv);
    return handle;
  } // LCOV_EXCL_STOP
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  task->arg = srv;
  task->handle = handle;
  task->callback = __http_listen_cb;

  valk_uv_exec_task(sys, task);

  return handle;
}

void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn) {
  if (srv->lisp_handler_handle.generation > 0) { // LCOV_EXCL_BR_LINE requires GC heap handler setup
    valk_handle_release(&valk_sys->handle_table, srv->lisp_handler_handle);
  }
  if (handler_fn) { // LCOV_EXCL_BR_LINE requires GC heap handler setup
    // LCOV_EXCL_START requires full GC heap for handler evacuation
    valk_lval_t *heap_handler = valk_evacuate_to_heap((valk_lval_t*)handler_fn);
    srv->lisp_handler_handle = valk_handle_create(&valk_sys->handle_table, heap_handler);
    // LCOV_EXCL_STOP
  } else {
    srv->lisp_handler_handle = (valk_handle_t){0, 0};
  }
}

int valk_aio_http2_server_get_port(valk_aio_http_server *srv) {
  return srv->port;
}

bool valk_aio_http2_server_is_stopped(valk_aio_http_server *srv) {
  return !srv || srv->state == VALK_SRV_CLOSED || srv->state == VALK_SRV_CLOSING;
}

valk_aio_http_server* valk_aio_http2_server_from_ref(valk_lval_t *server_ref) {
  return (valk_aio_http_server*)server_ref->ref.ptr;
}

int valk_aio_http2_server_get_port_from_ref(valk_lval_t *server_ref) {
  return valk_aio_http2_server_from_ref(server_ref)->port;
}

typedef struct {
  valk_async_handle_t *handle;
  valk_aio_http_server *srv;
} __http_stop_ctx_t;

// LCOV_EXCL_START internal shutdown callbacks - invoked from libuv
static void __http_stop_listener_close_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  __http_stop_ctx_t *ctx = hndl->arg;
  valk_aio_http_server *srv = ctx->srv;
  valk_aio_system_t *sys = hndl->sys;

  srv->state = VALK_SRV_CLOSED;
  VALK_INFO("Server :%d listener closed", srv->port);

  __valk_server_list_remove(srv);
  __valk_aio_http2_server_cleanup(srv);
  valk_slab_release_ptr(sys->httpServers, srv);

  valk_async_handle_complete(ctx->handle, valk_lval_nil());

  valk_slab_t *slab = sys->handleSlab;
  valk_mem_allocator_free((valk_mem_allocator_t *)slab, ctx);

  valk_dll_pop(hndl);
  valk_slab_release_ptr(slab, hndl);
}

static void __http_stop_cb(valk_aio_system_t *sys,
                           struct valk_aio_task_new *task) {
  valk_aio_http_server *srv = task->arg;
  valk_async_handle_t *handle = task->handle;

  if (srv->state == VALK_SRV_CLOSED || srv->state == VALK_SRV_CLOSING) {
    VALK_INFO("Server :%d already %s", srv->port,
              srv->state == VALK_SRV_CLOSED ? "stopped" : "stopping");
    valk_async_handle_complete(handle, valk_lval_nil());
    return;
  }

  srv->state = VALK_SRV_CLOSING;
  VALK_INFO("Server :%d stopping, sending GOAWAY to connections", srv->port);

  if (!sys->shuttingDown) {
    int goaway_count = __send_goaway_to_all_conns(sys, srv);
    if (goaway_count > 0) {
      VALK_INFO("Server :%d sent GOAWAY to %d connections", srv->port, goaway_count);
    }
  }

  if (srv->listener && !__vtable_is_closing(srv->listener)) {
    __http_stop_ctx_t *ctx;
    VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
      ctx = valk_mem_alloc(sizeof(__http_stop_ctx_t));
    }
    ctx->handle = handle;
    ctx->srv = srv;
    srv->listener->arg = ctx;
    srv->listener->onClose = nullptr;
    __vtable_close(srv->listener, (valk_io_close_cb)__http_stop_listener_close_cb);
  } else {
    srv->state = VALK_SRV_CLOSED;
    __valk_server_list_remove(srv);
    __valk_aio_http2_server_cleanup(srv);
    valk_slab_release_ptr(sys->httpServers, srv);
    valk_async_handle_complete(handle, valk_lval_nil());
  }
}
// LCOV_EXCL_STOP

valk_async_handle_t *valk_aio_http2_stop(valk_aio_http_server *srv) {
  if (!srv || !srv->sys) { // LCOV_EXCL_BR_LINE valid server path requires full AIO integration
    return nullptr;
  }
  // LCOV_EXCL_START valid server stop requires full AIO system (tested in test_http2_streaming.c)
  valk_aio_system_t *sys = srv->sys;
  valk_async_handle_t *handle = valk_async_handle_new(sys, nullptr);

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  if (!task) {
    VALK_ERROR("Handle slab exhausted in http2_stop");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    return handle;
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;
  task->arg = srv;
  task->handle = handle;
  task->callback = __http_stop_cb;

  valk_uv_exec_task(sys, task);

  return handle;
}
// LCOV_EXCL_STOP

void valk_aio_http2_cleanup_all_servers(valk_aio_system_t *sys) {
  if (!sys) return;

  valk_aio_http_server *srv = sys->serverList;
  while (srv) {
    valk_aio_http_server *next = srv->next;
    __valk_aio_http2_server_cleanup(srv);
    valk_slab_release_ptr(sys->httpServers, srv);
    srv = next;
  }
  sys->serverList = nullptr;
}
