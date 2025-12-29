#include "aio_http2_server.h"
#include "aio_internal.h"
#include "aio_http2_conn.h"
#include "aio_http2_session.h"
#include "aio_ssl.h"
#include "../gc.h"

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

static inline int __vtable_accept(valk_aio_handle_t *server, valk_aio_handle_t *client) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(server);
  if (!ops) return -1;
  return ops->accept(__conn_tcp(server), __conn_tcp(client));
}

static inline int __vtable_nodelay(valk_aio_handle_t *conn, int enable) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->nodelay(__conn_tcp(conn), enable);
}

static void __vtable_alloc_cb(valk_io_tcp_t *tcp, u64 suggested, void **buf, u64 *buflen);
static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf);

static inline int __vtable_read_start(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->read_start(__conn_tcp(conn), __vtable_alloc_cb, __vtable_read_cb);
}

static inline int __vtable_bind(valk_aio_handle_t *conn, const char *ip, int port) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->bind(__conn_tcp(conn), ip, port);
}

static void __vtable_connection_cb(valk_io_tcp_t *server, int status);

static inline int __vtable_listen(valk_aio_handle_t *conn, int backlog) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->listen(__conn_tcp(conn), backlog, __vtable_connection_cb);
}

static inline int __vtable_getsockname(valk_aio_handle_t *conn, void *addr, int *len) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->getsockname(__conn_tcp(conn), addr, len);
}

static inline int __vtable_getpeername(valk_aio_handle_t *conn, void *addr, int *len) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->getpeername(__conn_tcp(conn), addr, len);
}

#ifdef VALK_METRICS_ENABLED
valk_gauge_v2_t* client_connections_active = NULL;

void valk_http2_server_metrics_init(valk_aio_system_t* sys, valk_server_metrics_t* m,
                                 const char* name, int port, const char* protocol,
                                 const char* loop_name) {
  char* port_str = sys->port_strs[sys->port_str_idx++ % sys->config.max_servers];
  snprintf(port_str, 8, "%d", port);

  valk_label_set_v2_t base_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}},
    .count = 4
  };

  m->requests_total = valk_counter_get_or_create("http_requests_total", NULL, &base_labels);

  valk_label_set_v2_t success_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}, {"status", "2xx"}},
    .count = 5
  };
  m->requests_success = valk_counter_get_or_create("http_requests_total", NULL, &success_labels);

  valk_label_set_v2_t client_err_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}, {"status", "4xx"}},
    .count = 5
  };
  m->requests_client_error = valk_counter_get_or_create("http_requests_total", NULL, &client_err_labels);

  valk_label_set_v2_t server_err_labels = {
    .labels = {{"server", name}, {"port", port_str}, {"protocol", protocol}, {"loop", loop_name}, {"status", "5xx"}},
    .count = 5
  };
  m->requests_server_error = valk_counter_get_or_create("http_requests_total", NULL, &server_err_labels);

  m->connections_active = valk_gauge_get_or_create("http_connections_active", NULL, &base_labels);
  m->sse_streams_active = valk_gauge_get_or_create("http_sse_streams_active", NULL, &base_labels);

  static const double latency_buckets[] = {
    0.00005, 0.0001, 0.00025, 0.0005,
    0.001, 0.0025, 0.005, 0.01,
    0.025, 0.05, 0.1, 0.25, 0.5,
    1.0, 2.5, 5.0, 10.0
  };
  m->request_duration = valk_histogram_get_or_create("http_request_duration_seconds",
    NULL, latency_buckets, 17, &base_labels);

  static const double sse_duration_buckets[] = {
    1.0, 5.0, 10.0, 30.0, 60.0,
    120.0, 300.0, 600.0, 1800.0, 3600.0
  };
  m->sse_stream_duration = valk_histogram_get_or_create("http_sse_stream_duration_seconds",
    NULL, sse_duration_buckets, 10, &base_labels);

  m->bytes_sent = valk_counter_get_or_create("http_bytes_sent_total", NULL, &base_labels);
  m->bytes_recv = valk_counter_get_or_create("http_bytes_recv_total", NULL, &base_labels);
  m->overload_responses = valk_counter_get_or_create("http_overload_responses_total", NULL, &base_labels);
}
#endif

static void __load_shed_close_cb(uv_handle_t *handle) {
  free(handle);
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

static void __http_server_accept_impl(valk_aio_handle_t *listener, int status);

static void __vtable_connection_cb(valk_io_tcp_t *server, int status) {
  valk_aio_handle_t *listener = server->user_data;
  __http_server_accept_impl(listener, status);
}

static void __http_server_accept_impl(valk_aio_handle_t *hndl, int status) {
  valk_aio_http_server *srv = hndl->arg;
  if (status < 0) {
    fprintf(stderr, "New connection error %s\n", srv->sys->ops->tcp->strerror(status));
    return;
  }

  if (srv->state == VALK_SRV_CLOSING || srv->state == VALK_SRV_CLOSED) {
    return;
  }

  if (!srv->sys || !srv->sys->tcpBufferSlab) return;

  u64 now_ms = srv->sys->ops->loop->now(srv->sys);
  valk_pressure_state_t state = valk_conn_admission_snapshot(srv->sys, now_ms);
  valk_conn_admission_result_t result = valk_conn_admission_check(&srv->sys->admission, &state);

  if (!result.accept) {
    VALK_WARN("Load shedding: rejecting connection (%s, level=%s)",
              result.reason ? result.reason : "unknown",
              valk_pressure_level_str(result.level));
#ifdef VALK_METRICS_ENABLED
    atomic_fetch_add(&srv->sys->metrics_state->system_stats.connections_rejected_load, 1);
#endif
    uv_tcp_t *reject_tcp = malloc(sizeof(uv_tcp_t));
    if (reject_tcp) {
      uv_tcp_init(srv->sys->eventloop, reject_tcp);
      const valk_io_tcp_ops_t *tcp_ops = srv->sys->ops->tcp;
      if (tcp_ops->accept(__conn_tcp(hndl), (valk_io_tcp_t *)reject_tcp) == 0) {
        uv_close((uv_handle_t *)reject_tcp, __load_shed_close_cb);
      } else {
        free(reject_tcp);
      }
    }
    return;
  }

  valk_slab_item_t *slab_item = valk_slab_aquire(srv->sys->handleSlab);
  if (!slab_item) {
    VALK_ERROR("Failed to allocate connection handle from slab");
    return;
  }
  valk_aio_handle_t *conn = (valk_aio_handle_t *)slab_item->data;
  memset(conn, 0, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->kind = VALK_HNDL_HTTP_CONN;
  conn->sys = srv->sys;
  conn->onClose = valk_http2_conn_on_disconnect;

  conn->http.state = VALK_CONN_INIT;
  conn->http.server = srv;
  conn->http.httpHandler = &srv->handler;
  conn->http.active_arena_head = UINT32_MAX;
  conn->http.io.buf_size = HTTP_SLAB_ITEM_SIZE;

#ifdef VALK_METRICS_ENABLED
  conn->http.diag.state = VALK_DIAG_CONN_CONNECTING;
  conn->http.diag.owner_idx = srv->owner_idx;
  conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
#endif

  valk_dll_insert_after(&srv->sys->liveHandles, conn);

  __vtable_init(conn);
  conn->uv.tcp.uv.data = conn;
  conn->uv.tcp.user_data = conn;

  int res = __vtable_accept(hndl, conn);

  if (!res) {
    struct sockaddr_storage client_addr;
    int addr_len = sizeof(client_addr);

    const valk_io_tcp_ops_t *tcp_ops = srv->sys->ops->tcp;
    if (__vtable_getpeername(conn, &client_addr, &addr_len) == 0) {
      char ip[INET6_ADDRSTRLEN];
      memset(ip, 0, sizeof(ip));
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
    } else {
      VALK_WARN("Could not get peer name");
    }

    static nghttp2_session_callbacks *callbacks = nullptr;
    if (!callbacks) {
      nghttp2_session_callbacks_new(&callbacks);
      nghttp2_session_callbacks_set_on_begin_headers_callback(
          callbacks, valk_http2_on_begin_headers_callback);
      nghttp2_session_callbacks_set_on_header_callback(
          callbacks, valk_http2_on_header_callback);
      nghttp2_session_callbacks_set_on_frame_recv_callback(
          callbacks, valk_http2_on_frame_recv_callback);
      nghttp2_session_callbacks_set_on_frame_send_callback(
          callbacks, valk_http2_server_on_frame_send_callback);
      nghttp2_session_callbacks_set_on_stream_close_callback(
          callbacks, valk_http2_server_on_stream_close_callback);
    }

    nghttp2_session_server_new3(&conn->http.session, callbacks, conn, nullptr,
                                valk_aio_nghttp2_mem());
    if (valk_aio_ssl_accept(&conn->http.io.ssl, srv->ssl_ctx) != 0) {
      VALK_ERROR("Failed to initialize SSL for connection");
      __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
      return;
    }

    valk_http2_send_server_connection_header(conn->http.session, srv->sys);

    if (conn->http.httpHandler && conn->http.httpHandler->onConnect) {
      conn->http.httpHandler->onConnect(conn->http.httpHandler->arg, conn);
    }

#ifdef VALK_METRICS_ENABLED
    valk_aio_metrics_on_connection(&srv->sys->metrics_state->metrics, true);
    valk_gauge_v2_inc(srv->metrics.connections_active);

    conn->http.diag.state = VALK_DIAG_CONN_ACTIVE;
    conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
    conn->http.diag.owner_idx = srv->owner_idx;
#endif

    __vtable_read_start(conn);
  } else {
    VALK_WARN("Accept error: %s", srv->sys->ops->tcp->strerror(res));

#ifdef VALK_METRICS_ENABLED
    valk_aio_metrics_on_connection(&srv->sys->metrics_state->metrics, false);
#endif

    if (!__vtable_is_closing(conn)) {
      conn->http.state = VALK_CONN_CLOSING;
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_CLOSING;
      conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
#endif
      __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
  }
}

static void __http_shutdown_cb(valk_aio_handle_t *hndl) {
  valk_aio_http_server *srv = hndl->arg;
  if (!srv || !srv->sys) {
    return;
  }

  if (srv->state == VALK_SRV_CLOSING || srv->state == VALK_SRV_CLOSED) {
    return;
  }

  srv->state = VALK_SRV_CLOSING;
  VALK_INFO("Server :%d shutting down, sending GOAWAY to connections", srv->port);

  valk_aio_system_t *sys = srv->sys;
  if (sys->shuttingDown) {
    srv->state = VALK_SRV_CLOSED;
    return;
  }

  int goaway_count = 0;

  valk_aio_handle_t *h = sys->liveHandles.next;
  while (h && h != &sys->liveHandles) {
    valk_aio_handle_t *next = h->next;

    if (h->kind == VALK_HNDL_HTTP_CONN && h->http.server == srv) {
      if (h->http.state == VALK_CONN_ESTABLISHED && 
          h->http.session &&
          !__vtable_is_closing(h)) {
        valk_http2_submit_goaway(h, NGHTTP2_NO_ERROR);
        valk_http2_flush_pending(h);
        goaway_count++;
      }
    }

    h = next;
  }

  if (goaway_count > 0) {
    VALK_INFO("Server :%d sent GOAWAY to %d connections", srv->port, goaway_count);
  }
  srv->state = VALK_SRV_CLOSED;
}

extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern valk_lval_t *valk_lval_ref(const char *type, void *ptr, void (*free)(void *));
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);

static void __http_listen_cb(valk_aio_system_t *sys,
                             struct valk_aio_task_new *task) {
  int r;
  valk_arc_box *box = task->arg;
  valk_async_handle_t *handle = task->handle;

  valk_aio_http_server *srv = box->item;
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
    valk_arc_release(box);
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

#ifdef VALK_METRICS_ENABLED
  const char* protocol = srv->ssl_ctx ? "https" : "http";
  valk_http2_server_metrics_init(sys, &srv->metrics, srv->interface, srv->port, protocol, sys->name);
  valk_aio_system_stats_on_server_start(&sys->metrics_state->system_stats);

  char owner_name[32];
  snprintf(owner_name, sizeof(owner_name), ":%d", srv->port);
  srv->owner_idx = valk_owner_register(sys, owner_name, 0, srv);
#endif

  r = __vtable_listen(srv->listener, 128);
  if (r) {
    VALK_ERROR("Listen error: %d", r);
    valk_async_handle_fail(handle, valk_lval_err("Error on Listening"));
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  VALK_INFO("Listening on %s:%d", srv->interface, srv->port);

  valk_lval_t *server_ref = valk_lval_ref("http_server", box, NULL);
  valk_async_handle_complete(handle, server_ref);
  valk_dll_insert_after(&sys->liveHandles, srv->listener);
}

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

static void __valk_sandbox_env_free(valk_lenv_t *env) {
  if (!env) return;

  for (u64 i = 0; i < env->symbols.count; i++) {
    if (env->symbols.items && env->symbols.items[i]) {
      free(env->symbols.items[i]);
    }
    if (env->vals.items && env->vals.items[i]) {
      valk_lval_t *lval = env->vals.items[i];
      if (LVAL_TYPE(lval) == LVAL_SYM || LVAL_TYPE(lval) == LVAL_STR ||
          LVAL_TYPE(lval) == LVAL_ERR) {
        if (lval->str) free(lval->str);
      }
      free(lval);
    }
  }
  if (env->symbols.items) free(env->symbols.items);
  if (env->vals.items) free(env->vals.items);
  free(env);
}

static void __valk_aio_http2_server_free(valk_arc_box *box) {
  valk_aio_http_server *srv = box->item;
#ifdef VALK_METRICS_ENABLED
  valk_aio_system_stats_on_server_stop(&srv->sys->metrics_state->system_stats);
#endif
  if (srv->lisp_handler_fn) {
    valk_gc_remove_global_root(&srv->lisp_handler_fn);
  }
  __valk_sandbox_env_free(srv->sandbox_env);
  SSL_CTX_free(srv->ssl_ctx);
  valk_mem_allocator_free(box->allocator, box);
}

extern valk_async_handle_t *valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);

valk_async_handle_t *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler) {
  return valk_aio_http2_listen_with_config(sys, interface, port, keyfile, certfile,
                                            handler, lisp_handler, NULL);
}

valk_async_handle_t *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config) {
  valk_arc_box *box = (valk_arc_box *)valk_slab_aquire(sys->httpServers)->data;
  valk_async_handle_t *handle = valk_async_handle_new(sys, NULL);

  valk_aio_http_server *srv;
  {
    valk_arc_box_init(box, VALK_SUC, sizeof(valk_aio_http_server));

    box->allocator = (valk_mem_allocator_t *)sys->httpServers;
    box->free = __valk_aio_http2_server_free;

    srv = box->item;
    memset(srv, 0, sizeof(valk_aio_http_server));
    srv->sys = sys;

    strncpy(srv->interface, interface, 200);
    srv->port = port;
    if (handler) {
      srv->handler = *handler;
    }
    srv->lisp_handler_fn = (valk_lval_t*)lisp_handler;
    if (lisp_handler) {
      valk_gc_add_global_root(&srv->lisp_handler_fn);
      void* saved_heap = valk_thread_ctx.heap;
      valk_thread_ctx.heap = NULL;
      VALK_WITH_ALLOC(&valk_malloc_allocator) {
        srv->sandbox_env = valk_lenv_sandboxed(((valk_lval_t*)lisp_handler)->fun.env);
      }
      valk_thread_ctx.heap = saved_heap;
    }

    if (config) {
      srv->config = *config;
    } else {
      srv->config = valk_http_server_config_default();
    }

    valk_err_e ssl_err = valk_aio_ssl_server_init(&srv->ssl_ctx, keyfile, certfile);
    if (ssl_err != VALK_ERR_SUCCESS) {
      VALK_ERROR("Failed to initialize SSL context (key=%s, cert=%s)", keyfile, certfile);
      valk_async_handle_fail(handle, valk_lval_err("SSL initialization failed"));
      valk_arc_release(box);
      return handle;
    }
    SSL_CTX_set_alpn_select_cb(srv->ssl_ctx, __alpn_select_proto_cb, NULL);
  }

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  if (!task) {
    VALK_ERROR("Handle slab exhausted in http2_listen");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    valk_arc_release(box);
    return handle;
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  task->arg = box;
  task->handle = handle;
  task->callback = __http_listen_cb;

  valk_uv_exec_task(sys, task);

  return handle;
}

void valk_aio_http2_server_set_handler(valk_aio_http_server *srv, void *handler_fn) {
  srv->lisp_handler_fn = (valk_lval_t*)handler_fn;
  __valk_sandbox_env_free(srv->sandbox_env);
  srv->sandbox_env = NULL;
  if (handler_fn) {
    void* saved_heap = valk_thread_ctx.heap;
    valk_thread_ctx.heap = NULL;
    VALK_WITH_ALLOC(&valk_malloc_allocator) {
      srv->sandbox_env = valk_lenv_sandboxed(((valk_lval_t*)handler_fn)->fun.env);
    }
    valk_thread_ctx.heap = saved_heap;
  }
}

int valk_aio_http2_server_get_port(valk_aio_http_server *srv) {
  return srv->port;
}

valk_aio_http_server* valk_aio_http2_server_from_ref(valk_lval_t *server_ref) {
  valk_arc_box *box = (valk_arc_box*)server_ref->ref.ptr;
  return (valk_aio_http_server*)box->item;
}

int valk_aio_http2_server_get_port_from_ref(valk_lval_t *server_ref) {
  return valk_aio_http2_server_from_ref(server_ref)->port;
}

typedef struct {
  valk_async_handle_t *handle;
  valk_arc_box *box;
} __http_stop_ctx_t;

static void __http_stop_listener_close_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  __http_stop_ctx_t *ctx = hndl->arg;
  valk_arc_box *box = ctx->box;
  valk_aio_http_server *srv = box->item;

  srv->state = VALK_SRV_CLOSED;
  VALK_INFO("Server :%d listener closed", srv->port);

  valk_async_handle_complete(ctx->handle, valk_lval_nil());
  valk_arc_release(box);

  valk_slab_t *slab = hndl->sys->handleSlab;
  valk_mem_allocator_free((valk_mem_allocator_t *)slab, ctx);

  valk_dll_pop(hndl);
  valk_slab_release_ptr(slab, hndl);
}

static void __http_stop_cb(valk_aio_system_t *sys,
                           struct valk_aio_task_new *task) {
  valk_arc_box *box = task->arg;
  valk_async_handle_t *handle = task->handle;
  valk_aio_http_server *srv = box->item;

  if (srv->state == VALK_SRV_CLOSED) {
    VALK_INFO("Server :%d already stopped", srv->port);
    valk_async_handle_complete(handle, valk_lval_nil());
    valk_arc_release(box);
    return;
  }

  if (srv->state == VALK_SRV_CLOSING) {
    VALK_INFO("Server :%d already stopping", srv->port);
    valk_async_handle_complete(handle, valk_lval_nil());
    valk_arc_release(box);
    return;
  }

  srv->state = VALK_SRV_CLOSING;
  VALK_INFO("Server :%d stopping, sending GOAWAY to connections", srv->port);

  if (!sys->shuttingDown) {
    int goaway_count = 0;
    valk_aio_handle_t *h = sys->liveHandles.next;
    while (h && h != &sys->liveHandles) {
      valk_aio_handle_t *next = h->next;
      if (h->kind == VALK_HNDL_HTTP_CONN && h->http.server == srv) {
        if (h->http.state == VALK_CONN_ESTABLISHED &&
            h->http.session && !__vtable_is_closing(h)) {
          valk_http2_submit_goaway(h, NGHTTP2_NO_ERROR);
          valk_http2_flush_pending(h);
          goaway_count++;
        }
      }
      h = next;
    }
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
    ctx->box = box;
    srv->listener->arg = ctx;
    srv->listener->onClose = NULL;
    __vtable_close(srv->listener, (valk_io_close_cb)__http_stop_listener_close_cb);
  } else {
    srv->state = VALK_SRV_CLOSED;
    valk_async_handle_complete(handle, valk_lval_nil());
    valk_arc_release(box);
  }
}

valk_async_handle_t *valk_aio_http2_stop(valk_aio_http_server *srv,
                                         valk_arc_box *box) {
  valk_aio_system_t *sys = srv->sys;
  valk_async_handle_t *handle = valk_async_handle_new(sys, NULL);

  valk_arc_retain(box);

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  if (!task) {
    VALK_ERROR("Handle slab exhausted in http2_stop");
    valk_async_handle_fail(handle, valk_lval_err("Handle slab exhausted"));
    valk_arc_release(box);
    return handle;
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;
  task->arg = box;
  task->handle = handle;
  task->callback = __http_stop_cb;

  valk_uv_exec_task(sys, task);

  return handle;
}
