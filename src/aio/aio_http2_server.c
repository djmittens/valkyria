#include "aio_http2_server.h"
#include "aio_internal.h"
#include "aio_http2_conn.h"
#include "aio_http2_session.h"
#include "aio_ssl.h"

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

  m->bytes_sent = valk_counter_get_or_create("http_bytes_sent_total", NULL, &base_labels);
  m->bytes_recv = valk_counter_get_or_create("http_bytes_recv_total", NULL, &base_labels);
  m->overload_responses = valk_counter_get_or_create("http_overload_responses_total", NULL, &base_labels);
}
#endif

static void __load_shed_close_cb(uv_handle_t *handle) {
  free(handle);
}

static void __http_server_accept_cb(uv_stream_t *stream, int status) {
  if (status < 0) {
    fprintf(stderr, "New connection error %s\n", uv_strerror(status));
    return;
  }

  valk_aio_handle_t *hndl = stream->data;
  valk_aio_http_server *srv = hndl->arg;

  if (srv->state == VALK_SRV_CLOSING || srv->state == VALK_SRV_CLOSED) {
    return;
  }

  if (!srv->sys || !srv->sys->tcpBufferSlab) return;

  uint64_t now_ms = uv_now(stream->loop);
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
      uv_tcp_init(stream->loop, reject_tcp);
      if (uv_accept(stream, (uv_stream_t *)reject_tcp) == 0) {
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
  conn->uv.tcp.data = conn;

  conn->http.state = VALK_CONN_INIT;
  conn->http.server = srv;
  conn->http.httpHandler = &srv->handler;
  conn->http.active_arena_head = UINT32_MAX;

#ifdef VALK_METRICS_ENABLED
  conn->http.diag.state = VALK_DIAG_CONN_CONNECTING;
  conn->http.diag.owner_idx = srv->owner_idx;
  conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif

  valk_dll_insert_after(&srv->sys->liveHandles, conn);

  uv_tcp_init(stream->loop, &conn->uv.tcp);

  int res = uv_accept(stream, (uv_stream_t *)&conn->uv.tcp);

  if (!res) {
    struct sockaddr_storage client_addr;
    int addr_len = sizeof(client_addr);

    if (uv_tcp_getpeername(&conn->uv.tcp,
                           (struct sockaddr *)&client_addr, &addr_len) == 0) {
      char ip[INET6_ADDRSTRLEN];
      memset(ip, 0, sizeof(ip));
      uint16_t port = 0;
      if (client_addr.ss_family == AF_INET) {
        struct sockaddr_in *addr4 = (struct sockaddr_in *)&client_addr;
        uv_ip4_name(addr4, ip, sizeof(ip));
        port = ntohs(addr4->sin_port);
      } else if (client_addr.ss_family == AF_INET6) {
        struct sockaddr_in6 *addr6 = (struct sockaddr_in6 *)&client_addr;
        uv_ip6_name(addr6, ip, sizeof(ip));
        port = ntohs(addr6->sin6_port);
      }

      VALK_INFO("Accepted connection from %s:%d", ip, port);
    } else {
      VALK_WARN("Could not get peer name");
    };

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
      uv_close((uv_handle_t *)&conn->uv.tcp, valk_http2_conn_handle_closed_cb);
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
    conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
    conn->http.diag.owner_idx = srv->owner_idx;
#endif

    uv_read_start((uv_stream_t *)&conn->uv.tcp, valk_http2_conn_alloc_callback,
                  valk_http2_conn_tcp_read_cb);
  } else {
    VALK_WARN("Accept error: %s", uv_strerror(res));

#ifdef VALK_METRICS_ENABLED
    valk_aio_metrics_on_connection(&srv->sys->metrics_state->metrics, false);
#endif

    if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
      conn->http.state = VALK_CONN_CLOSING;
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_CLOSING;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
      uv_close((uv_handle_t *)&conn->uv.tcp, valk_http2_conn_handle_closed_cb);
    }
  }
}

static void __http_shutdown_cb(valk_aio_handle_t *hndl) {
  UNUSED(hndl);
  VALK_INFO("TODO: shutdown the server cleanly");
}

static void __http_listen_cb(valk_aio_system_t *sys,
                             struct valk_aio_task_new *task) {
  int r;
  struct sockaddr_in addr;
  valk_arc_box *box = task->arg;

  valk_aio_http_server *srv = box->item;
  srv->listener = (void *)valk_slab_aquire(sys->handleSlab)->data;

  memset(srv->listener, 0, sizeof(valk_aio_handle_t));
  srv->listener->magic = VALK_AIO_HANDLE_MAGIC;
  srv->listener->kind = VALK_HNDL_TCP;
  srv->listener->sys = sys;
  srv->listener->arg = srv;
  srv->listener->onClose = __http_shutdown_cb;
  srv->listener->uv.tcp.data = srv->listener;

  r = uv_tcp_init(srv->sys->eventloop, &srv->listener->uv.tcp);
  VALK_ASSERT(r == 0, "uv_tcp_init failed: %s", uv_strerror(r));
  uv_tcp_nodelay(&srv->listener->uv.tcp, 1);

  r = uv_ip4_addr(srv->interface, srv->port, &addr);
  if (r) {
    VALK_ERROR("Get addr error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Addr");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }
#ifdef __linux__
  r = uv_tcp_bind(&srv->listener->uv.tcp, (const struct sockaddr *)&addr,
                  UV_TCP_REUSEPORT);
#else
  r = uv_tcp_bind(&srv->listener->uv.tcp, (const struct sockaddr *)&addr, 0);
#endif
  if (r) {
    VALK_ERROR("Bind error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Bind");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  if (srv->port == 0) {
    struct sockaddr_in bound_addr;
    int namelen = sizeof(bound_addr);
    r = uv_tcp_getsockname(&srv->listener->uv.tcp, (struct sockaddr *)&bound_addr, &namelen);
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

  r = uv_listen((uv_stream_t *)&srv->listener->uv.tcp, 128,
                __http_server_accept_cb);
  if (r) {
    VALK_ERROR("Listen error: %s", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Listening");
    valk_promise_respond(&task->promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    valk_slab_release_ptr(sys->handleSlab, srv->listener);
    return;
  }

  VALK_INFO("Listening on %s:%d", srv->interface, srv->port);

  valk_promise_respond(&task->promise, box);
  valk_dll_insert_after(&sys->liveHandles, srv->listener);
  valk_arc_release(box);
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

  for (size_t i = 0; i < env->symbols.count; i++) {
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
  __valk_sandbox_env_free(srv->sandbox_env);
  SSL_CTX_free(srv->ssl_ctx);
  valk_mem_allocator_free(box->allocator, box);
}

valk_future *valk_aio_http2_listen(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler) {
  return valk_aio_http2_listen_with_config(sys, interface, port, keyfile, certfile,
                                            handler, lisp_handler, NULL);
}

valk_future *valk_aio_http2_listen_with_config(valk_aio_system_t *sys,
                                   const char *interface, const int port,
                                   const char *keyfile, const char *certfile,
                                   valk_http2_handler_t *handler,
                                   void *lisp_handler,
                                   valk_http_server_config_t *config) {
  valk_arc_box *box = (valk_arc_box *)valk_slab_aquire(sys->httpServers)->data;
  valk_future *res = valk_future_new();

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

    valk_aio_ssl_server_init(&srv->ssl_ctx, keyfile, certfile);
    SSL_CTX_set_alpn_select_cb(srv->ssl_ctx, __alpn_select_proto_cb, NULL);
  }

  struct valk_aio_task_new *task;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)sys->handleSlab) {
    task = valk_mem_alloc(sizeof(valk_aio_task_new));
  }
  if (!task) {
    VALK_ERROR("Handle slab exhausted in http2_listen");
    valk_arc_box *err = valk_arc_box_err("Handle slab exhausted");
    valk_promise p = {.item = res};
    valk_arc_retain(res);
    valk_promise_respond(&p, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return res;
  }
  task->allocator = (valk_mem_allocator_t *)sys->handleSlab;

  task->arg = box;
  task->promise.item = res;
  valk_arc_retain(res);
  task->callback = __http_listen_cb;

  valk_uv_exec_task(sys, task);

  return res;
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
