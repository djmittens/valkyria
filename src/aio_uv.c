#include "aio.h"
#include "aio_ssl.h"

#include "common.h"
#include "concurrency.h"
#include "memory.h"

#include <netinet/in.h>
#include <nghttp2/nghttp2.h>
#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <stdio.h>
#include <string.h>
#include <uv.h>
#include <uv/unix.h>

#define HTTP2_MAX_SEND_BYTES 2048

#define MAKE_NV(NAME, VALUE, VALUELEN)                                         \
  {                                                                            \
    (uint8_t *)NAME, (uint8_t *)VALUE, sizeof(NAME) - 1, VALUELEN,             \
        NGHTTP2_NV_FLAG_NONE,                                                  \
  }

#define MAKE_NV2(NAME, VALUE)                                                  \
  {                                                                            \
    (uint8_t *)NAME, (uint8_t *)VALUE, sizeof(NAME) - 1, sizeof(VALUE) - 1,    \
        NGHTTP2_NV_FLAG_NONE,                                                  \
  }

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf);
void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                      uv_buf_t *buf) {
  // TODO(networking): replace it with memory arena for the request
  buf->base = valk_mem_alloc(suggested_size);
  buf->len = suggested_size;
}

struct valk_aio_task {
  valk_arc_box *arg;
  void (*callback)(valk_arc_box *);
};

struct valk_aio_system {
  uv_loop_t *eventloop;
  uv_thread_t loopThread;
  struct valk_aio_task *items;
  size_t idx;
  size_t count;
  size_t capacity;
  uv_mutex_t taskLock;
  uv_async_t taskHandle;
};

struct valk_aio_http_server {
  uv_loop_t *eventloop;
  valk_aio_ssl_ctx_t sslCtx;
  uv_tcp_t server;
  char *interface;
  int port;
};

struct valk_aio_http_conn {
  uv_tcp_t tcpHandle;
  valk_aio_ssl_t ssl;
  nghttp2_session *session;
  int closed;
};

static void __event_loop(void *arg) {
  valk_aio_system *sys = arg;
  valk_mem_init_malloc();
  uv_run(sys->eventloop, UV_RUN_DEFAULT);
}

static void __task_cb(uv_async_t *handle) {
  valk_aio_system *sys = handle->data;
  uv_mutex_lock(&sys->taskLock);
  while (sys->count > 0) {
    struct valk_aio_task task;
    if (!valk_work_pop(sys, &task)) {
      task.callback(task.arg);
    }
  }
  uv_mutex_unlock(&sys->taskLock);
}

void valk_aio_start(valk_aio_system *sys) {
  sys->eventloop = uv_default_loop();
  sys->count = 0;
  sys->capacity = 10;
  sys->items = valk_mem_alloc(sizeof(struct valk_aio_task) * 10);

  uv_mutex_init(&sys->taskLock);
  uv_async_init(sys->eventloop, &sys->taskHandle, __task_cb);
  sys->taskHandle.data = sys;

  int status = uv_thread_create(&sys->loopThread, __event_loop, sys);
  if (status) {
    perror("pthread_create");
  }
}

void valk_aio_stop(valk_aio_system *sys) {
  uv_stop(sys->eventloop);
  uv_loop_close(sys->eventloop);
  uv_thread_join(&sys->loopThread);
}

valk_future *valk_aio_read_file(valk_aio_system *sys, const char *filename);

static int __http_on_header_callback(nghttp2_session *session,
                                     const nghttp2_frame *frame,
                                     const uint8_t *name, size_t namelen,
                                     const uint8_t *value, size_t valuelen,
                                     uint8_t flags, void *user_data) {
  /* For demonstration, just print incoming headers. */
  fprintf(stderr, "HDR: %.*s: %.*s\n", (int)namelen, name, (int)valuelen,
          value);

  return 0; // success
}
static int __http_on_begin_headers_callback(nghttp2_session *session,
                                            const nghttp2_frame *frame,
                                            void *user_data) {
  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    fprintf(stderr, ">>> Received HTTP/2 request (stream_id=%d)\n",
            frame->hd.stream_id);
  }
  return 0;
}

static void __http_tcp_on_write_cb(uv_write_t *handle, int status) {
  fflush(stdout);
  if (status) {
    fprintf(stderr, "On Write error: %s \n", uv_strerror(status));
  } else {
    printf("Receiving on write CB\n");
  }

  uv_buf_t *buf = handle->data;
  valk_mem_free(buf->base);
  valk_mem_free(buf);
  valk_mem_free(handle);
  // valk_mem_free(handle);
}

static nghttp2_ssize __http_byte_body_cb(nghttp2_session *session,
                                         int32_t stream_id, uint8_t *buf,
                                         size_t length, uint32_t *data_flags,
                                         nghttp2_data_source *source,
                                         void *user_data) {
  printf("Looking to get %ld bytes\n", length);
  memcpy(buf, source->ptr, strlen(source->ptr) + 1);
  // This marks that with this call we reached the end of the file, and dont
  // call us back again
  *data_flags |= NGHTTP2_DATA_FLAG_EOF;
  return strlen(source->ptr) + 1;
}

static int __demo_response(nghttp2_session *session, int stream_id) {

  printf("WE ARE sending a response ??\n");
  /* Prepare some pseudo-headers: */
  const nghttp2_nv response_headers[] = {
      MAKE_NV2(":status", "200"), MAKE_NV2("content-type", "text/plain"),
      // MAKE_NV2("fuckyou", "this is something else aint it"),
  };

  /* Send HEADERS frame */
  /* nghttp2_submit_headers( */
  /*     session, NGHTTP2_FLAG_END_HEADERS, stream_id, NULL, response_headers,
   */
  /*     sizeof(response_headers) / sizeof(response_headers[0]), NULL); */

  /* Send DATA frame */
  nghttp2_data_provider2 data_prd;
  data_prd.source.ptr = "Hello HTTP/2 from libuv + nghttp2\n";
  data_prd.read_callback = __http_byte_body_cb;

  /* return nghttp2_submit_push_promise(session, 0, stream_id, response_headers,
   * 2, */
  /*                                    (void *)body); */
  return nghttp2_submit_response2(
      session, stream_id, response_headers,
      sizeof(response_headers) / sizeof(response_headers[0]), &data_prd);
}

/* Called when a frame is fully received. For a request, we might respond here.
 */
static int __http_on_frame_recv_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data) {
  struct valk_aio_http_conn *client = (struct valk_aio_http_conn *)user_data;

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    /* Example: respond with a small HEADERS + DATA for "Hello HTTP/2" */
    int stream_id = frame->hd.stream_id;
    __demo_response(session, stream_id);

    /* if (nghttp2_session_send(session) < 0) { */
    /*   fprintf(stderr, "nghttp2_session_send error\n"); */
    /*   // uv_close((uv_handle_t *)&client->handle, NULL); */
    /*   return 0; */
    /* } */
    /* uv_write_t *req = malloc(sizeof(uv_write_t)); */
    /* uv_write(req, (uv_stream_t *)&client->handle, &client->send_buf, 1, */
    /*          __http_tcp_on_write_cb); */
  } else {
    printf("Not sending a response ??\n");
  }

  return 0;
}

static void __http2_flush_frames(struct valk_aio_http_conn *conn) {

  const uint8_t *data;

  int len = 0;
  do {
    len = nghttp2_session_mem_send2(conn->session, &data);
    if (len < 0) {
      printf("ERR: writing shit %s", nghttp2_strerror(len));
    } else if (len) {
      // TODO(networking): wht the fuck. This buffer needs to live until next
      // callback, which has to clean it up.

      valk_buffer_append(&conn->ssl.unencrypted, (void *)data, len);

      if (conn->ssl.unencrypted.count + len >= HTTP2_MAX_SEND_BYTES) {
        // We fill the whole buffer with the same message basically...
        break;
      }
      printf("Buffed frame data %d :: %ld\n", len, conn->ssl.unencrypted.count);
    } else {
      printf("Found no data to send Skipping CB\n");
    }
  } while (len > 0);
}

static void __http_tcp_unencrypted_read_cb(void *arg,
                                           const valk_buffer_t *buf) {

  struct valk_aio_http_conn *conn = arg;

  // Feed data to nghttp2
  ssize_t rv = nghttp2_session_mem_recv2(
      conn->session, (const uint8_t *)buf->items, buf->count);
  if (rv < 0) {
    fprintf(stderr, "nghttp2_session_mem_recv error: %zd\n", rv);
    uv_close((uv_handle_t *)&conn->tcpHandle, NULL);
    // valk_mem_free(buf->base);
  }
}

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {

  struct valk_aio_http_conn *conn = stream->data;

  if (nread < 0) {
    // Error or EOF
    if (nread == UV_EOF) {
      printf("EOF infact\n");
    } else {
      fprintf(stderr, "Read error: %s\n", uv_strerror((int)nread));
    }
    uv_close((uv_handle_t *)stream, NULL);
    // valk_mem_free(buf->base);
    return;
  }

  // Buffer ssl bytes
  conn->ssl.staging.count = 0;
  valk_buffer_append(&conn->ssl.staging, buf->base, nread);

  printf("Feeding data to http %ld\n", nread);

  valk_aio_ssl_on_read(&conn->ssl, conn, __http_tcp_unencrypted_read_cb);

  // Flushies
  __http2_flush_frames(conn);

  // Encrypt the new data n stuff
  valk_aio_ssl_encrypt(&conn->ssl);
  int wantToSend = conn->ssl.encrypted.count > 0;

  if (wantToSend) {
    // TODO(networking): Should not be allocating the write buffer
    uv_buf_t *sbuf = valk_mem_alloc(sizeof(uv_buf_t));
    sbuf->base = valk_mem_alloc(HTTP2_MAX_SEND_BYTES);
    memmove(sbuf->base, conn->ssl.encrypted.items, conn->ssl.encrypted.count);
    conn->ssl.encrypted.count = 0;
    sbuf->len = conn->ssl.encrypted.count;

    printf("Sending %ld bytes\n", sbuf->len);
    uv_write_t *req = malloc(sizeof(uv_write_t));
    req->data = sbuf;
    uv_write(req, (uv_stream_t *)&conn->tcpHandle, sbuf, 1,
             __http_tcp_on_write_cb);
  } else {
    printf("Nothing to send %d \n", wantToSend);
  }
}

static int __http_send_server_connection_header(nghttp2_session *session) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, 100}};
  int rv;

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    fprintf(stderr, "Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

static void __http_connection_cb(uv_stream_t *server, int status) {
  if (status < 0) {
    fprintf(stderr, "New connection error %s\n", uv_strerror(status));
    // error!

    return;
  }
  struct valk_aio_http_conn *conn =
      valk_mem_alloc(sizeof(struct valk_aio_http_conn));
  uv_tcp_init(server->loop, &conn->tcpHandle);
  conn->tcpHandle.data = conn;

  // dont neet for now because we are using nghttp2 mem buffer for send
  // conn->send_buf.base = valk_mem_alloc(MAX_SEND_BYTES);
  int res = uv_accept(server, (uv_stream_t *)&conn->tcpHandle);

  if (!res) {
    // Get the client IP address
    struct sockaddr_storage client_addr;
    int addr_len = sizeof(client_addr);

    if (uv_tcp_getpeername(&conn->tcpHandle, (struct sockaddr *)&client_addr,
                           &addr_len) == 0) {
      char ip[INET6_ADDRSTRLEN];
      memset(ip, 0, sizeof(ip));
      uint16_t port = 0;
      if (client_addr.ss_family == AF_INET) {
        // IPv4
        struct sockaddr_in *addr4 = (struct sockaddr_in *)&client_addr;
        uv_ip4_name(addr4, ip, sizeof(ip));
        port = ntohs(addr4->sin_port);
      } else if (client_addr.ss_family == AF_INET6) {
        // IPv6
        struct sockaddr_in6 *addr6 = (struct sockaddr_in6 *)&client_addr;
        uv_ip6_name(addr6, ip, sizeof(ip));
        port = ntohs(addr6->sin6_port);
      }

      printf("Accepted connection from IP: %s:%d\n", ip, port);
    } else {
      fprintf(stderr, "Could not get peer name\n");
    }
    static nghttp2_session_callbacks *callbacks = NULL;
    if (!callbacks) {
      nghttp2_session_callbacks_new(&callbacks);
      // nghttp2_session_callbacks_set_send_callback2(callbacks,
      //                                              __http_send_callback);
      nghttp2_session_callbacks_set_on_begin_headers_callback(
          callbacks, __http_on_begin_headers_callback);
      nghttp2_session_callbacks_set_on_header_callback(
          callbacks, __http_on_header_callback);
      nghttp2_session_callbacks_set_on_frame_recv_callback(
          callbacks, __http_on_frame_recv_callback);
    }

    nghttp2_session_server_new(&conn->session, callbacks, conn);

    valk_aio_http_server *srv = server->data;
    valk_aio_ssl_accept(&conn->ssl, &srv->sslCtx);

    // allocate ssl buffers should be max send bytes ? or maybe bigger?
    valk_buffer_alloc(&conn->ssl.encrypted, HTTP2_MAX_SEND_BYTES);
    valk_buffer_alloc(&conn->ssl.unencrypted, HTTP2_MAX_SEND_BYTES);
    valk_buffer_alloc(&conn->ssl.staging, HTTP2_MAX_SEND_BYTES);

    // Send settings to the client
    __http_send_server_connection_header(conn->session);

    // start the connection off by listening, (SSL expects client to send first)
    uv_read_start((uv_stream_t *)&conn->tcpHandle, __alloc_callback,
                  __http_tcp_read_cb);
  } else {
    fprintf(stderr, "Fuck closing %s\n", uv_strerror(res));
    uv_close((uv_handle_t *)&conn->tcpHandle, NULL);
    valk_mem_free(conn);
  }
}

static void __http_listen_cb(valk_arc_box *box) {
  int r;
  struct sockaddr_in addr;
  valk_aio_http_server *srv = box->succ;
  r = uv_tcp_init(srv->eventloop, &srv->server);
  uv_tcp_nodelay(&srv->server, 1);

  if (r) {
    fprintf(stderr, "TcpInit err: %s \n", uv_strerror(r));
    return;
  }
  r = uv_ip4_addr(srv->interface, srv->port, &addr);
  if (r) {
    fprintf(stderr, "Addr err: %s \n", uv_strerror(r));
    return;
  }
  r = uv_tcp_bind(&srv->server, (const struct sockaddr *)&addr,
                  UV_TCP_REUSEPORT);
  if (r) {
    fprintf(stderr, "Bind err: %s \n", uv_strerror(r));
    return;
  }

  srv->server.data = srv;
  r = uv_listen((uv_stream_t *)&srv->server, 128, __http_connection_cb);
  if (r) {
    fprintf(stderr, "Listen err: %s \n", uv_strerror(r));
    return;
  } else {
    printf("Listening on %s:%d\n", srv->interface, srv->port);
  }
  valk_arc_box_release(box);
}

static int __alpn_select_proto_cb(SSL *ssl, const unsigned char **out,
                                  unsigned char *outlen,
                                  const unsigned char *in, unsigned int inlen,
                                  void *arg) {
  int rv;
  UNUSED(ssl);
  UNUSED(arg);

  rv = nghttp2_select_alpn(out, outlen, in, inlen);

  if (rv != 1) {
    return SSL_TLSEXT_ERR_NOACK;
  }

  return SSL_TLSEXT_ERR_OK;
}

static void __no_free(void *arg) { UNUSED(arg); }
int valk_aio_http2_listen(valk_aio_http_server *srv, valk_aio_system *sys,
                          const char *interface, const int port,
                          const char *keyfile, const char *certfile) {
  srv->eventloop = sys->eventloop;
  srv->interface = strdup(interface);
  srv->port = port;

  uv_mutex_lock(&sys->taskLock);
  struct valk_aio_task task;

  valk_aio_ssl_server_init(&srv->sslCtx, keyfile, certfile);
  SSL_CTX_set_alpn_select_cb(srv->sslCtx.ssl_ctx, __alpn_select_proto_cb, NULL);

  task.arg = valk_arc_box_suc(srv, __no_free);
  task.callback = __http_listen_cb;

  valk_work_add(sys, task);

  uv_mutex_unlock(&sys->taskLock);
  uv_async_send(&sys->taskHandle);
  return 0;
}

void valk_aio_hangup(valk_aio_socket *socket);

void valk_server_demo(void) {
  valk_aio_system *sys = valk_mem_alloc(sizeof(valk_aio_system));
  valk_aio_http_server *srv = valk_mem_alloc(sizeof(valk_aio_http_server));
  valk_aio_start(sys);
  valk_aio_http2_listen(srv, sys, "0.0.0.0", 6969, "build/server.key",
                        "build/server.crt");
  uv_thread_join(&sys->loopThread);
  valk_aio_stop(sys);
  valk_mem_free(sys);
  valk_mem_free(srv);
}

char *valk_client_demo(const char *domain, const char *port) {
  valk_aio_system *sys = valk_mem_alloc(sizeof(valk_aio_system));
  valk_aio_start(sys);
  while (1)
    ;
  valk_aio_stop(sys);
  valk_mem_free(sys);
  return strdup("");
}

// reference code for openssl setup
//
// https://github.com/darrenjs/openssl_examples
