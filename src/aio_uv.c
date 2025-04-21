#include "aio.h"
#include "aio_ssl.h"

#include "common.h"
#include "concurrency.h"
#include "memory.h"

#include <netinet/in.h>
#include <nghttp2/nghttp2.h>
#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <openssl/tls1.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>
#include <uv/unix.h>

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

// It houses requests to the event loop
#define AIO_QUEUE_SIZE (10)

// times 2 just for fun
#define HTTP_SLAB_ITEM_SIZE (SSL3_RT_MAX_PACKET_SIZE * 2)
#define HTTP_MAX_IO_REQUESTS (1024)
#define HTTP_MAX_CONNECTIONS (10)
// TODO(networking): Figure out a good initial value for this.
#define HTTP_MAX_CONNECTION_HEAP (1024000)
#define HTTP_MAX_CONCURRENT_REQUESTS (1024)
#define HTTP_MAX_REQUEST_SIZE_BYTES (8e6)

#define HTTP_CONNECTION_STATE_SIZE

static __thread valk_slab_t tcp_buffer_slab;
typedef struct {
  uv_write_t req;
  uv_buf_t buf;
  char data[SSL3_RT_MAX_PACKET_SIZE];
} __tcp_buffer_slab_item_t;

struct __http2_connect_req {
  valk_aio_system *sys;
  valk_aio_http2_client *client;
};

struct __http2_client_req {
  valk_aio_http2_client *client;
  valk_promise *promise;
};

static __thread valk_slab_t tcp_connection_slab;
static __thread valk_slab_t tcp_request_arena_slab;

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf);
void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                      uv_buf_t *buf) {
  // TODO(networking): replace it with memory arena for the request
  buf->base = valk_slab_alloc_aquire(&tcp_buffer_slab)->data;
  buf->len = suggested_size;
}

struct valk_aio_task {
  valk_arc_box *arg;
  void (*callback)(valk_arc_box *);
};

struct valk_aio_system {
  uv_loop_t *eventloop;
  uv_thread_t loopThread;
  struct valk_aio_task items[AIO_QUEUE_SIZE];
  size_t idx;
  size_t count;
  size_t capacity;
  uv_mutex_t taskLock;
  uv_async_t taskHandle;
};

struct valk_aio_http_server {
  uv_loop_t *eventloop;
  SSL_CTX *ssl_ctx;
  uv_tcp_t server;
  char *interface;
  int port;
};

typedef struct valk_aio_http_conn {
  uv_connect_t req;
  uv_tcp_t tcpHandle;
  valk_aio_ssl_t ssl;
  // TODO(networking): Sessions could be pooled
  nghttp2_session *session;
  nghttp2_mem session_allocator;
  // connection memory arena
  valk_mem_arena_t *arena;
} valk_aio_http_conn;

static void __event_loop(void *arg) {
  valk_aio_system *sys = arg;
  valk_mem_init_malloc();
  printf("Allocating some shit\n");
  valk_slab_alloc_init(&tcp_buffer_slab, HTTP_SLAB_ITEM_SIZE,
                       HTTP_MAX_IO_REQUESTS);
  valk_slab_alloc_init(&tcp_connection_slab, HTTP_MAX_CONNECTION_HEAP,
                       HTTP_MAX_CONNECTIONS);
  valk_slab_alloc_init(&tcp_request_arena_slab, HTTP_MAX_REQUEST_SIZE_BYTES,
                       HTTP_MAX_CONCURRENT_REQUESTS);
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

void *__CRYPTO_malloc_fn(size_t num, const char *file, int line) {
  return valk_mem_alloc(num);
}

void *__CRYPTO_realloc_fn(void *addr, size_t num, const char *file, int line) {
  // TODO(networking): implement realloc ??? for arenas its even dumber....
  return realloc(addr, num);
}

void __CRYPTO_free_fn(void *addr, const char *file, int line) {
  valk_mem_free(addr);
}

void valk_aio_start(valk_aio_system *sys) {
  valk_asio_ssl_start();
  sys->eventloop = uv_default_loop();
  sys->count = 0;
  sys->capacity = 10;

  CRYPTO_set_mem_functions(__CRYPTO_malloc_fn, __CRYPTO_realloc_fn,
                           __CRYPTO_free_fn);
  // On linux definitely turn sigpipe off
  // Otherwise shit crashes.
  // When the socket dissapears a write may be queued in the event loop
  // In that case we just want to do proper error handling without the
  // signal
  struct sigaction sa = {.sa_handler = SIG_IGN};
  sigaction(SIGPIPE, &sa, NULL);
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

/**
 * @functypedef
 *
 * Custom memory allocator to replace malloc().  The |mem_user_data|
 * is the mem_user_data member of :type:`nghttp2_mem` structure.
 */
void *__nghttp2_malloc(size_t size, void *mem_user_data) {
  printf("HTTP2:: Malloc %ld\n", size);
  return valk_mem_arena_alloc(mem_user_data, size);
}

/**
 * @functypedef
 *
 * Custom memory allocator to replace free().  The |mem_user_data| is
 * the mem_user_data member of :type:`nghttp2_mem` structure.
 */
void __nghttp2_free(void *ptr, void *mem_user_data) {
  printf("HTTP2:: Free %p\n", ptr);
}

/**
 * @functypedef
 *
 * Custom memory allocator to replace calloc().  The |mem_user_data|
 * is the mem_user_data member of :type:`nghttp2_mem` structure.
 */
void *__nghttp2_calloc(size_t nmemb, size_t size, void *mem_user_data) {
  printf("HTTP2:: Calloc %ld, %ld\n", nmemb, size);
  void *res = valk_mem_arena_alloc(mem_user_data, nmemb * size);
  memset(res, 0, nmemb * size);
  return res;
}

/**
 * @functypedef
 *
 * Custom memory allocator to replace realloc().  The |mem_user_data|
 * is the mem_user_data member of :type:`nghttp2_mem` structure.
 */
void *__nghttp2_realloc(void *ptr, size_t size, void *mem_user_data) {
  printf("HTTP2:: Realloc %p, %ld\n", ptr, size);
  void *res = valk_mem_arena_alloc(mem_user_data, size);
  if (ptr != NULL) {
    size_t origSize = ((size_t *)ptr)[-1];
    memcpy(res, ptr, origSize);
  }
  return res;
}

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
  if (status) {
    fprintf(stderr, "Socket On Write error: %s \n", uv_strerror(status));
  } else {
    printf("Receiving on write CB\n");
  }

  valk_slab_alloc_release_ptr(&tcp_buffer_slab, handle);
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
      MAKE_NV2(":status", "200"),
      MAKE_NV2("content-type", "text/html; charset=utf-8"),
      // MAKE_NV2("fuckyou", "this is something else aint it"),
  };

  /* Send HEADERS frame */
  /* nghttp2_submit_headers( */
  /*     session, NGHTTP2_FLAG_END_HEADERS, stream_id, NULL, response_headers,
   */
  /*     sizeof(response_headers) / sizeof(response_headers[0]), NULL); */

  /* Send DATA frame */
  nghttp2_data_provider2 data_prd;
  data_prd.source.ptr = "<h1>Valkyria, valhallas treasure</h1>\n";
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

  if (frame->hd.type == NGHTTP2_GOAWAY) {
    printf("Received GO AWAY frame\n");
  }

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    printf("Received HEADERS frame(meaning request).. pushing response\n");
    /* Example: respond with a small HEADERS + DATA for "Hello HTTP/2" */
    int stream_id = frame->hd.stream_id;
    __demo_response(session, stream_id);

  } else {
    printf("Not sending a response ??\n");
  }

  return 0;
}

static void __http2_flush_frames(valk_buffer_t *buf,
                                 struct valk_aio_http_conn *conn) {

  const uint8_t *data;

  int len = 0;
  do {
    len = nghttp2_session_mem_send2(conn->session, &data);
    if (len < 0) {
      printf("ERR: writing shit %s", nghttp2_strerror(len));
    } else if (len) {
      // TODO(networking): Need to handle data greater than the buffer size here

      valk_buffer_append(buf, (void *)data, len);

      if ((buf->count + len) > buf->capacity) {
        // if we read the same amount of data again, we would overflow, so lets
        // stop for now
        printf("Fuck... couldnt cache it all %ld\n", buf->count + len);
        break;
      }

      printf("Buffed frame data %d :: %ld :: capacity %ld, %s\n", len,
             buf->count, buf->capacity, data);
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
  }
}

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {

  struct valk_aio_http_conn *conn = stream->data;

  if (nread < 0) {
    // Error or EOF
    if (nread == UV_EOF) {
      printf("Received EOF on tcp stream\n");
    } else {
      fprintf(stderr, "Read error: %s\n", uv_strerror((int)nread));
    }
    uv_close((uv_handle_t *)stream, NULL);
    return;
  }

  printf("Feeding data to OpenSSL %ld\n", nread);

  valk_buffer_t In = {
      .items = buf->base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_alloc_aquire(&tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  int err = valk_aio_ssl_on_read(&conn->ssl, &In, &Out, conn,
                                 __http_tcp_unencrypted_read_cb);

  // Only do this if ssl is established:
  if (!err) {
    // Flushies
    In.count = 0;
    memset(In.items, 0, In.capacity);
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
  }

  int wantToSend = Out.count > 0;
  if (wantToSend) {
    slabItem->buf.base = Out.items;
    slabItem->buf.len = Out.count;

    printf("Sending %ld bytes\n", Out.count);
    uv_write(&slabItem->req, (uv_stream_t *)&conn->tcpHandle, &slabItem->buf, 1,
             __http_tcp_on_write_cb);
  } else {
    printf("Nothing to send %d \n", wantToSend);
    valk_slab_alloc_release_ptr(&tcp_buffer_slab, slabItem);
  }

  valk_slab_alloc_release_ptr(&tcp_buffer_slab, In.items);
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

static int __http_send_client_connection_header(nghttp2_session *session) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, 100}};
  int rv;
  printf("[http2 Client] Sending connection frame\n");

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    fprintf(stderr, "Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

static void __http_server_accept_cb(uv_stream_t *server, int status) {
  if (status < 0) {
    fprintf(stderr, "New connection error %s\n", uv_strerror(status));
    // error!
    return;
  }

  // Init the arena
  valk_mem_arena_t *arena =
      (void *)valk_slab_alloc_aquire(&tcp_connection_slab)->data;
  arena->capacity = HTTP_MAX_CONNECTION_HEAP - sizeof(valk_mem_arena_t);
  arena->offset = 0;

  struct valk_aio_http_conn *conn =
      valk_mem_arena_alloc(arena, sizeof(struct valk_aio_http_conn));
  // haha point back to thy self
  conn->arena = arena;

  uv_tcp_init(server->loop, &conn->tcpHandle);
  conn->tcpHandle.data = conn;

  // dont need for now because we are using nghttp2 mem buffer for send
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
    };

    /**
     * An arbitrary user supplied data.  This is passed to each
     * allocator function.
     */
    conn->session_allocator.mem_user_data = conn->arena;
    /**
     * Custom allocator function to replace malloc().
     */
    conn->session_allocator.malloc = __nghttp2_malloc;
    /**
     * Custom allocator function to replace free().
     */
    conn->session_allocator.free = __nghttp2_free;
    /**
     * Custom allocator function to replace calloc().
     */
    conn->session_allocator.calloc = __nghttp2_calloc;
    /**
     * Custom allocator function to replace realloc().
     */
    conn->session_allocator.realloc = __nghttp2_realloc;

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

    nghttp2_session_server_new3(&conn->session, callbacks, conn, NULL,
                                &conn->session_allocator);
    valk_aio_http_server *srv = server->data;
    valk_aio_ssl_accept(&conn->ssl, srv->ssl_ctx);

    // Send settings to the client
    __http_send_server_connection_header(conn->session);

    // start the connection off by listening, (SSL expects client to send first)
    uv_read_start((uv_stream_t *)&conn->tcpHandle, __alloc_callback,
                  __http_tcp_read_cb);
  } else {
    fprintf(stderr, "Fuck closing %s\n", uv_strerror(res));
    uv_close((uv_handle_t *)&conn->tcpHandle, NULL);
    // TODO(networking): should probably have a function for properly disposing
    // of the connection objects
    valk_slab_alloc_release_ptr(&tcp_connection_slab, conn->arena);
  }
}

static void __http_listen_cb(valk_arc_box *box) {
  int r;
  struct sockaddr_in addr;
  valk_aio_http_server *srv = box->item;
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
#ifdef __linux__
  r = uv_tcp_bind(&srv->server, (const struct sockaddr *)&addr,
                  UV_TCP_REUSEPORT);
#else
  r = uv_tcp_bind(&srv->server, (const struct sockaddr *)&addr, 0);
#endif
  if (r) {
    fprintf(stderr, "Bind err: %s \n", uv_strerror(r));
    return;
  }

  srv->server.data = srv;
  r = uv_listen((uv_stream_t *)&srv->server, 128, __http_server_accept_cb);
  if (r) {
    fprintf(stderr, "Listen err: %s \n", uv_strerror(r));
    return;
  } else {
    printf("Listening on %s:%d\n", srv->interface, srv->port);
  }
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

static void __no_free(void *arg) { UNUSED(arg); }
int valk_aio_http2_listen(valk_aio_http_server *srv, valk_aio_system *sys,
                          const char *interface, const int port,
                          const char *keyfile, const char *certfile) {
  srv->eventloop = sys->eventloop;
  srv->interface = strdup(interface);
  srv->port = port;

  uv_mutex_lock(&sys->taskLock);
  struct valk_aio_task task;

  valk_aio_ssl_server_init(&srv->ssl_ctx, keyfile, certfile);
  SSL_CTX_set_alpn_select_cb(srv->ssl_ctx, __alpn_select_proto_cb, NULL);

  // TODO(networking): consider shove srv into a box to begin with, this is
  // otherwise sus
  task.arg = valk_arc_box_new(VALK_SUC, sizeof(void *));
  task.arg->item = srv;
  task.callback = __http_listen_cb;

  valk_work_add(sys, task);

  uv_mutex_unlock(&sys->taskLock);
  uv_async_send(&sys->taskHandle);
  return 0;
}

void valk_aio_hangup(valk_aio_socket *socket);

void valk_server_demo(void) {
  valk_aio_system sys;
  valk_aio_http_server srv;
  valk_aio_start(&sys);
  valk_aio_http2_listen(&srv, &sys, "0.0.0.0", 6969, "build/server.key",
                        "build/server.crt");
  uv_thread_join(&sys.loopThread);
  valk_aio_stop(&sys);
}

//// HTTP2 CLIENT

typedef struct valk_aio_http2_client {
  SSL_CTX *ssl_ctx;
  // TODO(networking):  connections could be pooled
  valk_aio_http_conn connection;
  /// resolves when connection has been established
  valk_promise *promise;
  char *interface;
  int port;
} valk_aio_http2_client;

static int __http_client_on_frame_recv_callback(nghttp2_session *session,
                                                const nghttp2_frame *frame,
                                                void *user_data) {
  printf("ON_RECV callback \n");

  switch (frame->hd.type) {
  case NGHTTP2_HEADERS:
    break;
  case NGHTTP2_RST_STREAM:
    printf("[INFO] C <---------------------------- S (RST_STREAM) %d\n",
           frame->hd.stream_id);
    break;
  case NGHTTP2_GOAWAY:
    printf("[INFO] C <---------------------------- S (GOAWAY) %d\n",
           frame->hd.stream_id);
    printf("[Client]Received GO AWAY frame\n");
    break;
  }

  return 0;
}

static int __http_on_data_chunk_recv_callback(nghttp2_session *session,
                                              uint8_t flags, int32_t stream_id,
                                              const uint8_t *data, size_t len,
                                              void *user_data) {
  struct Request *req;
  (void)flags;
  (void)user_data;

  req = nghttp2_session_get_stream_user_data(session, stream_id);
  if (req) {
    printf("[INFO] C <---------------------------- S (DATA chunk)\n"
           "%lu bytes\n",
           (unsigned long int)len);
    fwrite(data, 1, len, stdout);
    printf("\n");
  }
  return 0;
}

static void __uv_http2_connect_cb(uv_connect_t *req, int status) {
  valk_aio_http2_client *client = req->data;
  if (status < 0) {
    fprintf(stderr, "Client Connection err: %s\n", uv_strerror(status));
    valk_promise_respond(client->promise,
                         valk_arc_box_err("Client Connection err"));

    // TODO(networking): cleanup the client / connection resources
    // error!
    return;
  }
  printf("Gurr we connected\n");

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_alloc_aquire(&tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  static nghttp2_session_callbacks *callbacks = NULL;
  if (!callbacks) {
    nghttp2_session_callbacks_new(&callbacks);
    /*

      nghttp2_session_callbacks_set_on_frame_recv_callback(callbacks,
                                                           on_frame_recv_callback);

      nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
        callbacks, on_data_chunk_recv_callback);

      nghttp2_session_callbacks_set_on_stream_close_callback(
        callbacks, on_stream_close_callback);

      nghttp2_session_callbacks_set_on_header_callback(callbacks,
                                                       on_header_callback);

      nghttp2_session_callbacks_set_on_begin_headers_callback(
        callbacks, on_begin_headers_callback);
          */

    // nghttp2_session_callbacks_set_on_begin_headers_callback(
    //     callbacks, __http_on_begin_headers_callback);
    nghttp2_session_callbacks_set_on_header_callback(callbacks,
                                                     __http_on_header_callback);
    nghttp2_session_callbacks_set_on_frame_recv_callback(
        callbacks, __http_client_on_frame_recv_callback);

    nghttp2_session_callbacks_set_on_data_chunk_recv_callback(
        callbacks, __http_on_data_chunk_recv_callback);
  }

  nghttp2_session_client_new(&client->connection.session, callbacks, client);

  __http_send_client_connection_header(client->connection.session);

  valk_aio_ssl_client_init(&client->ssl_ctx);
  SSL_CTX_set_alpn_protos(client->ssl_ctx, (const unsigned char *)"\x02h2", 3);

  valk_aio_ssl_connect(&client->connection.ssl, client->ssl_ctx);
  SSL_set_tlsext_host_name(client->connection.ssl.ssl, "localhost");

  char buf[SSL3_RT_MAX_PACKET_SIZE] = {0};

  valk_buffer_t Tmp = {
      .items = &buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  valk_aio_ssl_handshake(&client->connection.ssl, &Out);

  int wantToSend = Out.count > 0;
  if (wantToSend) {
    slabItem->buf.base = Out.items;
    slabItem->buf.len = Out.count;

    printf("[Client] Sending %ld bytes\n", Out.count);
    uv_write(&slabItem->req, (uv_stream_t *)&client->connection.tcpHandle,
             &slabItem->buf, 1, __http_tcp_on_write_cb);
  } else {
    valk_slab_alloc_release_ptr(&tcp_buffer_slab, Out.items);
  }

  uv_read_start((uv_stream_t *)&client->connection.tcpHandle, __alloc_callback,
                __http_tcp_read_cb);

  valk_arc_box *res = valk_arc_box_new(VALK_SUC, 0);
  res->item = client;

  printf("Finished initializing client %p\n", (void *)res->item);
  // Shits connected but not fully established, it will buffer any requests tho
  valk_promise_respond(client->promise, res);
}

static void __aio_client_connect_cb(valk_arc_box *box) {

  int r;
  struct sockaddr_in addr;
  struct __http2_connect_req *req = box->item;

  valk_aio_http2_client *client = req->client;

  r = uv_tcp_init(req->sys->eventloop, &client->connection.tcpHandle);
  uv_tcp_nodelay(&client->connection.tcpHandle, 1);
  client->connection.tcpHandle.data = &client->connection;
  if (r) {
    fprintf(stderr, "TcpInit err: %s \n", uv_strerror(r));
    valk_promise_respond(client->promise, valk_arc_box_err("TcpInit err"));
    return;
  }

  r = uv_ip4_addr(client->interface, client->port, &addr);
  if (r) {
    fprintf(stderr, "Addr err: %s \n", uv_strerror(r));
    valk_promise_respond(client->promise, valk_arc_box_err("Addr err"));
    return;
  }

  client->connection.req.data = client;
  uv_tcp_connect(&client->connection.req, &client->connection.tcpHandle,
                 (const struct sockaddr *)&addr, __uv_http2_connect_cb);

  valk_arc_release(box);
}

valk_future *valk_aio_http2_connect(valk_aio_system *sys, const char *interface,
                                    const int port, const char *certfile) {
  uv_mutex_lock(&sys->taskLock);
  valk_aio_http2_client *client = valk_mem_alloc(sizeof(valk_aio_http2_client));
  client->interface = strdup(interface);
  client->port = port;

  printf("Initializing client %p\n", (void *)client);

  struct valk_aio_task task;

  valk_future *res = valk_future_new();
  // TODO(networking): do i even need boxes here?? 🤔
  task.arg = valk_arc_box_new(VALK_SUC, sizeof(struct __http2_connect_req));

  struct __http2_connect_req *req = task.arg->item;
  req->sys = sys;
  req->client = client;

  // TODO(networking):  is this proper? Eg. should i pass through comletions
  // through client or tasks
  client->promise = valk_promise_new(res);
  task.callback = __aio_client_connect_cb;

  valk_work_add(sys, task);

  uv_mutex_unlock(&sys->taskLock);
  uv_async_send(&sys->taskHandle);
  return res;
}

static void __http2_submit_demo_request_cb(valk_arc_box *arg) {

  valk_aio_http2_client *client = arg->item;

  printf("Constructing a request on client %p\n", (void *)client);
  valk_aio_http_conn *conn = &client->connection;
  int32_t stream_id;
  // http2_stream_data *stream_data = session_data->stream_data;
  // const char *uri = "local/";
  // const struct http_parser_url *u = stream_data->u;

  nghttp2_nv hdrs[] = {MAKE_NV2(":method", "GET"), MAKE_NV2(":scheme", "https"),
                       MAKE_NV2(":authority", "google.com"),
                       // stream_data->authoritylen),
                       MAKE_NV2(":path", "/")};
  // fprintf(stderr, "Request headers:\n");
  // print_headers(stderr, hdrs, ARRLEN(hdrs));

  stream_id = nghttp2_submit_request2(
      conn->session, NULL, hdrs, sizeof(hdrs) / sizeof(hdrs[0]), NULL, conn);

  if (stream_id < 0) {
    fprintf(stderr, "Could not submit HTTP request: %s\n",
            nghttp2_strerror(stream_id));
  }

  printf("Submitted request with stream id %d\n", stream_id);

  char buf[SSL3_RT_MAX_PACKET_SIZE];
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};
  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_alloc_aquire(&tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  // Only write stuff if ssl is established
  if (SSL_is_init_finished(client->connection.ssl.ssl)) {
    __http2_flush_frames(&In, conn);

    // Encrypt the new data n stuff
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    int wantToSend = Out.count > 0;
    if (wantToSend) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;

      printf("Sending %ld bytes\n", Out.count);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->tcpHandle, &slabItem->buf,
               1, __http_tcp_on_write_cb);
    } else {
      printf("Nothing to send %d \n", wantToSend);
      valk_slab_alloc_release_ptr(&tcp_buffer_slab, slabItem);
    }
  }

  valk_arc_release(arg);
  // return stream_id;
}

static void __http2_submit_demo_request(valk_arc_box *arg) {}

char *valk_client_demo(const char *domain, const char *port) {
  valk_aio_system sys;
  valk_aio_start(&sys);

  // GOOGLE
  valk_arc_box *clientBox = valk_future_await(
      valk_aio_http2_connect(&sys, "142.250.191.78", 443, ""));

  // Local
  // valk_aio_http2_connect(&client, &sys, "127.0.0.1", 3000, "");
  // valk_arc_box *clientBox =
  //     valk_future_await(valk_aio_http2_connect(&sys, "127.0.0.1", 3000, ""));

  VALK_ASSERT(clientBox->type == VALK_SUC, "Error creating client: %s",
              clientBox->item);

  uv_mutex_lock(&sys.taskLock);
  struct valk_aio_task task;
  task.arg = clientBox;
  task.callback = __http2_submit_demo_request_cb;

  valk_work_add(&sys, task);
  uv_mutex_unlock(&sys.taskLock);
  uv_async_send(&sys.taskHandle);

  while (1)
    ;
  valk_aio_stop(&sys);
  return strdup("");
}

// reference code for openssl setup
//
// https://github.com/darrenjs/openssl_examples
