#define _POSIX_C_SOURCE                                                        \
  200809L // The fuck is this ? turns out sigaction and shit has to be enabled
          // separately in strict mode
#include <netinet/in.h>
#include <nghttp2/nghttp2.h>
#include <openssl/bio.h>
#include <openssl/conf.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/ssl3.h>
#include <openssl/tls1.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>
#include <uv/unix.h>

#include "aio.h"
#include "aio_ssl.h"
#include "common.h"
#include "concurrency.h"
#include "memory.h"

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
enum {
  AIO_QUEUE_SIZE = 10,
  HTTP_SLAB_ITEM_SIZE = (SSL3_RT_MAX_PACKET_SIZE * 2),
  HTTP_MAX_IO_REQUESTS = (1024),
  HTTP_MAX_CONNECTIONS = (10),
  // TODO(networking): Figure out a good initial value for this.
  HTTP_MAX_CONNECTION_HEAP = (1024000),
  HTTP_MAX_CONCURRENT_REQUESTS = (1024),
  HTTP_MAX_REQUEST_SIZE_BYTES = ((int)8e6)
};

// times 2 just for fun

static __thread valk_slab_t *tcp_buffer_slab;

typedef struct {
  uv_write_t req;
  uv_buf_t buf;
  char data[SSL3_RT_MAX_PACKET_SIZE];
} __tcp_buffer_slab_item_t;

typedef struct __http2_connect_req {
  valk_aio_system *sys;
  valk_aio_http2_client *client;
} __http2_connect_req;

static __thread valk_slab_t *tcp_connection_slab;
static __thread valk_slab_t *tcp_request_arena_slab;

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf);
void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                      uv_buf_t *buf) {
  UNUSED(handle);
  // TODO(networking): replace it with memory arena for the request
  buf->base = (char *)valk_slab_aquire(tcp_buffer_slab)->data;
  buf->len = suggested_size;
}

typedef struct valk_aio_task {
  valk_arc_box *arg;
  valk_promise promise;
  void (*callback)(valk_aio_system *, valk_arc_box *, valk_promise *);
} valk_aio_task;

typedef enum {
  VALK_CONN_INIT,
  VALK_CONN_ESTABLISHED,
  VALK_CONN_CLOSING,
  VALK_CONN_CLOSED
} __aio_http_conn_e;

typedef struct valk_aio_http_conn {
  __aio_http_conn_e state;
  uv_connect_t req;
  uv_tcp_t tcpHandle;
  valk_aio_ssl_t ssl;
  // TODO(networking): Sessions could be pooled
  nghttp2_session *session;
  nghttp2_mem session_allocator;
  // connection memory arena
  valk_mem_arena_t *arena;
  valk_http2_handler_t *handler;
} valk_aio_http_conn;

typedef struct valk_aio_system {
  uv_loop_t *eventloop;
  uv_thread_t loopThread;
  valk_aio_task items[AIO_QUEUE_SIZE];
  size_t idx;
  size_t count;
  size_t capacity;
  uv_mutex_t taskLock;
  uv_async_t taskHandle;
  uv_async_t stopper;
} valk_aio_system;

typedef struct valk_aio_http_server {
  uv_loop_t *eventloop;
  SSL_CTX *ssl_ctx;
  uv_tcp_t listener;
  char *interface;
  int port;
  valk_http2_handler_t handler;
} valk_aio_http_server;

static void __event_loop(void *arg) {
  valk_aio_system *sys = arg;
  valk_mem_init_malloc();
  printf("Allocating some shit\n");
  tcp_buffer_slab = valk_slab_new(HTTP_SLAB_ITEM_SIZE, HTTP_MAX_IO_REQUESTS);
  tcp_connection_slab =
      valk_slab_new(HTTP_MAX_CONNECTION_HEAP, HTTP_MAX_CONNECTIONS);
  tcp_request_arena_slab =
      valk_slab_new(HTTP_MAX_REQUEST_SIZE_BYTES, HTTP_MAX_CONCURRENT_REQUESTS);

  uv_run(sys->eventloop, UV_RUN_DEFAULT);

  valk_slab_free(tcp_buffer_slab);
  valk_slab_free(tcp_connection_slab);
  valk_slab_free(tcp_request_arena_slab);
}

static void __task_cb(uv_async_t *handle) {
  valk_aio_system *sys = handle->data;
  uv_mutex_lock(&sys->taskLock);
  while (sys->count > 0) {
    struct valk_aio_task task;
    if (!valk_work_pop(sys, &task)) {
      task.callback(sys, task.arg, &task.promise);
    }
  }
  uv_mutex_unlock(&sys->taskLock);
}


static void __uv_http_on_tcp_disconnect_cb(uv_handle_t *handle) {
  // TODO(networking): tecnically dont need an allocation here, can probably
  // have a unit box  out there somwhere.
  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 0);
  printf("Disconnection handle -> %p\n", handle->data);
  valk_promise_respond(handle->data, box);
  valk_arc_release(box);
}

static void __valk_aio_http2_disconnect_cb(valk_aio_system *sys,
                                           valk_arc_box *arg,
                                           valk_promise *promise) {

  UNUSED(sys);
  // retain in caller

  // TODO(networking): This is where continuations come into play
  valk_aio_http_conn *conn = arg->item;

  if (conn->state != VALK_CONN_ESTABLISHED) {
    valk_arc_box *err = valk_arc_box_err(
        "ERR: Connection cant be closed as its not established \n");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    return;
  }

  conn->tcpHandle.data = promise;
  // if (!uv_is_closing((uv_handle_t *)&conn->tcpHandle)) {
  //   uv_close((uv_handle_t *)&conn->tcpHandle,
  //   __uv_http_on_tcp_disconnect_cb);
  // }

  valk_arc_release(arg);
}

void valk_aio_http2_client_free(void *arg, valk_arc_box *box) {
  UNUSED(box);
  valk_arc_box *argBox = (arg);
  valk_arc_retain(argBox);
  // TODO(networking): add function for unwrapping boxes
  valk_arc_retain(box);
  valk_aio_http_conn *conn = argBox->item;
  printf("Boo did i scare ya?\n");
  if (conn->handler && conn->handler->onDisconnect) {
    // IFF the callback is available
    conn->handler->onDisconnect(conn->handler->arg, conn);
  }
  valk_arc_release(argBox);

  valk_arc_release(box);
}

valk_future *valk_aio_http2_disconnect(valk_aio_system *sys,
                                       valk_arc_box *conn) {
  valk_future *res = valk_future_new();

  valk_arc_retain(conn);
  struct valk_future_and_then cb = {.arg = conn,
                                    .cb = valk_aio_http2_client_free};
  valk_future_and_then(res, &cb);

  uv_mutex_lock(&sys->taskLock);
  struct valk_aio_task task;

  task.arg = conn;
  task.promise.item = res;
  task.callback = __valk_aio_http2_disconnect_cb;

  valk_arc_retain(conn);
  // release conn in valk_aio_http2_client_free
  // release conn in __valk_aio_http2_disconnect_cb
  valk_arc_retain(res);
  // valk_arc_retain(res);  in promise_resolve

  valk_work_add(sys, task);
  uv_mutex_unlock(&sys->taskLock);
  uv_async_send(&sys->taskHandle);

  return res;
}

static void __aio_uv_stop(uv_async_t *h) { uv_stop(h->loop); }

//
valk_aio_system *valk_aio_start() {
  // On linux definitely turn sigpipe off
  // Otherwise shit crashes.
  // When the socket dissapears a write may be queued in the event loop
  // In that case we just want to do proper error handling without the
  // signal
  struct sigaction sa = {.sa_handler = SIG_IGN};
  sigaction(SIGPIPE, &sa, nullptr);

  valk_aio_system *sys = valk_mem_alloc(sizeof(valk_aio_system));
  valk_aio_ssl_start();
  sys->eventloop = uv_default_loop();
  sys->count = 0;
  sys->capacity = 10;

  uv_mutex_init(&sys->taskLock);
  uv_async_init(sys->eventloop, &sys->taskHandle, __task_cb);
  uv_async_init(sys->eventloop, &sys->stopper, __aio_uv_stop);
  sys->taskHandle.data = sys;

  int status = uv_thread_create(&sys->loopThread, __event_loop, sys);
  if (status) {
    perror("pthread_create");
  }
  return sys;
}

void valk_aio_stop(valk_aio_system *sys) {
  uv_async_send(&sys->stopper);
  printf("The before\n");
  printf("Processing the stopper\n");
  uv_thread_join(&sys->loopThread);
  printf("AFTER the Processing the stopper\n");
  printf("The after\n");
  uv_loop_close(sys->eventloop);
  // TODO(networking): need to properly free the system too
  valk_mem_free(sys);
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
  UNUSED(mem_user_data);
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
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memcpy(res, ptr, origSize);
  }
  return res;
}

static int __http_on_header_callback(nghttp2_session *session,
                                     const nghttp2_frame *frame,
                                     const uint8_t *name, size_t namelen,
                                     const uint8_t *value, size_t valuelen,
                                     uint8_t flags, void *user_data) {
  UNUSED(session);
  UNUSED(frame);
  UNUSED(flags);
  UNUSED(user_data);
  /* For demonstration, just print incoming headers. */
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  fprintf(stderr, "HDR: %.*s: %.*s\n", (int)namelen, name, (int)valuelen,
          value);

  return 0; // success
}
static int __http_on_begin_headers_callback(nghttp2_session *session,
                                            const nghttp2_frame *frame,
                                            void *user_data) {
  UNUSED(session);
  UNUSED(user_data);
  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, ">>> Received HTTP/2 request (stream_id=%d)\n",
            frame->hd.stream_id);
  }
  return 0;
}

static void __http_tcp_on_write_cb(uv_write_t *handle, int status) {
  if (status) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Socket On Write error: %s \n", uv_strerror(status));
  } else {
    printf("Receiving on write CB\n");
  }

  valk_slab_release_ptr(tcp_buffer_slab, handle);
}

static nghttp2_ssize __http_byte_body_cb(nghttp2_session *session,
                                         int32_t stream_id, uint8_t *buf,
                                         size_t length, uint32_t *data_flags,
                                         nghttp2_data_source *source,
                                         void *user_data) {
  UNUSED(session);
  UNUSED(stream_id);
  UNUSED(user_data);

  printf("Looking to get %ld bytes\n", length);
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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
  data_prd.source.ptr = VALK_HTTP_MOTD;
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
  UNUSED(user_data);
  // struct valk_aio_http_conn *client = (struct valk_aio_http_conn *)user_data;

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
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "nghttp2_session_mem_recv error: %zd\n", rv);
    uv_close((uv_handle_t *)&conn->tcpHandle, __uv_http_on_tcp_disconnect_cb);
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
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
      fprintf(stderr, "Read error: %s\n", uv_strerror((int)nread));
    }
    uv_close((uv_handle_t *)&conn->tcpHandle, __uv_http_on_tcp_disconnect_cb);
    return;
  }

  printf("Feeding data to OpenSSL %ld\n", nread);

  valk_buffer_t In = {
      .items = buf->base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  int err = valk_aio_ssl_on_read(&conn->ssl, &In, &Out, conn,
                                 __http_tcp_unencrypted_read_cb);

  // Only do this if ssl is established:
  if (!err) {
    // Flushies
    In.count = 0;
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
  }

  valk_slab_release_ptr(tcp_buffer_slab, In.items);
}

static int __http_send_server_connection_header(nghttp2_session *session) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, 100}};
  int rv;

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

static void __http_server_accept_cb(uv_stream_t *server, int status) {
  if (status < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "New connection error %s\n", uv_strerror(status));
    // error!
    return;
  }

  valk_aio_http_server *srv = server->data;
  // Init the arena
  valk_mem_arena_t *arena = (void *)valk_slab_aquire(tcp_connection_slab)->data;
  valk_mem_arena_init(arena,
                      HTTP_MAX_CONNECTION_HEAP - sizeof(valk_mem_arena_t));

  struct valk_aio_http_conn *conn =
      valk_mem_arena_alloc(arena, sizeof(struct valk_aio_http_conn));
  // haha point back to thy self
  conn->arena = arena;

  uv_tcp_init(server->loop, &conn->tcpHandle);
  conn->tcpHandle.data = conn;
  conn->handler = &srv->handler;

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
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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
      // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
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

    static nghttp2_session_callbacks *callbacks = nullptr;
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

    nghttp2_session_server_new3(&conn->session, callbacks, conn, nullptr,
                                &conn->session_allocator);
    valk_aio_ssl_accept(&conn->ssl, srv->ssl_ctx);

    // Send settings to the client
    __http_send_server_connection_header(conn->session);

    if (conn->handler) {
      conn->handler->onConnect(conn->handler->arg, conn);
    }

    // start the connection off by listening, (SSL expects client to send first)
    uv_read_start((uv_stream_t *)&conn->tcpHandle, __alloc_callback,
                  __http_tcp_read_cb);
  } else {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Fuck closing %s\n", uv_strerror(res));
    uv_close((uv_handle_t *)&conn->tcpHandle, __uv_http_on_tcp_disconnect_cb);
    // TODO(networking): should probably have a function for properly disposing
    // of the connection objects
    valk_slab_release_ptr(tcp_connection_slab, conn->arena);
  }
}

static void __http_listen_cb(valk_aio_system *sys, valk_arc_box *box,
                             valk_promise *promise) {
  UNUSED(sys);
  int r;
  struct sockaddr_in addr;
  valk_aio_http_server *srv = box->item;

  r = uv_tcp_init(srv->eventloop, &srv->listener);
  uv_tcp_nodelay(&srv->listener, 1);

  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "TcpInit err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on TcpInit");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }
  r = uv_ip4_addr(srv->interface, srv->port, &addr);
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Addr err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Addr");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }
#ifdef __linux__
  r = uv_tcp_bind(&srv->listener, (const struct sockaddr *)&addr,
                  UV_TCP_REUSEPORT);
#else
  r = uv_tcp_bind(&srv->listener, (const struct sockaddr *)&addr, 0);
#endif
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Bind err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Bind");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  srv->listener.data = srv;
  r = uv_listen((uv_stream_t *)&srv->listener, 128, __http_server_accept_cb);
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Listen err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Error on Listening");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  } else {
    printf("Listening on %s:%d\n", srv->interface, srv->port);
    valk_promise_respond(promise, box);
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

// static void __no_free(void *arg) { UNUSED(arg); }
valk_future *valk_aio_http2_listen(valk_aio_system *sys, const char *interface,
                                   const int port, const char *keyfile,
                                   const char *certfile,
                                   valk_http2_handler_t *handler) {
  valk_arc_box *box = valk_arc_box_new(VALK_SUC, sizeof(valk_aio_http_server));
  valk_aio_http_server *srv = box->item;
  valk_future *res = valk_future_new();

  srv->eventloop = sys->eventloop;
  srv->interface = strdup(interface);
  srv->port = port;
  srv->handler = *handler;

  uv_mutex_lock(&sys->taskLock);
  struct valk_aio_task task;

  valk_aio_ssl_server_init(&srv->ssl_ctx, keyfile, certfile);
  SSL_CTX_set_alpn_select_cb(srv->ssl_ctx, __alpn_select_proto_cb, NULL);

  task.arg = box;
  task.promise.item = res;
  task.callback = __http_listen_cb;

  valk_work_add(sys, task);

  uv_mutex_unlock(&sys->taskLock);
  uv_async_send(&sys->taskHandle);
  return res;
}

void valk_aio_hangup(valk_aio_socket *socket);

//// HTTP2 CLIENT

typedef struct valk_aio_http2_client {
  SSL_CTX *ssl_ctx;
  // TODO(networking):  connections could be pooled
  valk_aio_http_conn connection;
  char *interface;
  int port;
  // Totally internal, totally unneccessary, but i wanna avoid a tuple
  valk_promise _promise;
} valk_aio_http2_client;

static int __http_client_on_frame_recv_callback(nghttp2_session *session,
                                                const nghttp2_frame *frame,
                                                void *user_data) {
  UNUSED(session);
  UNUSED(user_data);

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
  (void)flags;
  (void)user_data;

  valk_promise *promise =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (promise) {
    printf("[INFO] C <---------------------------- S (DATA chunk)\n"
           "%lu bytes\n",
           (unsigned long int)len);
    fwrite(data, 1, len, stdout);
    printf("\n");

    valk_arc_box *box = valk_arc_box_new(VALK_SUC, len + 1);
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    memcpy(box->item, data, len);
    ((char *)box->item)[len] = '\0';

    valk_promise_respond(promise, box);
    valk_arc_release(box);
  }
  valk_mem_free(promise);
  return 0;
}

static void __uv_http2_connect_cb(uv_connect_t *req, int status) {
  valk_arc_box *box = req->data;
  // TODO(networking): assert that its a succefull box
  valk_aio_http2_client *client = box->item;

  if (status < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Client Connection err: %s\n", uv_strerror(status));
    valk_arc_box *err = valk_arc_box_err("Client Connection err");
    valk_promise_respond(&client->_promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  printf("Gurr we connected\n");

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  static nghttp2_session_callbacks *callbacks = nullptr;
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

  valk_aio_ssl_handshake(&client->connection.ssl, &Out);

  int wantToSend = Out.count > 0;
  if (wantToSend) {
    slabItem->buf.base = Out.items;
    slabItem->buf.len = Out.count;

    printf("[Client] Sending %ld bytes\n", Out.count);
    uv_write(&slabItem->req, (uv_stream_t *)&client->connection.tcpHandle,
             &slabItem->buf, 1, __http_tcp_on_write_cb);
  } else {
    valk_slab_release_ptr(tcp_buffer_slab, Out.items);
  }

  uv_read_start((uv_stream_t *)&client->connection.tcpHandle, __alloc_callback,
                __http_tcp_read_cb);

  printf("Finished initializing client %p\n", (void *)client);

  // Shits connected but not fully established, it will buffer any requests tho
  // releases the promise
  valk_promise_respond(&client->_promise, box);
  valk_arc_release(box);
}

static void __aio_client_connect_cb(valk_aio_system *sys, valk_arc_box *box,
                                    valk_promise *promise) {
  int r;
  struct sockaddr_in addr;

  valk_aio_http2_client *client = box->item;

  r = uv_tcp_init(sys->eventloop, &client->connection.tcpHandle);

  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "TcpInit err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("TcpInit err");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  uv_tcp_nodelay(&client->connection.tcpHandle, 1);
  client->connection.tcpHandle.data = &client->connection;

  r = uv_ip4_addr(client->interface, client->port, &addr);
  if (r) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Addr err: %s \n", uv_strerror(r));
    valk_arc_box *err = valk_arc_box_err("Addr err");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    valk_arc_release(box);
    return;
  }

  client->connection.req.data = box;
  client->_promise = *promise;
  uv_tcp_connect(&client->connection.req, &client->connection.tcpHandle,
                 (const struct sockaddr *)&addr, __uv_http2_connect_cb);
}

valk_future *valk_aio_http2_connect(valk_aio_system *sys, const char *interface,
                                    const int port, const char *certfile) {
  UNUSED(certfile);
  uv_mutex_lock(&sys->taskLock);

  struct valk_aio_task task;

  valk_future *res = valk_future_new();
  // TODO(networking): do i even need boxes here?? 🤔
  task.arg = valk_arc_box_new(VALK_SUC, sizeof(valk_aio_http2_client));
  memset(task.arg->item, 0, sizeof(valk_aio_http2_client));

  valk_aio_http2_client *client = task.arg->item;
  client->interface = strdup(interface);
  client->port = port;

  task.promise.item = res;
  task.callback = __aio_client_connect_cb;
  valk_arc_retain(res);
  // valk_arc_release(res) in resolve

  valk_work_add(sys, task);

  uv_mutex_unlock(&sys->taskLock);
  printf("Initializing client %p\n", (void *)client);
  uv_async_send(&sys->taskHandle);
  return res;
}

static void __http2_submit_demo_request_cb(valk_aio_system *sys,
                                           valk_arc_box *arg,
                                           valk_promise *promise) {
  UNUSED(sys);

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

  // TODO(networking): Allocating this promise here temporarily, ideally need to
  // be passing a request object with a promise on it
  valk_promise *prom = valk_mem_alloc(sizeof(valk_promise));
  // valk_mem_free(sizeof(valk_promise)); in callback to nghttp2 recv
  *prom = *promise; // copy this shit

  stream_id =
      nghttp2_submit_request2(conn->session, nullptr, hdrs,
                              sizeof(hdrs) / sizeof(hdrs[0]), nullptr, prom);

  if (stream_id < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr, "Could not submit HTTP request: %s\n",
            nghttp2_strerror(stream_id));
    valk_arc_box *err = valk_arc_box_err("Could not submit HTTP request");
    valk_promise_respond(promise, err);
    valk_arc_release(err);
    valk_arc_release(arg);
    return;
  }

  printf("Submitted request with stream id %d\n", stream_id);

  char buf[SSL3_RT_MAX_PACKET_SIZE];
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};
  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

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
      valk_slab_release_ptr(tcp_buffer_slab, slabItem);
    }
  }

  valk_arc_release(arg);
  // return stream_id;
}

static valk_future *__http2_submit_demo_request(valk_aio_system *sys,
                                                valk_arc_box *client) {
  valk_future *res = valk_future_new();
  uv_mutex_lock(&sys->taskLock);
  struct valk_aio_task task;

  task.arg = client;
  task.promise.item = res;
  task.callback = __http2_submit_demo_request_cb;
  valk_arc_retain(client);
  valk_arc_retain(res);

  // valk_arc_release(client); in callback
  // valk_arc_release(res); in resolve

  valk_work_add(sys, task);
  uv_mutex_unlock(&sys->taskLock);
  uv_async_send(&sys->taskHandle);
  return res;
}

char *valk_client_demo(valk_aio_system *sys, const char *domain,
                       const char *port) {
  UNUSED(domain);
  UNUSED(port);

  // GOOGLE
  // valk_arc_box *box = valk_future_await(
  //     valk_aio_http2_connect(&sys, "142.250.191.78", 443, ""));

  // Local
  valk_future *fut = valk_aio_http2_connect(sys, "127.0.0.1", 6969, "");
  printf("Arc count of fut : %d\n", fut->refcount);
  valk_arc_box *client = valk_future_await(fut);
  printf("Arc count of fut : %d\n", fut->refcount);
  valk_arc_release(fut);
  // printf("Arc count of fut : %d\n", fut->refcount);

  VALK_ASSERT(client->type == VALK_SUC, "Error creating client: %s",
              client->item);

  fut = __http2_submit_demo_request(sys, client);
  valk_arc_box *response = valk_future_await(fut);

  valk_arc_release(fut);

  VALK_ASSERT(response->type == VALK_SUC, "Error from the response: %s",
              response->item);

  printf("Got response %s\n", (char *)response->item);
  char *res = strdup(response->item);

  valk_arc_release(response);
  fut = valk_aio_http2_disconnect(sys, client);
  response = valk_future_await(fut);
  valk_arc_release(fut);
  // VALK_ASSERT(response->type == VALK_SUC, "Error from the disconnect : %s",
  //             response->item);

  valk_arc_release(response);

  valk_arc_release(client);

  return res;
}

// reference code for openssl setup
//
// https://github.com/darrenjs/openssl_examples
