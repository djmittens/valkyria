#include "aio.h"
#include "common.h"
#include "concurrency.h"
#include "memory.h"
#include <netinet/in.h>
#include <nghttp2/nghttp2.h>
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

void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                      uv_buf_t *buf) {}

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
  uv_tcp_t server;
  char *interface;
  int port;
};

struct valk_aio_http_conn {
  uv_tcp_t handle;
  nghttp2_session *session;
  uv_buf_t send_buf;
  int closed;
};

static void __event_loop(void *arg) {
  valk_aio_system *sys = arg;
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

/*
 * Called whenever nghttp2 wants to send data to the peer.
 * We'll buffer that data in client->send_buf, then schedule a uv_write.
 */
static ssize_t __http_send_callback(nghttp2_session *session,
                                    const uint8_t *data, size_t length,
                                    int flags, void *user_data) {
  struct valk_aio_http_conn *client = (struct valk_aio_http_conn *)user_data;

  /* Grow our send buffer and copy data in. */
  size_t old_len = client->send_buf.len;
  client->send_buf.base = realloc(client->send_buf.base, old_len + length);

  memcpy(client->send_buf.base + old_len, data, length);
  client->send_buf.len += length;

  return (ssize_t)length;
}

static int __demo_response(nghttp2_session *session, int stream_id) {

  /* Prepare some pseudo-headers: */
  const nghttp2_nv response_headers[] = {
      MAKE_NV2(":status", "200"), MAKE_NV2("content-type", "text/plain")};

  /* Send HEADERS frame */
  nghttp2_submit_headers(
      session, NGHTTP2_FLAG_END_HEADERS, stream_id, NULL, response_headers,
      sizeof(response_headers) / sizeof(response_headers[0]), NULL);

  /* Send DATA frame */
  const char *body = "Hello HTTP/2 from libuv + nghttp2\n";

  return nghttp2_submit_push_promise(session, 0, stream_id, response_headers, 2,
                                     (void *)body);
}

/* Called when a frame is fully received. For a request, we might respond here.
 */
static int __http_on_frame_recv_callback(nghttp2_session *session,
                                         const nghttp2_frame *frame,
                                         void *user_data) {
  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
    /* Example: respond with a small HEADERS + DATA for "Hello HTTP/2" */
    int stream_id = frame->hd.stream_id;
    __demo_response(session, stream_id);
  }

  return 0;
}

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {
  struct valk_aio_http_conn *client = (struct valk_aio_http_conn *)stream->data;
  if (nread < 0) {
    // Error or EOF
    if (nread != UV_EOF) {
      fprintf(stderr, "Read error: %s\n", uv_strerror((int)nread));
    }
    uv_close((uv_handle_t *)stream, NULL);
    valk_mem_free(buf->base);
    return;
  }
  // Feed data to nghttp2
  ssize_t rv = nghttp2_session_mem_recv(client->session,
                                        (const uint8_t *)buf->base, nread);
  if (rv < 0) {
    fprintf(stderr, "nghttp2_session_mem_recv error: %zd\n", rv);
    uv_close((uv_handle_t *)stream, NULL);
    valk_mem_free(buf->base);
    return;
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
  printf("Accepting new connection \n");
  struct valk_aio_http_conn *conn =
      valk_mem_alloc(sizeof(struct valk_aio_http_conn));
  uv_tcp_init(server->loop, &conn->handle);
  conn->handle.data = conn;
  int res = uv_accept(server, (uv_stream_t *)&conn->handle);
  if (res) {
    static nghttp2_session_callbacks *callbacks = NULL;
    if (!callbacks) {
      nghttp2_session_callbacks_new(&callbacks);
      nghttp2_session_callbacks_set_send_callback(callbacks,
                                                  __http_send_callback);
      nghttp2_session_callbacks_set_on_begin_headers_callback(
          callbacks, __http_on_begin_headers_callback);
      nghttp2_session_callbacks_set_on_header_callback(
          callbacks, __http_on_header_callback);
      nghttp2_session_callbacks_set_on_frame_recv_callback(
          callbacks, __http_on_frame_recv_callback);
    }

    nghttp2_session_server_new(&conn->session, callbacks, conn);

    // Send settings to the client
    __http_send_server_connection_header(conn->session);
    uv_read_start((uv_stream_t *)&conn->handle, __alloc_callback,
                  __http_tcp_read_cb);
  } else {
    uv_close((uv_handle_t *)&conn->handle, NULL);
    valk_mem_free(conn);
  }
}

static void __http_not_listencb(uv_work_t *req) {
  printf("Not listeing duuuh \n");
}
static void __http_listen_cb(valk_arc_box* box) {
  int r;
  struct sockaddr_in addr;
  valk_aio_http_server *srv = box->succ;
  r = uv_tcp_init(srv->eventloop, &srv->server);
  if (r) {
    fprintf(stderr, "TcpInit err: %s \n", uv_strerror(r));
    return;
  }
  r = uv_ip4_addr(srv->interface, srv->port, &addr);
  if (r) {
    fprintf(stderr, "Addr err: %s \n", uv_strerror(r));
    return;
  }
  r = uv_tcp_bind(&srv->server, (const struct sockaddr *)&addr, 0);
  if (r) {
    fprintf(stderr, "Bind err: %s \n", uv_strerror(r));
    return;
  }

  r = uv_listen((uv_stream_t *)&srv->server, 128, __http_connection_cb);
  if (r) {
    fprintf(stderr, "Listen err: %s \n", uv_strerror(r));
    return;
  } else {
    printf("Listening on %s:%d\n", srv->interface, srv->port);
  }
  valk_arc_box_release(box);
}

static void __no_free(void *arg) { UNUSED(arg); }
void valk_aio_http_listen(valk_aio_http_server *srv, valk_aio_system *sys,
                          const char *interface, const int port) {
  srv->eventloop = sys->eventloop;
  srv->interface = strdup(interface);
  srv->port = port;

  uv_mutex_lock(&sys->taskLock);
  struct valk_aio_task task;
  task.arg = valk_arc_box_suc(srv, __no_free);
  task.callback = __http_listen_cb;

  valk_work_add(sys, task);

  uv_mutex_unlock(&sys->taskLock);
  uv_async_send(&sys->taskHandle);
}

void valk_aio_hangup(valk_aio_socket *socket);

void valk_server_demo(void) {
  valk_aio_system *sys = valk_mem_alloc(sizeof(valk_aio_system));
  valk_aio_http_server *srv = valk_mem_alloc(sizeof(valk_aio_http_server));
  valk_aio_start(sys);
  valk_aio_http_listen(srv, sys, "0.0.0.0", 6969);
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
