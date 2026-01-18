#include "io_tcp_uv_types.h"
#include "aio/aio_internal.h"
#include <netdb.h>

typedef struct {
  uv_write_t req;
  uv_buf_t buf;
  valk_io_write_cb user_cb;
  valk_io_tcp_t *tcp;
} write_req_t;

typedef struct {
  uv_connect_t req;
  valk_io_tcp_t *tcp;
} connect_req_t;

static void __alloc_cb_adapter(uv_handle_t *handle, size_t suggested, uv_buf_t *buf) {
  valk_io_tcp_t *tcp = (valk_io_tcp_t *)handle;
  void *buffer = nullptr;
  u64 buflen = 0;
  if (tcp->user_alloc_cb) {  // LCOV_EXCL_BR_LINE - always set before read_start
    tcp->user_alloc_cb(tcp, suggested, &buffer, &buflen);
  }
  buf->base = buffer;
  buf->len = buflen;
}

static void __read_cb_adapter(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  valk_io_tcp_t *tcp = (valk_io_tcp_t *)stream;
  if (tcp->user_read_cb) {  // LCOV_EXCL_BR_LINE - always set before read_start
    tcp->user_read_cb(tcp, nread, buf->base);
  }
}

static void __connection_cb_adapter(uv_stream_t *server, int status) {
  valk_io_tcp_t *tcp = (valk_io_tcp_t *)server;
  if (tcp->user_connection_cb) {  // LCOV_EXCL_BR_LINE - always set before listen
    tcp->user_connection_cb(tcp, status);
  }
}

static void __connect_cb_adapter(uv_connect_t *req, int status) {
  connect_req_t *creq = (connect_req_t *)req;
  if (creq->tcp->user_connect_cb) {  // LCOV_EXCL_BR_LINE - always set before connect
    creq->tcp->user_connect_cb(creq->tcp, status);
  }
  free(creq);
}

// LCOV_EXCL_START - callback for tcp_write, not used (write_bufs used instead)
static void __write_cb_adapter(uv_write_t *req, int status) {
  write_req_t *wreq = (write_req_t *)req;
  if (wreq->user_cb) {
    wreq->user_cb(wreq, status);
  }
  free(wreq->buf.base);
  free(wreq);
}
// LCOV_EXCL_STOP

static int tcp_init(valk_aio_system_t *sys, valk_io_tcp_t *tcp) {
  memset(tcp, 0, sizeof(*tcp));
  return uv_tcp_init(sys->eventloop, &tcp->uv);
}

static void tcp_close(valk_io_tcp_t *tcp, valk_io_close_cb cb) {
  uv_close((uv_handle_t *)&tcp->uv, (uv_close_cb)cb);
}

static bool tcp_is_closing(valk_io_tcp_t *tcp) {
  return uv_is_closing((uv_handle_t *)&tcp->uv);
}

static int tcp_bind(valk_io_tcp_t *tcp, const char *ip, int port) {
  struct sockaddr_in addr;
  int r = uv_ip4_addr(ip, port, &addr);
  if (r) return r;
  return uv_tcp_bind(&tcp->uv, (const struct sockaddr *)&addr, 0);
}

static int tcp_listen(valk_io_tcp_t *tcp, int backlog, valk_io_connection_cb cb) {
  tcp->user_connection_cb = cb;
  return uv_listen((uv_stream_t *)&tcp->uv, backlog, __connection_cb_adapter);
}

static int tcp_accept(valk_io_tcp_t *server, valk_io_tcp_t *client) {
  return uv_accept((uv_stream_t *)&server->uv, (uv_stream_t *)&client->uv);
}

static int tcp_getpeername(valk_io_tcp_t *tcp, void *addr, int *len) {
  return uv_tcp_getpeername(&tcp->uv, (struct sockaddr *)addr, len);
}

static int tcp_connect(valk_io_tcp_t *tcp, const char *ip, int port, valk_io_connect_cb cb) {
  struct sockaddr_in addr;
  int r = uv_ip4_addr(ip, port, &addr);
  if (r) {
    struct addrinfo hints, *res = nullptr;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    char portstr[16];
    snprintf(portstr, sizeof portstr, "%d", port);
    int gai = getaddrinfo(ip, portstr, &hints, &res);
    // LCOV_EXCL_BR_START - DNS resolution error paths
    if (gai == 0 && res) {
      memcpy(&addr, res->ai_addr, sizeof(struct sockaddr_in));
      freeaddrinfo(res);
    } else {
      if (res) freeaddrinfo(res);
      return -1;
    }
    // LCOV_EXCL_BR_STOP
  }

  connect_req_t *creq = malloc(sizeof(connect_req_t));
  // LCOV_EXCL_START - OOM path
  if (!creq) return -1;
  // LCOV_EXCL_STOP
  creq->tcp = tcp;
  tcp->user_connect_cb = cb;

  int rv = uv_tcp_connect(&creq->req, &tcp->uv, (const struct sockaddr *)&addr, __connect_cb_adapter);
  // LCOV_EXCL_START - libuv connect init failure (essentially never fails for valid socket)
  if (rv != 0) {
    free(creq);
  }
  // LCOV_EXCL_STOP
  return rv;
}

static int tcp_read_start(valk_io_tcp_t *tcp, valk_io_alloc_cb alloc, valk_io_read_cb read) {
  tcp->user_alloc_cb = alloc;
  tcp->user_read_cb = read;
  return uv_read_start((uv_stream_t *)&tcp->uv, __alloc_cb_adapter, __read_cb_adapter);
}

static int tcp_read_stop(valk_io_tcp_t *tcp) {
  return uv_read_stop((uv_stream_t *)&tcp->uv);
}

// LCOV_EXCL_START - interface function, write_bufs used instead in production
static int tcp_write(valk_io_tcp_t *tcp, const void *data, u64 len, valk_io_write_cb cb) {
  write_req_t *wreq = malloc(sizeof(write_req_t));
  if (!wreq) return -1;

  wreq->buf.base = malloc(len);
  if (!wreq->buf.base) {
    free(wreq);
    return -1;
  }
  memcpy(wreq->buf.base, data, len);
  wreq->buf.len = len;
  wreq->user_cb = cb;
  wreq->tcp = tcp;

  int rv = uv_write(&wreq->req, (uv_stream_t *)&tcp->uv, &wreq->buf, 1, __write_cb_adapter);
  if (rv != 0) {
    free(wreq->buf.base);
    free(wreq);
  }
  return rv;
}
// LCOV_EXCL_STOP

static int tcp_nodelay(valk_io_tcp_t *tcp, int enable) {
  return uv_tcp_nodelay(&tcp->uv, enable);
}

// LCOV_EXCL_START - interface functions for extensibility, not used in production
static void tcp_set_data(valk_io_tcp_t *tcp, void *data) {
  tcp->user_data = data;
}

static void *tcp_get_data(valk_io_tcp_t *tcp) {
  return tcp->user_data;
}

static void *tcp_get_loop(valk_io_tcp_t *tcp) {
  return tcp->uv.loop;
}
// LCOV_EXCL_STOP

static int tcp_getsockname(valk_io_tcp_t *tcp, void *addr, int *len) {
  return uv_tcp_getsockname(&tcp->uv, (struct sockaddr *)addr, len);
}

static int tcp_ip4_name(const void *addr, char *dst, u64 size) {
  return uv_ip4_name((const struct sockaddr_in *)addr, dst, size);
}

static int tcp_ip6_name(const void *addr, char *dst, u64 size) {
  return uv_ip6_name((const struct sockaddr_in6 *)addr, dst, size);
}

static const char *tcp_strerror(int err) {
  return uv_strerror(err);
}

static void __write_bufs_cb_adapter(uv_write_t *req, int status) {
  valk_io_write_req_t *wreq = (valk_io_write_req_t *)req;
  if (wreq->user_cb) {  // LCOV_EXCL_BR_LINE - optional callback, defensive check
    wreq->user_cb(wreq, status);
  }
}

static int tcp_write_bufs(valk_io_tcp_t *tcp, valk_io_write_req_t *req,
                          const valk_io_buf_t *bufs, unsigned int nbufs,
                          valk_io_write_bufs_cb cb) {
  req->user_cb = cb;
  _Static_assert(sizeof(valk_io_buf_t) == sizeof(uv_buf_t), "valk_io_buf_t must match uv_buf_t");
  _Static_assert(offsetof(valk_io_buf_t, base) == offsetof(uv_buf_t, base), "buf base offset mismatch");
  _Static_assert(offsetof(valk_io_buf_t, len) == offsetof(uv_buf_t, len), "buf len offset mismatch");
  return uv_write(&req->uv, (uv_stream_t *)&tcp->uv, (const uv_buf_t *)bufs, nbufs, __write_bufs_cb_adapter);
}

const valk_io_tcp_ops_t valk_io_tcp_ops_uv = {
  .init = tcp_init,
  .close = tcp_close,
  .is_closing = tcp_is_closing,
  .bind = tcp_bind,
  .listen = tcp_listen,
  .accept = tcp_accept,
  .getpeername = tcp_getpeername,
  .connect = tcp_connect,
  .read_start = tcp_read_start,
  .read_stop = tcp_read_stop,
  .write = tcp_write,
  .write_bufs = tcp_write_bufs,
  .nodelay = tcp_nodelay,
  .set_data = tcp_set_data,
  .get_data = tcp_get_data,
  .get_loop = tcp_get_loop,
  .getsockname = tcp_getsockname,
  .ip4_name = tcp_ip4_name,
  .ip6_name = tcp_ip6_name,
  .strerror = tcp_strerror,
};
