#include "io_tcp_ops.h"
#include <stdlib.h>
#include <string.h>

struct valk_io_write_req {
  valk_io_write_bufs_cb user_cb;
  void *user_data;
};

struct valk_io_tcp {
  valk_io_alloc_cb alloc_cb;
  valk_io_read_cb read_cb;
  valk_io_connection_cb connection_cb;
  valk_io_connect_cb connect_cb;
  void *user_data;
  bool closing;
  bool listening;

  valk_test_tcp_state_t test_state;

  struct valk_io_tcp *pending_accept;
};

static int test_tcp_init(valk_aio_system_t *sys, valk_io_tcp_t *tcp) {
  (void)sys;
  memset(tcp, 0, sizeof(*tcp));
  return 0;
}

static void test_tcp_close(valk_io_tcp_t *tcp, valk_io_close_cb cb) {
  tcp->closing = true;
  if (cb) cb(tcp);
}

static bool test_tcp_is_closing(valk_io_tcp_t *tcp) {
  return tcp->closing;
}

static int test_tcp_bind(valk_io_tcp_t *tcp, const char *ip, int port) {
  (void)tcp;
  (void)ip;
  (void)port;
  return 0;
}

static int test_tcp_listen(valk_io_tcp_t *tcp, int backlog, valk_io_connection_cb cb) {
  (void)backlog;
  tcp->connection_cb = cb;
  tcp->listening = true;
  return 0;
}

static int test_tcp_accept(valk_io_tcp_t *server, valk_io_tcp_t *client) {
  if (!server->pending_accept) return -1;
  memcpy(client, server->pending_accept, sizeof(*client));
  server->pending_accept = nullptr;
  return 0;
}

static int test_tcp_getpeername(valk_io_tcp_t *tcp, void *addr, int *len) {
  (void)tcp;
  (void)addr;
  (void)len;
  return 0;
}

static int test_tcp_connect(valk_io_tcp_t *tcp, const char *ip, int port, valk_io_connect_cb cb) {
  (void)ip;
  (void)port;
  tcp->connect_cb = cb;
  if (cb) cb(tcp, 0);
  return 0;
}

static int test_tcp_read_start(valk_io_tcp_t *tcp, valk_io_alloc_cb alloc, valk_io_read_cb read) {
  tcp->alloc_cb = alloc;
  tcp->read_cb = read;
  return 0;
}

static int test_tcp_read_stop(valk_io_tcp_t *tcp) {
  tcp->alloc_cb = nullptr;
  tcp->read_cb = nullptr;
  return 0;
}

static int test_tcp_write(valk_io_tcp_t *tcp, const void *data, u64 len, valk_io_write_cb cb) {
  if (tcp->test_state.sent_len + len > tcp->test_state.sent_cap) {
    u64 new_cap = tcp->test_state.sent_cap == 0 ? 4096 : tcp->test_state.sent_cap * 2;
    while (new_cap < tcp->test_state.sent_len + len) new_cap *= 2;
    u8 *new_buf = realloc(tcp->test_state.sent_buf, new_cap);
    if (!new_buf) return -1;
    tcp->test_state.sent_buf = new_buf;
    tcp->test_state.sent_cap = new_cap;
  }

  memcpy(tcp->test_state.sent_buf + tcp->test_state.sent_len, data, len);
  tcp->test_state.sent_len += len;

  if (cb) cb(nullptr, 0);
  return 0;
}

static int test_tcp_nodelay(valk_io_tcp_t *tcp, int enable) {
  (void)tcp;
  (void)enable;
  return 0;
}

static void test_tcp_set_data(valk_io_tcp_t *tcp, void *data) {
  tcp->user_data = data;
}

static void *test_tcp_get_data(valk_io_tcp_t *tcp) {
  return tcp->user_data;
}

static void *test_tcp_get_loop(valk_io_tcp_t *tcp) {
  (void)tcp;
  return nullptr;
}

static int test_tcp_getsockname(valk_io_tcp_t *tcp, void *addr, int *len) {
  (void)tcp;
  (void)addr;
  (void)len;
  return 0;
}

static int test_tcp_ip4_name(const void *addr, char *dst, u64 size) {
  (void)addr;
  if (size > 0) dst[0] = '\0';
  return 0;
}

static int test_tcp_ip6_name(const void *addr, char *dst, u64 size) {
  (void)addr;
  if (size > 0) dst[0] = '\0';
  return 0;
}

static const char *test_tcp_strerror(int err) {
  (void)err;
  return "test error";
}

static int test_tcp_write_bufs(valk_io_tcp_t *tcp, valk_io_write_req_t *req,
                               const valk_io_buf_t *bufs, unsigned int nbufs,
                               valk_io_write_bufs_cb cb) {
  u64 total_len = 0;
  for (unsigned int i = 0; i < nbufs; i++) {
    total_len += bufs[i].len;
  }

  if (tcp->test_state.sent_len + total_len > tcp->test_state.sent_cap) {
    u64 new_cap = tcp->test_state.sent_cap == 0 ? 4096 : tcp->test_state.sent_cap * 2;
    while (new_cap < tcp->test_state.sent_len + total_len) new_cap *= 2;
    u8 *new_buf = realloc(tcp->test_state.sent_buf, new_cap);
    if (!new_buf) return -1;
    tcp->test_state.sent_buf = new_buf;
    tcp->test_state.sent_cap = new_cap;
  }

  for (unsigned int i = 0; i < nbufs; i++) {
    memcpy(tcp->test_state.sent_buf + tcp->test_state.sent_len, bufs[i].base, bufs[i].len);
    tcp->test_state.sent_len += bufs[i].len;
  }

  if (cb) cb(req, 0);
  return 0;
}

const valk_io_tcp_ops_t valk_io_tcp_ops_test = {
  .init = test_tcp_init,
  .close = test_tcp_close,
  .is_closing = test_tcp_is_closing,
  .bind = test_tcp_bind,
  .listen = test_tcp_listen,
  .accept = test_tcp_accept,
  .getpeername = test_tcp_getpeername,
  .connect = test_tcp_connect,
  .read_start = test_tcp_read_start,
  .read_stop = test_tcp_read_stop,
  .write = test_tcp_write,
  .write_bufs = test_tcp_write_bufs,
  .nodelay = test_tcp_nodelay,
  .set_data = test_tcp_set_data,
  .get_data = test_tcp_get_data,
  .get_loop = test_tcp_get_loop,
  .getsockname = test_tcp_getsockname,
  .ip4_name = test_tcp_ip4_name,
  .ip6_name = test_tcp_ip6_name,
  .strerror = test_tcp_strerror,
};

void valk_test_tcp_inject_data(valk_io_tcp_t *tcp, const void *data, u64 len) {
  if (!tcp->read_cb) return;

  void *buf = nullptr;
  u64 buflen = 0;
  if (tcp->alloc_cb) {
    tcp->alloc_cb(tcp, len, &buf, &buflen);
  }

  if (buf && buflen >= len) {
    memcpy(buf, data, len);
    tcp->read_cb(tcp, (ssize_t)len, buf);
  }
}

void valk_test_tcp_inject_connection(valk_io_tcp_t *server, valk_io_tcp_t *client) {
  if (!server->listening || !server->connection_cb) return;
  server->pending_accept = client;
  server->connection_cb(server, 0);
}

u64 valk_test_tcp_get_sent(valk_io_tcp_t *tcp, void *buf, u64 max_len) {
  u64 to_copy = tcp->test_state.sent_len < max_len ? tcp->test_state.sent_len : max_len;
  if (buf && to_copy > 0) {
    memcpy(buf, tcp->test_state.sent_buf, to_copy);
  }
  return tcp->test_state.sent_len;
}
