#pragma once

#include "types.h"
#include "io_types.h"
#include <sys/types.h>

typedef void (*valk_io_alloc_cb)(valk_io_tcp_t *tcp, u64 suggested, void **buf, u64 *buflen);
typedef void (*valk_io_read_cb)(valk_io_tcp_t *tcp, ssize_t nread, const void *buf);
typedef void (*valk_io_write_cb)(void *req, int status);
typedef void (*valk_io_write_bufs_cb)(valk_io_write_req_t *req, int status);
typedef void (*valk_io_connect_cb)(valk_io_tcp_t *tcp, int status);
typedef void (*valk_io_connection_cb)(valk_io_tcp_t *server, int status);

typedef struct valk_io_tcp_ops {
  int (*init)(valk_aio_system_t *sys, valk_io_tcp_t *tcp);
  void (*close)(valk_io_tcp_t *tcp, valk_io_close_cb cb);
  bool (*is_closing)(valk_io_tcp_t *tcp);

  int (*bind)(valk_io_tcp_t *tcp, const char *ip, int port);
  int (*listen)(valk_io_tcp_t *tcp, int backlog, valk_io_connection_cb cb);
  int (*accept)(valk_io_tcp_t *server, valk_io_tcp_t *client);
  int (*getpeername)(valk_io_tcp_t *tcp, void *addr, int *len);

  int (*connect)(valk_io_tcp_t *tcp, const char *ip, int port, valk_io_connect_cb cb);

  int (*read_start)(valk_io_tcp_t *tcp, valk_io_alloc_cb alloc, valk_io_read_cb read);
  int (*read_stop)(valk_io_tcp_t *tcp);
  int (*write)(valk_io_tcp_t *tcp, const void *data, u64 len, valk_io_write_cb cb);

  int (*write_bufs)(valk_io_tcp_t *tcp, valk_io_write_req_t *req,
                    const valk_io_buf_t *bufs, unsigned int nbufs,
                    valk_io_write_bufs_cb cb);

  int (*nodelay)(valk_io_tcp_t *tcp, int enable);

  void (*set_data)(valk_io_tcp_t *tcp, void *data);
  void *(*get_data)(valk_io_tcp_t *tcp);

  void *(*get_loop)(valk_io_tcp_t *tcp);

  int (*getsockname)(valk_io_tcp_t *tcp, void *addr, int *len);
  int (*ip4_name)(const void *addr, char *dst, u64 size);
  int (*ip6_name)(const void *addr, char *dst, u64 size);
  const char *(*strerror)(int err);

  u64 tcp_size;
  u64 write_req_size;
} valk_io_tcp_ops_t;

extern const valk_io_tcp_ops_t valk_io_tcp_ops_uv;
extern const valk_io_tcp_ops_t valk_io_tcp_ops_test;

typedef struct valk_test_tcp_state {
  struct valk_test_pending_conn {
    valk_io_tcp_t *client;
    struct valk_test_pending_conn *next;
  } *pending_conns;

  u8 *recv_buf;
  u64 recv_len;
  u64 recv_cap;

  u8 *sent_buf;
  u64 sent_len;
  u64 sent_cap;
} valk_test_tcp_state_t;

void valk_test_tcp_inject_data(valk_io_tcp_t *tcp, const void *data, u64 len);
void valk_test_tcp_inject_connection(valk_io_tcp_t *server, valk_io_tcp_t *client);
u64 valk_test_tcp_get_sent(valk_io_tcp_t *tcp, void *buf, u64 max_len);
