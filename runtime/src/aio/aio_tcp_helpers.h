#ifndef VALK_AIO_TCP_HELPERS_H
#define VALK_AIO_TCP_HELPERS_H

#include "aio_internal.h"

static inline const valk_io_tcp_ops_t *__tcp_ops(valk_aio_handle_t *conn) {
  return conn->sys ? conn->sys->ops->tcp : nullptr; // LCOV_EXCL_BR_LINE defensive null check
}

static inline valk_io_tcp_t *__conn_tcp(valk_aio_handle_t *conn) {
  return &conn->uv.tcp;
}

static inline bool __vtable_is_closing(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return true; // LCOV_EXCL_BR_LINE defensive null check
  return tcp->is_closing(__conn_tcp(conn));
}

static inline void __vtable_close(valk_aio_handle_t *conn, valk_io_close_cb cb) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return; // LCOV_EXCL_BR_LINE defensive null check
  tcp->close(__conn_tcp(conn), cb);
}

static inline int __vtable_init(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->init(conn->sys, __conn_tcp(conn));
}

static inline int __vtable_accept(valk_aio_handle_t *server, valk_aio_handle_t *client) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(server);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->accept(__conn_tcp(server), __conn_tcp(client));
}

static inline int __vtable_nodelay(valk_aio_handle_t *conn, int enable) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return ops->nodelay(__conn_tcp(conn), enable);
}

#endif
