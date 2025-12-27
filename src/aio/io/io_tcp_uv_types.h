#pragma once

#include "io_tcp_ops.h"
#include <uv.h>

struct valk_io_tcp {
  uv_tcp_t uv;
  valk_io_alloc_cb user_alloc_cb;
  valk_io_read_cb user_read_cb;
  valk_io_connection_cb user_connection_cb;
  valk_io_connect_cb user_connect_cb;
  void *user_data;
};

struct valk_io_write_req {
  uv_write_t uv;
  valk_io_write_bufs_cb user_cb;
  void *user_data;
};
