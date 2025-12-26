#include "aio_ops.h"

const valk_aio_ops_t valk_aio_ops_production = {
  .loop = &valk_io_loop_ops_uv,
  .timer = &valk_io_timer_ops_uv,
  .tcp = &valk_io_tcp_ops_uv,
  .http2 = &valk_http2_ops_nghttp2,
};

const valk_aio_ops_t valk_aio_ops_test = {
  .loop = &valk_io_loop_ops_test,
  .timer = &valk_io_timer_ops_test,
  .tcp = &valk_io_tcp_ops_test,
  .http2 = &valk_http2_ops_test,
};
