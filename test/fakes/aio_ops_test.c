#include "aio/aio_ops.h"
#include "aio/io/io_loop_ops.h"
#include "aio/io/io_timer_ops.h"
#include "aio/io/io_tcp_ops.h"

const valk_aio_ops_t valk_aio_ops_test = {
  .loop = &valk_io_loop_ops_test,
  .timer = &valk_io_timer_ops_test,
  .tcp = &valk_io_tcp_ops_test,
};
