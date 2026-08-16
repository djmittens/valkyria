#include "io_loop_ops.h"
#include "aio/aio_internal.h"

static void loop_destroy(valk_aio_system_t *sys) {
  sys->eventloop = nullptr;
}

static u64 loop_now(valk_aio_system_t *sys) {
  return uv_now(sys->eventloop);
}

const valk_io_loop_ops_t valk_io_loop_ops_uv = {
  .destroy = loop_destroy,
  .now = loop_now,
};
