#include "io_loop_ops.h"
#include "aio/aio_internal.h"

static int loop_init(valk_aio_system_t *sys) {
  sys->eventloop = malloc(sizeof(uv_loop_t));
  if (!sys->eventloop) return -1;
  
  int rc = uv_loop_init(sys->eventloop);
  if (rc != 0) {
    free(sys->eventloop);
    sys->eventloop = nullptr;
    return rc;
  }
  return 0;
}

static void loop_destroy(valk_aio_system_t *sys) {
  if (sys->eventloop) {
    uv_loop_close(sys->eventloop);
    free(sys->eventloop);
    sys->eventloop = nullptr;
  }
}

static int loop_run(valk_aio_system_t *sys, valk_io_run_mode_e mode) {
  uv_run_mode uv_mode;
  switch (mode) {
    case VALK_IO_RUN_ONCE: uv_mode = UV_RUN_ONCE; break;
    case VALK_IO_RUN_NOWAIT: uv_mode = UV_RUN_NOWAIT; break;
    default: uv_mode = UV_RUN_DEFAULT; break;
  }
  return uv_run(sys->eventloop, uv_mode);
}

static void loop_stop(valk_aio_system_t *sys) {
  uv_stop(sys->eventloop);
}

static bool loop_alive(valk_aio_system_t *sys) {
  return uv_loop_alive(sys->eventloop) != 0;
}

static void loop_walk(valk_aio_system_t *sys, valk_io_walk_cb cb, void *arg) {
  uv_walk(sys->eventloop, (uv_walk_cb)cb, arg);
}

static u64 loop_now(valk_aio_system_t *sys) {
  return uv_now(sys->eventloop);
}

static u64 sys_hrtime(void) {
  return uv_hrtime();
}

const valk_io_loop_ops_t valk_io_loop_ops_uv = {
  .init = loop_init,
  .destroy = loop_destroy,
  .run = loop_run,
  .stop = loop_stop,
  .alive = loop_alive,
  .walk = loop_walk,
  .now = loop_now,
  .hrtime = sys_hrtime,
};
