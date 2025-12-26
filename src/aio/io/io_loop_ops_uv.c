#include "io_loop_ops.h"
#include <uv.h>
#include <stdlib.h>

struct valk_io_loop {
  uv_loop_t *uv;
  bool owns_loop;
};

static valk_io_loop_t *loop_create(void) {
  valk_io_loop_t *loop = malloc(sizeof(valk_io_loop_t));
  if (!loop) return nullptr;
  
  loop->uv = malloc(sizeof(uv_loop_t));
  if (!loop->uv) {
    free(loop);
    return nullptr;
  }
  
  if (uv_loop_init(loop->uv) != 0) {
    free(loop->uv);
    free(loop);
    return nullptr;
  }
  
  loop->owns_loop = true;
  return loop;
}

static void loop_destroy(valk_io_loop_t *loop) {
  if (!loop) return;
  if (loop->owns_loop && loop->uv) {
    uv_loop_close(loop->uv);
    free(loop->uv);
  }
  free(loop);
}

static int loop_run(valk_io_loop_t *loop, valk_io_run_mode_e mode) {
  uv_run_mode uv_mode;
  switch (mode) {
    case VALK_IO_RUN_ONCE: uv_mode = UV_RUN_ONCE; break;
    case VALK_IO_RUN_NOWAIT: uv_mode = UV_RUN_NOWAIT; break;
    default: uv_mode = UV_RUN_DEFAULT; break;
  }
  return uv_run(loop->uv, uv_mode);
}

static void loop_stop(valk_io_loop_t *loop) {
  uv_stop(loop->uv);
}

static bool loop_alive(valk_io_loop_t *loop) {
  return uv_loop_alive(loop->uv) != 0;
}

static void loop_walk(valk_io_loop_t *loop, valk_io_walk_cb cb, void *arg) {
  uv_walk(loop->uv, (uv_walk_cb)cb, arg);
}

const valk_io_loop_ops_t valk_io_loop_ops_uv = {
  .create = loop_create,
  .destroy = loop_destroy,
  .run = loop_run,
  .stop = loop_stop,
  .alive = loop_alive,
  .walk = loop_walk,
  .timer = &valk_io_timer_ops_uv,
  .loop_size = sizeof(valk_io_loop_t),
};

valk_io_loop_t *valk_io_loop_wrap_uv(void *uv_loop) {
  valk_io_loop_t *loop = malloc(sizeof(valk_io_loop_t));
  if (!loop) return nullptr;
  loop->uv = (uv_loop_t *)uv_loop;
  loop->owns_loop = false;
  return loop;
}

void *valk_io_loop_unwrap_uv(valk_io_loop_t *loop) {
  return loop ? loop->uv : nullptr;
}
