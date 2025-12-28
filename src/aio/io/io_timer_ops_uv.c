#include "io_timer_ops.h"
#include "aio/aio_internal.h"

struct valk_io_timer {
  uv_timer_t uv;
  valk_io_timer_cb user_cb;
  void *user_data;
};

static void __timer_cb_adapter(uv_timer_t *uv_timer) {
  valk_io_timer_t *timer = (valk_io_timer_t *)uv_timer;
  if (timer->user_cb) timer->user_cb(timer);
}

static int timer_init(valk_aio_system_t *sys, valk_io_timer_t *timer) {
  memset(timer, 0, sizeof(*timer));
  return uv_timer_init(sys->eventloop, &timer->uv);
}

static int timer_start(valk_io_timer_t *timer, valk_io_timer_cb cb,
                       u64 timeout_ms, u64 repeat_ms) {
  timer->user_cb = cb;
  return uv_timer_start(&timer->uv, __timer_cb_adapter, timeout_ms, repeat_ms);
}

static int timer_stop(valk_io_timer_t *timer) {
  return uv_timer_stop(&timer->uv);
}

static void timer_close(valk_io_timer_t *timer, valk_io_close_cb cb) {
  uv_close((uv_handle_t *)&timer->uv, (uv_close_cb)cb);
}

static bool timer_is_closing(valk_io_timer_t *timer) {
  return uv_is_closing((uv_handle_t *)&timer->uv);
}

static void timer_set_data(valk_io_timer_t *timer, void *data) {
  timer->user_data = data;
}

static void *timer_get_data(valk_io_timer_t *timer) {
  return timer->user_data;
}

const valk_io_timer_ops_t valk_io_timer_ops_uv = {
  .init = timer_init,
  .start = timer_start,
  .stop = timer_stop,
  .close = timer_close,
  .is_closing = timer_is_closing,
  .set_data = timer_set_data,
  .get_data = timer_get_data,
  .timer_size = sizeof(valk_io_timer_t),
};
