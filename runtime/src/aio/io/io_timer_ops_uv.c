#include "io_timer_ops.h"
#include "aio/aio_internal.h"

struct valk_io_timer {
  uv_timer_t uv;
  // _Atomic: unit tests start timers from off-loop threads, so the loop's
  // callback read races the starter's store (TSAN-caught on arm64).
  _Atomic(valk_io_timer_cb) user_cb;
  void *user_data;
};

// LCOV_EXCL_START - libuv internal callback, only invoked from event loop thread
static void __timer_cb_adapter(uv_timer_t *uv_timer) {
  valk_io_timer_t *timer = (valk_io_timer_t *)uv_timer;
  valk_io_timer_cb cb =
      atomic_load_explicit(&timer->user_cb, memory_order_acquire);
  if (cb) cb(timer);
}
// LCOV_EXCL_STOP

static int timer_init(valk_aio_system_t *sys, valk_io_timer_t *timer) {
  memset(timer, 0, sizeof(*timer));
  return uv_timer_init(sys->eventloop, &timer->uv);
}

static int timer_start(valk_io_timer_t *timer, valk_io_timer_cb cb,
                       u64 timeout_ms, u64 repeat_ms) {
  atomic_store_explicit(&timer->user_cb, cb, memory_order_release);
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
};
