#include "io_timer_ops.h"
#include <stdlib.h>
#include <string.h>

struct valk_io_timer {
  valk_io_timer_cb user_cb;
  void *user_data;
  bool closing;
};

static __thread valk_test_timer_state_t *g_test_state = nullptr;

void valk_test_timer_init_state(valk_test_timer_state_t *state) {
  g_test_state = state;
  state->current_time_ms = 0;
  state->current_hrtime = 0;
  state->pending_head = nullptr;
}

void valk_test_timer_reset_state(void) {
  if (!g_test_state) return;
  
  struct valk_test_pending_timer *pt = g_test_state->pending_head;
  while (pt) {
    struct valk_test_pending_timer *next = pt->next;
    free(pt);
    pt = next;
  }
  g_test_state->pending_head = nullptr;
  g_test_state->current_time_ms = 0;
  g_test_state->current_hrtime = 0;
}

void valk_test_timer_advance(u64 ms) {
  if (!g_test_state) return;
  g_test_state->current_time_ms += ms;
  g_test_state->current_hrtime += ms * 1000000ULL;

  struct valk_test_pending_timer *pt = g_test_state->pending_head;
  while (pt) {
    struct valk_test_pending_timer *next = pt->next;
    if (pt->active && pt->fire_at_ms <= g_test_state->current_time_ms) {
      if (pt->cb && pt->timer) {
        pt->cb(pt->timer);
      }
      if (pt->repeat_ms > 0) {
        pt->fire_at_ms = g_test_state->current_time_ms + pt->repeat_ms;
      } else {
        pt->active = false;
      }
    }
    pt = next;
  }
}

u64 valk_test_timer_pending_count(void) {
  u64 count = 0;
  struct valk_test_pending_timer *pt = g_test_state ? g_test_state->pending_head : nullptr;
  while (pt) {
    if (pt->active) count++;
    pt = pt->next;
  }
  return count;
}

u64 valk_test_timer_current_time(void) {
  return g_test_state ? g_test_state->current_time_ms : 0;
}

static int test_timer_init(valk_aio_system_t *sys, valk_io_timer_t *timer) {
  (void)sys;
  memset(timer, 0, sizeof(*timer));
  timer->user_data = nullptr;
  timer->user_cb = nullptr;
  timer->closing = false;
  return 0;
}

static int test_timer_start(valk_io_timer_t *timer, valk_io_timer_cb cb,
                            u64 timeout_ms, u64 repeat_ms) {
  if (!g_test_state) return -1;

  struct valk_test_pending_timer *pt = g_test_state->pending_head;
  while (pt) {
    if (pt->timer == timer) {
      pt->cb = cb;
      pt->fire_at_ms = g_test_state->current_time_ms + timeout_ms;
      pt->repeat_ms = repeat_ms;
      pt->active = true;
      timer->user_cb = cb;
      return 0;
    }
    pt = pt->next;
  }

  pt = malloc(sizeof(struct valk_test_pending_timer));
  if (!pt) return -1;
  
  pt->timer = timer;
  pt->cb = cb;
  pt->fire_at_ms = g_test_state->current_time_ms + timeout_ms;
  pt->repeat_ms = repeat_ms;
  pt->active = true;
  pt->next = g_test_state->pending_head;
  g_test_state->pending_head = pt;

  timer->user_cb = cb;
  return 0;
}

static int test_timer_stop(valk_io_timer_t *timer) {
  struct valk_test_pending_timer *pt = g_test_state ? g_test_state->pending_head : nullptr;
  while (pt) {
    if (pt->timer == timer) {
      pt->active = false;
      break;
    }
    pt = pt->next;
  }
  return 0;
}

static void test_timer_close(valk_io_timer_t *timer, valk_io_close_cb cb) {
  test_timer_stop(timer);
  timer->closing = true;
  if (cb) cb(timer);
}

static bool test_timer_is_closing(valk_io_timer_t *timer) {
  return timer->closing;
}

static void test_timer_set_data(valk_io_timer_t *timer, void *data) {
  timer->user_data = data;
}

static void *test_timer_get_data(valk_io_timer_t *timer) {
  return timer->user_data;
}

const valk_io_timer_ops_t valk_io_timer_ops_test = {
  .init = test_timer_init,
  .start = test_timer_start,
  .stop = test_timer_stop,
  .close = test_timer_close,
  .is_closing = test_timer_is_closing,
  .set_data = test_timer_set_data,
  .get_data = test_timer_get_data,
};
