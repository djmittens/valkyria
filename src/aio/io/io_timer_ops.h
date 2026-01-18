#pragma once

#include "types.h"
#include "io_types.h"

typedef struct valk_io_timer_ops {
  int (*init)(valk_aio_system_t *sys, valk_io_timer_t *timer);
  int (*start)(valk_io_timer_t *timer, valk_io_timer_cb cb,
               u64 timeout_ms, u64 repeat_ms);
  int (*stop)(valk_io_timer_t *timer);
  void (*close)(valk_io_timer_t *timer, valk_io_close_cb cb);

  bool (*is_closing)(valk_io_timer_t *timer);
  void (*set_data)(valk_io_timer_t *timer, void *data);
  void *(*get_data)(valk_io_timer_t *timer);
} valk_io_timer_ops_t;

extern const valk_io_timer_ops_t valk_io_timer_ops_uv;
extern const valk_io_timer_ops_t valk_io_timer_ops_test;

typedef struct valk_test_timer_state {
  u64 current_time_ms;
  u64 current_hrtime;

  struct valk_test_pending_timer {
    valk_io_timer_t *timer;
    valk_io_timer_cb cb;
    u64 fire_at_ms;
    u64 repeat_ms;
    bool active;
    struct valk_test_pending_timer *next;
  } *pending_head;
} valk_test_timer_state_t;

void valk_test_timer_init_state(valk_test_timer_state_t *state);
void valk_test_timer_reset_state(void);
void valk_test_timer_advance(u64 ms);
u64 valk_test_timer_pending_count(void);
u64 valk_test_timer_current_time(void);
