#pragma once

#include "io_types.h"
#include "io_timer_ops.h"

typedef void (*valk_io_walk_cb)(void *handle, void *arg);

typedef struct valk_io_loop_ops {
  valk_io_loop_t *(*create)(void);
  void (*destroy)(valk_io_loop_t *loop);

  int (*run)(valk_io_loop_t *loop, valk_io_run_mode_e mode);
  void (*stop)(valk_io_loop_t *loop);
  bool (*alive)(valk_io_loop_t *loop);

  void (*walk)(valk_io_loop_t *loop, valk_io_walk_cb cb, void *arg);

  const valk_io_timer_ops_t *timer;
  
  size_t loop_size;
} valk_io_loop_ops_t;

extern const valk_io_loop_ops_t valk_io_loop_ops_uv;
extern const valk_io_loop_ops_t valk_io_loop_ops_test;

valk_io_loop_t *valk_io_loop_wrap_uv(void *uv_loop);
void *valk_io_loop_unwrap_uv(valk_io_loop_t *loop);
