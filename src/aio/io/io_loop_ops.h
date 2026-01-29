#pragma once

#include "types.h"
#include "io_types.h"

typedef void (*valk_io_walk_cb)(void *handle, void *arg);

typedef struct valk_io_loop_ops {
  int (*init)(valk_aio_system_t *sys);
  void (*destroy)(valk_aio_system_t *sys);

  int (*run)(valk_aio_system_t *sys, valk_io_run_mode_e mode);
  void (*stop)(valk_aio_system_t *sys);
  bool (*alive)(valk_aio_system_t *sys);

  void (*walk)(valk_aio_system_t *sys, valk_io_walk_cb cb, void *arg);

  u64 (*now)(valk_aio_system_t *sys);
  u64 (*hrtime)(void);
} valk_io_loop_ops_t;

extern const valk_io_loop_ops_t valk_io_loop_ops_uv;
extern const valk_io_loop_ops_t valk_io_loop_ops_test;
