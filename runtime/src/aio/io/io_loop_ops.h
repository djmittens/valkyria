#pragma once

#include "types.h"
#include "io_types.h"

typedef struct valk_io_loop_ops {
  void (*destroy)(valk_aio_system_t *sys);
  u64 (*now)(valk_aio_system_t *sys);
} valk_io_loop_ops_t;

extern const valk_io_loop_ops_t valk_io_loop_ops_uv;
extern const valk_io_loop_ops_t valk_io_loop_ops_test;
