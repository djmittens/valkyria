#pragma once

#include "io/io_loop_ops.h"
#include "io/io_timer_ops.h"
#include "io/io_tcp_ops.h"

typedef struct valk_aio_ops {
  const valk_io_loop_ops_t *loop;
  const valk_io_timer_ops_t *timer;
  const valk_io_tcp_ops_t *tcp;
} valk_aio_ops_t;

extern const valk_aio_ops_t valk_aio_ops_production;
extern const valk_aio_ops_t valk_aio_ops_test;
