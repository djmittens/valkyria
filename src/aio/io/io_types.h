#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct valk_io_timer valk_io_timer_t;
typedef struct valk_io_loop valk_io_loop_t;
typedef struct valk_io_tcp valk_io_tcp_t;

typedef void (*valk_io_timer_cb)(valk_io_timer_t *timer);
typedef void (*valk_io_close_cb)(void *handle);

typedef enum {
  VALK_IO_RUN_DEFAULT = 0,
  VALK_IO_RUN_ONCE = 1,
  VALK_IO_RUN_NOWAIT = 2,
} valk_io_run_mode_e;
