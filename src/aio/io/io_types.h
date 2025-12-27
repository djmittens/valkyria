#pragma once

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct valk_io_timer valk_io_timer_t;
typedef struct valk_io_tcp valk_io_tcp_t;
typedef struct valk_aio_system valk_aio_system_t;

typedef void (*valk_io_timer_cb)(valk_io_timer_t *timer);
typedef void (*valk_io_close_cb)(void *handle);

typedef enum {
  VALK_IO_RUN_DEFAULT = 0,
  VALK_IO_RUN_ONCE = 1,
  VALK_IO_RUN_NOWAIT = 2,
} valk_io_run_mode_e;

typedef struct valk_io_buf {
  char *base;
  size_t len;
} valk_io_buf_t;

typedef struct valk_io_write_req valk_io_write_req_t;
