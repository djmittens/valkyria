#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <uv.h>
#include "aio_ssl.h"
#include "../memory.h"

typedef struct valk_aio_handle_t valk_aio_handle_t;
typedef struct valk_aio_system valk_aio_system_t;

typedef struct valk_conn_io {
  valk_slab_item_t *read_buf;
  valk_slab_item_t *write_buf;
  size_t write_pos;
  bool write_flush_pending;
  uv_write_t write_req;
  uv_buf_t write_uv_buf;

  valk_aio_ssl_t ssl;
} valk_conn_io_t;

void valk_conn_io_init(valk_conn_io_t *io);

void valk_conn_io_free(valk_conn_io_t *io, valk_slab_t *slab);

bool valk_conn_io_read_buf_acquire(valk_conn_io_t *io, valk_slab_t *slab);
void valk_conn_io_read_buf_release(valk_conn_io_t *io, valk_slab_t *slab);
uint8_t *valk_conn_io_read_buf_data(valk_conn_io_t *io);
size_t valk_conn_io_read_buf_size(void);

bool valk_conn_io_write_buf_acquire(valk_conn_io_t *io, valk_slab_t *slab);
void valk_conn_io_write_buf_release(valk_conn_io_t *io, valk_slab_t *slab);
uint8_t *valk_conn_io_write_buf_data(valk_conn_io_t *io);
size_t valk_conn_io_write_buf_available(valk_conn_io_t *io);
bool valk_conn_io_write_buf_writable(valk_conn_io_t *io, valk_slab_t *slab, size_t min_space);
size_t valk_conn_io_write_buf_append(valk_conn_io_t *io, valk_slab_t *slab, 
                                      const uint8_t *data, size_t len);

typedef void (*valk_conn_io_flush_cb)(valk_aio_handle_t *conn, int status);

int valk_conn_io_flush(valk_conn_io_t *io, uv_stream_t *stream, 
                       valk_conn_io_flush_cb on_complete);

void valk_conn_io_on_flush_complete(valk_conn_io_t *io);
