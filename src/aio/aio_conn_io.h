#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include "io/io_types.h"
#include "aio_ssl.h"
#include "../memory.h"

typedef struct valk_aio_handle_t valk_aio_handle_t;
typedef struct valk_aio_system valk_aio_system_t;

typedef void (*valk_conn_io_flush_cb)(void *ctx, int status);

#define VALK_IO_WRITE_REQ_MAX_SIZE 256

typedef struct valk_conn_io {
  valk_slab_item_t *read_buf;
  valk_slab_item_t *write_buf;
  size_t write_pos;
  size_t buf_size;
  bool write_flush_pending;
  _Alignas(16) char write_req_storage[VALK_IO_WRITE_REQ_MAX_SIZE];
  valk_io_buf_t write_buf_desc;
  valk_conn_io_flush_cb flush_cb;
  void *flush_ctx;

  valk_aio_ssl_t ssl;
} valk_conn_io_t;

void valk_conn_io_init(valk_conn_io_t *io, size_t buf_size);

void valk_conn_io_free(valk_conn_io_t *io, valk_slab_t *slab);

bool valk_conn_io_read_buf_acquire(valk_conn_io_t *io, valk_slab_t *slab);
uint8_t *valk_conn_io_read_buf_data(valk_conn_io_t *io);
size_t valk_conn_io_read_buf_size(valk_conn_io_t *io);

bool valk_conn_io_write_buf_acquire(valk_conn_io_t *io, valk_slab_t *slab);
uint8_t *valk_conn_io_write_buf_data(valk_conn_io_t *io);
size_t valk_conn_io_write_buf_available(valk_conn_io_t *io);
bool valk_conn_io_write_buf_writable(valk_conn_io_t *io, valk_slab_t *slab, size_t min_space);
size_t valk_conn_io_write_buf_append(valk_conn_io_t *io, valk_slab_t *slab, 
                                      const uint8_t *data, size_t len);

int valk_conn_io_flush(valk_conn_io_t *io, valk_aio_handle_t *conn,
                       valk_conn_io_flush_cb cb, void *ctx);

void valk_conn_io_read_buf_release(valk_conn_io_t *io, valk_slab_t *slab);
