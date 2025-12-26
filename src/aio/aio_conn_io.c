#include "aio_conn_io.h"
#include "aio_internal.h"

void valk_conn_io_init(valk_conn_io_t *io, size_t buf_size) {
  memset(io, 0, sizeof(*io));
  io->buf_size = buf_size;
}

void valk_conn_io_free(valk_conn_io_t *io, valk_slab_t *slab) {
  if (!io) return;
  
  if (io->read_buf && slab) {
    valk_slab_release(slab, io->read_buf);
    io->read_buf = NULL;
  }
  if (io->write_buf && slab) {
    valk_slab_release(slab, io->write_buf);
    io->write_buf = NULL;
  }
}

bool valk_conn_io_read_buf_acquire(valk_conn_io_t *io, valk_slab_t *slab) {
  if (io->read_buf) return true;
  if (!slab) return false;
  
  valk_slab_item_t *item = valk_slab_aquire(slab);
  if (!item) {
    VALK_WARN("Failed to acquire read buffer from slab");
    return false;
  }
  
  io->read_buf = item;
  return true;
}

uint8_t *valk_conn_io_read_buf_data(valk_conn_io_t *io) {
  if (!io->read_buf) return NULL;
  __tcp_buffer_slab_item_t *item = (void *)io->read_buf->data;
  return (uint8_t *)item->data;
}

size_t valk_conn_io_read_buf_size(valk_conn_io_t *io) {
  return io->buf_size;
}

bool valk_conn_io_write_buf_acquire(valk_conn_io_t *io, valk_slab_t *slab) {
  if (io->write_buf) return true;
  if (!slab) return false;
  
  valk_slab_item_t *item = valk_slab_aquire(slab);
  if (!item) {
    VALK_WARN("Failed to acquire write buffer from slab");
    return false;
  }
  
  io->write_buf = item;
  io->write_pos = 0;
  io->write_flush_pending = false;
  return true;
}

uint8_t *valk_conn_io_write_buf_data(valk_conn_io_t *io) {
  if (!io->write_buf) return NULL;
  __tcp_buffer_slab_item_t *item = (void *)io->write_buf->data;
  return (uint8_t *)item->data;
}

size_t valk_conn_io_write_buf_available(valk_conn_io_t *io) {
  if (!io->write_buf) return 0;
  return io->buf_size - io->write_pos;
}

bool valk_conn_io_write_buf_writable(valk_conn_io_t *io, valk_slab_t *slab, size_t min_space) {
  if (io->write_flush_pending) return false;
  if (!io->write_buf && !valk_conn_io_write_buf_acquire(io, slab)) return false;
  return valk_conn_io_write_buf_available(io) >= min_space;
}

size_t valk_conn_io_write_buf_append(valk_conn_io_t *io, valk_slab_t *slab,
                                      const uint8_t *data, size_t len) {
  if (io->write_flush_pending) return 0;
  if (!io->write_buf && !valk_conn_io_write_buf_acquire(io, slab)) return 0;
  
  size_t available = valk_conn_io_write_buf_available(io);
  size_t to_write = len < available ? len : available;
  
  if (to_write > 0) {
    uint8_t *buf = valk_conn_io_write_buf_data(io);
    memcpy(buf + io->write_pos, data, to_write);
    io->write_pos += to_write;
  }
  
  return to_write;
}

static void __conn_io_flush_cb(uv_write_t *req, int status) {
  valk_conn_io_t *io = req->data;
  
  if (status != 0) {
    VALK_ERROR("Write flush failed: %s", uv_strerror(status));
  }
  
  io->write_flush_pending = false;
  io->write_pos = 0;
  
  VALK_TRACE("Write flush complete, buffer reset");
  
  if (io->flush_cb) {
    io->flush_cb(io->flush_ctx, status);
  }
}

int valk_conn_io_flush(valk_conn_io_t *io, uv_stream_t *stream,
                       valk_conn_io_flush_cb cb, void *ctx) {
  if (!io->write_buf || io->write_pos == 0) {
    return 0;
  }
  
  if (io->write_flush_pending) {
    return 1;
  }
  
  if (uv_is_closing((uv_handle_t *)stream)) {
    return -1;
  }
  
  io->write_flush_pending = true;
  io->write_uv_buf.base = (char *)valk_conn_io_write_buf_data(io);
  io->write_uv_buf.len = io->write_pos;
  io->write_req.data = io;
  io->flush_cb = cb;
  io->flush_ctx = ctx;
  
  VALK_TRACE("Flushing write buffer: %zu bytes", io->write_pos);
  
  int rv = uv_write(&io->write_req, stream, &io->write_uv_buf, 1, __conn_io_flush_cb);
  if (rv != 0) {
    VALK_ERROR("uv_write failed: %s", uv_strerror(rv));
    io->write_flush_pending = false;
    return -1;
  }
  
  return 0;
}
