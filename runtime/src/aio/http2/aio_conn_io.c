#include "aio_conn_io.h"
#include "aio_internal.h"

void valk_conn_io_init(valk_conn_io_t *io, u64 buf_size) {
  memset(io, 0, sizeof(*io));
  io->buf_size = buf_size;
}

// LCOV_EXCL_BR_START - buffer release null checks
void valk_conn_io_free(valk_conn_io_t *io, valk_slab_t *slab) {
  if (!io) return;
  
  if (io->read_buf && slab) {
    valk_slab_release(slab, io->read_buf);
    io->read_buf = nullptr;
  }
  if (io->write_buf && slab) {
    valk_slab_release(slab, io->write_buf);
    io->write_buf = nullptr;
  }
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - buffer acquire failure: requires slab exhaustion
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
// LCOV_EXCL_BR_STOP

void valk_conn_io_read_buf_release(valk_conn_io_t *io, valk_slab_t *slab) {
  if (!io || !io->read_buf || !slab) return; // LCOV_EXCL_BR_LINE
  valk_slab_release(slab, io->read_buf);
  io->read_buf = nullptr;
}

u8 *valk_conn_io_read_buf_data(valk_conn_io_t *io) {
  if (!io->read_buf) return nullptr;
  __tcp_buffer_slab_item_t *item = (void *)io->read_buf->data;
  return (u8 *)item->data;
}

u64 valk_conn_io_read_buf_size(valk_conn_io_t *io) {
  return io->buf_size;
}

// LCOV_EXCL_BR_START - write buffer acquire failure: requires slab exhaustion
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
// LCOV_EXCL_BR_STOP

u8 *valk_conn_io_write_buf_data(valk_conn_io_t *io) {
  if (!io->write_buf) return nullptr;
  __tcp_buffer_slab_item_t *item = (void *)io->write_buf->data;
  return (u8 *)item->data;
}

u64 valk_conn_io_write_buf_available(valk_conn_io_t *io) {
  if (!io->write_buf) return 0;
  return io->buf_size - io->write_pos;
}

bool valk_conn_io_write_buf_writable(valk_conn_io_t *io, valk_slab_t *slab, u64 min_space) {
  if (io->write_flush_pending) return false;
  if (!io->write_buf && !valk_conn_io_write_buf_acquire(io, slab)) return false; // LCOV_EXCL_BR_LINE
  return valk_conn_io_write_buf_available(io) >= min_space;
}

// LCOV_EXCL_BR_START - write append edge cases
u64 valk_conn_io_write_buf_append(valk_conn_io_t *io, valk_slab_t *slab,
                                      const u8 *data, u64 len) {
  if (io->write_flush_pending) return 0;
  if (!io->write_buf && !valk_conn_io_write_buf_acquire(io, slab)) return 0;
  
  u64 available = valk_conn_io_write_buf_available(io);
  u64 to_write = len < available ? len : available;
  
  if (to_write > 0) {
    u8 *buf = valk_conn_io_write_buf_data(io);
    memcpy(buf + io->write_pos, data, to_write);
    io->write_pos += to_write;
  }
  
  return to_write;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - flush callback state transitions
static void __conn_io_flush_cb(valk_io_write_req_t *req, int status) {
  valk_conn_io_t *io = req->user_data;
  
  if (status != 0) {
    VALK_DEBUG("Write flush failed: %d (client likely disconnected)", status);
  }
  
  u64 bytes_sent = io->write_buf_desc.len;
  u64 bytes_remaining = io->write_pos > bytes_sent ? io->write_pos - bytes_sent : 0;
  
  if (bytes_remaining > 0) {
    u8 *buf = valk_conn_io_write_buf_data(io);
    memmove(buf, buf + bytes_sent, bytes_remaining);
    VALK_DEBUG("Write flush complete, preserved %llu bytes added during write", 
               (unsigned long long)bytes_remaining);
  }
  
  io->write_flush_pending = false;
  io->write_pos = bytes_remaining;
  
  VALK_TRACE("Write flush complete, %llu bytes remaining", (unsigned long long)bytes_remaining);
  
  if (io->flush_cb) {
    io->flush_cb(io->flush_ctx, status);
  }
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - flush guard conditions and write failure paths
int valk_conn_io_flush(valk_conn_io_t *io, valk_aio_handle_t *conn,
                       valk_conn_io_flush_cb cb, void *ctx) {
  if (!io->write_buf || io->write_pos == 0) {
    return 0;
  }
  
  if (io->write_flush_pending) {
    return 1;
  }
  
  valk_aio_system_t *sys = conn->sys;
  if (!sys || !sys->ops || !sys->ops->tcp) {
    return -1;
  }
  
  if (sys->ops->tcp->is_closing(&conn->uv.tcp)) {
    return -1;
  }
  
  _Static_assert(sizeof(io->write_req_storage) >= sizeof(valk_io_write_req_t),
                 "write_req_storage too small for valk_io_write_req_t");
  
  io->write_flush_pending = true;
  io->write_buf_desc.base = (char *)valk_conn_io_write_buf_data(io);
  io->write_buf_desc.len = io->write_pos;
  valk_io_write_req_t *req = (valk_io_write_req_t *)io->write_req_storage;
  req->user_data = io;
  io->flush_cb = cb;
  io->flush_ctx = ctx;
  
  VALK_TRACE("Flushing write buffer: %zu bytes", io->write_pos);
  
  int rv = sys->ops->tcp->write_bufs(&conn->uv.tcp, req, &io->write_buf_desc, 1, __conn_io_flush_cb);
  if (rv != 0) {
    VALK_ERROR("write_bufs failed: %d", rv);
    io->write_flush_pending = false;
    return -1;
  }
  
  return 0;
}
// LCOV_EXCL_BR_STOP
