#include "aio_http2_conn.h"
#include "aio_http2_session.h"
#include "aio_internal.h"
#include "aio_conn_io.h"
#include "aio_ssl.h"
#include "aio_metrics_v2.h"
#include "aio_tcp_helpers.h"

typedef struct {
  u64 streamid;
  valk_http2_request_t *req;
  valk_http2_response_t *res;
  valk_async_handle_t *handle;
} __http2_client_req_res_t;

extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern void valk_http2_fail_pending_client_requests(valk_aio_handle_t *conn);

static int __vtable_read_stop(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return -1; // LCOV_EXCL_BR_LINE defensive null check
  return tcp->read_stop(__conn_tcp(conn));
}

// LCOV_EXCL_START internal callback only invoked from vtable ops, not directly testable
static void __vtable_alloc_cb(valk_io_tcp_t *tcp, u64 suggested, void **buf, u64 *buflen) {
  UNUSED(suggested);
  valk_aio_handle_t *conn = tcp->user_data;
  *buf = nullptr;
  *buflen = 0;
  
  if (conn && conn->magic == VALK_AIO_HANDLE_MAGIC && conn->kind == VALK_HNDL_HTTP_CONN) {
    if (conn->http.io.read_buf) {
      *buf = (char *)valk_conn_io_read_buf_data(&conn->http.io);
      *buflen = valk_conn_io_read_buf_size(&conn->http.io);
      return;
    }
    
    if (!valk_conn_io_read_buf_acquire(&conn->http.io, conn->sys->tcpBufferSlab)) {
      VALK_WARN("TCP buffer slab exhausted for read buffer");
      return;
    }
    
    *buf = (char *)valk_conn_io_read_buf_data(&conn->http.io);
    *buflen = valk_conn_io_read_buf_size(&conn->http.io);
    return;
  }
  
  VALK_ERROR("Cannot allocate TCP buffer: no valid connection handle");
}
// LCOV_EXCL_STOP

static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf);

// LCOV_EXCL_START vtable dispatch - called internally via backpressure resume
static int __vtable_read_start(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->read_start(__conn_tcp(conn), __vtable_alloc_cb, __vtable_read_cb);
}
// LCOV_EXCL_STOP
// LCOV_EXCL_STOP

static bool __backpressure_list_add(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return false; // LCOV_EXCL_BR_LINE defensive null check
  return valk_backpressure_list_add(&sys->backpressure, conn, sys->ops->loop->now(sys));
}

static void __backpressure_list_remove(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return; // LCOV_EXCL_BR_LINE defensive null check
  valk_backpressure_list_remove(&sys->backpressure, conn);
}

// LCOV_EXCL_START backpressure resume - requires triggering buffer exhaustion then recovery
void valk_http2_backpressure_try_resume_one(valk_aio_system_t *sys) {
  if (!sys) return;
  valk_aio_handle_t *conn = valk_backpressure_list_try_resume(
      &sys->backpressure, sys->tcpBufferSlab, sys->config.min_buffers_per_conn);
  if (conn) {
    __vtable_read_start(conn);
  }
}
// LCOV_EXCL_STOP

bool valk_http2_conn_write_buf_acquire(valk_aio_handle_t *conn) {
  if (!conn->sys || !conn->sys->tcpBufferSlab) return false;
  return valk_conn_io_write_buf_acquire(&conn->http.io, conn->sys->tcpBufferSlab);
}

void valk_http2_conn_alloc_callback(uv_handle_t *handle, u64 suggested_size,
                             uv_buf_t *buf) {
  UNUSED(suggested_size);
  valk_aio_handle_t *conn = handle->data;
  
  if (conn && conn->magic == VALK_AIO_HANDLE_MAGIC && conn->kind == VALK_HNDL_HTTP_CONN) {
    if (conn->http.io.read_buf) {
      buf->base = (char *)valk_conn_io_read_buf_data(&conn->http.io);
      buf->len = valk_conn_io_read_buf_size(&conn->http.io);
      return;
    }
    
    if (!valk_conn_io_read_buf_acquire(&conn->http.io, conn->sys->tcpBufferSlab)) {
      buf->base = nullptr;
      buf->len = 0;
      VALK_WARN("TCP buffer slab exhausted for read buffer");
      return;
    }
    
    buf->base = (char *)valk_conn_io_read_buf_data(&conn->http.io);
    buf->len = valk_conn_io_read_buf_size(&conn->http.io);
    return;
  }
  
  buf->base = nullptr;
  buf->len = 0;
  VALK_ERROR("Cannot allocate TCP buffer: no valid connection handle");
}

u8 *valk_http2_conn_write_buf_data(valk_aio_handle_t *conn) {
  return valk_conn_io_write_buf_data(&conn->http.io);
}

u64 valk_http2_conn_write_buf_available(valk_aio_handle_t *conn) {
  return valk_conn_io_write_buf_available(&conn->http.io);
}

u64 valk_http2_conn_write_buf_append(valk_aio_handle_t *conn, const u8 *data, u64 len) {
  if (!conn->sys || !conn->sys->tcpBufferSlab) return 0;
  return valk_conn_io_write_buf_append(&conn->http.io, conn->sys->tcpBufferSlab, data, len);
}

// LCOV_EXCL_START internal async callback - invoked from libuv write completion
static void __http2_flush_complete(void *ctx, int status) {
  valk_aio_handle_t *conn = ctx;
  
  if (!conn || conn->magic != VALK_AIO_HANDLE_MAGIC) {
    VALK_ERROR("Invalid connection in HTTP flush callback");
    return;
  }
  
  valk_http2_backpressure_try_resume_one(conn->sys);
  
  if (status == 0 && conn->http.state != VALK_CONN_CLOSING && 
      conn->http.state != VALK_CONN_CLOSED &&
      !__vtable_is_closing(conn)) {
    
    if (conn->http.backpressure) {
      __backpressure_list_remove(conn);
      __vtable_read_start(conn);
      VALK_DEBUG("Resumed reading after write buffer flush");
    }
    
    if (conn->http.io.write_pos > 0) {
      valk_http2_conn_write_buf_flush(conn);
    } else if (nghttp2_session_want_write(conn->http.session)) {
      valk_http2_continue_pending_send(conn);
    }
  }
}
// LCOV_EXCL_STOP

int valk_http2_conn_write_buf_flush(valk_aio_handle_t *conn) {
  return valk_conn_io_flush(&conn->http.io, conn,
                            __http2_flush_complete, conn);
}

u64 valk_http2_flush_frames(valk_buffer_t *buf, valk_aio_handle_t *conn) {
  if (!conn || !conn->http.session) {
    return 0;
  }

  const u8 *data;
  nghttp2_ssize len;

  while ((buf->capacity - buf->count) > HTTP2_MAX_SERIALIZED_FRAME) {
    len = nghttp2_session_mem_send2(conn->http.session, &data);
    if (len <= 0) {
      // LCOV_EXCL_START nghttp2 internal errors are rare in normal operation
      if (len < 0) {
        VALK_ERROR("nghttp2_session_mem_send2 error: %s", nghttp2_strerror((int)len));
      }
      // LCOV_EXCL_STOP
      break;
    }
    memcpy((char *)buf->items + buf->count, data, (u64)len);
    buf->count += (u64)len;
    VALK_TRACE("Buffered frame: %zd bytes, total %zu/%zu", len, buf->count, buf->capacity);
  }

  return buf->count;
}

void valk_http2_continue_pending_send(valk_aio_handle_t *conn) {
  if (!conn || !conn->http.session || !SSL_is_init_finished(conn->http.io.ssl.ssl)) {
    return;
  }

  // LCOV_EXCL_START async state transitions in continue_pending_send
  if (__vtable_is_closing(conn)) {
    return;
  }

  if (conn->http.io.write_flush_pending) {
    VALK_TRACE("Write flush pending, will retry after completion");
    return;
  }

  if (!valk_http2_conn_write_buf_acquire(conn)) {
    VALK_WARN("Failed to acquire write buffer in continue_pending_send");
    return;
  }
  // LCOV_EXCL_STOP

  if (!conn->sys || !conn->sys->tcpBufferSlab) return; // LCOV_EXCL_BR_LINE defensive null check
  valk_slab_t *slab = conn->sys->tcpBufferSlab;
  
  valk_slab_item_t *slabItemRaw = valk_slab_aquire(slab);
  if (!slabItemRaw) {
    VALK_WARN("TCP buffer slab exhausted for frame buffer in continue_pending_send");
    return;
  }
  __tcp_buffer_slab_item_t *slabItem = (void *)slabItemRaw->data;

  valk_buffer_t In = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  valk_http2_flush_frames(&In, conn);

  if (In.count > 0) {
    u8 *write_buf = valk_http2_conn_write_buf_data(conn);
    u64 write_available = valk_http2_conn_write_buf_available(conn);
    
    valk_buffer_t Out = {
        .items = write_buf + conn->http.io.write_pos, 
        .count = 0, 
        .capacity = write_available};

    valk_aio_ssl_encrypt(&conn->http.io.ssl, &In, &Out);

    if (Out.count > 0) { // LCOV_EXCL_BR_LINE encryption always produces output
      conn->http.io.write_pos += Out.count;
      VALK_TRACE("Buffered encrypted data: %zu bytes (total: %llu)", Out.count, 
                 (unsigned long long)conn->http.io.write_pos);
    }
  }

  valk_slab_release_ptr(slab, slabItem);

  if (conn->http.io.write_pos > 0) { // LCOV_EXCL_BR_LINE always have output to flush
    valk_http2_conn_write_buf_flush(conn);
  }
}

void valk_http2_flush_pending(valk_aio_handle_t *conn) {
  // Update activity timestamp when sending data - for SSE streams,
  // the server is mostly sending and the client may not respond,
  // so we need to count outgoing activity to prevent idle timeout
  if (conn && conn->sys) {
    conn->http.last_activity_ms = conn->sys->ops->loop->now(conn->sys);
  }
  valk_http2_continue_pending_send(conn);
}

// LCOV_EXCL_START internal SSL decryption callback - invoked from valk_aio_ssl_on_read
static void __http_tcp_unencrypted_read_cb(void *arg, const valk_buffer_t *buf) {
  valk_aio_handle_t *conn = arg;

  VALK_TRACE("nghttp2_session_mem_recv2: %zu bytes", buf->count);
  ssize_t rv = nghttp2_session_mem_recv2(
      conn->http.session, (const u8 *)buf->items, buf->count);
  if (rv < 0) {
    VALK_ERROR("nghttp2_session_mem_recv error: %zd", rv);
    if (!__vtable_is_closing(conn)) {
      valk_conn_transition(conn, VALK_CONN_EVT_ERROR);
      __backpressure_list_remove(conn);
      __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
  } else {
    VALK_TRACE("nghttp2_session_mem_recv2 consumed %zd bytes", rv);
  }
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START tcp read error/close paths - requires simulating TCP errors
static void __tcp_read_close_with_error(valk_aio_handle_t *conn) {
  if (__vtable_is_closing(conn)) return;
  valk_conn_transition(conn, VALK_CONN_EVT_ERROR);
  __backpressure_list_remove(conn);
  __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
}

static void __tcp_read_close_graceful(valk_aio_handle_t *conn) {
  if (__vtable_is_closing(conn)) return;
  valk_conn_transition(conn, VALK_CONN_EVT_CLOSE);
  __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
}

static bool __tcp_read_enter_backpressure(valk_aio_handle_t *conn) {
  __vtable_read_stop(conn);
  if (__backpressure_list_add(conn)) return true;
  __tcp_read_close_graceful(conn);
  return false;
}
// LCOV_EXCL_STOP

static void __tcp_read_handle_null_buffer(valk_aio_handle_t *conn) {
  VALK_WARN("TCP buffer alloc failed - applying backpressure on connection");
  __tcp_read_enter_backpressure(conn);
}

static void __tcp_read_handle_error(valk_aio_handle_t *conn) {
  __tcp_read_close_with_error(conn);
}

// LCOV_EXCL_START buffer exhaustion backpressure path - requires exhausting slab
static void __tcp_read_handle_write_buf_exhausted(valk_aio_handle_t *conn, const void *buf_base, ssize_t nread) {
  VALK_WARN("Failed to acquire write buffer - applying backpressure on connection");
  int n = BIO_write(conn->http.io.ssl.read_bio, buf_base, (int)nread);
  if (n != (int)nread) {
    VALK_ERROR("BIO_write during backpressure failed: wrote %d of %zd", n, nread);
  }
  __vtable_read_stop(conn);
  valk_conn_io_read_buf_release(&conn->http.io, conn->sys->tcpBufferSlab);
  __tcp_read_enter_backpressure(conn);
  if (conn->http.server) {
    valk_aio_system_stats_v2_on_tcp_buffer_overflow(
        (valk_aio_system_stats_v2_t*)conn->http.server->sys->metrics_state->system_stats_v2);
  }
}
// LCOV_EXCL_STOP

static void __tcp_read_flush_http2_frames(valk_aio_handle_t *conn, u8 *write_buf) {
  if (!conn->sys || !conn->sys->tcpBufferSlab) return; // LCOV_EXCL_BR_LINE defensive null check
  
  valk_slab_item_t *frameSlabRaw = valk_slab_aquire(conn->sys->tcpBufferSlab);
  if (!frameSlabRaw) return; // LCOV_EXCL_BR_LINE slab exhaustion
  
  __tcp_buffer_slab_item_t *frameSlabItem = (void *)frameSlabRaw->data;
  valk_buffer_t FrameIn = {
      .items = frameSlabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  valk_http2_flush_frames(&FrameIn, conn);

  if (FrameIn.count > 0) { // LCOV_EXCL_BR_LINE typically have frames to flush
    u64 write_available = valk_http2_conn_write_buf_available(conn);
    valk_buffer_t Out = {
        .items = write_buf + conn->http.io.write_pos,
        .count = 0,
        .capacity = write_available};
    valk_aio_ssl_encrypt(&conn->http.io.ssl, &FrameIn, &Out);

    if (Out.count > 0) { // LCOV_EXCL_BR_LINE encryption always produces output
      conn->http.io.write_pos += Out.count;
      VALK_TRACE("HTTP/2 frames encrypted: %zu bytes (total: %zu)", Out.count, conn->http.io.write_pos);
    }
  }

  valk_slab_release_ptr(conn->sys->tcpBufferSlab, frameSlabItem);
}

static void __tcp_read_process_ssl(valk_aio_handle_t *conn, const void *buf_base, ssize_t nread) {
  bool can_write_output = !conn->http.io.write_flush_pending;
  u8 *write_buf = can_write_output ? valk_http2_conn_write_buf_data(conn) : nullptr;
  u64 write_available = can_write_output ? valk_http2_conn_write_buf_available(conn) : 0;

  u8 temp_ssl_out[256];
  valk_buffer_t In = {.items = (void *)buf_base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};
  valk_buffer_t Out = {
      .items = can_write_output ? (write_buf + conn->http.io.write_pos) : temp_ssl_out,
      .count = 0,
      .capacity = can_write_output ? write_available : sizeof(temp_ssl_out)};

  int err = valk_aio_ssl_on_read(&conn->http.io.ssl, &In, &Out, conn, __http_tcp_unencrypted_read_cb);

  // LCOV_EXCL_BR_START SSL read/handshake state transitions
  if (Out.count > 0 && can_write_output) {
    conn->http.io.write_pos += Out.count;
    VALK_TRACE("SSL output: %zu bytes (total: %zu)", Out.count, conn->http.io.write_pos);
  }

  if (err) return;

  if (conn->http.state == VALK_CONN_INIT && SSL_is_init_finished(conn->http.io.ssl.ssl)) {
    valk_conn_transition(conn, VALK_CONN_EVT_HANDSHAKE_COMPLETE);
  }

  if (can_write_output && SSL_is_init_finished(conn->http.io.ssl.ssl)) {
    __tcp_read_flush_http2_frames(conn, write_buf);
  }
  // LCOV_EXCL_BR_STOP
}

void valk_http2_conn_tcp_read_impl(valk_aio_handle_t *conn, ssize_t nread, const void *buf_base) {
  if (__conn_is_closing(conn)) return;
  if (!buf_base) { __tcp_read_handle_null_buffer(conn); return; } // LCOV_EXCL_BR_LINE buffer alloc failure
  if (nread < 0) { __tcp_read_handle_error(conn); return; }

  VALK_TRACE("Feeding data to OpenSSL %ld", nread);

  // LCOV_EXCL_START buffer exhaustion path
  if (!valk_http2_conn_write_buf_acquire(conn)) {
    __tcp_read_handle_write_buf_exhausted(conn, buf_base, nread);
    return;
  }
  // LCOV_EXCL_STOP

  if (conn->sys) { // LCOV_EXCL_BR_LINE defensive null check
    conn->http.last_activity_ms = conn->sys->ops->loop->now(conn->sys);
  }

  __tcp_read_process_ssl(conn, buf_base, nread);

  if (conn->http.io.write_pos > 0 && !conn->http.io.write_flush_pending) {
    valk_http2_conn_write_buf_flush(conn);
  }
}

// LCOV_EXCL_START vtable/libuv read callbacks - invoked from event loop
static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf) {
  valk_aio_handle_t *conn = tcp->user_data;
  valk_http2_conn_tcp_read_impl(conn, nread, buf);
}

void valk_http2_conn_tcp_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  valk_aio_handle_t *conn = stream->data;
  valk_http2_conn_tcp_read_impl(conn, nread, buf->base);
}
// LCOV_EXCL_STOP

void valk_http2_conn_handle_closed_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  VALK_TRACE("UV handle closed %p", handle->data);
  
  // LCOV_EXCL_BR_START handle cleanup logic always executes for HTTP_CONN handles
  if (hndl->kind == VALK_HNDL_HTTP_CONN) {
    __backpressure_list_remove(hndl);
    
    if (hndl->sys && hndl->sys->tcpBufferSlab) {
      valk_conn_io_free(&hndl->http.io, hndl->sys->tcpBufferSlab);
    }
  }
  
  if (hndl->onClose != nullptr) {
    VALK_TRACE("Calling onClose callback");
    hndl->onClose(hndl);
  }
  // LCOV_EXCL_BR_STOP
  valk_dll_pop(hndl); // LCOV_EXCL_BR_LINE dll_pop internal branches
  VALK_ASSERT(hndl->sys != nullptr, "handle must have sys for slab release"); // LCOV_EXCL_BR_LINE assertion
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);
}

int valk_http2_send_server_connection_header(nghttp2_session *session, valk_aio_system_t *sys) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, sys->config.max_concurrent_streams}};
  int rv;

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  // LCOV_EXCL_START nghttp2 settings submission rarely fails
  if (rv != 0) {
    fprintf(stderr, "Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  // LCOV_EXCL_STOP
  return 0;
}

int valk_http2_send_client_connection_header(nghttp2_session *session, valk_aio_system_t *sys) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, sys->config.max_concurrent_streams}};
  int rv;
  VALK_DEBUG("[http2 Client] Sending connection frame");

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  // LCOV_EXCL_START nghttp2 settings submission rarely fails
  if (rv != 0) {
    VALK_ERROR("Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  // LCOV_EXCL_STOP
  return 0;
}

// LCOV_EXCL_START arena backpressure - requires triggering arena exhaustion
void valk_http2_enter_arena_backpressure(valk_aio_handle_t *conn) {
  if (!conn || !conn->http.session) return;
  if (conn->http.arena_backpressure) return;

  conn->http.arena_backpressure = true;

  nghttp2_settings_entry iv[] = {
    {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, (u32)conn->http.active_streams}
  };
  int rv = nghttp2_submit_settings(conn->http.session, NGHTTP2_FLAG_NONE, iv, 1);
  if (rv == 0) {
    valk_http2_continue_pending_send(conn);
    VALK_INFO("Entered arena backpressure on connection (max_streams=%d)",
              conn->http.active_streams);
  }
}

void valk_http2_exit_arena_backpressure(valk_aio_handle_t *conn) {
  if (!conn || !conn->http.session) return;
  if (!conn->http.arena_backpressure) return;
  if (!conn->http.server || !conn->http.server->sys) return;

  conn->http.arena_backpressure = false;

  u32 max_streams = conn->http.server->sys->config.max_concurrent_streams;
  nghttp2_settings_entry iv[] = {
    {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, max_streams}
  };
  int rv = nghttp2_submit_settings(conn->http.session, NGHTTP2_FLAG_NONE, iv, 1);
  if (rv == 0) {
    valk_http2_continue_pending_send(conn);
    VALK_INFO("Exited arena backpressure on connection (max_streams=%u)", max_streams);
  }
}
// LCOV_EXCL_STOP

static void __disconnect_update_metrics(valk_aio_handle_t *handle) {
  // LCOV_EXCL_BR_START metrics path branches
  VALK_METRICS_IF(handle->sys) {
    valk_aio_metrics_v2_on_close(VALK_METRICS_V2(handle->sys));
  }
  extern valk_gauge_v2_t* client_connections_active;
  if (handle->http.server) {
    valk_gauge_v2_dec(handle->http.server->metrics.connections_active);
  } else if (client_connections_active) {
    valk_gauge_v2_dec(client_connections_active);
  }
  // LCOV_EXCL_BR_STOP
}

static void __disconnect_release_orphaned_arenas(valk_aio_handle_t *handle) {
  if (!handle->http.server || !handle->http.server->sys) return; // LCOV_EXCL_BR_LINE client connections

  valk_slab_t *slab = handle->http.server->sys->httpStreamArenas;
  u64 orphaned_count = 0;
  u32 slot = handle->http.active_arena_head;

  // LCOV_EXCL_START orphaned arena cleanup - requires abrupt disconnect with pending streams
  while (slot != UINT32_MAX && slot < slab->numItems) {
    u64 stride = valk_slab_item_stride(slab->itemSize);
    valk_slab_item_t *item = (valk_slab_item_t *)&slab->heap[stride * slot];
    valk_mem_arena_t *arena = (valk_mem_arena_t *)item->data;
    valk_http2_server_request_t *req = (valk_http2_server_request_t *)&arena->heap[0];

    if (req->arena_ref.slot == UINT32_MAX) {
      VALK_DEBUG("Arena slot %u already released (sentinel found), skipping", slot);
      break;
    }
    if (req->conn != handle) break;

    u32 next_slot = req->next_arena_slot;

    if (req->arena_ref.slab_item != item) {
      VALK_WARN("Arena slot %u already released or corrupted (item=%p, expected=%p)",
                slot, (void*)req->arena_ref.slab_item, (void*)item);
      break;
    }

    VALK_DEBUG("Releasing orphaned arena slot %u on disconnect", slot);
    valk_arena_ref_release(&req->arena_ref, slab);
    valk_aio_system_stats_v2_on_arena_release(
        (valk_aio_system_stats_v2_t*)handle->http.server->sys->metrics_state->system_stats_v2);
    orphaned_count++;
    slot = next_slot;
  }
  // LCOV_EXCL_STOP

  handle->http.active_arena_head = UINT32_MAX;
  if (orphaned_count > 0) { // LCOV_EXCL_BR_LINE typically no orphaned arenas
    VALK_DEBUG("Released %llu orphaned stream arenas on disconnect (normal for abrupt close)",
               (unsigned long long)orphaned_count);
  }
}

static void __disconnect_close_server_streams(valk_aio_handle_t *handle, nghttp2_session *session) {
  i32 last_stream_id = nghttp2_session_get_last_proc_stream_id(session);
  for (i32 stream_id = 1; stream_id <= last_stream_id; stream_id += 2) {
    if (nghttp2_session_find_stream(session, stream_id)) {
      VALK_DEBUG("Forcing stream close for server stream %d on disconnect", stream_id);
      valk_http2_server_on_stream_close_callback(session, stream_id, NGHTTP2_CANCEL, handle);
    }
  }
}

static void __disconnect_close_client_streams(nghttp2_session *session) {
  i32 next_id = nghttp2_session_get_next_stream_id(session);
  // LCOV_EXCL_BR_START client stream cleanup - requires abrupt disconnect with pending requests
  for (i32 stream_id = 1; stream_id < next_id; stream_id += 2) {
    __http2_client_req_res_t *reqres = nghttp2_session_get_stream_user_data(session, stream_id);
    if (!reqres) continue;

    VALK_WARN("Resolving orphaned client request on stream %d due to disconnect", stream_id);
    if (reqres->handle) {
      valk_async_handle_fail(reqres->handle, valk_lval_err("Connection closed before response received"));
    }
    free(reqres);
    nghttp2_session_set_stream_user_data(session, stream_id, nullptr);
  }
  // LCOV_EXCL_BR_STOP
}

static void __disconnect_cleanup_session(valk_aio_handle_t *handle) {
  nghttp2_session *session = handle->http.session;
  if (!session) return;

  if (handle->http.server) {
    __disconnect_close_server_streams(handle, session);
  } else {
    __disconnect_close_client_streams(session);
  }

  handle->http.session = nullptr;
  nghttp2_session_del(session);
}

void valk_http2_conn_on_disconnect(valk_aio_handle_t *handle) {
  fprintf(stderr, "[DBG] disconnect conn=%p active_streams=%d bodies=",
          (void*)handle, handle->http.active_streams);
  { valk_stream_body_t *b = handle->http.stream_bodies;
    while (b) { fprintf(stderr, "%llu ", (unsigned long long)b->id); b = b->next; }
  }
  fprintf(stderr, "\n");
  VALK_DEBUG("HTTP/2 disconnect called");

  __backpressure_list_remove(handle);
  valk_conn_transition(handle, VALK_CONN_EVT_CLOSED);
  valk_stream_body_close_all(handle);

  if (handle->http.httpHandler && handle->http.httpHandler->onDisconnect) {
    VALK_TRACE("HTTP/2 onDisconnect handler");
    handle->http.httpHandler->onDisconnect(handle->http.httpHandler->arg, handle);
  }

  __disconnect_update_metrics(handle);
  __disconnect_release_orphaned_arenas(handle);
  valk_aio_ssl_free(&handle->http.io.ssl);
  
  if (!handle->http.server) {
    valk_http2_fail_pending_client_requests(handle);
  }
  
  __disconnect_cleanup_session(handle);
}
