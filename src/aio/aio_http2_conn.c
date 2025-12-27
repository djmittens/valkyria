#include "aio_http2_conn.h"
#include "aio_internal.h"
#include "aio_conn_io.h"
#include "aio_ssl.h"

static inline const valk_io_tcp_ops_t *__tcp_ops(valk_aio_handle_t *conn) {
  return conn->sys ? conn->sys->ops->tcp : NULL;
}

static inline valk_io_tcp_t *__conn_tcp(valk_aio_handle_t *conn) {
  return &conn->uv.tcp;
}

static int __vtable_read_stop(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return -1;
  return tcp->read_stop(__conn_tcp(conn));
}

static bool __vtable_is_closing(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return true;
  return tcp->is_closing(__conn_tcp(conn));
}

static void __vtable_close(valk_aio_handle_t *conn, valk_io_close_cb cb) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return;
  tcp->close(__conn_tcp(conn), cb);
}

static void __vtable_alloc_cb(valk_io_tcp_t *tcp, size_t suggested, void **buf, size_t *buflen) {
  UNUSED(suggested);
  valk_aio_handle_t *conn = tcp->user_data;
  *buf = NULL;
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
  
  valk_aio_system_t *sys = valk_aio_active_system;
  if (!sys || !sys->tcpBufferSlab) {
    VALK_ERROR("No active AIO system in alloc callback");
    return;
  }
  valk_slab_item_t *item = valk_slab_aquire(sys->tcpBufferSlab);
  if (!item) {
    VALK_ERROR("TCP buffer slab exhausted in alloc callback");
    return;
  }
  *buf = (char *)item->data;
  *buflen = HTTP_SLAB_ITEM_SIZE;
}

static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf);

static int __vtable_read_start(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->read_start(__conn_tcp(conn), __vtable_alloc_cb, __vtable_read_cb);
}

static int __vtable_init(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->init(conn->sys, __conn_tcp(conn));
}

static int __vtable_accept(valk_aio_handle_t *server, valk_aio_handle_t *client) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(server);
  if (!ops) return -1;
  return ops->accept(__conn_tcp(server), __conn_tcp(client));
}

static int __vtable_nodelay(valk_aio_handle_t *conn, int enable) {
  const valk_io_tcp_ops_t *ops = __tcp_ops(conn);
  if (!ops) return -1;
  return ops->nodelay(__conn_tcp(conn), enable);
}

static bool __backpressure_list_add(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return false;
  return valk_backpressure_list_add(&sys->backpressure, conn, sys->ops->loop->now(sys));
}

static void __backpressure_list_remove(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return;
  valk_backpressure_list_remove(&sys->backpressure, conn);
}

void valk_http2_backpressure_try_resume_one(valk_aio_system_t *sys) {
  if (!sys) return;
  valk_aio_handle_t *conn = valk_backpressure_list_try_resume(
      &sys->backpressure, sys->tcpBufferSlab, sys->config.min_buffers_per_conn);
  if (conn) {
    __vtable_read_start(conn);
  }
}

bool valk_http2_conn_write_buf_acquire(valk_aio_handle_t *conn) {
  if (!conn->sys || !conn->sys->tcpBufferSlab) return false;
  return valk_conn_io_write_buf_acquire(&conn->http.io, conn->sys->tcpBufferSlab);
}

void valk_http2_conn_alloc_callback(uv_handle_t *handle, size_t suggested_size,
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
      buf->base = NULL;
      buf->len = 0;
      VALK_WARN("TCP buffer slab exhausted for read buffer");
      return;
    }
    
    buf->base = (char *)valk_conn_io_read_buf_data(&conn->http.io);
    buf->len = valk_conn_io_read_buf_size(&conn->http.io);
    return;
  }
  
  valk_aio_system_t *sys = valk_aio_active_system;
  if (!sys || !sys->tcpBufferSlab) {
    buf->base = NULL;
    buf->len = 0;
    VALK_ERROR("No active AIO system in alloc callback");
    return;
  }
  valk_slab_item_t *item = valk_slab_aquire(sys->tcpBufferSlab);
  if (!item) {
    buf->base = NULL;
    buf->len = 0;
    VALK_ERROR("TCP buffer slab exhausted in alloc callback");
    return;
  }
  buf->base = (char *)item->data;
  buf->len = HTTP_SLAB_ITEM_SIZE;
}

uint8_t *valk_http2_conn_write_buf_data(valk_aio_handle_t *conn) {
  return valk_conn_io_write_buf_data(&conn->http.io);
}

size_t valk_http2_conn_write_buf_available(valk_aio_handle_t *conn) {
  return valk_conn_io_write_buf_available(&conn->http.io);
}

bool valk_http2_conn_write_buf_writable(valk_aio_handle_t *conn) {
  if (!conn->sys || !conn->sys->tcpBufferSlab) return false;
  return valk_conn_io_write_buf_writable(&conn->http.io, conn->sys->tcpBufferSlab, 
                                          HTTP2_MAX_SERIALIZED_FRAME);
}

size_t valk_http2_conn_write_buf_append(valk_aio_handle_t *conn, const uint8_t *data, size_t len) {
  if (!conn->sys || !conn->sys->tcpBufferSlab) return 0;
  return valk_conn_io_write_buf_append(&conn->http.io, conn->sys->tcpBufferSlab, data, len);
}

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
    
    if (nghttp2_session_want_write(conn->http.session)) {
      valk_http2_continue_pending_send(conn);
    }
  }
}

int valk_http2_conn_write_buf_flush(valk_aio_handle_t *conn) {
  return valk_conn_io_flush(&conn->http.io, conn,
                            __http2_flush_complete, conn);
}

size_t valk_http2_flush_frames(valk_buffer_t *buf, valk_aio_handle_t *conn) {
  if (!conn || !conn->http.session) {
    return 0;
  }

  const uint8_t *data;
  nghttp2_ssize len;

  while ((buf->capacity - buf->count) > HTTP2_MAX_SERIALIZED_FRAME) {
    len = nghttp2_session_mem_send2(conn->http.session, &data);
    if (len <= 0) {
      if (len < 0) {
        VALK_ERROR("nghttp2_session_mem_send2 error: %s", nghttp2_strerror((int)len));
      }
      break;
    }
    memcpy((char *)buf->items + buf->count, data, (size_t)len);
    buf->count += (size_t)len;
    VALK_TRACE("Buffered frame: %zd bytes, total %zu/%zu", len, buf->count, buf->capacity);
  }

  return buf->count;
}

void valk_http2_continue_pending_send(valk_aio_handle_t *conn) {
  if (!conn || !conn->http.session || !SSL_is_init_finished(conn->http.io.ssl.ssl)) {
    return;
  }

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

  if (!conn->sys || !conn->sys->tcpBufferSlab) return;
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
    uint8_t *write_buf = valk_http2_conn_write_buf_data(conn);
    size_t write_available = valk_http2_conn_write_buf_available(conn);
    
    valk_buffer_t Out = {
        .items = write_buf + conn->http.io.write_pos, 
        .count = 0, 
        .capacity = write_available};

    valk_aio_ssl_encrypt(&conn->http.io.ssl, &In, &Out);

    if (Out.count > 0) {
      conn->http.io.write_pos += Out.count;
      VALK_TRACE("Buffered encrypted data: %zu bytes (total: %zu)", Out.count, conn->http.io.write_pos);
    }
  }

  valk_slab_release_ptr(slab, slabItem);

  if (conn->http.io.write_pos > 0) {
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

static void __http_tcp_unencrypted_read_cb(void *arg, const valk_buffer_t *buf) {
  valk_aio_handle_t *conn = arg;

  ssize_t rv = nghttp2_session_mem_recv2(
      conn->http.session, (const uint8_t *)buf->items, buf->count);
  if (rv < 0) {
    VALK_ERROR("nghttp2_session_mem_recv error: %zd", rv);
    if (!__vtable_is_closing(conn)) {
      conn->http.state = VALK_CONN_CLOSING;
      __backpressure_list_remove(conn);
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_CLOSING;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
      __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
  }
}

void valk_http2_conn_tcp_read_impl(valk_aio_handle_t *conn, ssize_t nread, const void *buf_base) {
  if (conn->http.state == VALK_CONN_CLOSING || conn->http.state == VALK_CONN_CLOSED) {
    return;
  }

  if (!buf_base) {
    VALK_WARN("TCP buffer alloc failed - applying backpressure on connection");
    __vtable_read_stop(conn);
    if (!__backpressure_list_add(conn)) {
      if (!__vtable_is_closing(conn)) {
        conn->http.state = VALK_CONN_CLOSING;
        __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
      }
    }
    return;
  }

  if (nread < 0) {
    if (!__vtable_is_closing(conn)) {
      conn->http.state = VALK_CONN_CLOSING;
      __backpressure_list_remove(conn);
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_CLOSING;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
      __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
    return;
  }

  VALK_TRACE("Feeding data to OpenSSL %ld", nread);

  if (!valk_http2_conn_write_buf_acquire(conn)) {
    VALK_WARN("Failed to acquire write buffer - applying backpressure on connection");
    int n = BIO_write(conn->http.io.ssl.read_bio, buf_base, (int)nread);
    if (n != (int)nread) {
      VALK_ERROR("BIO_write during backpressure failed: wrote %d of %zd", n, nread);
    }
    __vtable_read_stop(conn);
    valk_conn_io_read_buf_release(&conn->http.io, conn->sys->tcpBufferSlab);
    if (!__backpressure_list_add(conn)) {
      if (!__vtable_is_closing(conn)) {
        conn->http.state = VALK_CONN_CLOSING;
        __vtable_close(conn, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
      }
    }
#ifdef VALK_METRICS_ENABLED
    if (conn->http.server) {
      atomic_fetch_add(&conn->http.server->sys->metrics_state->system_stats.tcp_buffer_overflow, 1);
    }
#endif
    return;
  }

  if (conn->sys) {
    conn->http.last_activity_ms = conn->sys->ops->loop->now(conn->sys);
  }

  valk_buffer_t In = {
      .items = (void *)buf_base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};

  // If a write is pending, we still need to process incoming data (to receive
  // WINDOW_UPDATE, PING, etc.) but we can't safely append to the write buffer.
  // Buffer the incoming SSL data and process it - any output will be generated
  // on the next read after the flush completes.
  bool can_write_output = !conn->http.io.write_flush_pending;

  uint8_t *write_buf = can_write_output ? valk_http2_conn_write_buf_data(conn) : NULL;
  size_t write_available = can_write_output ? valk_http2_conn_write_buf_available(conn) : 0;

  // Use a temporary stack buffer for SSL output if we can't write to the main buffer
  uint8_t temp_ssl_out[256];  // Small buffer for handshake/alert data
  valk_buffer_t Out = {
      .items = can_write_output ? (write_buf + conn->http.io.write_pos) : temp_ssl_out,
      .count = 0,
      .capacity = can_write_output ? write_available : sizeof(temp_ssl_out)};

  int err = valk_aio_ssl_on_read(&conn->http.io.ssl, &In, &Out, conn,
                                 __http_tcp_unencrypted_read_cb);

  if (Out.count > 0 && can_write_output) {
    conn->http.io.write_pos += Out.count;
    VALK_TRACE("SSL output: %zu bytes (total: %zu)", Out.count, conn->http.io.write_pos);
  }

  if (!err) {
    if (conn->http.state == VALK_CONN_INIT && SSL_is_init_finished(conn->http.io.ssl.ssl)) {
      conn->http.state = VALK_CONN_ESTABLISHED;
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_ACTIVE;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
    }
    // Only flush HTTP/2 frames if we can write output
    if (can_write_output && SSL_is_init_finished(conn->http.io.ssl.ssl) && conn->sys && conn->sys->tcpBufferSlab) {
      valk_slab_item_t *frameSlabRaw = valk_slab_aquire(conn->sys->tcpBufferSlab);
      if (frameSlabRaw) {
        __tcp_buffer_slab_item_t *frameSlabItem = (void *)frameSlabRaw->data;
        valk_buffer_t FrameIn = {
            .items = frameSlabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

        valk_http2_flush_frames(&FrameIn, conn);

        if (FrameIn.count > 0) {
          write_available = valk_http2_conn_write_buf_available(conn);
          Out.items = write_buf + conn->http.io.write_pos;
          Out.count = 0;
          Out.capacity = write_available;
          valk_aio_ssl_encrypt(&conn->http.io.ssl, &FrameIn, &Out);

          if (Out.count > 0) {
            conn->http.io.write_pos += Out.count;
            VALK_TRACE("HTTP/2 frames encrypted: %zu bytes (total: %zu)", Out.count, conn->http.io.write_pos);
          }
        }

        valk_slab_release_ptr(conn->sys->tcpBufferSlab, frameSlabItem);
      }
    }
  }

  if (conn->http.io.write_pos > 0 && !conn->http.io.write_flush_pending) {
    valk_http2_conn_write_buf_flush(conn);
  }
}

static void __vtable_read_cb(valk_io_tcp_t *tcp, ssize_t nread, const void *buf) {
  valk_aio_handle_t *conn = tcp->user_data;
  valk_http2_conn_tcp_read_impl(conn, nread, buf);
}

void valk_http2_conn_tcp_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  valk_aio_handle_t *conn = stream->data;
  valk_http2_conn_tcp_read_impl(conn, nread, buf->base);
}

void valk_http2_conn_handle_closed_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  VALK_TRACE("UV handle closed %p", handle->data);
  
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
  valk_dll_pop(hndl);
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);
}

int valk_http2_send_server_connection_header(nghttp2_session *session, valk_aio_system_t *sys) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, sys->config.max_concurrent_streams}};
  int rv;

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    fprintf(stderr, "Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

int valk_http2_send_client_connection_header(nghttp2_session *session, valk_aio_system_t *sys) {
  nghttp2_settings_entry iv[1] = {
      {NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, sys->config.max_concurrent_streams}};
  int rv;
  VALK_DEBUG("[http2 Client] Sending connection frame");

  rv = nghttp2_submit_settings(session, NGHTTP2_FLAG_NONE, iv,
                               sizeof(iv) / sizeof(iv[0]));
  if (rv != 0) {
    VALK_ERROR("Fatal error: %s", nghttp2_strerror(rv));
    return -1;
  }
  return 0;
}

void valk_http2_conn_on_disconnect(valk_aio_handle_t *handle) {
  VALK_DEBUG("HTTP/2 disconnect called");

  __backpressure_list_remove(handle);

  handle->http.state = VALK_CONN_CLOSED;

  if (handle->http.httpHandler && handle->http.httpHandler->onDisconnect) {
    VALK_TRACE("HTTP/2 onDisconnect handler");
    handle->http.httpHandler->onDisconnect(handle->http.httpHandler->arg, handle);
  }

#ifdef VALK_METRICS_ENABLED
  VALK_METRICS_IF(handle->sys) {
    valk_aio_metrics_on_close(&VALK_METRICS(handle->sys));
  }
  extern valk_gauge_v2_t* client_connections_active;
  if (handle->http.server) {
    valk_gauge_v2_dec(handle->http.server->metrics.connections_active);
  } else if (client_connections_active) {
    valk_gauge_v2_dec(client_connections_active);
  }
#endif

  if (handle->http.sse_streams) {
    valk_sse_close_all_streams(handle);
  }

  if (handle->http.server && handle->http.server->sys) {
    valk_sse_stream_registry_t *registry = &handle->http.server->sys->sse_registry;
    size_t sse_count = valk_sse_registry_unsubscribe_connection(registry, handle);
#ifdef VALK_METRICS_ENABLED
    for (size_t i = 0; i < sse_count; i++) {
      valk_gauge_v2_dec(handle->http.server->metrics.sse_streams_active);
    }
#else
    UNUSED(sse_count);
#endif
  }

  if (handle->http.server && handle->http.server->sys) {
    valk_slab_t *slab = handle->http.server->sys->httpStreamArenas;
    size_t leaked_arenas = 0;
    uint32_t slot = handle->http.active_arena_head;
    while (slot != UINT32_MAX && slot < slab->numItems) {
      size_t stride = valk_slab_item_stride(slab->itemSize);
      valk_slab_item_t *item = (valk_slab_item_t *)&slab->heap[stride * slot];
      valk_mem_arena_t *arena = (valk_mem_arena_t *)item->data;
      valk_http2_server_request_t *req = (valk_http2_server_request_t *)&arena->heap[0];

      if (req->arena_slot == UINT32_MAX) {
        VALK_DEBUG("Arena slot %u already released (sentinel found), skipping", slot);
        break;
      }

      if (req->conn != handle) {
        VALK_WARN("Arena slot %u belongs to different connection, stopping traversal", slot);
        break;
      }

      uint32_t next_slot = req->next_arena_slot;

      if (req->arena_slab_item == item) {
        VALK_INFO("Releasing leaked arena slot %u on disconnect", slot);
        req->arena_slot = UINT32_MAX;
        req->arena_slab_item = NULL;
        valk_slab_release(slab, item);
#ifdef VALK_METRICS_ENABLED
        valk_aio_system_stats_on_arena_release(&handle->http.server->sys->metrics_state->system_stats);
#endif
        leaked_arenas++;
      } else {
        VALK_WARN("Arena slot %u already released or corrupted (item=%p, expected=%p)",
                  slot, (void*)req->arena_slab_item, (void*)item);
        break;
      }
      slot = next_slot;
    }
    handle->http.active_arena_head = UINT32_MAX;
    if (leaked_arenas > 0) {
      VALK_WARN("Released %zu leaked stream arenas on disconnect", leaked_arenas);
    }
  }

  valk_aio_ssl_free(&handle->http.io.ssl);

  nghttp2_session *session = handle->http.session;
  if (session && !handle->http.server) {
    int32_t next_id = nghttp2_session_get_next_stream_id(session);
    for (int32_t stream_id = 1; stream_id < next_id; stream_id += 2) {
      __http2_req_res_t *reqres = nghttp2_session_get_stream_user_data(session, stream_id);
      if (reqres) {
        VALK_WARN("Resolving orphaned client request on stream %d due to disconnect", stream_id);
        valk_arc_box *err = valk_arc_box_err("Connection closed before response received");
        valk_promise_respond(&reqres->promise, err);
        valk_arc_release(err);
        valk_mem_free(reqres);
        nghttp2_session_set_stream_user_data(session, stream_id, NULL);
      }
    }
  }

  handle->http.session = NULL;
  nghttp2_session_del(session);
}
