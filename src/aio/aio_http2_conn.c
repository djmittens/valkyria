#include "aio_http2_conn.h"
#include "aio_internal.h"
#include "aio_ssl.h"

static bool __backpressure_list_add(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return false;
  return valk_backpressure_list_add(&sys->backpressure, conn, uv_now(conn->uv.tcp.loop));
}

static void __backpressure_list_remove(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return;
  valk_backpressure_list_remove(&sys->backpressure, conn);
}

bool valk_http2_backpressure_list_add(valk_aio_handle_t *conn) {
  return __backpressure_list_add(conn);
}

void valk_http2_backpressure_list_remove(valk_aio_handle_t *conn) {
  __backpressure_list_remove(conn);
}

void valk_http2_backpressure_try_resume_one(valk_aio_system_t *sys) {
  if (!sys) return;
  valk_aio_handle_t *conn = valk_backpressure_list_try_resume(
      &sys->backpressure, sys->tcpBufferSlab, sys->config.min_buffers_per_conn);
  if (conn) {
    uv_read_start((uv_stream_t *)&conn->uv.tcp, valk_http2_conn_alloc_callback, 
                  valk_http2_conn_tcp_read_cb);
  }
}

bool valk_http2_conn_write_buf_acquire(valk_aio_handle_t *conn) {
  if (conn->http.write_buf) return true;
  if (!conn->sys || !conn->sys->tcpBufferSlab) return false;
  
  valk_slab_item_t *item = valk_slab_aquire(conn->sys->tcpBufferSlab);
  if (!item) {
    VALK_WARN("Failed to acquire write buffer for connection");
    return false;
  }
  
  conn->http.write_buf = item;
  conn->http.write_pos = 0;
  conn->http.write_flush_pending = false;
  return true;
}

void valk_http2_conn_alloc_callback(uv_handle_t *handle, size_t suggested_size,
                             uv_buf_t *buf) {
  UNUSED(suggested_size);
  valk_aio_handle_t *conn = handle->data;
  
  if (conn && conn->magic == VALK_AIO_HANDLE_MAGIC && conn->kind == VALK_HNDL_HTTP_CONN) {
    if (conn->http.read_buf) {
      __tcp_buffer_slab_item_t *item = (void *)conn->http.read_buf->data;
      buf->base = item->data;
      buf->len = HTTP_SLAB_ITEM_SIZE;
      return;
    }
    
    valk_slab_item_t *item = valk_slab_aquire(conn->sys->tcpBufferSlab);
    if (!item) {
      buf->base = NULL;
      buf->len = 0;
      VALK_WARN("TCP buffer slab exhausted for read buffer");
      return;
    }
    
    conn->http.read_buf = item;
    __tcp_buffer_slab_item_t *slab_item = (void *)item->data;
    buf->base = slab_item->data;
    buf->len = HTTP_SLAB_ITEM_SIZE;
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
  if (!conn->http.write_buf) return NULL;
  __tcp_buffer_slab_item_t *item = (void *)conn->http.write_buf->data;
  return (uint8_t *)item->data;
}

size_t valk_http2_conn_write_buf_available(valk_aio_handle_t *conn) {
  if (!conn->http.write_buf) return 0;
  return HTTP_SLAB_ITEM_SIZE - conn->http.write_pos;
}

bool valk_http2_conn_write_buf_writable(valk_aio_handle_t *conn) {
  if (conn->http.write_flush_pending) return false;
  if (!conn->http.write_buf && !valk_http2_conn_write_buf_acquire(conn)) return false;
  return valk_http2_conn_write_buf_available(conn) > HTTP2_MAX_SERIALIZED_FRAME;
}

size_t valk_http2_conn_write_buf_append(valk_aio_handle_t *conn, const uint8_t *data, size_t len) {
  if (conn->http.write_flush_pending) return 0;
  if (!conn->http.write_buf && !valk_http2_conn_write_buf_acquire(conn)) return 0;
  
  size_t available = valk_http2_conn_write_buf_available(conn);
  size_t to_write = len < available ? len : available;
  
  if (to_write > 0) {
    uint8_t *buf = valk_http2_conn_write_buf_data(conn);
    memcpy(buf + conn->http.write_pos, data, to_write);
    conn->http.write_pos += to_write;
  }
  
  return to_write;
}

static void __conn_write_buf_on_flush_complete(uv_write_t *req, int status);

int valk_http2_conn_write_buf_flush(valk_aio_handle_t *conn) {
  if (!conn->http.write_buf || conn->http.write_pos == 0) {
    return 0;
  }
  
  if (conn->http.write_flush_pending) {
    return 1;
  }
  
  if (uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
    return -1;
  }
  
  conn->http.write_flush_pending = true;
  conn->http.write_uv_buf.base = (char *)valk_http2_conn_write_buf_data(conn);
  conn->http.write_uv_buf.len = conn->http.write_pos;
  conn->http.write_req.data = conn;
  
  VALK_TRACE("Flushing write buffer: %zu bytes", conn->http.write_pos);
  
  int rv = uv_write(&conn->http.write_req, (uv_stream_t *)&conn->uv.tcp,
                    &conn->http.write_uv_buf, 1, __conn_write_buf_on_flush_complete);
  if (rv != 0) {
    VALK_ERROR("uv_write failed: %s", uv_strerror(rv));
    conn->http.write_flush_pending = false;
    return -1;
  }
  
  return 0;
}

static void __conn_write_buf_on_flush_complete(uv_write_t *req, int status) {
  valk_aio_handle_t *conn = req->data;
  
  if (!conn || conn->magic != VALK_AIO_HANDLE_MAGIC) {
    VALK_ERROR("Invalid connection in write flush callback");
    return;
  }
  
  if (status != 0) {
    VALK_ERROR("Write flush failed: %s", uv_strerror(status));
  }
  
  conn->http.write_flush_pending = false;
  conn->http.write_pos = 0;
  
  VALK_TRACE("Write flush complete, buffer reset");
  
  valk_http2_backpressure_try_resume_one(conn->sys);
  
  if (status == 0 && conn->http.state != VALK_CONN_CLOSING && 
      conn->http.state != VALK_CONN_CLOSED &&
      !uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
    
    if (conn->http.backpressure) {
      __backpressure_list_remove(conn);
      uv_read_start((uv_stream_t *)&conn->uv.tcp,
                    valk_http2_conn_alloc_callback, valk_http2_conn_tcp_read_cb);
      VALK_DEBUG("Resumed reading after write buffer flush");
    }
    
    if (nghttp2_session_want_write(conn->http.session)) {
      valk_http2_continue_pending_send(conn);
    }
  }
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
  if (!conn || !conn->http.session || !SSL_is_init_finished(conn->http.ssl.ssl)) {
    return;
  }

  if (uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
    return;
  }

  if (conn->http.write_flush_pending) {
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
        .items = write_buf + conn->http.write_pos, 
        .count = 0, 
        .capacity = write_available};

    valk_aio_ssl_encrypt(&conn->http.ssl, &In, &Out);

    if (Out.count > 0) {
      conn->http.write_pos += Out.count;
      VALK_TRACE("Buffered encrypted data: %zu bytes (total: %zu)", Out.count, conn->http.write_pos);
    }
  }

  valk_slab_release_ptr(slab, slabItem);

  if (conn->http.write_pos > 0) {
    valk_http2_conn_write_buf_flush(conn);
  }
}

void valk_http2_flush_pending(valk_aio_handle_t *conn) {
  valk_http2_continue_pending_send(conn);
}

static void __http_tcp_unencrypted_read_cb(void *arg, const valk_buffer_t *buf) {
  valk_aio_handle_t *conn = arg;

  ssize_t rv = nghttp2_session_mem_recv2(
      conn->http.session, (const uint8_t *)buf->items, buf->count);
  if (rv < 0) {
    VALK_ERROR("nghttp2_session_mem_recv error: %zd", rv);
    if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
      conn->http.state = VALK_CONN_CLOSING;
      __backpressure_list_remove(conn);
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_CLOSING;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
      uv_close((uv_handle_t *)&conn->uv.tcp, valk_http2_conn_handle_closed_cb);
    }
  }
}

void valk_http2_conn_tcp_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf) {
  valk_aio_handle_t *conn = stream->data;

  if (conn->http.state == VALK_CONN_CLOSING || conn->http.state == VALK_CONN_CLOSED) {
    return;
  }

  if (!buf->base) {
    VALK_WARN("TCP buffer alloc failed - applying backpressure on connection");
    uv_read_stop((uv_stream_t *)&conn->uv.tcp);
    if (!__backpressure_list_add(conn)) {
      if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
        conn->http.state = VALK_CONN_CLOSING;
        uv_close((uv_handle_t *)&conn->uv.tcp, valk_http2_conn_handle_closed_cb);
      }
    }
    return;
  }

  if (nread < 0) {
    if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
      conn->http.state = VALK_CONN_CLOSING;
      __backpressure_list_remove(conn);
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_CLOSING;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
      uv_close((uv_handle_t *)&conn->uv.tcp, valk_http2_conn_handle_closed_cb);
    }
    return;
  }

  VALK_TRACE("Feeding data to OpenSSL %ld", nread);

  if (conn->http.write_flush_pending) {
    VALK_WARN("Write buffer flush pending - applying backpressure on connection");
    int n = BIO_write(conn->http.ssl.read_bio, buf->base, nread);
    if (n != nread) {
      VALK_ERROR("BIO_write during backpressure failed: wrote %d of %ld", n, nread);
    }
    uv_read_stop((uv_stream_t *)&conn->uv.tcp);
    if (!__backpressure_list_add(conn)) {
      if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
        conn->http.state = VALK_CONN_CLOSING;
        uv_close((uv_handle_t *)&conn->uv.tcp, valk_http2_conn_handle_closed_cb);
      }
    }
    return;
  }

  if (!valk_http2_conn_write_buf_acquire(conn)) {
    VALK_WARN("Failed to acquire write buffer - applying backpressure on connection");
    int n = BIO_write(conn->http.ssl.read_bio, buf->base, nread);
    if (n != nread) {
      VALK_ERROR("BIO_write during backpressure failed: wrote %d of %ld", n, nread);
    }
    uv_read_stop((uv_stream_t *)&conn->uv.tcp);
    if (!__backpressure_list_add(conn)) {
      if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
        conn->http.state = VALK_CONN_CLOSING;
        uv_close((uv_handle_t *)&conn->uv.tcp, valk_http2_conn_handle_closed_cb);
      }
    }
#ifdef VALK_METRICS_ENABLED
    if (conn->http.server) {
      atomic_fetch_add(&conn->http.server->sys->metrics_state->system_stats.tcp_buffer_overflow, 1);
    }
#endif
    return;
  }

  if (conn->sys && conn->sys->eventloop) {
    conn->http.last_activity_ms = uv_now(conn->sys->eventloop);
  }

  valk_buffer_t In = {
      .items = buf->base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};

  uint8_t *write_buf = valk_http2_conn_write_buf_data(conn);
  size_t write_available = valk_http2_conn_write_buf_available(conn);
  
  valk_buffer_t Out = {
      .items = write_buf + conn->http.write_pos, 
      .count = 0, 
      .capacity = write_available};

  int err = valk_aio_ssl_on_read(&conn->http.ssl, &In, &Out, conn,
                                 __http_tcp_unencrypted_read_cb);

  if (Out.count > 0) {
    conn->http.write_pos += Out.count;
    VALK_TRACE("SSL output: %zu bytes (total: %zu)", Out.count, conn->http.write_pos);
  }

  if (!err) {
    if (conn->http.state == VALK_CONN_INIT && SSL_is_init_finished(conn->http.ssl.ssl)) {
      conn->http.state = VALK_CONN_ESTABLISHED;
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_ACTIVE;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
    }
    if (SSL_is_init_finished(conn->http.ssl.ssl) && conn->sys && conn->sys->tcpBufferSlab) {
      valk_slab_item_t *frameSlabRaw = valk_slab_aquire(conn->sys->tcpBufferSlab);
      if (frameSlabRaw) {
        __tcp_buffer_slab_item_t *frameSlabItem = (void *)frameSlabRaw->data;
        valk_buffer_t FrameIn = {
            .items = frameSlabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};
        
        valk_http2_flush_frames(&FrameIn, conn);

        if (FrameIn.count > 0) {
          write_available = valk_http2_conn_write_buf_available(conn);
          Out.items = write_buf + conn->http.write_pos;
          Out.count = 0;
          Out.capacity = write_available;
          valk_aio_ssl_encrypt(&conn->http.ssl, &FrameIn, &Out);
          
          if (Out.count > 0) {
            conn->http.write_pos += Out.count;
            VALK_TRACE("HTTP/2 frames encrypted: %zu bytes (total: %zu)", Out.count, conn->http.write_pos);
          }
        }
        
        valk_slab_release_ptr(conn->sys->tcpBufferSlab, frameSlabItem);
      }
    }
  }

  if (conn->http.write_pos > 0) {
    valk_http2_conn_write_buf_flush(conn);
  }
}

void valk_http2_conn_handle_closed_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  VALK_TRACE("UV handle closed %p", handle->data);
  
  if (hndl->kind == VALK_HNDL_HTTP_CONN) {
    __backpressure_list_remove(hndl);
    
    if (hndl->http.read_buf && hndl->sys && hndl->sys->tcpBufferSlab) {
      valk_slab_release(hndl->sys->tcpBufferSlab, hndl->http.read_buf);
      hndl->http.read_buf = NULL;
    }
    if (hndl->http.write_buf && hndl->sys && hndl->sys->tcpBufferSlab) {
      valk_slab_release(hndl->sys->tcpBufferSlab, hndl->http.write_buf);
      hndl->http.write_buf = NULL;
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

  valk_aio_ssl_free(&handle->http.ssl);

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
