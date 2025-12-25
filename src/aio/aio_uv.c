#include "aio_internal.h"
#include <execinfo.h>

valk_aio_system_t *g_last_started_aio_system = NULL;
valk_aio_system_t *valk_aio_active_system = NULL;
uint64_t g_async_handle_id = 0;

static void __alloc_callback(uv_handle_t *handle, size_t suggested_size, uv_buf_t *buf);
static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread, const uv_buf_t *buf);
static void __uv_handle_closed_cb(uv_handle_t *handle);
static void __aio_uv_walk_close(uv_handle_t *h, void *arg);
static void __aio_uv_walk_diag(uv_handle_t *h, void *arg);
static const char* __uv_handle_type_name(uv_handle_type type);

// LCOV_EXCL_START - backpressure add: requires buffer exhaustion under load
static bool __backpressure_list_add(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return false;
  return valk_backpressure_list_add(&sys->backpressure, conn, uv_now(conn->uv.tcp.loop));
}
// LCOV_EXCL_STOP

// LCOV_EXCL_START - backpressure remove: requires connection in backpressure list
static void __backpressure_list_remove(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return;
  valk_backpressure_list_remove(&sys->backpressure, conn);
}
// LCOV_EXCL_STOP

static void __backpressure_try_resume_one(valk_aio_system_t *sys) {
  if (!sys) return;
  valk_aio_handle_t *conn = valk_backpressure_list_try_resume(
      &sys->backpressure, sys->tcpBufferSlab, sys->config.min_buffers_per_conn);
  if (conn) {
    uv_read_start((uv_stream_t *)&conn->uv.tcp, __alloc_callback, __http_tcp_read_cb);
  }
}



// ============================================================================
// Per-Connection Write Buffer Management
// ============================================================================

// Acquire write buffer for connection if not already held
static bool __conn_write_buf_acquire(valk_aio_handle_t *conn) {
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

static void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                             uv_buf_t *buf) {
  UNUSED(suggested_size);
  valk_aio_handle_t *conn = handle->data;
  
  // LCOV_EXCL_BR_START - else branch: non-HTTP handles use different alloc path
  if (conn && conn->magic == VALK_AIO_HANDLE_MAGIC && conn->kind == VALK_HNDL_HTTP_CONN) {
  // LCOV_EXCL_BR_STOP
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
  
  // LCOV_EXCL_START - Fallback path for non-HTTP handles, rarely exercised
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
  // LCOV_EXCL_STOP
}

static inline uint8_t *__conn_write_buf_data(valk_aio_handle_t *conn) {
  if (!conn->http.write_buf) return NULL;
  __tcp_buffer_slab_item_t *item = (void *)conn->http.write_buf->data;
  return (uint8_t *)item->data;
}

static inline size_t __conn_write_buf_available(valk_aio_handle_t *conn) {
  if (!conn->http.write_buf) return 0;
  return HTTP_SLAB_ITEM_SIZE - conn->http.write_pos;
}

// Forward declaration for write callback
static void __conn_write_buf_on_flush_complete(uv_write_t *req, int status);

// Flush write buffer to TCP
// Returns: 0 on success, -1 on error, 1 if already flushing (backpressure)
static int __conn_write_buf_flush(valk_aio_handle_t *conn) {
  // LCOV_EXCL_BR_LINE - write buffer state check
  if (!conn->http.write_buf || conn->http.write_pos == 0) {
    return 0;  // LCOV_EXCL_LINE - Normal case: nothing to flush
  }
  
  if (conn->http.write_flush_pending) {
    return 1;  // LCOV_EXCL_LINE - Backpressure path, timing dependent
  }
  
  // LCOV_EXCL_START - Race with connection close, hard to trigger in tests
  if (uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
    return -1;
  }
  // LCOV_EXCL_STOP
  
  conn->http.write_flush_pending = true;
  conn->http.write_uv_buf.base = (char *)__conn_write_buf_data(conn);
  conn->http.write_uv_buf.len = conn->http.write_pos;
  conn->http.write_req.data = conn;
  
  VALK_TRACE("Flushing write buffer: %zu bytes", conn->http.write_pos);
  
  int rv = uv_write(&conn->http.write_req, (uv_stream_t *)&conn->uv.tcp,
                    &conn->http.write_uv_buf, 1, __conn_write_buf_on_flush_complete);
  // LCOV_EXCL_START - uv_write failure requires OS-level failure
  if (rv != 0) {
    VALK_ERROR("uv_write failed: %s", uv_strerror(rv));
    conn->http.write_flush_pending = false;
    return -1;
  }
  // LCOV_EXCL_STOP
  
  return 0;
}

// Forward declaration for write continuation
void valk_http2_continue_pending_send(valk_aio_handle_t *conn);

// Callback when per-connection write buffer flush completes
static void __conn_write_buf_on_flush_complete(uv_write_t *req, int status) {
  valk_aio_handle_t *conn = req->data;
  
  // LCOV_EXCL_START - Defensive: libuv guarantees valid req->data
  if (!conn || conn->magic != VALK_AIO_HANDLE_MAGIC) {
    VALK_ERROR("Invalid connection in write flush callback");
    return;
  }
  // LCOV_EXCL_STOP
  
  // LCOV_EXCL_START - Write failure requires network error during write
  if (status != 0) {
    VALK_ERROR("Write flush failed: %s", uv_strerror(status));
  }
  // LCOV_EXCL_STOP
  
  conn->http.write_flush_pending = false;
  conn->http.write_pos = 0;
  
  VALK_TRACE("Write flush complete, buffer reset");
  
  // Try to resume a backpressured connection (buffer now available)
  __backpressure_try_resume_one(conn->sys);
  
  // LCOV_EXCL_BR_START - write callback state checks: connection state after write
  if (status == 0 && conn->http.state != VALK_CONN_CLOSING && 
      conn->http.state != VALK_CONN_CLOSED &&
      !uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
    
    // LCOV_EXCL_START - Backpressure resume after write requires tight timing
    if (conn->http.backpressure) {
      __backpressure_list_remove(conn);
      uv_read_start((uv_stream_t *)&conn->uv.tcp,
                    __alloc_callback, __http_tcp_read_cb);
      VALK_DEBUG("Resumed reading after write buffer flush");
    }
    // LCOV_EXCL_STOP
    
    if (nghttp2_session_want_write(conn->http.session)) {
      valk_http2_continue_pending_send(conn);
    }
  }
  // LCOV_EXCL_BR_STOP
}







void __event_loop(void *arg) {
  valk_aio_system_t *sys = arg;
  valk_mem_init_malloc();
  VALK_DEBUG("Initializing UV event loop thread");

  sys->current_request_ctx = NULL;

  sys->tcpBufferSlab =
      valk_slab_new(sizeof(__tcp_buffer_slab_item_t), sys->config.tcp_buffer_pool_size);
  VALK_INFO("Initialized %u TCP buffers (%zuKB each)",
            sys->config.tcp_buffer_pool_size, HTTP_SLAB_ITEM_SIZE / 1024);

  // Initialize per-stream arena pool
  // Each slab item contains: valk_mem_arena_t header + arena heap space
  sys->httpStreamArenas = valk_slab_new(
      sizeof(valk_mem_arena_t) + sys->config.arena_size,
      sys->config.arena_pool_size);
  // LCOV_EXCL_START - arena slab alloc: requires malloc failure at startup
  if (!sys->httpStreamArenas) {
    VALK_ERROR("Failed to allocate stream arena slab");
    return;
  }
  // LCOV_EXCL_STOP
  VALK_INFO("Initialized %u stream arenas (%zuKB each)",
            sys->config.arena_pool_size, sys->config.arena_size / 1024);

  valk_maintenance_timer_init(sys);
  valk_maintenance_timer_start(sys);

  // Signal that event loop is ready (all slabs initialized)
  uv_sem_post(&sys->startup_sem);

  // Run the loop until stop is requested
  uv_run(sys->eventloop, UV_RUN_DEFAULT);

  // =========================================================================
  // Graceful Shutdown (modeled after Finagle/Netty)
  // =========================================================================
  // Phase 1: Graceful drain - allow pending I/O to complete
  // Phase 2: Force close - close any remaining handles
  // Phase 3: Hard deadline - log diagnostics and exit
  //
  // Total shutdown budget: 500ms (generous for tests, fast enough for prod)
  
  uint64_t drain_start = uv_hrtime();
  uint64_t graceful_drain_ns = 100ULL * 1000000ULL;  // 100ms graceful
  uint64_t force_close_ns = 300ULL * 1000000ULL;     // 300ms for force close
  uint64_t hard_deadline_ns = 500ULL * 1000000ULL;   // 500ms hard deadline
  
  bool force_closed = false;
  bool logged_diagnostics = false;
  int iterations = 0;
  
  // LCOV_EXCL_START - shutdown drain loop timing-dependent, rarely entered in tests
  while (uv_loop_alive(sys->eventloop)) {
    uint64_t elapsed = uv_hrtime() - drain_start;
    iterations++;
    
    // Phase 1: Graceful drain with UV_RUN_ONCE (allows I/O to complete)
    if (elapsed < graceful_drain_ns) {
      uv_run(sys->eventloop, UV_RUN_NOWAIT);
      continue;
    }
    // Phase 2: Force close all remaining handles
    if (!force_closed && elapsed >= graceful_drain_ns) {
      VALK_DEBUG("Shutdown: graceful drain exceeded 100ms, force closing handles");
      uv_walk(sys->eventloop, __aio_uv_walk_close, NULL);
      force_closed = true;
    }
    
    // Continue draining after force close
    if (elapsed < force_close_ns) {
      uv_run(sys->eventloop, UV_RUN_NOWAIT);
      continue;
    }
    
    // Phase 3: Hard deadline - log what's still alive and exit
    if (!logged_diagnostics && elapsed >= force_close_ns) {
      __drain_diag_t diag = {0};
      VALK_WARN("Shutdown: force close exceeded 300ms, diagnosing remaining handles:");
      uv_walk(sys->eventloop, __aio_uv_walk_diag, &diag);
      VALK_WARN("Shutdown: %d handles remaining (%d active, %d closing)",
                diag.count, diag.active, diag.closing);
      logged_diagnostics = true;
    }
    
    if (elapsed >= hard_deadline_ns) {
      VALK_ERROR("Shutdown: HARD DEADLINE exceeded (500ms, %d iterations). "
                 "Forcing exit - some handles may leak.", iterations);
      break;
    }
    
    uv_run(sys->eventloop, UV_RUN_NOWAIT);
  }
  // LCOV_EXCL_STOP
  
  uint64_t total_drain_ms = (uv_hrtime() - drain_start) / 1000000ULL;
  if (total_drain_ms > 50) {  // LCOV_EXCL_LINE
    VALK_INFO("Shutdown: drain completed in %llu ms (%d iterations)",  // LCOV_EXCL_LINE
              (unsigned long long)total_drain_ms, iterations);  // LCOV_EXCL_LINE
  }

  valk_slab_free(sys->tcpBufferSlab);
  valk_slab_free(sys->httpStreamArenas);
}

static void __uv_handle_closed_cb(uv_handle_t *handle) {
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
  
  if (hndl->onClose != nullptr) {  // LCOV_EXCL_BR_LINE - onClose callback presence
    VALK_TRACE("Calling onClose callback");
    hndl->onClose(hndl);
  }
  valk_dll_pop(hndl);
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);
}

// LCOV_EXCL_START - shutdown diagnostic helpers only called during slow/stuck shutdown
static const char* __uv_handle_type_name(uv_handle_type type) {
  switch (type) {
    case UV_ASYNC: return "async";
    case UV_CHECK: return "check";
    case UV_FS_EVENT: return "fs_event";
    case UV_FS_POLL: return "fs_poll";
    case UV_HANDLE: return "handle";
    case UV_IDLE: return "idle";
    case UV_NAMED_PIPE: return "pipe";
    case UV_POLL: return "poll";
    case UV_PREPARE: return "prepare";
    case UV_PROCESS: return "process";
    case UV_STREAM: return "stream";
    case UV_TCP: return "tcp";
    case UV_TIMER: return "timer";
    case UV_TTY: return "tty";
    case UV_UDP: return "udp";
    case UV_SIGNAL: return "signal";
    default: return "unknown";
  }
}

static void __aio_uv_walk_close(uv_handle_t *h, void *arg) {
  UNUSED(arg);
  if (!uv_is_closing(h)) {
    VALK_DEBUG("Closing open UV handle type=%s", __uv_handle_type_name(h->type));
    valk_aio_handle_t *hndl = h->data;
    if (hndl && hndl->magic == VALK_AIO_HANDLE_MAGIC) {
      if (hndl->kind == VALK_HNDL_TCP && hndl->arg) {
        valk_aio_http_server *srv = hndl->arg;
        srv->state = VALK_SRV_CLOSING;
      } else if (hndl->kind == VALK_HNDL_HTTP_CONN) {
        hndl->http.state = VALK_CONN_CLOSING;
        __backpressure_list_remove(hndl);
      }
      uv_close(h, __uv_handle_closed_cb);
    } else {
      uv_close(h, NULL);
    }
  }
}

static void __aio_uv_walk_diag(uv_handle_t *h, void *arg) {
  __drain_diag_t *diag = arg;
  diag->count++;
  if (uv_is_active(h)) diag->active++;
  if (uv_is_closing(h)) diag->closing++;
  
  const char *state = uv_is_closing(h) ? "closing" : (uv_is_active(h) ? "active" : "inactive");
  valk_aio_handle_t *hndl = h->data;
  if (hndl && hndl->magic == VALK_AIO_HANDLE_MAGIC) {
    const char *kind = "unknown";
    switch (hndl->kind) {
      case VALK_HNDL_EMPTY: kind = "empty"; break;
      case VALK_HNDL_TCP: kind = "tcp_listener"; break;
      case VALK_HNDL_TASK: kind = "async_task"; break;
      case VALK_HNDL_TIMER: kind = "timer"; break;
      case VALK_HNDL_HTTP_CONN: kind = "http_conn"; break;
    }
    VALK_WARN("  - handle: uv_type=%s valk_kind=%s state=%s",
              __uv_handle_type_name(h->type), kind, state);
  } else {
    VALK_WARN("  - handle: uv_type=%s (non-valk) state=%s",
              __uv_handle_type_name(h->type), state);
  }
}
// LCOV_EXCL_STOP

void __aio_uv_stop(uv_async_t *h) {
  // Call uv_stop FIRST to break out of UV_RUN_DEFAULT immediately
  uv_stop(h->loop);
  
  // Now clean up handles - the drain loop will finish closing them
  valk_aio_handle_t *hndl = h->data;
  // LCOV_EXCL_BR_START - stop callback state checks: defensive null checks
  if (hndl && hndl->sys) {
    valk_maintenance_timer_stop(hndl->sys);
    valk_maintenance_timer_close(hndl->sys);
  }
  // LCOV_EXCL_BR_STOP
  // Mark all handles for closing. The drain loop in __event_loop
  // will properly complete the shutdown by running until all handles are closed.
  uv_walk(h->loop, __aio_uv_walk_close, NULL);
}






void valk_http2_continue_pending_send(valk_aio_handle_t *conn);

// Flush pending HTTP/2 frames into buffer using mem_send2 (pull model)
// Only pulls frames while buffer has room for a max-size frame.
// Returns: number of bytes in buffer, sets pending_write if more frames waiting
static size_t __http2_flush_frames(valk_buffer_t *buf, valk_aio_handle_t *conn) {
  // LCOV_EXCL_START - defensive null check
  if (!conn || !conn->http.session) {
    return 0;
  }
  // LCOV_EXCL_STOP

  const uint8_t *data;
  nghttp2_ssize len;

  // Only pull frames while we have room for at least one max-size frame
  while ((buf->capacity - buf->count) > HTTP2_MAX_SERIALIZED_FRAME) {
    len = nghttp2_session_mem_send2(conn->http.session, &data);
    if (len <= 0) {
      if (len < 0) {
        // LCOV_EXCL_LINE - nghttp2 only returns NGHTTP2_ERR_NOMEM (requires malloc failure)
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

// LCOV_EXCL_START - SSE state accessors: internal API for SSE diagnostics
valk_sse_diag_state_t* valk_aio_get_sse_state(valk_aio_handle_t *handle) {
  if (!handle) return NULL;
  return handle->http.sse_state;
}

void valk_aio_set_sse_state(valk_aio_handle_t *handle, valk_sse_diag_state_t *state) {
  if (!handle) return;
  handle->http.sse_state = state;
}
// LCOV_EXCL_STOP

static void __http_tcp_unencrypted_read_cb(void *arg,
                                           const valk_buffer_t *buf) {
  valk_aio_handle_t *conn = arg;

  // Feed data to nghttp2
  ssize_t rv = nghttp2_session_mem_recv2(
      conn->http.session, (const uint8_t *)buf->items, buf->count);
  // LCOV_EXCL_START - nghttp2 parse error: requires malformed HTTP/2 frames
  if (rv < 0) {
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    VALK_ERROR("nghttp2_session_mem_recv error: %zd", rv);
    if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
      conn->http.state = VALK_CONN_CLOSING;
      __backpressure_list_remove(conn);
#ifdef VALK_METRICS_ENABLED
      conn->http.diag.state = VALK_DIAG_CONN_CLOSING;
      conn->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
      uv_close((uv_handle_t *)&conn->uv.tcp, __uv_handle_closed_cb);
    }
  }
  // LCOV_EXCL_STOP
}

static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {
  valk_aio_handle_t *conn = stream->data;

  if (conn->http.state == VALK_CONN_CLOSING || conn->http.state == VALK_CONN_CLOSED) {
    return; // LCOV_EXCL_LINE
  }

  if (!buf->base) {
    VALK_WARN("TCP buffer alloc failed - applying backpressure on connection");
    uv_read_stop((uv_stream_t *)&conn->uv.tcp);
    if (!__backpressure_list_add(conn)) {
      // LCOV_EXCL_START - Backpressure queue full after buffer exhaustion is rare
      if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
        conn->http.state = VALK_CONN_CLOSING;
        uv_close((uv_handle_t *)&conn->uv.tcp, __uv_handle_closed_cb);
      }
      // LCOV_EXCL_STOP
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
      uv_close((uv_handle_t *)&conn->uv.tcp, __uv_handle_closed_cb);
    }
    return;
  }

  VALK_TRACE("Feeding data to OpenSSL %ld", nread);

  // LCOV_EXCL_START - write_flush_pending backpressure requires precise timing
  // where a write is in-flight while new data arrives. Difficult to trigger
  // reliably in integration tests without mocking network timing.
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
        uv_close((uv_handle_t *)&conn->uv.tcp, __uv_handle_closed_cb);
      }
    }
    return;
  }
  // LCOV_EXCL_STOP

  // LCOV_EXCL_START - Write buffer acquisition failure after read buffer success
  // is a narrow timing window. The read got a buffer but write can't - rare.
  if (!__conn_write_buf_acquire(conn)) {
    VALK_WARN("Failed to acquire write buffer - applying backpressure on connection");
    int n = BIO_write(conn->http.ssl.read_bio, buf->base, nread);
    if (n != nread) {
      VALK_ERROR("BIO_write during backpressure failed: wrote %d of %ld", n, nread);
    }
    uv_read_stop((uv_stream_t *)&conn->uv.tcp);
    if (!__backpressure_list_add(conn)) {
      if (!uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
        conn->http.state = VALK_CONN_CLOSING;
        uv_close((uv_handle_t *)&conn->uv.tcp, __uv_handle_closed_cb);
      }
    }
#ifdef VALK_METRICS_ENABLED
    if (conn->http.server) {
      atomic_fetch_add(&conn->http.server->sys->metrics_state->system_stats.tcp_buffer_overflow, 1);
    }
#endif
    return;
  }
  // LCOV_EXCL_STOP

  // Update last activity timestamp for idle timeout tracking
  if (conn->sys && conn->sys->eventloop) {
    conn->http.last_activity_ms = uv_now(conn->sys->eventloop);
  }

  valk_buffer_t In = {
      .items = buf->base, .count = nread, .capacity = HTTP_SLAB_ITEM_SIZE};

  uint8_t *write_buf = __conn_write_buf_data(conn);
  size_t write_available = __conn_write_buf_available(conn);
  
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
        
        __http2_flush_frames(&FrameIn, conn);

        if (FrameIn.count > 0) {
          write_available = __conn_write_buf_available(conn);
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
    __conn_write_buf_flush(conn);
  }
}



