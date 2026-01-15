#include "aio_internal.h"
#include <execinfo.h>

u64 g_async_handle_id = 0;

static void __uv_handle_closed_cb(uv_handle_t *handle);
static void __aio_uv_walk_close(uv_handle_t *h, void *arg);
static void __aio_uv_walk_diag(uv_handle_t *h, void *arg);
static const char* __uv_handle_type_name(uv_handle_type type);

static void __backpressure_list_remove(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return; // LCOV_EXCL_BR_LINE
  valk_backpressure_list_remove(&sys->backpressure, conn);
}











void __event_loop(void *arg) {
  valk_aio_system_t *sys = arg;

  if (sys->config.thread_onboard_fn) {
    sys->config.thread_onboard_fn();
    VALK_DEBUG("Event loop thread onboarded via config callback");
  } else {
    valk_mem_init_malloc();
    valk_gc_thread_register();

    valk_gc_malloc_heap_t *gc_heap = valk_gc_malloc_heap_init(0);
    if (!gc_heap) { // LCOV_EXCL_BR_LINE
      VALK_ERROR("Failed to create event loop GC heap");
    } else {
      valk_thread_ctx.heap = gc_heap;
      sys->loop_gc_heap = gc_heap;
      VALK_DEBUG("Created event loop GC heap: %p", gc_heap);
    }
  }

  VALK_DEBUG("Initializing UV event loop thread");

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

  valk_aio_task_queue_init(sys);

  // Signal that event loop is ready (all slabs initialized)
  uv_sem_post(&sys->startup_sem);

  sys->ops->loop->run(sys, VALK_IO_RUN_DEFAULT);

  // =========================================================================
  // Graceful Shutdown (modeled after Finagle/Netty)
  // =========================================================================
  // Phase 1: Graceful drain - allow pending I/O to complete
  // Phase 2: Force close - close any remaining handles
  // Phase 3: Hard deadline - log diagnostics and exit
  //
  // Total shutdown budget: 500ms (generous for tests, fast enough for prod)
  
  u64 drain_start = sys->ops->loop->hrtime();
  u64 graceful_drain_ns = 100ULL * 1000000ULL;  // 100ms graceful
  u64 force_close_ns = 300ULL * 1000000ULL;     // 300ms for force close
  u64 hard_deadline_ns = 500ULL * 1000000ULL;   // 500ms hard deadline
  
  bool force_closed = false;
  bool logged_diagnostics = false;
  int iterations = 0;
  
  // LCOV_EXCL_START - shutdown drain loop timing-dependent, rarely entered in tests
  while (sys->ops->loop->alive(sys)) {
    u64 elapsed = sys->ops->loop->hrtime() - drain_start;
    iterations++;
    
    // Phase 1: Graceful drain with UV_RUN_ONCE (allows I/O to complete)
    if (elapsed < graceful_drain_ns) {
      sys->ops->loop->run(sys, VALK_IO_RUN_NOWAIT);
      continue;
    }
    // Phase 2: Force close all remaining handles
    if (!force_closed && elapsed >= graceful_drain_ns) {
      VALK_DEBUG("Shutdown: graceful drain exceeded 100ms, force closing handles");
      uv_walk(sys->eventloop, __aio_uv_walk_close, nullptr);
      force_closed = true;
    }
    
    // Continue draining after force close
    if (elapsed < force_close_ns) {
      sys->ops->loop->run(sys, VALK_IO_RUN_NOWAIT);
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
    
    sys->ops->loop->run(sys, VALK_IO_RUN_NOWAIT);
  }
  // LCOV_EXCL_STOP
  
  u64 total_drain_ms = (sys->ops->loop->hrtime() - drain_start) / 1000000ULL;
  if (total_drain_ms > 50) {  // LCOV_EXCL_BR_LINE
    VALK_INFO("Shutdown: drain completed in %llu ms (%d iterations)",  // LCOV_EXCL_LINE
              (unsigned long long)total_drain_ms, iterations);  // LCOV_EXCL_LINE
  }

  valk_aio_task_queue_shutdown(sys);

  valk_slab_free(sys->tcpBufferSlab);
  valk_slab_free(sys->httpStreamArenas);

  if (sys->loop_gc_heap) {
    valk_gc_malloc_heap_destroy(sys->loop_gc_heap);
    sys->loop_gc_heap = nullptr;
  }
  
  valk_gc_thread_unregister();
}

static void __uv_handle_closed_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  VALK_TRACE("UV handle closed %p", handle->data);
  
  // LCOV_EXCL_BR_START - buffer release null checks: defensive for partially initialized handles
  if (hndl->kind == VALK_HNDL_HTTP_CONN) {
    __backpressure_list_remove(hndl);
    
    if (hndl->http.io.read_buf && hndl->sys && hndl->sys->tcpBufferSlab) {
      valk_slab_release(hndl->sys->tcpBufferSlab, hndl->http.io.read_buf);
      hndl->http.io.read_buf = nullptr;
    }
    if (hndl->http.io.write_buf && hndl->sys && hndl->sys->tcpBufferSlab) {
      valk_slab_release(hndl->sys->tcpBufferSlab, hndl->http.io.write_buf);
      hndl->http.io.write_buf = nullptr;
    }
  }
  // LCOV_EXCL_BR_STOP
  
  if (hndl->onClose != nullptr) {  // LCOV_EXCL_BR_LINE - onClose callback presence
    VALK_TRACE("Calling onClose callback");
    hndl->onClose(hndl);
  }
  valk_dll_pop(hndl);
  VALK_ASSERT(hndl->sys != nullptr, "handle must have sys for slab release"); // LCOV_EXCL_BR_LINE
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
        valk_conn_transition(hndl, VALK_CONN_EVT_CLOSE);
        __backpressure_list_remove(hndl);
      }
      uv_close(h, __uv_handle_closed_cb);
    } else {
      uv_close(h, nullptr);
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
    const char *kind = "unknown";  // NOLINT(clang-analyzer-deadcode.DeadStores)
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
  uv_walk(h->loop, __aio_uv_walk_close, nullptr);
}



