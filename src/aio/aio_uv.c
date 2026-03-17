#include "aio_internal.h"
#include "gc.h"

u64 g_async_handle_id = 0;

static void __loop_gc_wake(void *ctx) {
  valk_aio_loop_t *loop = ctx;
  if (loop && loop->uv_loop && !loop->sys->shuttingDown) { // LCOV_EXCL_BR_LINE - GC wake: ctx/loop always valid
    uv_async_send(&loop->gc_wakeup);
  }
}

static void __uv_handle_closed_cb(uv_handle_t *handle);
static void __aio_uv_walk_close(uv_handle_t *h, void *arg);
static void __aio_uv_walk_diag(uv_handle_t *h, void *arg);
static const char* __uv_handle_type_name(uv_handle_type type);

static void __backpressure_list_remove(valk_aio_handle_t *conn) {
  valk_aio_system_t *sys = conn->sys;
  if (!sys) return; // LCOV_EXCL_BR_LINE
  valk_backpressure_list_remove(&sys->backpressure, conn);
}

void __gc_wakeup_cb(uv_async_t *handle) {
  (void)handle;
  VALK_GC_SAFE_POINT();
}

void __loop_stop_cb(uv_async_t *h) {
  valk_aio_loop_t *loop = h->data;
  uv_stop(loop->uv_loop);
  uv_timer_stop(&loop->maintenance_timer);
  if (!uv_is_closing((uv_handle_t *)&loop->maintenance_timer)) { // LCOV_EXCL_BR_LINE
    uv_close((uv_handle_t *)&loop->maintenance_timer, nullptr);
  }
  uv_walk(loop->uv_loop, __aio_uv_walk_close, nullptr);
}

void __loop_thread_fn(void *arg) {
  valk_aio_loop_t *loop = arg;
  valk_aio_system_t *sys = loop->sys;

  if (valk_sys->initialized) {
    valk_system_register_thread(valk_sys, __loop_gc_wake, loop);
  } else {
    valk_mem_init_malloc(); // LCOV_EXCL_LINE
  }

  sz scratch_bytes = 128ULL * 1024 * 1024;
  const char *scratch_env = getenv("VALK_SCRATCH_SIZE");
  if (scratch_env && scratch_env[0] != '\0') { // LCOV_EXCL_BR_LINE
    scratch_bytes = strtoull(scratch_env, nullptr, 10);
  }
  valk_mem_arena_t *scratch = malloc(scratch_bytes);
  valk_mem_arena_init(scratch, scratch_bytes - sizeof(*scratch));
  loop->scratch = scratch;
  valk_thread_ctx.scratch = scratch;
  valk_thread_ctx.checkpoint_threshold = VALK_CHECKPOINT_THRESHOLD_DEFAULT;
  valk_thread_ctx.checkpoint_enabled = true;

  VALK_DEBUG("Initializing event loop thread %u", loop->id);

  if (loop->id == 0) {
    sys->tcpBufferSlab =
        valk_slab_new(sizeof(__tcp_buffer_slab_item_t), sys->config.tcp_buffer_pool_size);
    VALK_INFO("Initialized %u TCP buffers (%zuKB each)",
              sys->config.tcp_buffer_pool_size, HTTP_SLAB_ITEM_SIZE / 1024);

    sys->httpStreamArenas = valk_slab_new(
        sizeof(valk_mem_arena_t) + sys->config.arena_size,
        sys->config.arena_pool_size);
    // LCOV_EXCL_START
    if (!sys->httpStreamArenas) {
      VALK_ERROR("Failed to allocate stream arena slab");
      return;
    }
    // LCOV_EXCL_STOP
    VALK_INFO("Initialized %u stream arenas (%zuKB each)",
              sys->config.arena_pool_size, sys->config.arena_size / 1024);
  }

  uv_timer_init(loop->uv_loop, &loop->maintenance_timer);
  loop->maintenance_timer.data = sys;
  if (loop->id == 0) {
    uv_timer_start(&loop->maintenance_timer, __loop_maintenance_timer_cb,
                   sys->config.maintenance_interval_ms,
                   sys->config.maintenance_interval_ms);
  }

  valk_aio_loop_task_queue_init(loop);

  valk_chase_lev_init(&loop->work_deque, 64);

  uv_sem_post(&loop->ready_sem);

  uv_run(loop->uv_loop, UV_RUN_DEFAULT);

  if (valk_sys->initialized) {
    valk_system_unregister_thread(valk_sys);
  }

  // Graceful Shutdown
  u64 drain_start = uv_hrtime();
  u64 graceful_drain_ns = 100ULL * 1000000ULL;
  u64 force_close_ns = 300ULL * 1000000ULL;
  u64 hard_deadline_ns = 500ULL * 1000000ULL;

  bool force_closed = false;
  bool logged_diagnostics = false;
  int iterations = 0;

  // LCOV_EXCL_START
  while (uv_loop_alive(loop->uv_loop)) {
    u64 elapsed = uv_hrtime() - drain_start;
    iterations++;

    if (elapsed < graceful_drain_ns) {
      uv_run(loop->uv_loop, UV_RUN_NOWAIT);
      continue;
    }
    if (!force_closed && elapsed >= graceful_drain_ns) {
      uv_walk(loop->uv_loop, __aio_uv_walk_close, nullptr);
      force_closed = true;
    }
    if (elapsed < force_close_ns) {
      uv_run(loop->uv_loop, UV_RUN_NOWAIT);
      continue;
    }
    if (!logged_diagnostics && elapsed >= force_close_ns) {
      __drain_diag_t diag = {0};
      VALK_WARN("Loop %u shutdown: force close exceeded 300ms", loop->id);
      uv_walk(loop->uv_loop, __aio_uv_walk_diag, &diag);
      VALK_WARN("Loop %u: %d handles remaining (%d active, %d closing)",
                loop->id, diag.count, diag.active, diag.closing);
      logged_diagnostics = true;
    }
    if (elapsed >= hard_deadline_ns) {
      VALK_ERROR("Loop %u: HARD DEADLINE exceeded (500ms, %d iterations)",
                 loop->id, iterations);
      break;
    }
    uv_run(loop->uv_loop, UV_RUN_NOWAIT);
  }
  // LCOV_EXCL_STOP

  valk_aio_loop_task_queue_shutdown(loop);
  valk_chase_lev_destroy(&loop->work_deque);

  if (loop->id == 0) {
    valk_slab_free(sys->tcpBufferSlab);
    valk_slab_free(sys->httpStreamArenas);
  }

  if (loop->scratch) { // LCOV_EXCL_BR_LINE - scratch always allocated in thread init
    free(loop->scratch);
    loop->scratch = nullptr;
  }

  uv_loop_close(loop->uv_loop);
  free(loop->uv_loop);
  loop->uv_loop = nullptr;
}

static void __uv_handle_closed_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  VALK_TRACE("UV handle closed %p", handle->data);

  // LCOV_EXCL_BR_START
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

  if (hndl->onClose != nullptr) {  // LCOV_EXCL_BR_LINE
    VALK_TRACE("Calling onClose callback");
    hndl->onClose(hndl);
  }
  valk_dll_pop(hndl);
  VALK_ASSERT(hndl->sys != nullptr, "handle must have sys for slab release");
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);
}

// LCOV_EXCL_START
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
