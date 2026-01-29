#include "aio_maintenance.h"
#include "aio_internal.h"
#include "aio_overload_backpressure.h"
#include "aio_http2_conn.h"
#include "aio_stream_body.h"

static inline const valk_io_tcp_ops_t *__tcp_ops(valk_aio_handle_t *conn) {
  return conn->sys ? conn->sys->ops->tcp : nullptr; // LCOV_EXCL_BR_LINE
}

static inline valk_io_tcp_t *__conn_tcp(valk_aio_handle_t *conn) {
  return &conn->uv.tcp;
}

static inline bool __vtable_is_closing(valk_aio_handle_t *conn) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return true; // LCOV_EXCL_BR_LINE
  return tcp->is_closing(__conn_tcp(conn));
}

static inline void __vtable_close(valk_aio_handle_t *conn, valk_io_close_cb cb) {
  const valk_io_tcp_ops_t *tcp = __tcp_ops(conn);
  if (!tcp) return; // LCOV_EXCL_BR_LINE
  tcp->close(__conn_tcp(conn), cb);
}

static void __maintenance_timer_close_cb(uv_handle_t *handle) {
  UNUSED(handle);
}

void valk_maintenance_check_orphaned_streams(valk_aio_system_t *sys);

static void __maintenance_timer_cb(uv_timer_t *timer) {
  valk_aio_system_t *sys = timer->data;
  if (!sys || sys->shuttingDown) return; // LCOV_EXCL_BR_LINE
  
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE

  u64 now = sys->ops->loop->now(sys);

  valk_maintenance_check_connection_timeouts(sys, now);
  valk_maintenance_check_backpressure_timeouts(sys, now);
  valk_maintenance_check_orphaned_streams(sys);
}

void valk_maintenance_timer_init(valk_aio_system_t *sys) {
  uv_timer_init(sys->eventloop, &sys->maintenance_timer);
  sys->maintenance_timer.data = sys;
}

void valk_maintenance_timer_start(valk_aio_system_t *sys) {
  uv_timer_start(&sys->maintenance_timer, __maintenance_timer_cb,
                 sys->config.maintenance_interval_ms,
                 sys->config.maintenance_interval_ms);
  VALK_INFO("Started maintenance timer (interval: %u ms)",
            sys->config.maintenance_interval_ms);
}

void valk_maintenance_timer_stop(valk_aio_system_t *sys) {
  uv_timer_stop(&sys->maintenance_timer);
}

void valk_maintenance_timer_close(valk_aio_system_t *sys) {
  if (!uv_is_closing((uv_handle_t *)&sys->maintenance_timer)) { // LCOV_EXCL_BR_LINE
    uv_close((uv_handle_t *)&sys->maintenance_timer, __maintenance_timer_close_cb);
  }
}

void valk_maintenance_check_connection_timeouts(valk_aio_system_t *sys, u64 now) {
  if (sys->config.connection_idle_timeout_ms == 0) return; // LCOV_EXCL_BR_LINE
  
  valk_aio_handle_t *h = sys->liveHandles.next;
  while (h && h != &sys->liveHandles) { // LCOV_EXCL_BR_LINE
    valk_aio_handle_t *next = h->next;
    if (h->kind == VALK_HNDL_HTTP_CONN && // LCOV_EXCL_BR_LINE
        h->http.state == VALK_CONN_ESTABLISHED && // LCOV_EXCL_BR_LINE
        h->http.last_activity_ms > 0) {
      u64 idle_time = now - h->http.last_activity_ms;
      // LCOV_EXCL_START - timeout path requires specific runtime state
      if (idle_time > sys->config.connection_idle_timeout_ms) {
        VALK_INFO("Connection idle timeout after %llu ms (limit: %u ms)",
                  (unsigned long long)idle_time, sys->config.connection_idle_timeout_ms);
        if (!__vtable_is_closing(h)) {
          valk_conn_transition(h, VALK_CONN_EVT_TIMEOUT);
          valk_backpressure_list_remove(&sys->backpressure, h);
          __vtable_close(h, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
        }
      }
      // LCOV_EXCL_STOP
    }
    h = next;
  }
}

void valk_maintenance_check_backpressure_timeouts(valk_aio_system_t *sys, u64 now) {
  if (sys->config.backpressure_timeout_ms == 0) return; // LCOV_EXCL_BR_LINE
  
  valk_aio_handle_t *expired[16];
  u64 count = valk_backpressure_list_timeout_expired(
      &sys->backpressure, now, expired, 16); // LCOV_EXCL_BR_LINE
  // LCOV_EXCL_START - timeout path requires specific runtime state
  for (u64 i = 0; i < count; i++) {
    valk_aio_handle_t *bp = expired[i];
    VALK_WARN("Connection backpressure timeout");
    if (!__vtable_is_closing(bp)) {
      valk_conn_transition(bp, VALK_CONN_EVT_TIMEOUT);
      __vtable_close(bp, (valk_io_close_cb)valk_http2_conn_handle_closed_cb);
    }
  }
  // LCOV_EXCL_STOP
}

void valk_maintenance_check_orphaned_streams(valk_aio_system_t *sys) {
  valk_aio_handle_t *h = sys->liveHandles.next;
  while (h && h != &sys->liveHandles) { // LCOV_EXCL_BR_LINE
    valk_aio_handle_t *next = h->next;
    if (h->kind == VALK_HNDL_HTTP_CONN && // LCOV_EXCL_BR_LINE
        h->http.state == VALK_CONN_ESTABLISHED && // LCOV_EXCL_BR_LINE
        h->http.stream_bodies != nullptr) {
      // LCOV_EXCL_START - orphaned stream path requires specific runtime state
      valk_stream_body_check_orphaned(h);
      // LCOV_EXCL_STOP
    }
    h = next;
  }
}
