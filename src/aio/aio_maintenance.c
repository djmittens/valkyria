#include "aio_maintenance.h"
#include "aio_internal.h"
#include "aio_backpressure.h"
#include "aio_pending_stream.h"
#include "aio_http2_conn.h"

static void __maintenance_timer_close_cb(uv_handle_t *handle) {
  UNUSED(handle);
}

static void __maintenance_timer_cb(uv_timer_t *timer) {
  valk_aio_system_t *sys = timer->data;
  if (!sys || sys->shuttingDown) return;

  uint64_t now = uv_now(sys->eventloop);

  valk_maintenance_check_connection_timeouts(sys, now);
  valk_maintenance_check_pending_stream_timeouts(sys, now);
  valk_maintenance_check_backpressure_timeouts(sys, now);
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
  if (!uv_is_closing((uv_handle_t *)&sys->maintenance_timer)) {
    uv_close((uv_handle_t *)&sys->maintenance_timer, __maintenance_timer_close_cb);
  }
}

void valk_maintenance_check_connection_timeouts(valk_aio_system_t *sys, uint64_t now) {
  if (sys->config.connection_idle_timeout_ms == 0) return;
  
  valk_aio_handle_t *h = sys->liveHandles.next;
  while (h && h != &sys->liveHandles) {
    valk_aio_handle_t *next = h->next;
    if (h->kind == VALK_HNDL_HTTP_CONN && 
        h->http.state == VALK_CONN_ESTABLISHED &&
        h->http.last_activity_ms > 0) {
      uint64_t idle_time = now - h->http.last_activity_ms;
      if (idle_time > sys->config.connection_idle_timeout_ms) {
        VALK_INFO("Connection idle timeout after %llu ms (limit: %u ms)",
                  (unsigned long long)idle_time, sys->config.connection_idle_timeout_ms);
        if (!uv_is_closing((uv_handle_t *)&h->uv.tcp)) {
          h->http.state = VALK_CONN_CLOSING;
          valk_backpressure_list_remove(&sys->backpressure, h);
#ifdef VALK_METRICS_ENABLED
          h->http.diag.state = VALK_DIAG_CONN_CLOSING;
          h->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
          uv_close((uv_handle_t *)&h->uv.tcp, valk_http2_conn_handle_closed_cb);
        }
      }
    }
    h = next;
  }
}

void valk_maintenance_check_pending_stream_timeouts(valk_aio_system_t *sys, uint64_t now) {
  if (sys->config.pending_stream_timeout_ms == 0) return;
  
  pending_stream_t *ps = sys->pending_streams.head;
  while (ps) {
    pending_stream_t *next_ps = ps->next;
    uint64_t age = now - ps->queued_time_ms;
    if (age > sys->config.pending_stream_timeout_ms) {
      VALK_WARN("Pending stream %d timeout after %llu ms",
                ps->stream_id, (unsigned long long)age);
      if (ps->session) {
        nghttp2_submit_rst_stream(ps->session, NGHTTP2_FLAG_NONE,
                                   ps->stream_id, NGHTTP2_REFUSED_STREAM);
        nghttp2_session_send(ps->session);
      }
      valk_pending_stream_remove(&sys->pending_streams, ps);
    }
    ps = next_ps;
  }
}

void valk_maintenance_check_backpressure_timeouts(valk_aio_system_t *sys, uint64_t now) {
  if (sys->config.backpressure_timeout_ms == 0) return;
  
  valk_aio_handle_t *expired[16];
  size_t count = valk_backpressure_list_timeout_expired(
      &sys->backpressure, now, expired, 16);
  for (size_t i = 0; i < count; i++) {
    valk_aio_handle_t *bp = expired[i];
    VALK_WARN("Connection backpressure timeout");
    if (!uv_is_closing((uv_handle_t *)&bp->uv.tcp)) {
      bp->http.state = VALK_CONN_CLOSING;
#ifdef VALK_METRICS_ENABLED
      bp->http.diag.state = VALK_DIAG_CONN_CLOSING;
      bp->http.diag.state_change_time = (uint64_t)(uv_hrtime() / 1000000ULL);
#endif
      uv_close((uv_handle_t *)&bp->uv.tcp, valk_http2_conn_handle_closed_cb);
    }
  }
}
