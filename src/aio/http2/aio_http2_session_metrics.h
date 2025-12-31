#pragma once

#include "aio_metrics.h"
#include "aio_types.h"
#include "common.h"

#ifdef VALK_METRICS_ENABLED
#include <uv.h>
#include "aio_internal.h"
#include "metrics_v2.h"
#endif

static inline void valk_http2_metrics_on_header_recv(
    valk_http2_server_request_t *req, size_t name_len, size_t value_len) {
#ifdef VALK_METRICS_ENABLED
  req->bytes_recv += name_len + value_len + 4;
#else
  UNUSED(req); UNUSED(name_len); UNUSED(value_len);
#endif
}

static inline void valk_http2_metrics_on_stream_start(
    valk_aio_handle_t *conn) {
#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_on_stream_start(&conn->http.server->sys->metrics_state->metrics);

  if (conn->http.active_streams == 1) {
    conn->http.diag.state = VALK_DIAG_CONN_ACTIVE;
    conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
  }
#else
  UNUSED(conn);
#endif
}

static inline void valk_http2_metrics_on_arena_overflow_pending(
    valk_aio_handle_t *conn) {
#ifdef VALK_METRICS_ENABLED
  atomic_fetch_add(&conn->http.server->sys->metrics_state->system_stats.arena_pool_overflow, 1);
  valk_aio_system_stats_on_pending_enqueue(&conn->http.server->sys->metrics_state->system_stats);
#else
  UNUSED(conn);
#endif
}

static inline void valk_http2_metrics_on_arena_overflow_rejected(
    valk_aio_handle_t *conn) {
#ifdef VALK_METRICS_ENABLED
  valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, true, 0, 0, 0);
  atomic_fetch_add(&conn->http.server->sys->metrics_state->system_stats.arena_pool_overflow, 1);
  valk_counter_v2_inc(conn->http.server->metrics.overload_responses);
  valk_counter_v2_inc(conn->http.server->metrics.requests_server_error);
#else
  UNUSED(conn);
#endif
}

static inline void valk_http2_metrics_on_arena_acquire(
    valk_aio_handle_t *conn) {
#ifdef VALK_METRICS_ENABLED
  valk_aio_system_stats_on_arena_acquire(&conn->http.server->sys->metrics_state->system_stats);
#else
  UNUSED(conn);
#endif
}

static inline void valk_http2_metrics_on_request_init(
    valk_http2_server_request_t *req) {
#ifdef VALK_METRICS_ENABLED
  req->start_time_us = uv_hrtime() / 1000;
  req->bytes_sent = 0;
  req->bytes_recv = 0;
#else
  UNUSED(req);
#endif
}

static inline void valk_http2_metrics_on_sse_start(
    valk_aio_handle_t *conn) {
#ifdef VALK_METRICS_ENABLED
  valk_gauge_v2_inc(conn->http.server->metrics.sse_streams_active);
#else
  UNUSED(conn);
#endif
}

static inline void valk_http2_metrics_on_response_body(
    void *session, i32 stream_id, u64 body_len, const char *status) {
#ifdef VALK_METRICS_ENABLED
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data((nghttp2_session *)session, stream_id);
  if (req) {
    req->bytes_sent = body_len;
    req->status_code = atoi(status);
  }
#else
  UNUSED(session); UNUSED(stream_id); UNUSED(body_len); UNUSED(status);
#endif
}

static inline void valk_http2_metrics_on_frame_send_eof(
    void *session, i32 stream_id) {
#ifdef VALK_METRICS_ENABLED
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data((nghttp2_session *)session, stream_id);
  if (req) {
    req->response_sent_time_us = uv_hrtime() / 1000;
    req->response_complete = true;
  }
#else
  UNUSED(session); UNUSED(stream_id);
#endif
}

static inline void valk_http2_metrics_on_pending_stream_close(
    valk_aio_handle_t *conn, i32 stream_id) {
#ifdef VALK_METRICS_ENABLED
  if (conn->http.server && conn->http.server->sys) {
    valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, true, 0, 0, 0);
    valk_aio_system_stats_on_pending_drop(&conn->http.server->sys->metrics_state->system_stats);

    valk_server_metrics_t* m = &conn->http.server->metrics;
    valk_counter_v2_inc(m->requests_total);
    valk_counter_v2_inc(m->requests_server_error);

    VALK_INFO("Pending stream %d timeout: recorded as 5xx", stream_id);
  }
#else
  UNUSED(conn); UNUSED(stream_id);
#endif
}

static inline bool valk_http2_metrics_on_sse_stream_close(
    valk_aio_handle_t *conn, i32 stream_id) {
#ifdef VALK_METRICS_ENABLED
  if (conn->http.server && conn->http.stream_bodies) {
    valk_stream_body_t *body = conn->http.stream_bodies;
    while (body) {
      if (body->stream_id == stream_id) {
        VALK_INFO("Stream %d closing, decrementing SSE gauge", stream_id);
        valk_gauge_v2_dec(conn->http.server->metrics.sse_streams_active);
        return true;
      }
      body = body->next;
    }
  }
  return false;
#else
  UNUSED(conn); UNUSED(stream_id);
  return false;
#endif
}

static inline void valk_http2_metrics_on_stream_close(
    valk_aio_handle_t *conn, valk_http2_server_request_t *req,
    u32 error_code, bool was_sse_stream) {
#ifdef VALK_METRICS_ENABLED
  u64 end_time_us;
  if (req->response_complete && req->response_sent_time_us > 0) {
    end_time_us = req->response_sent_time_us;
  } else {
    end_time_us = uv_hrtime() / 1000;
  }
  u64 duration_us = end_time_us - req->start_time_us;
  bool is_error = (error_code != 0);
  u64 bytes_recv = req->bytes_recv + req->bodyLen;
  valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, is_error,
                                   duration_us, req->bytes_sent, bytes_recv);

  valk_server_metrics_t* m = &conn->http.server->metrics;

  valk_counter_v2_inc(m->requests_total);

  int status = req->status_code;
  if (status >= 200 && status < 300) {
    valk_counter_v2_inc(m->requests_success);
  } else if (status >= 400 && status < 500) {
    valk_counter_v2_inc(m->requests_client_error);
  } else if (status >= 500) {
    valk_counter_v2_inc(m->requests_server_error);
  }

  if (!was_sse_stream) {
    valk_histogram_v2_observe_us(m->request_duration, duration_us);
  } else {
    valk_histogram_v2_observe_us(m->sse_stream_duration, duration_us);
  }

  valk_counter_v2_add(m->bytes_sent, req->bytes_sent);
  valk_counter_v2_add(m->bytes_recv, bytes_recv);
#else
  UNUSED(conn); UNUSED(req); UNUSED(error_code); UNUSED(was_sse_stream);
#endif
}

static inline void valk_http2_metrics_on_arena_release(
    valk_aio_handle_t *conn) {
#ifdef VALK_METRICS_ENABLED
  valk_aio_system_stats_on_arena_release(&conn->http.server->sys->metrics_state->system_stats);
#else
  UNUSED(conn);
#endif
}

static inline void valk_http2_metrics_on_async_request_timeout(
    valk_aio_handle_t *conn, valk_http2_server_request_t *req,
    i32 stream_id, u32 error_code, bool was_sse_stream) {
#ifdef VALK_METRICS_ENABLED
  if (conn->http.server && conn->http.server->sys) {
    u64 end_time_us = uv_hrtime() / 1000;
    u64 duration_us = end_time_us - req->start_time_us;
    bool is_error = !was_sse_stream && (error_code != 0);
    valk_aio_metrics_on_stream_end(&conn->http.server->sys->metrics_state->metrics, is_error,
                                     duration_us, req->bytes_sent, req->bytes_recv);

    if (was_sse_stream) {
      valk_server_metrics_t* m = &conn->http.server->metrics;
      valk_histogram_v2_observe_us(m->sse_stream_duration, duration_us);
      VALK_INFO("SSE stream %d closed by client (already counted as 2xx)", stream_id);
    } else {
      valk_server_metrics_t* m = &conn->http.server->metrics;
      valk_counter_v2_inc(m->requests_total);
      valk_counter_v2_inc(m->requests_server_error);
      valk_histogram_v2_observe_us(m->request_duration, duration_us);
      VALK_INFO("Async request timeout: stream %d closed by client after %llu us",
                stream_id, (unsigned long long)duration_us);
    }
  }
#else
  UNUSED(conn); UNUSED(req); UNUSED(stream_id); UNUSED(error_code); UNUSED(was_sse_stream);
#endif
}

static inline void valk_http2_metrics_on_conn_idle(
    valk_aio_handle_t *conn) {
#ifdef VALK_METRICS_ENABLED
  if (conn->http.active_streams == 0) {
    conn->http.diag.state = VALK_DIAG_CONN_IDLE;
    conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
  }
#else
  UNUSED(conn);
#endif
}

static inline void valk_http2_metrics_on_pending_stream_acquire(
    valk_aio_system_t *sys, u64 wait_ms) {
#ifdef VALK_METRICS_ENABLED
  VALK_METRICS_IF(sys) {
    valk_aio_system_stats_on_arena_acquire(&VALK_SYSTEM_STATS(sys));
    valk_aio_system_stats_on_pending_dequeue(&VALK_SYSTEM_STATS(sys), wait_ms * 1000);
  }
#else
  UNUSED(sys); UNUSED(wait_ms);
#endif
}

static inline void valk_http2_metrics_on_pending_request_init(
    valk_http2_server_request_t *req, u64 wait_ms) {
#ifdef VALK_METRICS_ENABLED
  req->start_time_us = (uv_hrtime() / 1000) - (wait_ms * 1000);
  req->bytes_sent = 0;
  req->bytes_recv = 0;
#else
  UNUSED(req); UNUSED(wait_ms);
#endif
}
