#pragma once

#include "aio_metrics.h"
#include "aio_metrics_v2.h"
#include "aio_types.h"
#include "common.h"
#include <uv.h>
#include "aio_internal.h"
#include "metrics_v2.h"

static inline void valk_http2_metrics_on_header_recv(
    valk_http2_server_request_t *req, size_t name_len, size_t value_len) {
  req->bytes_recv += name_len + value_len + 4;
}

static inline void valk_http2_metrics_on_stream_start(
    valk_aio_handle_t *conn) {
  valk_aio_metrics_v2_on_stream_start(
      (valk_aio_metrics_v2_t*)conn->http.server->sys->metrics_state->metrics_v2);

  if (conn->http.active_streams == 1) {
    conn->http.diag.state = VALK_DIAG_CONN_ACTIVE;
    conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
  }
}

static inline void valk_http2_metrics_on_arena_overflow_rejected(
    valk_aio_handle_t *conn) {
  valk_aio_metrics_v2_on_stream_end(
      (valk_aio_metrics_v2_t*)conn->http.server->sys->metrics_state->metrics_v2,
      true, 0, 0, 0);
  valk_aio_system_stats_v2_on_arena_overflow(
      (valk_aio_system_stats_v2_t*)conn->http.server->sys->metrics_state->system_stats_v2);
  valk_counter_v2_inc(conn->http.server->metrics.overload_responses);
  valk_counter_v2_inc(conn->http.server->metrics.requests_server_error);
}

static inline void valk_http2_metrics_on_arena_acquire(
    valk_aio_handle_t *conn) {
  valk_aio_system_stats_v2_on_arena_acquire(
      (valk_aio_system_stats_v2_t*)conn->http.server->sys->metrics_state->system_stats_v2);
}

static inline void valk_http2_metrics_on_request_init(
    valk_http2_server_request_t *req) {
  req->start_time_us = uv_hrtime() / 1000;
  req->bytes_sent = 0;
  req->bytes_recv = 0;
}

static inline void valk_http2_metrics_on_sse_start(
    valk_aio_handle_t *conn) {
  valk_gauge_v2_inc(conn->http.server->metrics.sse_streams_active);
}

static inline void valk_http2_metrics_on_response_body(
    void *session, i32 stream_id, u64 body_len, const char *status) {
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data((nghttp2_session *)session, stream_id);
  if (req) {
    req->bytes_sent = body_len;
    req->status_code = atoi(status);
  }
}

static inline void valk_http2_metrics_on_frame_send_eof(
    void *session, i32 stream_id) {
  valk_http2_server_request_t *req =
      nghttp2_session_get_stream_user_data((nghttp2_session *)session, stream_id);
  if (req) {
    req->response_sent_time_us = uv_hrtime() / 1000;
    req->response_complete = true;
  }
}

static inline bool valk_http2_metrics_on_sse_stream_close(
    valk_aio_handle_t *conn, i32 stream_id) {
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
}

static inline void valk_http2_metrics_on_stream_close(
    valk_aio_handle_t *conn, valk_http2_server_request_t *req,
    u32 error_code, bool was_sse_stream, u64 stream_body_bytes) {
  u64 end_time_us;
  if (req->response_complete && req->response_sent_time_us > 0) {
    end_time_us = req->response_sent_time_us;
  } else {
    end_time_us = uv_hrtime() / 1000;
  }
  u64 duration_us = end_time_us - req->start_time_us;
  bool is_error = (error_code != 0);
  u64 bytes_recv = req->bytes_recv + req->bodyLen;
  u64 non_body_bytes_sent = req->bytes_sent > stream_body_bytes ? req->bytes_sent - stream_body_bytes : 0;
  valk_aio_metrics_v2_on_stream_end(
      (valk_aio_metrics_v2_t*)conn->http.server->sys->metrics_state->metrics_v2,
      is_error, duration_us, non_body_bytes_sent, bytes_recv);

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

  u64 non_body_bytes = req->bytes_sent > stream_body_bytes ? req->bytes_sent - stream_body_bytes : 0;
  valk_counter_v2_add(m->bytes_sent, non_body_bytes);
  valk_counter_v2_add(m->bytes_recv, bytes_recv);
}

static inline void valk_http2_metrics_on_arena_release(
    valk_aio_handle_t *conn) {
  valk_aio_system_stats_v2_on_arena_release(
      (valk_aio_system_stats_v2_t*)conn->http.server->sys->metrics_state->system_stats_v2);
}

static inline void valk_http2_metrics_on_client_close(
    valk_aio_handle_t *conn, valk_http2_server_request_t *req,
    i32 stream_id, u32 error_code, bool was_sse_stream, u64 stream_body_bytes) {
  if (conn->http.server && conn->http.server->sys) {
    u64 end_time_us = uv_hrtime() / 1000;
    u64 duration_us = end_time_us - req->start_time_us;
    u64 non_body_bytes_sent = req->bytes_sent > stream_body_bytes ? req->bytes_sent - stream_body_bytes : 0;
    
    valk_aio_metrics_v2_on_stream_end(
        (valk_aio_metrics_v2_t*)conn->http.server->sys->metrics_state->metrics_v2,
        false, duration_us, non_body_bytes_sent, req->bytes_recv);

    if (was_sse_stream) {
      valk_server_metrics_t* m = &conn->http.server->metrics;
      valk_histogram_v2_observe_us(m->sse_stream_duration, duration_us);
      VALK_DEBUG("SSE stream %d closed by client (already counted as 2xx)", stream_id);
    } else {
      VALK_DEBUG("Stream %d closed by client before response (error_code=%u, duration=%llu us)",
                stream_id, error_code, (unsigned long long)duration_us);
    }
  }
}

static inline void valk_http2_metrics_on_conn_idle(
    valk_aio_handle_t *conn) {
  if (conn->http.active_streams == 0) {
    conn->http.diag.state = VALK_DIAG_CONN_IDLE;
    conn->http.diag.state_change_time = (u64)(uv_hrtime() / 1000000ULL);
  }
}
