#include "aio_stream_body.h"
#include "aio_internal.h"

void valk_stream_body_register(valk_stream_body_t *body) {
  if (!body || !body->conn) {
    return;
  }

  body->next = body->conn->http.stream_bodies;
  body->conn->http.stream_bodies = body;

  VALK_DEBUG("stream_body: registered body id=%llu with connection",
             (unsigned long long)body->id);
}

void valk_stream_body_unregister(valk_stream_body_t *body) {
  if (!body || !body->conn) {
    return;
  }

  valk_stream_body_t **pp = &body->conn->http.stream_bodies;
  while (*pp) {
    if (*pp == body) {
      *pp = body->next;
      body->next = nullptr;
      VALK_DEBUG("stream_body: unregistered body id=%llu from connection",
                 (unsigned long long)body->id);
      return;
    }
    pp = &(*pp)->next;
  }

  VALK_WARN("stream_body: body id=%llu not found in connection's stream list",
            (unsigned long long)body->id);
}

void valk_stream_body_close_by_stream_id(valk_aio_handle_t *conn, i32 stream_id) {
  if (!conn) {
    return;
  }

  valk_stream_body_t *body = conn->http.stream_bodies;
  while (body) {
    if (body->stream_id == stream_id) {
      VALK_INFO("stream_body: closing body id=%llu for stream %d on stream close",
                (unsigned long long)body->id, stream_id);
      valk_stream_body_close(body);
      return;
    }
    body = body->next;
  }
}

void valk_stream_body_close_all(valk_aio_handle_t *conn) {
  if (!conn) {
    return;
  }

  valk_stream_body_t *body = conn->http.stream_bodies;
  u64 count = 0;

  while (body) {
    valk_stream_body_t *next = body->next;
    valk_stream_body_close(body);
    body = next;
    count++;
  }

  conn->http.stream_bodies = nullptr;

  if (count > 0) {
    VALK_INFO("stream_body: closed %llu bodies on connection cleanup",
              (unsigned long long)count);
  }
}

u64 valk_stream_body_get_bytes_sent(valk_aio_handle_t *conn, i32 stream_id) {
  if (!conn) {
    return 0;
  }

  valk_stream_body_t *body = conn->http.stream_bodies;
  while (body) {
    if (body->stream_id == stream_id) {
      return body->bytes_sent;
    }
    body = body->next;
  }
  return 0;
}

void valk_stream_body_check_orphaned(valk_aio_handle_t *conn) {
  if (!conn || !conn->http.session) {
    return;
  }

  valk_stream_body_t *body = conn->http.stream_bodies;
  while (body) {
    valk_stream_body_t *next = body->next;

    if (body->state != VALK_STREAM_OPEN) {
      body = next;
      continue;
    }

    nghttp2_stream *stream = nghttp2_session_find_stream(body->session, body->stream_id);
    if (!stream) {
      VALK_WARN("BUG: orphaned stream body id=%llu http2_stream=%d (stream gone but body not closed) - "
                "this indicates a missing cleanup path, please report",
                (unsigned long long)body->id, body->stream_id);
      valk_stream_body_close(body);
    } else if (valk_stream_body_is_idle_expired(body)) {
      VALK_INFO("stream_body: idle timeout for id=%llu http2_stream=%d, closing",
                (unsigned long long)body->id, body->stream_id);
      valk_stream_body_cancel(body, NGHTTP2_NO_ERROR);
    }

    body = next;
  }
}
