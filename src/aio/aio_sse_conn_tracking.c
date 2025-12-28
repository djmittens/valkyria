#include "aio_sse_conn_tracking.h"
#include "aio_internal.h"

void valk_sse_conn_stream_register(valk_sse_stream_t *stream) {
  if (!stream || !stream->conn) {
    return;
  }

  stream->next = stream->conn->http.sse_streams;
  stream->conn->http.sse_streams = stream;

  VALK_DEBUG("SSE: registered stream id=%llu with connection", (unsigned long long)stream->id);
}

void valk_sse_conn_stream_unregister(valk_sse_stream_t *stream) {
  if (!stream || !stream->conn) {
    return;
  }

  valk_sse_stream_t **pp = &stream->conn->http.sse_streams;
  while (*pp) {
    if (*pp == stream) {
      *pp = stream->next;
      stream->next = nullptr;
      VALK_DEBUG("SSE: unregistered stream id=%llu from connection", (unsigned long long)stream->id);
      return;
    }
    pp = &(*pp)->next;
  }

  VALK_WARN("SSE: stream id=%llu not found in connection's stream list", (unsigned long long)stream->id);
}

void valk_sse_conn_close_all_streams(valk_aio_handle_t *conn) {
  if (!conn) {
    return;
  }

  valk_sse_stream_t *stream = conn->http.sse_streams;
  u64 count = 0;

  while (stream) {
    valk_sse_stream_t *next = stream->next;

    valk_sse_stream_close(stream);

    stream = next;
    count++;
  }

  conn->http.sse_streams = nullptr;

  if (count > 0) {
    VALK_INFO("SSE: closed %llu streams on connection cleanup", (unsigned long long)count);
  }
}

void valk_sse_stream_register(valk_sse_stream_t *stream) {
  valk_sse_conn_stream_register(stream);
}

void valk_sse_stream_unregister(valk_sse_stream_t *stream) {
  valk_sse_conn_stream_unregister(stream);
}

void valk_sse_close_all_streams(valk_aio_handle_t *conn) {
  valk_sse_conn_close_all_streams(conn);
}
