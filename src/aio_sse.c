#include "aio_sse.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "log.h"
#include "memory.h"
#include "parser.h"

// ============================================================================
// Global State
// ============================================================================

// Global stream ID counter for debugging/tracking
static uint64_t g_sse_stream_id = 0;

// ============================================================================
// Constants
// ============================================================================

#define SSE_DEFAULT_QUEUE_MAX 1000
#define SSE_DEFAULT_BUFFER_SIZE 65536  // 64KB

// ============================================================================
// Static Function Declarations
// ============================================================================

static nghttp2_ssize __sse_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data);

static void __sse_event_free(valk_sse_event_t *event);

// Forward declaration from aio_sse_diagnostics.h
void valk_http2_flush_pending(valk_aio_handle_t *conn);

// ============================================================================
// Stream Lifecycle
// ============================================================================

valk_sse_stream_t *valk_sse_stream_new(
    valk_aio_handle_t *conn,
    nghttp2_session *session,
    int32_t stream_id,
    nghttp2_data_provider2 *data_prd_out) {

  if (!conn || !session || !data_prd_out) {
    VALK_ERROR("SSE: invalid arguments to valk_sse_stream_new");
    return NULL;
  }

  // Allocate stream struct
  valk_sse_stream_t *stream = malloc(sizeof(valk_sse_stream_t));
  if (!stream) {
    VALK_ERROR("SSE: failed to allocate stream struct");
    return NULL;
  }

  // Initialize all fields
  memset(stream, 0, sizeof(*stream));

  // Assign atomic ID
  stream->id = __atomic_fetch_add(&g_sse_stream_id, 1, __ATOMIC_RELAXED);

  // Set initial state
  stream->state = VALK_SSE_OPEN;

  // Store HTTP/2 context
  stream->conn = conn;
  stream->session = session;
  stream->stream_id = stream_id;

  // Set queue limits
  stream->queue_max = SSE_DEFAULT_QUEUE_MAX;

  // Allocate pending_data buffer
  stream->pending_capacity = SSE_DEFAULT_BUFFER_SIZE;
  stream->pending_data = malloc(stream->pending_capacity);
  if (!stream->pending_data) {
    VALK_ERROR("SSE: failed to allocate pending buffer");
    free(stream);
    return NULL;
  }

  // Start with data deferred (no events yet)
  stream->data_deferred = true;

  // Set up nghttp2 data provider
  data_prd_out->source.ptr = stream;
  data_prd_out->read_callback = __sse_data_read_callback;

  VALK_DEBUG("SSE: created stream id=%lu, http2_stream=%d", stream->id, stream_id);

  return stream;
}

void valk_sse_stream_close(valk_sse_stream_t *stream) {
  if (!stream) {
    return;
  }

  // Check if already closed
  if (stream->state == VALK_SSE_CLOSED) {
    return;
  }

  VALK_DEBUG("SSE: closing stream id=%lu (http2_stream=%d)", stream->id, stream->stream_id);

  // Set state to closed
  stream->state = VALK_SSE_CLOSED;

  // Free all queued events
  valk_sse_event_t *event = stream->queue_head;
  while (event) {
    valk_sse_event_t *next = event->next;
    __sse_event_free(event);
    event = next;
  }
  stream->queue_head = NULL;
  stream->queue_tail = NULL;
  stream->queue_len = 0;

  // Free pending_data buffer
  if (stream->pending_data) {
    free(stream->pending_data);
    stream->pending_data = NULL;
  }

  // Call on_close callback if set
  if (stream->on_close) {
    stream->on_close(stream, stream->user_data);
  }

  // TODO(networking): Call lisp_on_close if set (requires eval context)

  // Unregister from connection's stream list
  // Note: valk_sse_stream_unregister is implemented in aio_uv.c
  valk_sse_stream_unregister(stream);

  // Free the stream struct
  free(stream);
}

// Note: Connection tracking functions (register, unregister, close_all_streams)
// are implemented in aio_uv.c since they need access to valk_aio_handle_t internals

// ============================================================================
// Event Sending
// ============================================================================

int valk_sse_send_event(valk_sse_stream_t *stream, const char *event_type,
                        const char *data, size_t len, uint64_t id) {
  if (!stream || !data) {
    return -1;
  }

  // Validate stream is open
  if (stream->state != VALK_SSE_OPEN) {
    VALK_DEBUG("SSE: send_event failed, stream %lu not open (state=%d)",
               stream->id, stream->state);
    return -1;
  }

  // Check backpressure
  if (stream->queue_len >= stream->queue_max) {
    VALK_DEBUG("SSE: send_event backpressure, stream %lu queue full (%zu/%zu)",
               stream->id, stream->queue_len, stream->queue_max);
    return -2;  // EAGAIN - queue full
  }

  // Calculate event size (SSE format: "id: X\nevent: Y\ndata: Z\n\n")
  size_t event_size = 0;
  if (id > 0) {
    event_size += snprintf(NULL, 0, "id: %lu\n", id);
  }
  if (event_type) {
    event_size += snprintf(NULL, 0, "event: %s\n", event_type);
  }
  event_size += 6;  // "data: "
  event_size += len;
  event_size += 2;  // "\n\n"

  // Allocate event struct + buffer space
  valk_sse_event_t *event = malloc(sizeof(valk_sse_event_t) + event_size + 1);
  if (!event) {
    VALK_ERROR("SSE: failed to allocate event");
    return -3;
  }

  // Format SSE event into buffer
  char *buf = (char *)(event + 1);
  char *p = buf;

  if (id > 0) {
    p += sprintf(p, "id: %lu\n", id);
  }
  if (event_type) {
    p += sprintf(p, "event: %s\n", event_type);
  }
  p += sprintf(p, "data: ");
  memcpy(p, data, len);
  p += len;
  *p++ = '\n';
  *p++ = '\n';
  *p = '\0';

  // Set event fields
  event->data = buf;
  event->data_len = p - buf;
  event->event_type = NULL;  // Already formatted into buffer
  event->id = id;
  event->retry_ms = 0;
  event->next = NULL;

  // Enqueue to tail of queue
  if (stream->queue_tail) {
    stream->queue_tail->next = event;
  } else {
    stream->queue_head = event;
  }
  stream->queue_tail = event;
  stream->queue_len++;

  VALK_DEBUG("SSE: enqueued event to stream %lu (queue_len=%zu, event_size=%zu)",
             stream->id, stream->queue_len, event->data_len);

  // If data_deferred, resume the stream
  if (stream->data_deferred) {
    stream->data_deferred = false;
    int rv = nghttp2_session_resume_data(stream->session, stream->stream_id);
    if (rv != 0) {
      VALK_ERROR("SSE: failed to resume stream %d: %s",
                 stream->stream_id, nghttp2_strerror(rv));
      return -4;
    }
    valk_http2_flush_pending(stream->conn);
  }

  return 0;
}

int valk_sse_send(valk_sse_stream_t *stream, const char *data, size_t len) {
  // Wrapper calling valk_sse_send_event with NULL event_type and 0 id
  return valk_sse_send_event(stream, NULL, data, len, 0);
}

int valk_sse_send_retry(valk_sse_stream_t *stream, uint32_t retry_ms) {
  if (!stream) {
    return -1;
  }

  // Validate stream is open
  if (stream->state != VALK_SSE_OPEN) {
    return -1;
  }

  // Format retry directive: "retry: N\n\n"
  char buf[64];
  int len = snprintf(buf, sizeof(buf), "retry: %u\n\n", retry_ms);
  if (len < 0 || len >= (int)sizeof(buf)) {
    return -1;
  }

  // Send as raw data (use send_event with NULL type and 0 id)
  // Actually, we need to send it directly without the "data: " prefix
  // For now, we'll use the event sending mechanism

  // Check backpressure
  if (stream->queue_len >= stream->queue_max) {
    return -2;
  }

  // Allocate event
  valk_sse_event_t *event = malloc(sizeof(valk_sse_event_t) + len + 1);
  if (!event) {
    return -3;
  }

  // Copy retry directive
  char *event_buf = (char *)(event + 1);
  memcpy(event_buf, buf, len);
  event_buf[len] = '\0';

  event->data = event_buf;
  event->data_len = len;
  event->event_type = NULL;
  event->id = 0;
  event->retry_ms = retry_ms;
  event->next = NULL;

  // Enqueue
  if (stream->queue_tail) {
    stream->queue_tail->next = event;
  } else {
    stream->queue_head = event;
  }
  stream->queue_tail = event;
  stream->queue_len++;

  // Resume if deferred
  if (stream->data_deferred) {
    stream->data_deferred = false;
    nghttp2_session_resume_data(stream->session, stream->stream_id);
    valk_http2_flush_pending(stream->conn);
  }

  return 0;
}

// ============================================================================
// Backpressure
// ============================================================================

bool valk_sse_is_writable(valk_sse_stream_t *stream) {
  if (!stream) {
    return false;
  }
  return stream->queue_len < stream->queue_max;
}

size_t valk_sse_queue_len(valk_sse_stream_t *stream) {
  if (!stream) {
    return 0;
  }
  return stream->queue_len;
}

// ============================================================================
// Internal Functions
// ============================================================================

static void __sse_event_free(valk_sse_event_t *event) {
  if (!event) {
    return;
  }
  // event->data points into the buffer allocated with the event struct
  // event->event_type is not separately allocated in current implementation
  free(event);
}

static nghttp2_ssize __sse_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data) {

  UNUSED(session);
  UNUSED(stream_id);
  UNUSED(user_data);

  // Extract stream from source->ptr
  valk_sse_stream_t *stream = (valk_sse_stream_t *)source->ptr;

  if (!stream) {
    VALK_ERROR("SSE: data_read_callback called with NULL stream");
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  // If closed, set EOF flag and return 0
  if (stream->state == VALK_SSE_CLOSED) {
    VALK_DEBUG("SSE: stream %lu closed, returning EOF", stream->id);
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  // If pending_offset < pending_len, copy remaining pending data
  if (stream->pending_offset < stream->pending_len) {
    size_t remaining = stream->pending_len - stream->pending_offset;
    size_t to_send = remaining < length ? remaining : length;
    memcpy(buf, stream->pending_data + stream->pending_offset, to_send);
    stream->pending_offset += to_send;

    VALK_DEBUG("SSE: stream %lu flushing pending (%zu bytes, %zu remaining)",
               stream->id, to_send, remaining - to_send);

    return (nghttp2_ssize)to_send;
  }

  // If queue empty, set data_deferred=true and return NGHTTP2_ERR_DEFERRED
  if (!stream->queue_head) {
    stream->data_deferred = true;
    VALK_DEBUG("SSE: stream %lu queue empty, deferring", stream->id);
    return NGHTTP2_ERR_DEFERRED;
  }

  // Dequeue next event
  valk_sse_event_t *event = stream->queue_head;
  stream->queue_head = event->next;
  if (!stream->queue_head) {
    stream->queue_tail = NULL;
  }
  stream->queue_len--;

  // Copy event data to pending buffer (grow if needed)
  if (event->data_len > stream->pending_capacity) {
    size_t new_capacity = event->data_len;
    char *new_buf = realloc(stream->pending_data, new_capacity);
    if (!new_buf) {
      VALK_ERROR("SSE: failed to grow pending buffer for stream %lu", stream->id);
      __sse_event_free(event);
      *data_flags |= NGHTTP2_DATA_FLAG_EOF;
      return 0;
    }
    stream->pending_data = new_buf;
    stream->pending_capacity = new_capacity;
  }

  memcpy(stream->pending_data, event->data, event->data_len);
  stream->pending_len = event->data_len;
  stream->pending_offset = 0;

  // Update stats
  stream->events_sent++;
  stream->bytes_sent += event->data_len;

  VALK_DEBUG("SSE: stream %lu dequeued event (size=%zu, queue_len=%zu, total_events=%lu)",
             stream->id, event->data_len, stream->queue_len, stream->events_sent);

  // Free the event
  __sse_event_free(event);

  // Copy from pending to output buffer
  size_t to_send = stream->pending_len < length ? stream->pending_len : length;
  memcpy(buf, stream->pending_data, to_send);
  stream->pending_offset = to_send;

  // If queue dropped below queue_max/2 and on_drain is set, call it
  if (stream->queue_len < stream->queue_max / 2 && stream->on_drain) {
    VALK_DEBUG("SSE: stream %lu calling on_drain (queue_len=%zu)",
               stream->id, stream->queue_len);
    stream->on_drain(stream, stream->user_data);
  }

  // Don't set EOF - this is a streaming response
  return (nghttp2_ssize)to_send;
}
