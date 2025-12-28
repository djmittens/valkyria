#include "sse_test.h"

#include <stdlib.h>
#include <string.h>

#define SSE_TEST_CAPTURE_INITIAL_CAP 4096
#define SSE_TEST_QUEUE_MAX 1000

typedef struct test_event {
  char *event_type;
  char *data;
  u64 data_len;
  struct test_event *next;
} test_event_t;

struct valk_test_sse_ctx {
  char *capture_buf;
  u64 capture_len;
  u64 capture_cap;

  u64 event_count;
  u64 bytes_written;

  test_event_t *events;
  test_event_t *events_tail;

  void (*saved_on_drain)(valk_sse_stream_t *stream, void *user_data);
  void (*saved_on_close)(valk_sse_stream_t *stream, void *user_data);
  void (*saved_on_timeout)(valk_sse_stream_t *stream, void *user_data);
  void *saved_user_data;
};

static bool __is_test_stream(valk_sse_stream_t *stream) {
  return stream && stream->conn == nullptr && stream->session == nullptr;
}

static valk_test_sse_ctx_t *__get_ctx(valk_sse_stream_t *stream) {
  if (!stream) return nullptr;
  return (valk_test_sse_ctx_t *)stream->user_data;
}

static void __capture_append(valk_test_sse_ctx_t *ctx, const char *data, u64 len) {
  if (!ctx || !data || len == 0) return;

  u64 needed = ctx->capture_len + len + 1;
  if (needed > ctx->capture_cap) {
    u64 new_cap = ctx->capture_cap * 2;
    while (new_cap < needed) new_cap *= 2;
    char *new_buf = realloc(ctx->capture_buf, new_cap);
    if (!new_buf) return;
    ctx->capture_buf = new_buf;
    ctx->capture_cap = new_cap;
  }

  memcpy(ctx->capture_buf + ctx->capture_len, data, len);
  ctx->capture_len += len;
  ctx->capture_buf[ctx->capture_len] = '\0';
}

static void __store_event(valk_test_sse_ctx_t *ctx, const char *event_type, const char *data, u64 data_len) {
  if (!ctx) return;

  test_event_t *evt = malloc(sizeof(test_event_t));
  if (!evt) return;

  evt->event_type = event_type ? strdup(event_type) : nullptr;
  evt->data = nullptr;
  evt->data_len = 0;
  evt->next = nullptr;

  if (data && data_len > 0) {
    evt->data = malloc(data_len + 1);
    if (evt->data) {
      memcpy(evt->data, data, data_len);
      evt->data[data_len] = '\0';
      evt->data_len = data_len;
    }
  }

  if (ctx->events_tail) {
    ctx->events_tail->next = evt;
  } else {
    ctx->events = evt;
  }
  ctx->events_tail = evt;
}

static void __free_events(test_event_t *events) {
  while (events) {
    test_event_t *next = events->next;
    free(events->event_type);
    free(events->data);
    free(events);
    events = next;
  }
}

valk_sse_stream_t *valk_test_sse_create(void) {
  valk_sse_stream_t *stream = calloc(1, sizeof(valk_sse_stream_t));
  if (!stream) return nullptr;

  valk_test_sse_ctx_t *ctx = calloc(1, sizeof(valk_test_sse_ctx_t));
  if (!ctx) {
    free(stream);
    return nullptr;
  }

  ctx->capture_cap = SSE_TEST_CAPTURE_INITIAL_CAP;
  ctx->capture_buf = malloc(ctx->capture_cap);
  if (!ctx->capture_buf) {
    free(ctx);
    free(stream);
    return nullptr;
  }
  ctx->capture_buf[0] = '\0';

  stream->state = VALK_SSE_OPEN;
  stream->queue_max = SSE_TEST_QUEUE_MAX;
  stream->data_deferred = false;
  stream->pending_capacity = 4096;
  stream->pending_data = malloc(stream->pending_capacity);
  if (!stream->pending_data) {
    free(ctx->capture_buf);
    free(ctx);
    free(stream);
    return nullptr;
  }

  stream->conn = nullptr;
  stream->session = nullptr;
  stream->stream_id = 0;
  stream->user_data = ctx;

  return stream;
}

void valk_test_sse_free(valk_sse_stream_t *stream) {
  if (!stream) return;

  valk_test_sse_ctx_t *ctx = __get_ctx(stream);
  if (ctx) {
    free(ctx->capture_buf);
    __free_events(ctx->events);
    free(ctx);
  }

  valk_sse_event_t *event = stream->queue_head;
  while (event) {
    valk_sse_event_t *next = event->next;
    free(event);
    event = next;
  }

  free(stream->pending_data);
  free(stream);
}

u64 valk_test_sse_bytes_written(valk_sse_stream_t *stream) {
  valk_test_sse_ctx_t *ctx = __get_ctx(stream);
  if (!ctx) return 0;
  return ctx->bytes_written;
}

u64 valk_test_sse_events_count(valk_sse_stream_t *stream) {
  valk_test_sse_ctx_t *ctx = __get_ctx(stream);
  if (!ctx) return 0;
  return ctx->event_count;
}

char *valk_test_sse_capture_output(valk_sse_stream_t *stream) {
  valk_test_sse_ctx_t *ctx = __get_ctx(stream);
  if (!ctx || !ctx->capture_buf) return nullptr;
  return strdup(ctx->capture_buf);
}

void valk_test_sse_reset_capture(valk_sse_stream_t *stream) {
  valk_test_sse_ctx_t *ctx = __get_ctx(stream);
  if (!ctx) return;

  ctx->capture_len = 0;
  if (ctx->capture_buf) {
    ctx->capture_buf[0] = '\0';
  }
  ctx->event_count = 0;
  ctx->bytes_written = 0;

  __free_events(ctx->events);
  ctx->events = nullptr;
  ctx->events_tail = nullptr;
}

bool valk_test_sse_has_event(valk_sse_stream_t *stream, const char *event_type, const char *data) {
  valk_test_sse_ctx_t *ctx = __get_ctx(stream);
  if (!ctx) return false;

  for (test_event_t *evt = ctx->events; evt; evt = evt->next) {
    bool type_match = false;
    if (event_type == nullptr && evt->event_type == nullptr) {
      type_match = true;
    } else if (event_type && evt->event_type && strcmp(event_type, evt->event_type) == 0) {
      type_match = true;
    }

    if (!type_match) continue;

    if (data == nullptr && (evt->data == nullptr || evt->data_len == 0)) {
      return true;
    }
    if (data && evt->data && strcmp(data, evt->data) == 0) {
      return true;
    }
  }

  return false;
}

void valk_test_sse_simulate_drain(valk_sse_stream_t *stream) {
  if (!stream) return;

  if (stream->on_drain) {
    stream->on_drain(stream, stream->user_data);
  }
}

void valk_test_sse_simulate_close(valk_sse_stream_t *stream) {
  if (!stream) return;

  stream->state = VALK_SSE_CLOSED;

  if (stream->on_close) {
    stream->on_close(stream, stream->user_data);
  }
}

int valk_test_sse_send_event(valk_sse_stream_t *stream, const char *event_type,
                              const char *data, u64 len, u64 id) {
  if (!stream || !__is_test_stream(stream)) {
    return valk_sse_send_event(stream, event_type, data, len, id);
  }

  if (stream->state != VALK_SSE_OPEN) {
    return -1;
  }

  if (!data) {
    return -1;
  }

  if (stream->queue_len >= stream->queue_max) {
    return -2;
  }

  valk_test_sse_ctx_t *ctx = __get_ctx(stream);
  if (!ctx) return -3;

  u64 event_size = 0;
  char id_buf[32] = {0};
  if (id > 0) {
    int id_len = snprintf(id_buf, sizeof(id_buf), "id: %llu\n", (unsigned long long)id);
    event_size += id_len;
  }

  char type_buf[256] = {0};
  if (event_type) {
    int type_len = snprintf(type_buf, sizeof(type_buf), "event: %s\n", event_type);
    event_size += type_len;
  }

  event_size += 6;  // "data: "
  event_size += len;
  event_size += 2;  // "\n\n"

  char *formatted = malloc(event_size + 1);
  if (!formatted) return -3;

  char *p = formatted;
  if (id > 0) {
    u64 id_len = strlen(id_buf);
    memcpy(p, id_buf, id_len);
    p += id_len;
  }
  if (event_type) {
    u64 type_len = strlen(type_buf);
    memcpy(p, type_buf, type_len);
    p += type_len;
  }
  memcpy(p, "data: ", 6);
  p += 6;
  memcpy(p, data, len);
  p += len;
  *p++ = '\n';
  *p++ = '\n';
  *p = '\0';

  u64 total_len = p - formatted;

  __capture_append(ctx, formatted, total_len);
  __store_event(ctx, event_type, data, len);
  ctx->event_count++;
  ctx->bytes_written += total_len;

  stream->events_sent++;
  stream->bytes_sent += total_len;
  stream->queue_len++;

  free(formatted);

  return 0;
}
