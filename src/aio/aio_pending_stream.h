#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef struct nghttp2_session nghttp2_session;

#define PENDING_STREAM_MAX_HEADERS 32

typedef struct {
  char *name;
  char *value;
  size_t name_len;
  size_t value_len;
} valk_pending_header_t;

typedef struct valk_pending_stream {
  struct valk_pending_stream *next;
  struct valk_aio_handle_t *conn;
  nghttp2_session *session;
  int32_t stream_id;
  char *method;
  char *scheme;
  char *authority;
  char *path;
  valk_pending_header_t headers[PENDING_STREAM_MAX_HEADERS];
  size_t header_count;
  uint8_t *body;
  size_t body_len;
  size_t body_capacity;
  uint64_t queued_time_ms;
  bool headers_complete;
} valk_pending_stream_t;

typedef struct valk_pending_stream_pool {
  valk_pending_stream_t *items;
  bool *used;
  size_t capacity;
} valk_pending_stream_pool_t;

typedef struct valk_pending_stream_queue {
  valk_pending_stream_t *head;
  valk_pending_stream_t *tail;
  size_t count;
  valk_pending_stream_pool_t pool;
} valk_pending_stream_queue_t;

int valk_pending_stream_queue_init(valk_pending_stream_queue_t *queue, size_t pool_capacity);
void valk_pending_stream_queue_destroy(valk_pending_stream_queue_t *queue);

valk_pending_stream_t *valk_pending_stream_alloc(valk_pending_stream_queue_t *queue);
void valk_pending_stream_free(valk_pending_stream_queue_t *queue, valk_pending_stream_t *ps);

void valk_pending_stream_enqueue(valk_pending_stream_queue_t *queue, valk_pending_stream_t *ps);
valk_pending_stream_t *valk_pending_stream_dequeue(valk_pending_stream_queue_t *queue);

void valk_pending_stream_remove(valk_pending_stream_queue_t *queue, valk_pending_stream_t *target);

static inline bool valk_is_pending_stream_marker(void *user_data) {
  return user_data && ((uintptr_t)user_data & (1ULL << 63));
}

static inline valk_pending_stream_t *valk_get_pending_stream_from_marker(void *user_data) {
  if (!valk_is_pending_stream_marker(user_data)) return NULL;
  return (valk_pending_stream_t *)((uintptr_t)user_data & ~(1ULL << 63));
}

static inline void *valk_make_pending_stream_marker(valk_pending_stream_t *ps) {
  return (void *)((uintptr_t)ps | (1ULL << 63));
}
