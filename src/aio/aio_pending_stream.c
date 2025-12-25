#include "aio_pending_stream.h"

#include <stdlib.h>
#include <string.h>

#include "../log.h"

int valk_pending_stream_queue_init(valk_pending_stream_queue_t *queue, size_t pool_capacity) {
  if (!queue || pool_capacity == 0) return -1;

  queue->head = nullptr;
  queue->tail = nullptr;
  queue->count = 0;

  queue->pool.items = calloc(pool_capacity, sizeof(valk_pending_stream_t));
  if (!queue->pool.items) return -1;

  queue->pool.used = calloc(pool_capacity, sizeof(bool));
  if (!queue->pool.used) {
    free(queue->pool.items);
    queue->pool.items = nullptr;
    return -1;
  }

  queue->pool.capacity = pool_capacity;
  return 0;
}

void valk_pending_stream_queue_destroy(valk_pending_stream_queue_t *queue) {
  if (!queue) return;

  while (queue->head) {
    valk_pending_stream_t *ps = queue->head;
    queue->head = ps->next;
    valk_pending_stream_free(queue, ps);
  }

  free(queue->pool.items);
  free(queue->pool.used);
  queue->pool.items = nullptr;
  queue->pool.used = nullptr;
  queue->pool.capacity = 0;
}

valk_pending_stream_t *valk_pending_stream_alloc(valk_pending_stream_queue_t *queue) {
  if (!queue || !queue->pool.items) return nullptr;

  for (size_t i = 0; i < queue->pool.capacity; i++) {
    if (!queue->pool.used[i]) {
      queue->pool.used[i] = true;
      valk_pending_stream_t *ps = &queue->pool.items[i];
      memset(ps, 0, sizeof(valk_pending_stream_t));
      return ps;
    }
  }
  return nullptr;
}

void valk_pending_stream_free(valk_pending_stream_queue_t *queue, valk_pending_stream_t *ps) {
  if (!ps) return;

  if (ps->method) { free(ps->method); ps->method = nullptr; }
  if (ps->scheme) { free(ps->scheme); ps->scheme = nullptr; }
  if (ps->authority) { free(ps->authority); ps->authority = nullptr; }
  if (ps->path) { free(ps->path); ps->path = nullptr; }

  for (size_t i = 0; i < ps->header_count; i++) {
    if (ps->headers[i].name) free(ps->headers[i].name);
    if (ps->headers[i].value) free(ps->headers[i].value);
  }
  ps->header_count = 0;

  if (ps->body) { free(ps->body); ps->body = nullptr; }

  if (queue && queue->pool.items) {
    size_t idx = (size_t)(ps - queue->pool.items);
    if (idx < queue->pool.capacity) {
      queue->pool.used[idx] = false;
    }
  }
}

void valk_pending_stream_enqueue(valk_pending_stream_queue_t *queue, valk_pending_stream_t *ps) {
  if (!queue || !ps) return;

  ps->next = nullptr;
  if (queue->tail) {
    queue->tail->next = ps;
  } else {
    queue->head = ps;
  }
  queue->tail = ps;
  queue->count++;
  VALK_INFO("Pending stream ENQUEUED: stream_id=%d, queue_size=%zu",
            ps->stream_id, queue->count);
}

valk_pending_stream_t *valk_pending_stream_dequeue(valk_pending_stream_queue_t *queue) {
  if (!queue || !queue->head) return nullptr;

  valk_pending_stream_t *ps = queue->head;
  queue->head = ps->next;
  if (!queue->head) {
    queue->tail = nullptr;
  }
  ps->next = nullptr;
  queue->count--;
  VALK_INFO("Pending stream DEQUEUED: stream_id=%d, queue_size=%zu",
            ps->stream_id, queue->count);
  return ps;
}

void valk_pending_stream_remove(valk_pending_stream_queue_t *queue, valk_pending_stream_t *target) {
  if (!queue || !target) return;

  valk_pending_stream_t **pp = &queue->head;
  while (*pp) {
    if (*pp == target) {
      *pp = target->next;
      if (queue->tail == target) {
        queue->tail = nullptr;
        for (valk_pending_stream_t *p = queue->head; p; p = p->next) {
          if (!p->next) queue->tail = p;
        }
      }
      queue->count--;
      valk_pending_stream_free(queue, target);
      return;
    }
    pp = &(*pp)->next;
  }
}
