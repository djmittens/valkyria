#include "aio_backpressure.h"
#include "aio_internal.h"

#include "../log.h"

void valk_backpressure_list_init(valk_backpressure_list_t *list, size_t max_size, uint32_t timeout_ms) {
  if (!list) return;
  list->head = nullptr;
  list->size = 0;
  list->max_size = max_size;
  list->timeout_ms = timeout_ms;
}

bool valk_backpressure_list_add(valk_backpressure_list_t *list, valk_aio_handle_t *conn,
                                 uint64_t now_ms) {
  if (!list || !conn) return false;
  if (conn->http.backpressure) return true;

  if (list->size >= list->max_size) {
    VALK_WARN("Backpressure queue full (%zu >= %zu), dropping connection",
              list->size, list->max_size);
    return false;
  }

  conn->http.backpressure = true;
  conn->http.backpressure_start_time = now_ms;
  conn->http.backpressure_next = list->head;
  list->head = conn;
  list->size++;
  return true;
}

void valk_backpressure_list_remove(valk_backpressure_list_t *list, valk_aio_handle_t *conn) {
  if (!list || !conn || !conn->http.backpressure) return;

  conn->http.backpressure = false;

  valk_aio_handle_t **pp = &list->head;
  while (*pp) {
    if (*pp == conn) {
      *pp = conn->http.backpressure_next;
      conn->http.backpressure_next = nullptr;
      list->size--;
      return;
    }
    pp = &(*pp)->http.backpressure_next;
  }
}

struct valk_aio_handle_t *valk_backpressure_list_try_resume(valk_backpressure_list_t *list,
                                                              valk_slab_t *tcp_buffer_slab,
                                                              uint32_t min_buffers) {
  if (!list || !list->head || !tcp_buffer_slab) return nullptr;

  size_t available = valk_slab_available(tcp_buffer_slab);
  uint32_t threshold = min_buffers > 0 ? min_buffers / 2 : 2;

  if (available < threshold) {
    return nullptr;
  }

  while (list->head) {
    valk_aio_handle_t *conn = list->head;

    if (conn->http.state == VALK_CONN_CLOSING || conn->http.state == VALK_CONN_CLOSED ||
        uv_is_closing((uv_handle_t *)&conn->uv.tcp)) {
      list->head = conn->http.backpressure_next;
      conn->http.backpressure_next = nullptr;
      conn->http.backpressure = false;
      list->size--;
      continue;
    }

    list->head = conn->http.backpressure_next;
    conn->http.backpressure_next = nullptr;
    conn->http.backpressure = false;
    list->size--;

    VALK_DEBUG("Resumed backpressured connection (available buffers: %zu)", available);
    return conn;
  }

  return nullptr;
}

size_t valk_backpressure_list_timeout_expired(valk_backpressure_list_t *list, uint64_t now_ms,
                                               valk_aio_handle_t **out_expired, size_t max_expired) {
  if (!list || !out_expired || max_expired == 0 || list->timeout_ms == 0) return 0;

  size_t count = 0;
  valk_aio_handle_t **pp = &list->head;

  while (*pp && count < max_expired) {
    valk_aio_handle_t *conn = *pp;

    if (conn->http.backpressure_start_time > 0) {
      uint64_t age = now_ms - conn->http.backpressure_start_time;
      if (age > list->timeout_ms) {
        *pp = conn->http.backpressure_next;
        conn->http.backpressure_next = nullptr;
        conn->http.backpressure = false;
        list->size--;
        out_expired[count++] = conn;
        continue;
      }
    }
    pp = &(*pp)->http.backpressure_next;
  }

  return count;
}
