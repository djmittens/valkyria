#include "uv_fake.h"
#include <stdlib.h>
#include <string.h>

int uv_timer_init(uv_loop_t *loop, uv_timer_t *handle) {
  memset(handle, 0, sizeof(*handle));
  handle->loop = loop;
  handle->type = UV_TIMER;
  handle->cb = NULL;
  handle->active = false;
  handle->closing = false;
  handle->closed = false;
  
  handle->timer_next = loop->timer_head;
  loop->timer_head = handle;
  
  handle->handle_next = loop->handle_head;
  loop->handle_head = (uv_handle_t *)handle;
  
  return 0;
}

int uv_timer_start(uv_timer_t *handle, uv_timer_cb cb, uint64_t timeout, uint64_t repeat) {
  handle->cb = cb;
  handle->timeout = timeout;
  handle->repeat = repeat;
  handle->next_fire = handle->loop->time + timeout;
  handle->active = true;
  return 0;
}

int uv_timer_stop(uv_timer_t *handle) {
  handle->active = false;
  return 0;
}
