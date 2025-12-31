#include "aio_internal.h"

#ifdef VALK_METRICS_ENABLED

valk_aio_handle_t* valk_aio_timer_alloc(valk_aio_system_t* sys) {
  if (!sys || !sys->handleSlab) return nullptr;

  valk_slab_item_t *item = valk_slab_aquire(sys->handleSlab);
  if (!item) return nullptr;

  valk_aio_handle_t *handle = (valk_aio_handle_t *)item->data;
  VALK_INFO("Timer ALLOC: handle=%p slot=%zu", (void*)handle, item->handle);
  memset(handle, 0, sizeof(valk_aio_handle_t));
  handle->magic = VALK_AIO_HANDLE_MAGIC;
  handle->kind = VALK_HNDL_TIMER;
  handle->sys = sys;

  return handle;
}

void valk_aio_timer_init(valk_aio_handle_t* handle) {
  if (!handle || !handle->sys) return;
  uv_timer_init(handle->sys->eventloop, &handle->uv.timer);
}

void valk_aio_timer_start(valk_aio_handle_t* handle, u64 timeout_ms, u64 repeat_ms,
                           void (*callback)(uv_timer_t*)) {
  if (!handle) return;
  uv_timer_start(&handle->uv.timer, callback, timeout_ms, repeat_ms);
}

void valk_aio_timer_stop(valk_aio_handle_t* handle) {
  if (!handle) return;
  uv_timer_stop(&handle->uv.timer);
}

void valk_aio_timer_close(valk_aio_handle_t* handle, void (*close_cb)(uv_handle_t*)) {
  if (!handle) return;
  if (uv_is_closing((uv_handle_t*)&handle->uv.timer)) {
    VALK_DEBUG("Timer already closing, skipping");
    return;
  }
  uv_close((uv_handle_t*)&handle->uv.timer, close_cb);
}

void valk_aio_timer_set_data(valk_aio_handle_t* handle, void* data) {
  if (!handle) return;
  handle->uv.timer.data = data;
}

void valk_aio_timer_free(valk_aio_handle_t* handle) {
  if (!handle || !handle->sys) return;
  valk_slab_item_t *item = valk_container_of(handle, valk_slab_item_t, data);
  VALK_INFO("Timer FREE: handle=%p slot=%zu kind=%d", (void*)handle, item->handle, handle->kind);
  if (handle->kind != VALK_HNDL_TIMER) {
    VALK_ERROR("Timer FREE: DOUBLE FREE DETECTED! kind=%d expected=%d", handle->kind, VALK_HNDL_TIMER);
    return;
  }
  handle->kind = 0;
  valk_slab_release_ptr(handle->sys->handleSlab, handle);
}

#endif
