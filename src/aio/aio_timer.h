#pragma once

#include <uv.h>
#include "aio_types.h"

#ifdef VALK_METRICS_ENABLED
valk_aio_handle_t* valk_aio_timer_alloc(valk_aio_system_t* sys);
void valk_aio_timer_init(valk_aio_handle_t* handle);
void valk_aio_timer_start(valk_aio_handle_t* handle, u64 timeout_ms, u64 repeat_ms,
                           void (*callback)(uv_timer_t*));
void valk_aio_timer_stop(valk_aio_handle_t* handle);
void valk_aio_timer_close(valk_aio_handle_t* handle, void (*close_cb)(uv_handle_t*));
void valk_aio_timer_set_data(valk_aio_handle_t* handle, void* data);
void valk_aio_timer_free(valk_aio_handle_t* handle);
#endif
