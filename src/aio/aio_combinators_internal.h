#ifndef VALK_AIO_COMBINATORS_INTERNAL_H
#define VALK_AIO_COMBINATORS_INTERNAL_H

#include <math.h>
#include "aio_internal.h"
#include "aio_request_ctx.h"
#include "builtins_internal.h"

extern valk_async_status_t valk_async_handle_get_status(valk_async_handle_t *handle);
extern void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result);
extern valk_lval_t *valk_async_handle_await(valk_async_handle_t *handle);
extern valk_lval_t* valk_lval_copy(valk_lval_t* lval);
extern valk_async_handle_t* valk_async_handle_new(valk_aio_system_t *sys, valk_lenv_t *env);
extern valk_lval_t *valk_lval_handle(valk_async_handle_t *handle);
extern void valk_async_handle_free(valk_async_handle_t *handle);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);
extern bool valk_async_handle_cancel(valk_async_handle_t *handle);
extern void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child);
extern void valk_async_propagate_region(valk_async_handle_t *handle, valk_region_t *region, valk_lenv_t *env);
extern void valk_async_notify_done(valk_async_handle_t *handle);
extern bool valk_async_is_resource_closed(valk_async_handle_t *handle);
extern valk_standalone_async_ctx_t* valk_standalone_async_ctx_new(valk_aio_system_t *sys);
extern void valk_standalone_async_done_callback(valk_async_handle_t *handle, void *ctx);
extern valk_lval_t* valk_async_status_to_sym(valk_async_status_t status);

void valk_async_notify_parent(valk_async_handle_t *child);
void valk_async_propagate_completion(valk_async_handle_t *source);

static inline void __sleep_timer_close_cb(uv_handle_t *handle) {
  UNUSED(handle);
}

static inline void __sleep_timer_cb(uv_timer_t *timer_handle) {
  valk_async_handle_uv_data_t *data = (valk_async_handle_uv_data_t *)timer_handle->data;
  valk_async_handle_t *async_handle = data->handle;
  uv_timer_stop(timer_handle);
  uv_close((uv_handle_t *)timer_handle, __sleep_timer_close_cb);
  async_handle->uv_handle_ptr = NULL;
  valk_lval_t *result = valk_lval_nil();
  valk_async_handle_complete(async_handle, result);
}

void valk_register_comb_timers(valk_lenv_t *env);
void valk_register_comb_syntax(valk_lenv_t *env);
void valk_register_comb_handle(valk_lenv_t *env);
void valk_register_comb_chain(valk_lenv_t *env);
void valk_register_comb_collection(valk_lenv_t *env);
void valk_register_comb_all(valk_lenv_t *env);
void valk_register_comb_race(valk_lenv_t *env);
void valk_register_comb_any(valk_lenv_t *env);
void valk_register_comb_all_settled(valk_lenv_t *env);
void valk_register_comb_resource(valk_lenv_t *env);
void valk_register_comb_timeout(valk_lenv_t *env);
void valk_register_comb_util(valk_lenv_t *env);

#endif
