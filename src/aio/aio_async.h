#pragma once

#include <stdbool.h>

#include "aio_types.h"

struct valk_lval_t;
struct valk_lenv_t;
struct valk_mem_allocator;
struct valk_mem_arena;
struct valk_slab_item;
struct valk_aio_system;
struct valk_aio_handle_t;
struct uv_loop_s;
typedef struct uv_timer_s uv_timer_t;

typedef struct valk_async_handle_uv_data valk_async_handle_uv_data_t;
typedef struct valk_http_async_ctx valk_http_async_ctx_t;
typedef struct valk_standalone_async_ctx valk_standalone_async_ctx_t;

valk_async_handle_t *valk_async_handle_new(struct valk_aio_system *sys, struct valk_lenv_t *env);
void valk_async_handle_free(valk_async_handle_t *handle);
void valk_async_handle_complete(valk_async_handle_t *handle, struct valk_lval_t *result);
void valk_async_handle_fail(valk_async_handle_t *handle, struct valk_lval_t *error);
bool valk_async_handle_cancel(valk_async_handle_t *handle);
void valk_async_handle_add_child(valk_async_handle_t *parent, valk_async_handle_t *child);

struct valk_lval_t *valk_lval_handle(valk_async_handle_t *handle);
struct valk_lval_t *valk_async_status_to_sym(valk_async_status_t status);

void valk_async_notify_done(valk_async_handle_t *handle);
bool valk_async_is_resource_closed(valk_async_handle_t *handle);

void valk_http_async_done_callback(valk_async_handle_t *handle, void *ctx);
bool valk_http_async_is_closed_callback(void *ctx);

valk_standalone_async_ctx_t *valk_standalone_async_ctx_new(struct valk_aio_system *sys);
void valk_standalone_async_done_callback(valk_async_handle_t *handle, void *ctx);

void valk_register_async_handle_builtins(struct valk_lenv_t *env);

struct valk_lval_t *valk_async_handle_await(valk_async_handle_t *handle);
struct valk_lval_t *valk_async_handle_await_timeout(valk_async_handle_t *handle, u32 timeout_ms);
