#pragma once
#include "types.h"

#include <stddef.h>
#include <stdbool.h>
#include "memory.h"

struct valk_aio_handle_t;

typedef struct valk_backpressure_list {
  struct valk_aio_handle_t *head;
  u64 size;
  u64 max_size;
  u32 timeout_ms;
} valk_backpressure_list_t;

void valk_backpressure_list_init(valk_backpressure_list_t *list, u64 max_size, u32 timeout_ms);

bool valk_backpressure_list_add(valk_backpressure_list_t *list, struct valk_aio_handle_t *conn,
                                 u64 now_ms);

void valk_backpressure_list_remove(valk_backpressure_list_t *list, struct valk_aio_handle_t *conn);

struct valk_aio_handle_t *valk_backpressure_list_try_resume(valk_backpressure_list_t *list,
                                                             valk_slab_t *tcp_buffer_slab,
                                                             u32 min_buffers);

u64 valk_backpressure_list_timeout_expired(valk_backpressure_list_t *list, u64 now_ms,
                                               struct valk_aio_handle_t **out_expired, u64 max_expired);
