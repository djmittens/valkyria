#pragma once

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include "../memory.h"

struct valk_aio_handle_t;

typedef struct valk_backpressure_list {
  struct valk_aio_handle_t *head;
  size_t size;
  size_t max_size;
  uint32_t timeout_ms;
} valk_backpressure_list_t;

void valk_backpressure_list_init(valk_backpressure_list_t *list, size_t max_size, uint32_t timeout_ms);

bool valk_backpressure_list_add(valk_backpressure_list_t *list, struct valk_aio_handle_t *conn,
                                 uint64_t now_ms);

void valk_backpressure_list_remove(valk_backpressure_list_t *list, struct valk_aio_handle_t *conn);

struct valk_aio_handle_t *valk_backpressure_list_try_resume(valk_backpressure_list_t *list,
                                                             valk_slab_t *tcp_buffer_slab,
                                                             uint32_t min_buffers);

size_t valk_backpressure_list_timeout_expired(valk_backpressure_list_t *list, uint64_t now_ms,
                                               struct valk_aio_handle_t **out_expired, size_t max_expired);
