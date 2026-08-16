#pragma once

#include "aio_types.h"
#include "memory.h"

typedef struct valk_aio_task_new {
  void *arg;
  valk_async_handle_t *handle;
  void (*callback)(valk_aio_system_t *, struct valk_aio_task_new *);
  valk_mem_allocator_t *allocator;
} valk_aio_task_new;

void valk_uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task);
