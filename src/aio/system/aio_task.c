#include "aio_internal.h"

extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);

typedef struct {
  valk_aio_system_t *sys;
  valk_aio_task_new *task;
} __task_wrapper_ctx_t;

static void __task_wrapper_fn(void *ctx) {
  __task_wrapper_ctx_t *wrapper = ctx;
  valk_aio_system_t *sys = wrapper->sys;
  valk_aio_task_new *task = wrapper->task;
  free(wrapper);

  task->callback(sys, task);
}

// LCOV_EXCL_BR_START - malloc failure is extremely rare
void valk_uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task) {
  __task_wrapper_ctx_t *wrapper = malloc(sizeof(__task_wrapper_ctx_t));
  if (!wrapper) {
    VALK_ERROR("Failed to allocate task wrapper");
    if (task->handle) {
      valk_async_handle_fail(task->handle, valk_lval_err("Task allocation failed"));
    }
    valk_mem_allocator_free(task->allocator, task);
    return;
  }
  wrapper->sys = sys;
  wrapper->task = task;

  valk_aio_enqueue_task(sys, __task_wrapper_fn, wrapper);
}
// LCOV_EXCL_BR_STOP
