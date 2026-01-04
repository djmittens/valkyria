#include "aio_internal.h"

static void __uv_task_close_cb(uv_handle_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  valk_aio_task_new *task = hndl->arg;

  if (task->promise.item) {
    valk_arc_release(task->promise.item);
  }
  valk_mem_allocator_free(task->allocator, task);

  valk_dll_pop(hndl);
  valk_slab_release_ptr(hndl->sys->handleSlab, hndl);
}

static void __uv_task_cb_new(uv_async_t *handle) {
  valk_aio_handle_t *hndl = handle->data;
  valk_aio_task_new *task = hndl->arg;

  task->callback(hndl->sys, task);

  uv_close((uv_handle_t *)&hndl->uv.task, __uv_task_close_cb);
}

extern valk_lval_t *valk_lval_err(const char *fmt, ...);
extern void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error);

void valk_uv_exec_task(valk_aio_system_t *sys, valk_aio_task_new *task) {
  valk_slab_item_t *slab_item = valk_slab_aquire(sys->handleSlab);
  if (!slab_item) {
    VALK_ERROR("Handle slab exhausted in valk_uv_exec_task");
    if (task->handle) {
      valk_async_handle_fail(task->handle, valk_lval_err("Handle slab exhausted"));
    } else if (task->promise.item) {
      valk_arc_box *err = valk_arc_box_err("Handle slab exhausted");
      valk_promise_respond(&task->promise, err);
      valk_arc_release(err);
      valk_arc_release(task->promise.item);
    }
    valk_mem_allocator_free(task->allocator, task);
    return;
  }
  valk_aio_handle_t *hndl = (valk_aio_handle_t *)slab_item->data;
  memset(hndl, 0, sizeof(valk_aio_handle_t));
  hndl->magic = VALK_AIO_HANDLE_MAGIC;
  hndl->kind = VALK_HNDL_TASK;
  hndl->sys = sys;
  hndl->arg = task;
  hndl->uv.task.data = hndl;

  int r = uv_async_init(sys->eventloop, &hndl->uv.task, __uv_task_cb_new);
  if (r) {
    VALK_ERROR("uv_async_init failed: %d", r);
  }
  valk_dll_insert_after(&sys->liveHandles, hndl);
  
  r = uv_async_send(&hndl->uv.task);
  if (r) {
    VALK_ERROR("uv_async_send failed: %d", r);
  }
}
