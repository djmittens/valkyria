#include "aio_internal.h"

static void __task_queue_notify_cb(uv_async_t *handle) {
  (void)handle;
}

static void __task_queue_drain_cb(uv_check_t *handle) {
  VALK_GC_SAFE_POINT();
  
  valk_aio_system_t *sys = handle->data;
  if (!sys || sys->shuttingDown) return;
  
  valk_aio_task_queue_t *tq = &sys->task_queue;
  void *item;
  int processed = 0;
  const int max_per_iteration = 256;

  while (processed < max_per_iteration) {
    item = valk_chase_lev_steal(&tq->deque);
    if (item == VALK_CHASE_LEV_EMPTY || item == VALK_CHASE_LEV_ABORT) break;

    valk_aio_task_item_t *task = (valk_aio_task_item_t *)item;
    if (task->fn) {
      task->fn(task->ctx);
    }
    free(task);
    processed++;
  }
}

void valk_aio_task_queue_init(valk_aio_system_t *sys) {
  valk_aio_task_queue_t *tq = &sys->task_queue;
  if (tq->initialized) return;

  valk_chase_lev_init(&tq->deque, 64);

  uv_async_init(sys->eventloop, &tq->notify, __task_queue_notify_cb);
  tq->notify.data = sys;

  uv_check_init(sys->eventloop, &tq->drain_check);
  tq->drain_check.data = sys;
  uv_check_start(&tq->drain_check, __task_queue_drain_cb);

  tq->initialized = true;
}

static void __task_queue_close_cb(uv_handle_t *handle) {
  (void)handle;
}

void valk_aio_task_queue_shutdown(valk_aio_system_t *sys) {
  valk_aio_task_queue_t *tq = &sys->task_queue;
  if (!tq->initialized) return;

  uv_check_stop(&tq->drain_check);
  if (!uv_is_closing((uv_handle_t *)&tq->drain_check)) {
    uv_close((uv_handle_t *)&tq->drain_check, __task_queue_close_cb);
  }
  if (!uv_is_closing((uv_handle_t *)&tq->notify)) {
    uv_close((uv_handle_t *)&tq->notify, __task_queue_close_cb);
  }

  void *item;
  while ((item = valk_chase_lev_steal(&tq->deque)) != VALK_CHASE_LEV_EMPTY && 
         item != VALK_CHASE_LEV_ABORT) {
    free(item);
  }
  valk_chase_lev_destroy(&tq->deque);

  tq->initialized = false;
}

void valk_aio_enqueue_task(valk_aio_system_t *sys, valk_aio_task_fn fn, void *ctx) {
  if (!sys || !fn) return;

  valk_aio_task_item_t *task = malloc(sizeof(valk_aio_task_item_t));
  task->fn = fn;
  task->ctx = ctx;

  valk_chase_lev_push(&sys->task_queue.deque, task);
  uv_async_send(&sys->task_queue.notify);
}

bool valk_aio_task_queue_empty(valk_aio_system_t *sys) {
  if (!sys) return true;
  return valk_chase_lev_empty(&sys->task_queue.deque);
}

i64 valk_aio_task_queue_size(valk_aio_system_t *sys) {
  if (!sys) return 0;
  return valk_chase_lev_size(&sys->task_queue.deque);
}
