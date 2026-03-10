#include "aio_internal.h"

#define TASK_QUEUE_CAPACITY 4096

static void __loop_task_notify_cb(uv_async_t *handle) {
  valk_aio_loop_t *loop = handle->data;
  if (!loop || loop->sys->shuttingDown) return;

  valk_aio_task_queue_t *tq = &loop->task_queue;
  void *item;
  int processed = 0;
  const int max_per_iteration = 256;

  while (processed < max_per_iteration) {
    item = valk_mpmc_pop(&tq->queue);
    if (!item) break;

    valk_aio_task_item_t *task = (valk_aio_task_item_t *)item;
    task->fn(task->ctx);
    free(task);
    processed++;
  }
}

static void __loop_task_drain_cb(uv_check_t *handle) {
  VALK_GC_SAFE_POINT();

  valk_aio_loop_t *loop = handle->data;
  if (!loop || loop->sys->shuttingDown) return;

  valk_aio_task_queue_t *tq = &loop->task_queue;
  void *item;
  int processed = 0;
  const int max_per_iteration = 256;

  while (processed < max_per_iteration) {
    item = valk_mpmc_pop(&tq->queue);
    if (!item) break;

    valk_aio_task_item_t *task = (valk_aio_task_item_t *)item;
    task->fn(task->ctx);
    free(task);
    processed++;
  }
}

static void __task_queue_close_cb(uv_handle_t *handle) {
  (void)handle;
}

// Per-loop task queue init/shutdown
void valk_aio_loop_task_queue_init(valk_aio_loop_t *loop) {
  valk_aio_task_queue_t *tq = &loop->task_queue;
  if (tq->initialized) return;

  valk_mpmc_init(&tq->queue, TASK_QUEUE_CAPACITY);

  uv_async_init(loop->uv_loop, &tq->notify, __loop_task_notify_cb);
  tq->notify.data = loop;
  uv_unref((uv_handle_t *)&tq->notify);

  uv_check_init(loop->uv_loop, &tq->drain_check);
  tq->drain_check.data = loop;
  uv_check_start(&tq->drain_check, __loop_task_drain_cb);
  uv_unref((uv_handle_t *)&tq->drain_check);

  tq->initialized = true;
}

void valk_aio_loop_task_queue_shutdown(valk_aio_loop_t *loop) {
  valk_aio_task_queue_t *tq = &loop->task_queue;
  if (!tq->initialized) return;

  uv_check_stop(&tq->drain_check);
  if (!uv_is_closing((uv_handle_t *)&tq->drain_check)) {
    uv_close((uv_handle_t *)&tq->drain_check, __task_queue_close_cb);
  }
  if (!uv_is_closing((uv_handle_t *)&tq->notify)) {
    uv_close((uv_handle_t *)&tq->notify, __task_queue_close_cb);
  }

  void *item;
  while ((item = valk_mpmc_pop(&tq->queue)) != NULL) {
    free(item);
  }
  valk_mpmc_destroy(&tq->queue);

  tq->initialized = false;
}

void valk_aio_loop_enqueue_task(valk_aio_loop_t *loop, valk_aio_task_fn fn, void *ctx) {
  if (!loop || !fn) return;

  valk_aio_task_item_t *task = malloc(sizeof(valk_aio_task_item_t));
  task->fn = fn;
  task->ctx = ctx;

  if (!valk_mpmc_push(&loop->task_queue.queue, task)) {
    VALK_ERROR("Loop %u task queue full, dropping task", loop->id); // LCOV_EXCL_LINE
    free(task); // LCOV_EXCL_LINE
    return; // LCOV_EXCL_LINE
  }
  uv_async_send(&loop->task_queue.notify);
}

// Backward-compat: system-level wrappers delegate to loop 0
void valk_aio_task_queue_init(valk_aio_system_t *sys) {
  valk_aio_loop_task_queue_init(&sys->loops[0]);
}

void valk_aio_task_queue_shutdown(valk_aio_system_t *sys) {
  valk_aio_loop_task_queue_shutdown(&sys->loops[0]);
}

void valk_aio_enqueue_task(valk_aio_system_t *sys, valk_aio_task_fn fn, void *ctx) {
  if (!sys || !sys->loops) return;
  valk_aio_loop_enqueue_task(&sys->loops[0], fn, ctx);
}

bool valk_aio_task_queue_empty(valk_aio_system_t *sys) {
  if (!sys || !sys->loops) return true;
  return valk_mpmc_empty(&sys->loops[0].task_queue.queue);
}

i64 valk_aio_task_queue_size(valk_aio_system_t *sys) {
  if (!sys || !sys->loops) return 0;
  return (i64)valk_mpmc_size(&sys->loops[0].task_queue.queue);
}
