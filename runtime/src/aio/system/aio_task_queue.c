#include "aio_internal.h"

#define TASK_QUEUE_CAPACITY 4096

static inline void __run_task_in_scratch(valk_aio_task_item_t *task) {
  valk_mem_arena_t *scratch = valk_thread_ctx.scratch;
  if (scratch) {
    VALK_WITH_ALLOC((void *)scratch) {
      task->fn(task->ctx);
    }
    valk_mem_arena_reset(scratch);
  } else {
    task->fn(task->ctx); // LCOV_EXCL_LINE
  }
}

static void __loop_task_notify_cb(uv_async_t *handle) {
  valk_aio_loop_t *loop = handle->data;
  if (!loop || loop->sys->shuttingDown) return; // LCOV_EXCL_BR_LINE - handle->data always set in init

  valk_aio_task_queue_t *tq = &loop->task_queue;
  void *item;
  int processed = 0;
  const int max_per_iteration = 256;

  while (processed < max_per_iteration) {
    item = valk_mpmc_pop(&tq->queue);
    if (!item) break;

    valk_aio_task_item_t *task = (valk_aio_task_item_t *)item;
    __run_task_in_scratch(task);
    free(task);
    processed++;
  }
}

static void __loop_task_drain_cb(uv_check_t *handle) {
  VALK_GC_SAFE_POINT(); // LCOV_EXCL_BR_LINE - GC coordination, not unit-testable

  valk_aio_loop_t *loop = handle->data;
  if (!loop || loop->sys->shuttingDown) return; // LCOV_EXCL_BR_LINE - handle->data always set in init

  valk_aio_task_queue_t *tq = &loop->task_queue;
  void *item;
  int processed = 0;
  const int max_per_iteration = 256;

  while (processed < max_per_iteration) {
    item = valk_mpmc_pop(&tq->queue);
    if (!item) break;

    valk_aio_task_item_t *task = (valk_aio_task_item_t *)item;
    __run_task_in_scratch(task);
    free(task);
    processed++;
  }
}

static void __task_queue_close_cb(uv_handle_t *handle) {
  (void)handle;
}

static void __drain_unrun_tasks(valk_aio_task_queue_t *tq) {
  void *item;
  while ((item = valk_mpmc_pop(&tq->queue)) != nullptr) {
    valk_aio_task_item_t *task = (valk_aio_task_item_t *)item;
    if (task->drop) task->drop(task->ctx);
    free(task);
  }
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

  __drain_unrun_tasks(tq);

  tq->initialized = false;
}

void valk_aio_loop_task_queue_destroy(valk_aio_loop_t *loop) {
  valk_aio_task_queue_t *tq = &loop->task_queue;
  if (!tq->queue.buffer) return;
  __drain_unrun_tasks(tq);
  valk_mpmc_destroy(&tq->queue);
}

bool valk_aio_loop_enqueue_task_owned(valk_aio_loop_t *loop, valk_aio_task_fn fn,
                                      void *ctx, valk_aio_task_fn drop) {
  if (!loop || !fn) { // LCOV_EXCL_BR_LINE - defensive, callers always pass both
    if (drop) drop(ctx); // LCOV_EXCL_LINE LCOV_EXCL_BR_LINE
    return false; // LCOV_EXCL_LINE
  }
  if (loop->sys && loop->sys->shuttingDown) {
    if (drop) drop(ctx);
    return false;
  }

  valk_aio_task_item_t *task = malloc(sizeof(valk_aio_task_item_t));
  task->fn = fn;
  task->drop = drop;
  task->ctx = ctx;

  if (!valk_mpmc_push(&loop->task_queue.queue, task)) { // LCOV_EXCL_BR_LINE - queue full
    VALK_ERROR("Loop %u task queue full, dropping task", loop->id); // LCOV_EXCL_LINE
    if (drop) drop(ctx); // LCOV_EXCL_LINE LCOV_EXCL_BR_LINE
    free(task); // LCOV_EXCL_LINE
    return false; // LCOV_EXCL_LINE
  }
  uv_async_send(&loop->task_queue.notify);
  return true;
}

bool valk_aio_loop_enqueue_task(valk_aio_loop_t *loop, valk_aio_task_fn fn, void *ctx) {
  return valk_aio_loop_enqueue_task_owned(loop, fn, ctx, nullptr);
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
