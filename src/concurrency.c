#include "concurrency.h"

#include "collections.h"
#include "common.h"
#include "memory.h"
#include "log.h"

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const int VALK_NUM_WORKERS = 4;

// Capture the allocator from the context, it MUST be concurrency safe. \
  // This context is going to be threaded through the continuations for \
  // callbacks \
  // Should probably be request context or something instead perhaps, but \
  // keeping it simple for now
#define __assert_thread_safe_allocator()                                    \
  do {                                                                      \
    static valk_mem_allocator_e supported[] = {                             \
        VALK_ALLOC_MALLOC, VALK_ALLOC_SLAB, VALK_ALLOC_ARENA};              \
    bool found = 0;                                                         \
    for (u64 i = 0; i < sizeof(supported) / sizeof(supported[0]); ++i) { \
      if (supported[i] == valk_thread_ctx.allocator->type) {                \
        found = 1;                                                          \
      }                                                                     \
    }                                                                       \
    VALK_ASSERT(                                                            \
        found, "Current context is not thread safe: %s",                    \
        valk_mem_allocator_e_to_string(valk_thread_ctx.allocator->type));   \
  } while (0)

valk_arc_box *valk_arc_box_new(valk_res_t type, u64 capacity) {
  valk_arc_box *res = valk_mem_alloc(sizeof(valk_arc_box) + capacity);
  valk_arc_box_init(res, type, capacity);
  __assert_thread_safe_allocator();
  res->allocator = valk_thread_ctx.allocator;
  return res;
}

void valk_arc_box_init(valk_arc_box *self, valk_res_t type, u64 capacity) {
  memset(self, 0, sizeof(valk_arc_box) + capacity);
  self->type = type;
  self->refcount = 1;
  self->capacity = capacity;
  self->item = &((char *)self)[sizeof(valk_arc_box)];
  self->allocator = nullptr;
  self->free = nullptr;
  valk_capture_trace(VALK_TRACE_NEW, 1, self);
}

valk_arc_box *valk_arc_box_err(const char *msg) {
  int len = strlen(msg);
  valk_arc_box *res = valk_mem_alloc(sizeof(valk_arc_box) + len + 1);
  valk_arc_box_init(res, VALK_ERR, len + 1);
  strncpy(res->item, msg, len);
  return res;
}

void valk_future_free(valk_future *self) {
  VALK_WITH_ALLOC(self->allocator) {
    valk_mutex_lock(&self->mutex);
    VALK_ASSERT(self->done,
                "Attempting to free an unresolved future, means "
                "there is a hanging promise(pointer) out there %p",
                (void *)self);
    valk_arc_release(self->item);
    valk_mutex_unlock(&self->mutex);

    VALK_WITH_ALLOC(self->allocator) {
      da_free(&self->andThen);  // args leaked for now
    }
    valk_cond_destroy(&self->resolved);
    valk_mutex_destroy(&self->mutex);

    valk_mem_allocator_free(self->allocator, self);
  }
}

valk_future *valk_future_new() {
  valk_future *self;
  VALK_WITH_ALLOC(&valk_malloc_allocator) {
    self = valk_mem_alloc(sizeof(valk_future));
    memset(self, 0, sizeof(valk_future));

    valk_mutex_init(&self->mutex);
    valk_cond_init(&self->resolved);

    self->refcount = 1;
    self->done = 0;
    self->item = nullptr;
    self->free = valk_future_free;
    self->allocator = &valk_malloc_allocator;
    da_init(&self->andThen);
  }

  return self;
}

valk_future *valk_future_done(valk_arc_box *item) {
  valk_future *self = valk_future_new();
  self->done = 1;
  self->item = item;
  valk_arc_retain(item);
  return self;
}

void valk_future_and_then(valk_future *self,
                          struct valk_future_and_then *callback) {
  valk_arc_retain(self);
  valk_mutex_lock(&self->mutex);
  if (self->done) {
    callback->cb(callback->arg, self->item);
  } else {
    da_add(&self->andThen, *callback);
  }
  valk_mutex_unlock(&self->mutex);
  valk_arc_release(self);
}

valk_arc_box *valk_future_await(valk_future *future) {
  valk_arc_retain(future);
  valk_mutex_lock(&future->mutex);
  if (!future->done) {
    valk_cond_wait(&future->resolved, &future->mutex);
  }

  valk_arc_box *res = future->item;

  valk_mutex_unlock(&future->mutex);
  valk_arc_release(future);
  return res;
}

valk_arc_box *valk_future_await_timeout(valk_future *self, u32 msec) {
  valk_arc_box *res;
  if (self->done) {
    res = self->item;
    valk_arc_retain(res);

    valk_arc_release(self);
    return res;
  }

  valk_mutex_lock(&self->mutex);
  int ret = valk_cond_timedwait(&self->resolved, &self->mutex, msec);

  if (ret == ETIMEDOUT) {
    int old = __atomic_fetch_add(&self->done, 1, __ATOMIC_ACQ_REL);
    if (old) {
      valk_mutex_unlock(&self->mutex);
      res = self->item;
      valk_arc_retain(res);
      valk_arc_release(self);
      return res;
    }
    char buf[1000];
    snprintf(buf, sizeof(buf), "Timeout [%u ms] reached waiting for future", msec);
    self->item = valk_arc_box_err(buf);
    valk_cond_signal(&self->resolved);
  } else if (ret != 0) {
    char buf[1000];
    snprintf(buf, sizeof(buf), "Unexpected error during [valk_cond_timedwait]: %s",
            strerror(errno));
    self->done = 1;
    self->item = valk_arc_box_err(buf);
    valk_cond_signal(&self->resolved);
  }
  res = self->item;
  valk_mutex_unlock(&self->mutex);

  valk_arc_retain(res);

  valk_arc_release(self);
  return res;
}

void valk_promise_respond(valk_promise *promise, valk_arc_box *result) {
  u64 count = 0;
  valk_future *fut = promise->item;
  valk_arc_retain(fut);
  valk_arc_retain(result);

  valk_mutex_lock(&fut->mutex);

  int old = __atomic_fetch_add(&fut->done, 1, __ATOMIC_RELEASE);
  if (old) {
    fprintf(stderr, "ERROR: Promise already resolved, cannot resolve twice.\n");
    valk_mutex_unlock(&fut->mutex);
    valk_arc_release(result);
    valk_arc_release(fut);
    return;
  } 

  fut->item = result;

  count = __atomic_exchange_n(&fut->andThen.count, 0, __ATOMIC_ACQ_REL);
  valk_cond_signal(&fut->resolved);
  valk_mutex_unlock(&fut->mutex);

  while (count > 0) {
    struct valk_future_and_then *item = &fut->andThen.items[count - 1];
    item->cb(item->arg, fut->item);
    count--;
  }
  valk_arc_release(fut);
}

static void *valk_worker_routine(void *arg) {
  valk_mem_init_malloc();

  valk_worker *self = arg;
  VALK_INFO("Starting thread: %s", self->name);
  valk_task_queue *queue = self->queue;

  valk_mutex_lock(&queue->mutex);
  queue->numWorkers++;
  valk_cond_signal(&queue->workerReady);
  valk_mutex_unlock(&queue->mutex);
  do {
    int res = 0;
    valk_task task;

    valk_mutex_lock(&queue->mutex);

    if (queue->count == 0) {
      valk_cond_wait(&queue->notEmpty, &queue->mutex);
    }

    res = valk_work_pop(queue, &task);

    if (!res) {
      if (queue->count == 0) {
        valk_cond_signal(&queue->isEmpty);
      }

      if (task.type == VALK_TASK) {
        valk_cond_signal(&queue->notFull);
        VALK_TRACE("Worker executing task");
        valk_promise_respond(&task.promise, task.func(task.arg));
      } else if (task.type == VALK_POISON) {
        VALK_INFO("%s: received poison pill (shutdown)", self->name);
        queue->numWorkers--;
        valk_cond_signal(&queue->workerDead);
        valk_mutex_unlock(&queue->mutex);
        break;
      }
    }
    valk_mutex_unlock(&queue->mutex);
  } while (1);

  return nullptr;
}

int valk_start_pool(valk_worker_pool *pool) {
  pool->items = valk_mem_alloc(sizeof(valk_worker) * VALK_NUM_WORKERS);
  valk_work_init(&pool->queue, 8);

  for (u64 i = 0; i < VALK_NUM_WORKERS; i++) {
    pool->items[i].queue = &pool->queue;
    int len = snprintf(nullptr, 0, "Worker [%llu]", (unsigned long long)i);
    pool->items[i].name = malloc(len + 1);
    snprintf(pool->items[i].name, len + 1, "Worker [%llu]", (unsigned long long)i);

    valk_thread_attr_t attr;
    valk_thread_attr_init(&attr);
    valk_thread_attr_setdetached(&attr, true);

    int res = valk_thread_create(&pool->items[i].thread, &attr, valk_worker_routine,
                                 (void *)&pool->items[i]);
    if (res) {
      perror("valk_thread_create");
      free(pool->items[i].name);
      return 1;
    }
    ++pool->count;
  }

  valk_mutex_lock(&pool->queue.mutex);
  while (pool->queue.numWorkers < VALK_NUM_WORKERS) {
    valk_cond_wait(&pool->queue.workerReady, &pool->queue.mutex);
  }
  valk_mutex_unlock(&pool->queue.mutex);
  return 0;
}

void valk_drain_pool(valk_worker_pool *pool) {
  valk_mutex_lock(&pool->queue.mutex);
  if (!pool->queue.isShuttingDown) {
    pool->queue.isShuttingDown = 1;
    if (pool->queue.count > 0) {
      valk_cond_wait(&pool->queue.isEmpty, &pool->queue.mutex);
    }
  } else {
    VALK_WARN("Pool is already draining; not doing anything");
  }
  valk_mutex_unlock(&pool->queue.mutex);
}

void valk_free_pool(valk_worker_pool *pool) {
  valk_mutex_lock(&pool->queue.mutex);
  if (pool->queue.count > 0) {
    valk_mutex_unlock(&pool->queue.mutex);
    valk_drain_pool(pool);
  } else {
    valk_mutex_unlock(&pool->queue.mutex);
  }

  valk_mutex_lock(&pool->queue.mutex);
  valk_task poison = {.type = VALK_POISON};
  u64 numWorkers = pool->queue.numWorkers;
  for (u64 i = 0; i < numWorkers; i++) {
    valk_work_add(&pool->queue, poison);
    valk_cond_signal(&pool->queue.notEmpty);
  }
  valk_mutex_unlock(&pool->queue.mutex);

  valk_mutex_lock(&pool->queue.mutex);
  while (pool->queue.numWorkers > 0) {
    valk_cond_wait(&pool->queue.workerDead, &pool->queue.mutex);
  }
  valk_mutex_unlock(&pool->queue.mutex);

  for (u64 i = 0; i < numWorkers; i++) {
    free(pool->items[i].name);
  }
  free(pool->items);

  valk_work_free(&pool->queue);
}

valk_future *valk_schedule(valk_worker_pool *pool, valk_arc_box *arg,
                           valk_arc_box *(*func)(valk_arc_box *)) {
  valk_task_queue *queue = &pool->queue;
  valk_mutex_lock(&queue->mutex);
  valk_future *res;

  if (queue->isShuttingDown) {
    res = valk_future_done(
        valk_arc_box_err("Error trying to submit work to threadpool, "
                         "while its shutting down"));
  } else {
    if (queue->capacity == queue->count) {
      valk_cond_wait(&queue->notFull, &queue->mutex);
    }

    res = valk_future_new();

    valk_task task = {
        .type = VALK_TASK, .arg = arg, .func = func, .promise = {res}};

    int err = valk_work_add(queue, task);
    if (err) {
      valk_arc_box *berr =
          valk_arc_box_err("Could not add task to queue for pool scheduling");
      valk_promise_respond(&task.promise, berr);
      valk_arc_release(berr);
      valk_arc_release(task.promise.item);
      valk_arc_release(task.arg);
    }
    valk_cond_signal(&queue->notEmpty);
  }

  valk_mutex_unlock(&pool->queue.mutex);
  return res;
}

typedef struct {
  valk_promise *promise;
  valk_arc_box *result;
} __valk_resolve_promise;

static valk_arc_box *__valk_pool_resolve_promise_cb(valk_arc_box *arg) {
  if (arg->type != VALK_SUC) {
    // Cannot resolve an error - this should not happen
    // TODO(networking): maybe turn this into a hard assert
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr,
            "ERROR: Invalid condition, could not resolve an error "
            "boxsed promise.\n");
    return arg;
  }
  __valk_resolve_promise *a = arg->item;
  valk_promise_respond(a->promise, a->result);
  valk_arc_release(a->result);
  return arg;
}

void valk_pool_resolve_promise(valk_worker_pool *pool, valk_promise *promise,
                               valk_arc_box *result) {
  valk_arc_box *arg =
      valk_arc_box_new(VALK_SUC, sizeof(__valk_resolve_promise));
  __valk_resolve_promise *pair = arg->item;
  pair->promise = promise;
  pair->result = result;
  valk_arc_retain(result);

  valk_future *res = valk_schedule(pool, arg, __valk_pool_resolve_promise_cb);
  valk_arc_retain(res);
  valk_arc_box *completion = valk_future_await(res);
  valk_arc_release(completion);
  valk_arc_release(res);
}
