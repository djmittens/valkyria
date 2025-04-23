#include "concurrency.h"
#define _GNU_SOURCE
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "memory.h"

const int VALK_NUM_WORKERS = 4;

// Capture the allocator from the context, it MUST be concurrency safe. \
  // This context is going to be threaded through the continuations for \
  // callbacks \
  // Should probably be request context or something instead perhaps, but \
  // keeping it simple for now
#define __assert_thread_safe_allocator()                                    \
  do {                                                                      \
    static valk_mem_allocator_e supported[] = {VALK_ALLOC_MALLOC,           \
                                               VALK_ALLOC_ARENA};           \
    bool found = 0;                                                         \
    for (size_t i = 0; i < sizeof(supported) / sizeof(supported[0]); ++i) { \
      if (supported[i] == valk_thread_ctx.allocator->type) {                \
        found = 1;                                                          \
      }                                                                     \
    }                                                                       \
    VALK_ASSERT(                                                            \
        found, "Current Allocator Context is not supported: %s",            \
        valk_mem_allocator_e_to_string(valk_thread_ctx.allocator->type));   \
  } while (0)

valk_arc_box *valk_arc_box_new(valk_res_t type, size_t capacity) {
  valk_arc_box *res = valk_mem_alloc(sizeof(valk_arc_box) + capacity);
  res->type = type;
  res->refcount = 1;
  res->capacity = capacity;
  res->item = &((char *)res)[sizeof(valk_arc_box)];

  res->free = nullptr;
  __assert_thread_safe_allocator();
  res->allocator = valk_thread_ctx.allocator;

  return res;
}

valk_arc_box *valk_arc_box_err(const char *msg) {
  int len = strlen(msg);
  valk_arc_box *res = valk_mem_alloc(sizeof(valk_arc_box) + len + 1);
  memset(res, 0, sizeof(valk_arc_box) + len + 1);
  res->type = VALK_ERR;
  res->refcount = 1;
  res->item = &((char *)res)[sizeof(valk_arc_box)];
  res->free = nullptr;
  __assert_thread_safe_allocator();
  res->allocator = valk_thread_ctx.allocator;

  strncpy(res->item, msg, len);
  return res;
}

void valk_future_free(valk_future *self) {
  pthread_cond_destroy(&self->resolved);
  pthread_mutex_destroy(&self->mutex);
  valk_arc_release(self->item);
  valk_mem_allocator_free(self->allocator, self);
}

valk_future *valk_future_new() {
  valk_future *self = valk_mem_alloc(sizeof(valk_future));
  pthread_mutex_init(&self->mutex, nullptr);
  pthread_cond_init(&self->resolved, nullptr);

  self->refcount = 1;
  self->done = 0;
  self->item = nullptr;
  __assert_thread_safe_allocator();
  self->allocator = valk_thread_ctx.allocator;
  self->free = valk_future_free;
  return self;
}

valk_future *valk_future_done(valk_arc_box *item) {
  valk_future *self = valk_future_new();
  self->done = 1;
  self->item = item;
  valk_arc_retain(item);
  return self;
}

valk_arc_box *valk_future_await(valk_future *future) {
  pthread_mutex_lock(&future->mutex);
  if (!future->done) {
    pthread_cond_wait(&future->resolved, &future->mutex);
  }

  valk_arc_box *res = future->item;
  valk_arc_retain(res);

  pthread_mutex_unlock(&future->mutex);
  valk_arc_release(future);
  return res;
}

valk_arc_box *valk_future_await_timeout(valk_future *future, uint32_t msec) {
  pthread_mutex_lock(&future->mutex);
  if (!future->done) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);

    ts.tv_nsec += msec * 1000000;
    if (ts.tv_nsec >= 1000000000) {
      ts.tv_sec += ts.tv_nsec / 1000000000;
      ts.tv_nsec = ts.tv_nsec % 1000000000;
    }
    int ret = pthread_cond_timedwait(&future->resolved, &future->mutex, &ts);
    if (ret == ETIMEDOUT) {
      char buf[1000];
      sprintf(buf, "Timeout [%u ms] reached waiting for future", msec);
      // TODO(networking): figure out error codes across the system for the
      // language
      pthread_mutex_unlock(&future->mutex);
      valk_arc_release(future);
      return valk_arc_box_err(buf);
    } else if (ret != 0) {
      char buf[1000];
      sprintf(buf, "Unexpected error during [pthread_cond_timedwait]: %s",
              strerror(errno));
      pthread_mutex_unlock(&future->mutex);
      valk_arc_release(future);
      return valk_arc_box_err(buf);
    }
  }
  valk_arc_box *res = future->item;
  valk_arc_retain(res);

  pthread_mutex_unlock(&future->mutex);
  valk_arc_release(future);
  return res;
}

valk_promise *valk_promise_new(valk_future *future) {
  valk_promise *self = valk_mem_alloc(sizeof(valk_promise));
  self->item = future;
  self->refcount = 1;
  self->allocator = valk_thread_ctx.allocator;
  valk_arc_retain(future);
  return self;
}

void valk_promise_free(valk_promise *self) {
  valk_arc_release(self->item);
  valk_mem_allocator_free(self->allocator, self);
}

void valk_promise_respond(valk_promise *promise, valk_arc_box *result) {
  pthread_mutex_lock(&promise->item->mutex);

  int old = __atomic_fetch_add(&promise->item->done, 1, __ATOMIC_RELEASE);
  if (old) {
    printf(
        "Welll... this is awkward, the promise is already resolved.... what "
        "the fuck");
  } else {
    promise->item->item = result;
    pthread_cond_signal(&promise->item->resolved);
  }
  pthread_mutex_unlock(&promise->item->mutex);
}

static void *valk_worker_routine(void *arg) {
  // Use malloc for now, by default
  // probably should think of how to add this by default everywhere
  valk_mem_init_malloc();

  valk_worker *self = arg;
  printf("Starting Thread : %s\n", self->name);
  valk_task_queue *queue = self->queue;

  // pthread_setname_np(pthread_self(), self->name);

  pthread_mutex_lock(&queue->mutex);
  queue->numWorkers++;
  // if queue became empty after the pop, signal that its now empty
  pthread_cond_signal(&queue->workerReady);
  pthread_mutex_unlock(&queue->mutex);
  do {
    int res = 0;
    valk_task task;

    pthread_mutex_lock(&queue->mutex);

    if (queue->count == 0) {
      // if queue is empty until it has stuff
      // this will temporarily release the lock, and will wait on full signal
      pthread_cond_wait(&queue->notEmpty, &queue->mutex);
    }

    res = valk_work_pop(queue, &task);

    if (!res) {
      // Only do stuff if  pop succeeded, so nothing to do
      if (queue->count == 0) {
        // if queue became empty after the pop, signal that its now empty
        pthread_cond_signal(&queue->isEmpty);
      }

      if (task.type == VALK_TASK) {
        // only signal if we successfully popped, otherwise there was a
        // problem
        pthread_cond_signal(&queue->notFull);
        printf("MMM yummy task!\n");

        // Ok now lets execute the task

        valk_promise_respond(task.promise, task.func(task.arg));
        valk_arc_release(task.promise);
        // TODO(networking): How do we clean up the arg? maybe the callback
        // has to do it.
      } else if (task.type == VALK_POISON) {
        printf("%s : Swallowed poison\n", self->name);
        queue->numWorkers--;
        pthread_cond_signal(&queue->workerDead);
        pthread_mutex_unlock(&queue->mutex);
        break;
      }
    }
    pthread_mutex_unlock(&queue->mutex);
  } while (1);

  return NULL;
}

int valk_start_pool(valk_worker_pool *pool) {
  pool->items = valk_mem_alloc(sizeof(valk_worker) * VALK_NUM_WORKERS);
  valk_work_init(&pool->queue, 8);

  for (size_t i = 0; i < VALK_NUM_WORKERS; i++) {
    pool->items[i].queue = &pool->queue;
    int len = snprintf(NULL, 0, "Worker [%ld]", i);
    pool->items[i].name = malloc(len + 1);
    snprintf(pool->items[i].name, len + 1, "Worker [%ld]", i);

    // Setting this attribute, makes it so you dont have to join the thread
    // when you shut it down. Since we dont care about the result its simpler to
    // do this and saves a bit of time at the end.
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

    int res = pthread_create(&pool->items[i].thread, &attr, valk_worker_routine,
                             (void *)&pool->items[i]);
    if (res) {
      perror("pthread_create");
      free(pool->items[i].name);
      return 1;
    }
    ++pool->count;
  }

  // Wait for all workers to become ready
  pthread_mutex_lock(&pool->queue.mutex);
  while (pool->queue.numWorkers < VALK_NUM_WORKERS) {
    pthread_cond_wait(&pool->queue.workerReady, &pool->queue.mutex);
  }
  pthread_mutex_unlock(&pool->queue.mutex);
  return 0;
}

void valk_drain_pool(valk_worker_pool *pool) {
  pthread_mutex_lock(&pool->queue.mutex);
  if (!pool->queue.isShuttingDown) {
    // put the queue in draining mode, to prevent incoming schedule requets
    pool->queue.isShuttingDown = 1;
    if (pool->queue.count > 0) {
      // if there are remaining items, drop em
      pthread_cond_wait(&pool->queue.isEmpty, &pool->queue.mutex);
    }
  } else {
    printf("Pool is already draining, not doing anything\n");
  }
  pthread_mutex_unlock(&pool->queue.mutex);
}

void valk_free_pool(valk_worker_pool *pool) {
  pthread_mutex_lock(&pool->queue.mutex);
  if (pool->queue.count > 0) {
    // if there are remaining items, resolve them
    // TODO(networking):  this can be avoided with recursive mutexes, through
    // attributes
    pthread_mutex_unlock(&pool->queue.mutex);
    valk_drain_pool(pool);
  } else {
    pthread_mutex_unlock(&pool->queue.mutex);
  }

  // wait for all workers to become dead
  pthread_mutex_lock(&pool->queue.mutex);
  valk_task poison = {.type = VALK_POISON};
  size_t numWorkers = pool->queue.numWorkers;
  for (size_t i = 0; i < numWorkers; i++) {
    valk_work_add(&pool->queue, poison);
    pthread_cond_signal(&pool->queue.notEmpty);
  }
  pthread_mutex_unlock(&pool->queue.mutex);

  pthread_mutex_lock(&pool->queue.mutex);
  while (pool->queue.numWorkers > 0) {
    pthread_cond_wait(&pool->queue.workerDead, &pool->queue.mutex);
  }
  pthread_mutex_unlock(&pool->queue.mutex);

  for (size_t i = 0; i < numWorkers; i++) {
    // TODO(networking): More elegant  solution is poison message in queue, but
    // im too lazy now
    // void *res;
    // pthread_join(pool->items[i].thread, &res);
    free(pool->items[i].name);
  }
  free(pool->items);

  valk_work_free(&pool->queue);

  // free(pool->name);
}

valk_future *valk_schedule(valk_worker_pool *pool, valk_arc_box *arg,
                           valk_arc_box *(*func)(valk_arc_box *)) {
  valk_task_queue *queue = &pool->queue;
  pthread_mutex_lock(&queue->mutex);
  valk_future *res;

  if (queue->isShuttingDown) {
    res = valk_future_done(
        valk_arc_box_err("Error trying to submit work to threadpool, "
                         "while its shutting down"));
  } else {
    if (queue->capacity == queue->count) {
      // if queue is full block until it has space
      // this will temporarily release the lock, and will wait on full signal
      pthread_cond_wait(&queue->notFull, &queue->mutex);
    }

    res = valk_future_new();

    valk_task task = {.type = VALK_TASK,
                      .arg = arg,
                      .func = func,
                      .promise = valk_promise_new(res)};

    int err = valk_work_add(queue, task);
    if (err) {
      valk_promise_respond(
          task.promise,
          valk_arc_box_err("Could not add task to queue for pool scheduling"));
      valk_arc_release(task.promise);
      valk_arc_release(task.arg);
    }
    pthread_cond_signal(&queue->notEmpty);
  }

  pthread_mutex_unlock(&pool->queue.mutex);
  return res;
}

typedef struct {
  valk_promise *promise;
  valk_arc_box *result;
} __valk_resolve_promise;

static valk_arc_box *__valk_pool_resolve_promise_cb(valk_arc_box *arg) {
  if (arg->type != VALK_SUC) {
    // cant resolve an error ??? why the heck did that even get in here
    // TODO(networking): maybe turn this into a hard assert
    // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
    fprintf(stderr,
            "ERROR: Invalid condition, could not resolve an error "
            "boxsed promise.\n");
    return arg;
  }
  __valk_resolve_promise *a = arg->item;
  valk_promise_respond(a->promise, a->result);
  return arg;
}

void valk_pool_resolve_promise(valk_worker_pool *pool, valk_promise *promise,
                               valk_arc_box *result) {
  valk_arc_box *arg =
      valk_arc_box_new(VALK_SUC, sizeof(__valk_resolve_promise));
  __valk_resolve_promise *pair = arg->item;
  pair->promise = promise;
  pair->result = result;

  valk_future *res = valk_schedule(pool, arg, __valk_pool_resolve_promise_cb);
  valk_arc_retain(promise);
  valk_arc_release(res);  // dont need the result
}
