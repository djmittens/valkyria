#include "concurrency.h"
#include "collections.h"
#define _GNU_SOURCE
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const int VALK_NUM_WORKERS = 4;

valk_arc_box *valk_arc_box_suc(void *succ, valk_callback_void *free) {
  valk_arc_box *res = malloc(sizeof(valk_arc_box));
  res->type = VALK_SUC;
  res->succ = succ;
  res->free = free;
  res->refcount = 1;
  return res;
}

valk_arc_box *valk_arc_box_err(int code, const char *msg) {
  valk_arc_box *res = malloc(sizeof(valk_arc_box));
  res->type = VALK_ERR;
  res->err.size = strlen(msg);
  res->err.code = code;
  res->err.msg = strdup(msg);
  res->free = NULL;
  res->refcount = 1;
  return res;
}

static void _valk_arc_box_free(valk_arc_box *result) {
  switch (result->type) {
  case VALK_SUC:
    result->free(result->succ);
    break;
  case VALK_ERR:
    free(result->err.msg);
    break;
  };
  free(result);
}

void valk_arc_box_release(valk_arc_box *result) {
  valk_arc_release(result, _valk_arc_box_free);
}

valk_future *valk_future_new(void) {
  valk_future *res = malloc(sizeof(valk_future));
  pthread_mutex_init(&res->mutex, 0);
  pthread_cond_init(&res->resolved, 0);

  res->refcount = 1;
  res->done = 0;
  res->item = NULL;
  return res;
}

valk_future *valk_future_done(valk_arc_box *item) {
  valk_future *res = valk_future_new();
  res->done = 1;
  res->item = item;
  return res;
}

static void _valk_future_free(valk_future *future) {
  pthread_cond_destroy(&future->resolved);
  pthread_mutex_destroy(&future->mutex);
  if (future->done) {
    valk_arc_box_release(future->item);
  }
  free(future);
}

void valk_future_release(valk_future *future) {
  valk_arc_release(future, _valk_future_free);
}

valk_arc_box *valk_future_await(valk_future *future) {
  pthread_mutex_lock(&future->mutex);
  if (!future->done) {
    pthread_cond_wait(&future->resolved, &future->mutex);
  }
  valk_arc_box *res = future->item;
  valk_arc_retain(res);

  pthread_mutex_unlock(&future->mutex);
  valk_future_release(future);
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
      valk_future_release(future);
      return valk_arc_box_err(1, buf);
    } else if (ret != 0) {
      char buf[1000];
      sprintf(buf, "Unexpected error during [pthread_cond_timedwait]: %s",
              strerror(errno));
      pthread_mutex_unlock(&future->mutex);
      valk_future_release(future);
      return valk_arc_box_err(1, buf);
    }
  }
  valk_arc_box *res = future->item;
  valk_arc_retain(res);

  pthread_mutex_unlock(&future->mutex);
  valk_future_release(future);
  return res;
}

valk_promise *valk_promise_new(valk_future *future) {
  valk_promise *res = malloc(sizeof(valk_promise));
  res->item = future;
  res->refcount = 1;
  return res;
}

static void _valk_promise_free(valk_promise *promise) {
  valk_future_release(promise->item);
  free(promise);
}

void valk_promise_release(valk_promise *promise) {
  valk_arc_release(promise, _valk_promise_free);
}

void valk_promise_respond(valk_promise *promise, valk_arc_box *result) {
  pthread_mutex_lock(&promise->item->mutex);

  int old = __atomic_fetch_add(&promise->item->done, 1, __ATOMIC_RELEASE);
  if (old) {
    printf("Welll... this is awkward, the promise is already resolved.... what "
           "the fuck");
  } else {
    promise->item->item = result;
    pthread_cond_signal(&promise->item->resolved);
  }
  pthread_mutex_unlock(&promise->item->mutex);
}

static void *valk_worker_routine(void *arg) {
  valk_worker *self = arg;
  printf("Starting Thread : %s\n", self->name);
  valk_task_queue *queue = self->queue;

  pthread_setname_np(pthread_self(), self->name);

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
        valk_promise_release(task.promise);
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
  pool->items = malloc(sizeof(valk_worker) * VALK_NUM_WORKERS);
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
    void *res;
    // pthread_join(pool->items[i].thread, &res);
    free(pool->items[i].name);
  }
  free(pool->items);

  valk_work_free(&pool->queue);

  // free(pool->name);
}

valk_future *valk_schedule(valk_worker_pool *pool, valk_arc_box *arg,
                           valk_callback *func) {
  valk_task_queue *queue = &pool->queue;
  pthread_mutex_lock(&queue->mutex);
  valk_future *res;
  if (queue->isShuttingDown) {
    res = valk_future_done(valk_arc_box_err(
        1,
        "Error trying to submit work to threadpool, while its shutting down"));
  } else {
    if (queue->capacity == queue->count) {
      // if queue is full block until it has space
      // this will temporarily release the lock, and will wait on full signal
      pthread_cond_wait(&queue->notFull, &queue->mutex);
    }

    res = valk_future_new();
    valk_arc_retain(res);

    valk_task task = {.type = VALK_TASK,
                      .arg = arg,
                      .func = func,
                      .promise = valk_promise_new(res)};
    int err = valk_work_add(queue, task);
    if (err) {
      valk_promise_respond(
          task.promise,
          valk_arc_box_err(1,
                           "Could not add task to queue for pool scheduling"));
      valk_promise_release(task.promise);
      valk_arc_box_release(task.arg);
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

void __valk_resolve_promise_free(void *arg) {
  __valk_resolve_promise *self = arg;
  valk_promise_release(self->promise);
  valk_arc_box_release(self->result);
  free(self);
}

static valk_arc_box *__valk_pool_resolve_promise_cb(valk_arc_box *arg) {
  if (arg->type != VALK_SUC) {
    // cant resolve an error ??? why the heck did that even get in here
    // TODO(networking): maybe turn this into a hard assert
    fprintf(stderr, "ERROR: Invalid condition, could not resolve an error "
                    "boxsed promise.\n");
    return arg;
  }
  __valk_resolve_promise *a = arg->succ;
  valk_promise_respond(a->promise, a->result);
  return arg;
}

void valk_pool_resolve_promise(valk_worker_pool *pool, valk_promise *promise,
                               valk_arc_box *result) {
  __valk_resolve_promise *pair = malloc(sizeof(__valk_resolve_promise));
  pair->promise = promise;
  pair->result = result;
  valk_future *res =
      valk_schedule(pool, valk_arc_box_suc(pair, __valk_resolve_promise_free),
                    __valk_pool_resolve_promise_cb);
  valk_future_release(res); // dont need the result
}
