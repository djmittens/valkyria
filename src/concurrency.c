#include "concurrency.h"
#include "collections.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

const int VALK_NUM_WORKERS = 12;

valk_conc_res *valk_conc_res_suc(void *succ, valk_callback_void *free) {
  valk_conc_res *res = malloc(sizeof(valk_conc_res));
  res->type = VALK_SUC;
  res->succ = succ;
  res->free = free;
  return res;
}

valk_conc_res *valk_conc_res_err(int code, int size, char *msg) {
  valk_conc_res *res = malloc(sizeof(valk_conc_res));
  res->type = VALK_ERR;
  res->err.size = size;
  res->err.code = code;
  res->err.msg = msg;
  res->free = NULL;
  return res;
}

static void _valk_conc_res_free(valk_conc_res *result) {
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

void valk_conc_res_release(valk_conc_res *result) {
  valk_arc_release(result, _valk_conc_res_free);
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

static void _valk_future_free(valk_future *future) {
  pthread_cond_destroy(&future->resolved);
  if (future->done) {
    valk_conc_res_release(future->item);
  }
  free(future);
}

void valk_future_release(valk_future *future) {
  valk_arc_release(future, _valk_future_free);
}

valk_conc_res *valk_future_await(valk_future *future) {
  pthread_mutex_lock(&future->mutex);
  if (!future->done) {
    pthread_cond_wait(&future->resolved, &future->mutex);
  }
  valk_conc_res *res = valk_arc_retain(future->item);
  pthread_mutex_unlock(&future->mutex);
  valk_future_release(future);
  return res;
}

valk_promise *valk_promise_new(valk_future *future) {
  valk_promise *res = malloc(sizeof(valk_promise));
  res->item = valk_arc_retain(future);
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

void valk_promise_respond(valk_promise *promise, valk_conc_res *result) {
  pthread_mutex_lock(&promise->item->mutex);
  if (promise->item->done) {
    printf("Welll... this is awward, the promise is already resolved.... what "
           "the fuck");
  } else {
    promise->item->item = valk_arc_retain(result);
    __sync_fetch_and_add(&promise->item->done, 1);
    pthread_cond_signal(&promise->item->resolved);
  }
  pthread_mutex_unlock(&promise->item->mutex);
}

static void *valk_worker_routine(void *arg) {
  valk_worker *self = arg;
  printf("Starting Thread : %s\n", self->name);
  valk_task_queue *queue = self->queue;

  do {
    int res = 0;
    valk_task task;

    pthread_mutex_lock(&queue->mutex);

    if (queue->count == 0) {
      // if queue is full block until it has space
      // this will temporarily release the lock, and will wait on full signal
      pthread_cond_wait(&queue->notEmpty, &queue->mutex);
    }

    res = valk_work_pop(queue, &task);

    if (!res) {
      // only signal if we successfully popped, otherwise there was a problem
      pthread_cond_signal(&queue->notFull);

      // Ok now lets execute the task

      valk_promise_respond(task.promise, task.func(task.arg));

      // TODO(networking): How do we clean up the arg? maybe the callback has to
      // do it.
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
    int res = pthread_create(&pool->items[i].thread, NULL, valk_worker_routine,
                             (void *)&pool->items[i]);
    if (res) {
      perror("pthread_create");
      free(pool->items[i].name);
      return 1;
    }
    ++pool->count;
  }

  return 0;
}

int valk_drain_pool(valk_worker_pool *pool) { return 0; }

void valk_free_pool(valk_worker_pool *pool) {}

valk_future *valk_schedule(valk_worker_pool *pool, void *arg,
                           valk_callback *func) {
  valk_task_queue *queue = &pool->queue;
  pthread_mutex_lock(&queue->mutex);
  if (queue->capacity == queue->count) {
    // if queue is full block until it has space
    // this will temporarily release the lock, and will wait on full signal
    pthread_cond_wait(&queue->notFull, &queue->mutex);
  }

  valk_future *res = valk_future_new();
  valk_promise *promise = valk_promise_new(res);
  int err = valk_work_add(queue, arg, func, promise);

  pthread_cond_signal(&queue->notEmpty);

  pthread_mutex_unlock(&pool->queue.mutex);
  return res;
}
