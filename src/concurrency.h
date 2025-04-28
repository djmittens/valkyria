#pragma once
// TODO(networking): Abstract pthread away in here, only available on posix
// system very inconsistent api across different systems too
#define _GNU_SOURCE
#include "memory.h"
#include <pthread.h>
#include <stdint.h>

#define valk_work_init(queue, _capacity)                                       \
  do {                                                                         \
    (queue)->capacity = (_capacity);                                           \
    (queue)->items = malloc(sizeof(valk_task) * (_capacity));                  \
    (queue)->count = 0;                                                        \
    (queue)->numWorkers = 0;                                                   \
    (queue)->isShuttingDown = 0;                                               \
    valk_slab_alloc_init(&(queue)->futureSlab, sizeof(valk_future), 1000);     \
    valk_slab_alloc_init(&(queue)->promiseSlab, sizeof(valk_promise), 100);    \
    pthread_mutex_init(&(queue)->mutex, 0);                                    \
    pthread_cond_init(&(queue)->isEmpty, 0);                                   \
    pthread_cond_init(&(queue)->notEmpty, 0);                                  \
    pthread_cond_init(&(queue)->notFull, 0);                                   \
    pthread_cond_init(&(queue)->workerReady, 0);                               \
    pthread_cond_init(&(queue)->workerDead, 0);                                \
  } while (0)

#define valk_work_free(queue)                                                  \
  do {                                                                         \
    free((queue)->items);                                                      \
    pthread_mutex_destroy(&(queue)->mutex);                                    \
    pthread_cond_destroy(&(queue)->isEmpty);                                   \
    pthread_cond_destroy(&(queue)->notEmpty);                                  \
    pthread_cond_destroy(&(queue)->notFull);                                   \
    pthread_cond_destroy(&(queue)->workerReady);                               \
    pthread_cond_destroy(&(queue)->workerDead);                                \
  } while (0)

#define valk_work_add(queue, _task)                                            \
  ({                                                                           \
    int _err = 0;                                                              \
    do {                                                                       \
      if ((queue)->count < (queue)->capacity) {                                \
        (queue)                                                                \
            ->items[((queue)->idx + (queue)->count++) % (queue)->capacity] =   \
            (_task);                                                           \
      } else {                                                                 \
        printf("ERR[%s:%d]: worker queue is full, not pushing \n", __FILE__,   \
               __LINE__);                                                      \
        _err = 1;                                                              \
      }                                                                        \
    } while (0);                                                               \
    _err;                                                                      \
  })

#define valk_work_pop(queue, _task)                                            \
  ({                                                                           \
    int _err = 0;                                                              \
    do {                                                                       \
      if ((queue)->count == 0) {                                               \
        _err = 1;                                                              \
        printf("ERR[%s:%d]: worker queue is empty , not popping\n", __FILE__,  \
               __LINE__);                                                      \
      } else {                                                                 \
        (*_task) = (queue)->items[((queue)->idx++) % (queue)->capacity];       \
        --(queue)->count;                                                      \
      }                                                                        \
    } while (0);                                                               \
    _err;                                                                      \
  })

#define valk_arc_retain(ref)                                                   \
  ({                                                                           \
    do {                                                                       \
      __atomic_fetch_add(&(ref)->refcount, 1, __ATOMIC_RELEASE);               \
    } while (0);                                                               \
    (ref);                                                                     \
  })

// This is bootleg arc
#define valk_arc_release(ref)                                                  \
  do {                                                                         \
    int old = __atomic_fetch_sub(&(ref)->refcount, 1, __ATOMIC_RELEASE);       \
    /*char _buf[512];                                                          \
    pthread_getname_np(pthread_self(), _buf, sizeof(_buf));*/                  \
    if (old == 1) {                                                            \
      /* printf("[%s] Arc is freeing %d\n", _buf, old); */                     \
      /* Only free using the allocator if a custom one is not defined*/        \
      if ((ref)->free) {                                                       \
        (ref)->free(ref);                                                      \
      } else {                                                                 \
        valk_mem_allocator_free((ref)->allocator, (ref));                      \
      }                                                                        \
    } else {                                                                   \
      /* printf("[%s] Arc is decrementing %d\n", _buf, old); */                \
    }                                                                          \
  } while (0)

typedef enum { VALK_SUC, VALK_ERR } valk_res_t;

typedef struct valk_arc_box {
  valk_res_t type;
  int refcount;
  valk_mem_allocator_t *allocator;
  size_t capacity;
  void (*free)(struct valk_arc_box *);
  void *item;
} valk_arc_box;

valk_arc_box *valk_arc_box_new(valk_res_t type, size_t capacity);

valk_arc_box *valk_arc_box_err(const char *msg);

struct valk_future_and_then {
  void *arg;
  void (*cb)(void *, valk_arc_box *);
};

typedef void(valk_future_free_cb)(void *userData, void *future);
typedef struct valk_future {
  int done;
  int refcount;
  pthread_mutex_t mutex;
  pthread_cond_t resolved;
  valk_arc_box *item;
  void (*free)(struct valk_future *);
  valk_mem_allocator_t *allocator;
  struct {
    struct valk_future_and_then *items;
    size_t count;
    size_t capacity;
  } andThen;
} valk_future;

valk_future *valk_future_new();
valk_future *valk_future_done(valk_arc_box *item);
void valk_future_and_then(valk_future *self,
                          struct valk_future_and_then *callback);

void valk_future_free(valk_future *self);

valk_arc_box *valk_future_await(valk_future *future);
valk_arc_box *valk_future_await_timeout(valk_future *future, uint32_t msec);

typedef struct valk_promise {
  valk_future *item;
  int refcount;
  valk_mem_allocator_t *allocator;
  void (*free)(struct valk_promise *);
} valk_promise;

valk_promise *valk_promise_new(valk_future *future);
void valk_promise_free(valk_promise *self);
void valk_promise_respond(valk_promise *promise, valk_arc_box *result);

typedef enum { VALK_TASK, VALK_POISON } valk_task_type_t;
typedef struct {
  valk_task_type_t type;
  // Task
  struct {
    // TODO(networking): figure out the lifetime for this arg.
    // who owns this ? when is it freed? in the callback?
    valk_arc_box *arg;
    valk_arc_box *(*func)(valk_arc_box *);
    valk_promise *promise;
  };
} valk_task;

typedef struct {
  pthread_mutex_t mutex;
  pthread_cond_t isEmpty;
  pthread_cond_t notEmpty;
  pthread_cond_t notFull;
  pthread_cond_t workerReady;
  pthread_cond_t workerDead;
  valk_slab_t futureSlab;
  valk_slab_t promiseSlab;
  valk_task *items;
  size_t idx;
  size_t count;
  size_t capacity;
  size_t isShuttingDown;
  size_t numWorkers;
} valk_task_queue;

typedef struct valk_worker {
  char *name;
  valk_task_queue *queue;
  pthread_t thread;
} valk_worker;

typedef struct {
  // char *name;
  // Dynamic List
  valk_worker *items;
  size_t count;
  size_t capacity;
  valk_task_queue queue;
} valk_worker_pool;

int valk_start_pool(valk_worker_pool *pool);
valk_future *valk_schedule(valk_worker_pool *pool, valk_arc_box *arg,
                           valk_arc_box *(*func)(valk_arc_box *));

void valk_drain_pool(valk_worker_pool *pool);
void valk_free_pool(valk_worker_pool *pool);

void valk_pool_resolve_promise(valk_worker_pool *pool, valk_promise *promise,
                               valk_arc_box *result);
