#pragma once
#define _GNU_SOURCE
// TODO(networking): Abstract pthread away in here, only available on posix
// system very inconsistent api across different systems too
#include <pthread.h>
#include <stdint.h>

#include "memory.h"

// #define VALK_ARC_DEBUG
#define VALK_ARC_TRACE_DEPTH 10

#define valk_work_init(queue, _capacity)                             \
  do {                                                               \
    (queue)->capacity = (_capacity);                                 \
    (queue)->items = malloc(sizeof(valk_task) * (_capacity));        \
    (queue)->count = 0;                                              \
    (queue)->numWorkers = 0;                                         \
    (queue)->isShuttingDown = 0;                                     \
    (queue)->futureSlab = valk_slab_new(sizeof(valk_future), 1000);  \
    (queue)->promiseSlab = valk_slab_new(sizeof(valk_promise), 100); \
    pthread_mutex_init(&(queue)->mutex, 0);                          \
    pthread_cond_init(&(queue)->isEmpty, 0);                         \
    pthread_cond_init(&(queue)->notEmpty, 0);                        \
    pthread_cond_init(&(queue)->notFull, 0);                         \
    pthread_cond_init(&(queue)->workerReady, 0);                     \
    pthread_cond_init(&(queue)->workerDead, 0);                      \
  } while (0)

#define valk_work_free(queue)                    \
  do {                                           \
    free((queue)->items);                        \
    pthread_mutex_destroy(&(queue)->mutex);      \
    pthread_cond_destroy(&(queue)->isEmpty);     \
    pthread_cond_destroy(&(queue)->notEmpty);    \
    pthread_cond_destroy(&(queue)->notFull);     \
    pthread_cond_destroy(&(queue)->workerReady); \
    pthread_cond_destroy(&(queue)->workerDead);  \
  } while (0)

#define valk_work_add(queue, _task)                                          \
  ({                                                                         \
    int _err = 0;                                                            \
    do {                                                                     \
      if ((queue)->count < (queue)->capacity) {                              \
        (queue)                                                              \
            ->items[((queue)->idx + (queue)->count++) % (queue)->capacity] = \
            (_task);                                                         \
      } else {                                                               \
        printf("ERR[%s:%d]: worker queue is full, not pushing \n", __FILE__, \
               __LINE__);                                                    \
        _err = 1;                                                            \
      }                                                                      \
    } while (0);                                                             \
    _err;                                                                    \
  })

#define valk_work_pop(queue, _task)                                           \
  ({                                                                          \
    int _err = 0;                                                             \
    do {                                                                      \
      if ((queue)->count == 0) {                                              \
        _err = 1;                                                             \
        printf("ERR[%s:%d]: worker queue is empty , not popping\n", __FILE__, \
               __LINE__);                                                     \
      } else {                                                                \
        (*_task) = (queue)->items[((queue)->idx++) % (queue)->capacity];      \
        --(queue)->count;                                                     \
      }                                                                       \
    } while (0);                                                              \
    _err;                                                                     \
  })

#define valk_arc_retain(ref)                                                  \
  ({                                                                          \
    size_t __old = __atomic_fetch_add(&(ref)->refcount, 1, __ATOMIC_RELEASE); \
    valk_capture_trace(VALK_TRACE_ACQUIRE, __old + 1, ref);                   \
    (ref);                                                                    \
  })

// This is bootleg arc
#define valk_arc_release(ref)                                               \
  do {                                                                      \
    size_t old = __atomic_fetch_sub(&(ref)->refcount, 1, __ATOMIC_RELEASE); \
    valk_capture_trace(VALK_TRACE_RELEASE, old - 1, ref);                   \
    /*char _buf[512];                                                       \
    pthread_getname_np(pthread_self(), _buf, sizeof(_buf));*/               \
    if (old == 1) {                                                         \
      /* printf("[%s] Arc is freeing %d\n", _buf, old); */                  \
      /* Only free using the allocator if a custom one is not defined*/     \
      if ((ref)->free) {                                                    \
        valk_arc_trace_report_print(ref);                                   \
        (ref)->free(ref);                                                   \
      } else if ((ref)->allocator) {                                        \
        valk_mem_allocator_free((ref)->allocator, (ref));                   \
      }                                                                     \
    } else {                                                                \
      /* printf("[%s] Arc is decrementing %d\n", _buf, old); */             \
    }                                                                       \
  } while (0)

typedef enum { VALK_SUC, VALK_ERR } valk_res_t;

#ifdef VALK_ARC_DEBUG
#include <dlfcn.h>
#include <execinfo.h>
#define VALK_ARC_TRACE_MAX 50

typedef enum { VALK_TRACE_ACQUIRE, VALK_TRACE_RELEASE } valk_trace_kind_e;
typedef struct valk_arc_trace_info {
  valk_trace_kind_e kind;
  const char *file;
  const char *function;
  int line;
  size_t refcount;
  void *stack[VALK_ARC_TRACE_DEPTH];
  size_t size;
} valk_arc_trace_info;

#define valk_capture_trace(_kind, _refcount, ref)                             \
  do {                                                                        \
    size_t _old = __atomic_fetch_add(&(ref)->nextTrace, 1, __ATOMIC_RELEASE); \
    VALK_ASSERT(                                                              \
        _old < VALK_ARC_TRACE_MAX,                                            \
        "Cannot keep tracing this variable, please increase the max traces"); \
    (ref)->traces[_old].kind = (_kind);                                       \
    (ref)->traces[_old].file = __FILE__;                                      \
    (ref)->traces[_old].function = __func__;                                  \
    (ref)->traces[_old].line = __LINE__;                                      \
    (ref)->traces[_old].refcount = (_refcount);                               \
    (ref)->traces[_old].size =                                                \
        backtrace((ref)->traces[_old].stack, VALK_ARC_TRACE_DEPTH);           \
  } while (0)

#define valk_arc_trace_report_print(report) \
  __valk_arc_trace_report_print((report)->traces, (report)->nextTrace)

void __valk_arc_trace_report_print(valk_arc_trace_info *traces, size_t num);

#else
#define valk_capture_trace(_kind, _refcount, ref)
#define valk_arc_trace_report_print(report)
#endif

typedef struct valk_arc_box {
  valk_res_t type;
  size_t refcount;
  valk_mem_allocator_t *allocator;
#ifdef VALK_ARC_DEBUG
  valk_arc_trace_info traces[VALK_ARC_TRACE_MAX];
  size_t nextTrace;
#endif
  size_t capacity;
  void (*free)(struct valk_arc_box *);
  void *item;
} valk_arc_box;

valk_arc_box *valk_arc_box_new(valk_res_t type, size_t capacity);
void valk_arc_box_init(valk_arc_box *self, valk_res_t type, size_t capacity);

valk_arc_box *valk_arc_box_err(const char *msg);

struct valk_future_and_then {
  void *arg;  // TODO(networking): should i provide a free callback for this?
  void (*cb)(void *, valk_arc_box *);
};

typedef void(valk_future_free_cb)(void *userData, void *future);
typedef struct valk_future {
  int done;
  size_t refcount;
  pthread_mutex_t mutex;
  pthread_cond_t resolved;
  valk_arc_box *item;

#ifdef VALK_ARC_DEBUG
  valk_arc_trace_info traces[VALK_ARC_TRACE_MAX];
  size_t nextTrace;
#endif
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

valk_arc_box *valk_future_await(valk_future *future);
valk_arc_box *valk_future_await_timeout(valk_future *future, uint32_t msec);

typedef struct valk_promise {
  valk_future *item;
} valk_promise;

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
    valk_promise promise;
  };
} valk_task;

typedef struct {
  pthread_mutex_t mutex;
  pthread_cond_t isEmpty;
  pthread_cond_t notEmpty;
  pthread_cond_t notFull;
  pthread_cond_t workerReady;
  pthread_cond_t workerDead;
  valk_slab_t *futureSlab;
  valk_slab_t *promiseSlab;
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
