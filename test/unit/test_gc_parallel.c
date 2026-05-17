#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/gc.h"
#include "../../src/parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

void test_gc_coordinator_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_create(NULL);

  VALK_TEST_ASSERT(atomic_load(&valk_sys->phase) == VALK_GC_PHASE_IDLE,
                   "Phase should be IDLE after init");
  VALK_TEST_ASSERT(atomic_load(&valk_sys->threads_registered) == 1,
                   "threads_registered should be 1");

  VALK_PASS();
}

void test_gc_barrier_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_barrier_t barrier;
  valk_barrier_init(&barrier, 1);

  valk_barrier_wait(&barrier);

  valk_barrier_destroy(&barrier);

  VALK_PASS();
}

typedef struct {
  valk_barrier_t *barrier;
  int *counter;
  pthread_mutex_t *mutex;
} barrier_ctx_t;

static void *barrier_thread(void *arg) {
  barrier_ctx_t *ctx = arg;

  pthread_mutex_lock(ctx->mutex);
  (*ctx->counter)++;
  pthread_mutex_unlock(ctx->mutex);

  valk_barrier_wait(ctx->barrier);

  return nullptr;
}

void test_gc_barrier_multithread(VALK_TEST_ARGS()) {
  VALK_TEST();

  const int NUM_THREADS = 4;
  valk_barrier_t barrier;
  valk_barrier_init(&barrier, NUM_THREADS);

  int counter = 0;
  pthread_mutex_t mutex;
  pthread_mutex_init(&mutex, nullptr);

  pthread_t threads[NUM_THREADS];
  barrier_ctx_t ctxs[NUM_THREADS];

  for (int i = 0; i < NUM_THREADS; i++) {
    ctxs[i].barrier = &barrier;
    ctxs[i].counter = &counter;
    ctxs[i].mutex = &mutex;
    pthread_create(&threads[i], nullptr, barrier_thread, &ctxs[i]);
  }

  for (int i = 0; i < NUM_THREADS; i++) {
    pthread_join(threads[i], nullptr);
  }

  VALK_TEST_ASSERT(counter == NUM_THREADS, "All threads should have incremented counter");

  pthread_mutex_destroy(&mutex);
  valk_barrier_destroy(&barrier);

  VALK_PASS();
}

void test_gc_mark_queue_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  VALK_TEST_ASSERT(valk_gc_mark_queue_empty(&queue), "Queue should be empty");

  valk_gc_mark_queue_destroy(&queue);

  VALK_PASS();
}

void test_gc_mark_queue_push_pop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap_t *heap = valk_gc_heap_create(10 * 1024 * 1024);

  valk_lval_t *vals[10];
  for (int i = 0; i < 10; i++) {
    vals[i] = valk_gc_heap_alloc(heap, sizeof(valk_lval_t));
    vals[i]->flags = LVAL_NUM;
    vals[i]->num = i;
  }

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  for (int i = 0; i < 10; i++) {
    valk_gc_mark_queue_push(&queue, vals[i]);
  }

  VALK_TEST_ASSERT(!valk_gc_mark_queue_empty(&queue), "Queue should not be empty");

  for (int i = 9; i >= 0; i--) {
    valk_lval_t *popped = valk_gc_mark_queue_pop(&queue);
    VALK_TEST_ASSERT(popped == vals[i], "Pop should return vals[%d]", i);
  }

  VALK_TEST_ASSERT(valk_gc_mark_queue_empty(&queue), "Queue should be empty after pops");

  valk_lval_t *empty_pop = valk_gc_mark_queue_pop(&queue);
  VALK_TEST_ASSERT(empty_pop == nullptr, "Pop from empty queue should return nullptr");

  valk_gc_mark_queue_destroy(&queue);
  valk_gc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_mark_queue_steal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap_t *heap = valk_gc_heap_create(10 * 1024 * 1024);

  valk_lval_t *vals[5];
  for (int i = 0; i < 5; i++) {
    vals[i] = valk_gc_heap_alloc(heap, sizeof(valk_lval_t));
    vals[i]->flags = LVAL_NUM;
    vals[i]->num = i;
  }

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  for (int i = 0; i < 5; i++) {
    valk_gc_mark_queue_push(&queue, vals[i]);
  }

  valk_lval_t *stolen = valk_gc_mark_queue_steal(&queue);
  VALK_TEST_ASSERT(stolen == vals[0], "Steal should return first element (FIFO)");

  stolen = valk_gc_mark_queue_steal(&queue);
  VALK_TEST_ASSERT(stolen == vals[1], "Second steal should return second element");

  valk_lval_t *popped = valk_gc_mark_queue_pop(&queue);
  VALK_TEST_ASSERT(popped == vals[4], "Pop should return last element (LIFO)");

  valk_gc_mark_queue_destroy(&queue);
  valk_gc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_mark_queue_dynamic_growth(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap_t *heap = valk_gc_heap_create(100 * 1024 * 1024);

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  const size_t COUNT = VALK_GC_MARK_QUEUE_INITIAL_SIZE + 100;
  int pushed = 0;
  for (size_t i = 0; i < COUNT; i++) {
    valk_lval_t *val = valk_gc_heap_alloc(heap, sizeof(valk_lval_t));
    val->flags = LVAL_NUM;
    valk_gc_mark_queue_push(&queue, val);
    pushed++;
  }

  VALK_TEST_ASSERT((size_t)pushed == COUNT,
                   "Should push all items (pushed=%d, expected=%zu)", pushed, COUNT);

  int popped = 0;
  while (valk_gc_mark_queue_pop(&queue) != nullptr) {
    popped++;
  }

  VALK_TEST_ASSERT(pushed == popped,
                   "Should pop all pushed items (pushed=%d, popped=%d)", pushed, popped);

  valk_gc_mark_queue_destroy(&queue);
  valk_gc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_thread_register_unregister(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_create(NULL);
  valk_gc_thread_unregister();

  size_t before = atomic_load(&valk_sys->threads_registered);

  valk_gc_thread_register();
  VALK_TEST_ASSERT(valk_thread_ctx.gc_registered, "Should be registered");
  VALK_TEST_ASSERT(atomic_load(&valk_sys->threads_registered) == before + 1,
                   "threads_registered should increase");

  size_t my_id = valk_thread_ctx.gc_thread_id;
  VALK_TEST_ASSERT(valk_sys->threads[my_id].active, "Thread slot should be active");

  valk_gc_thread_unregister();
  VALK_TEST_ASSERT(!valk_thread_ctx.gc_registered, "Should be unregistered");
  VALK_TEST_ASSERT(!valk_sys->threads[my_id].active, "Thread slot should be inactive");

  VALK_PASS();
}

void test_gc_safe_point_idle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_create(NULL);
  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);

  VALK_GC_SAFE_POINT();

  VALK_PASS();
}

typedef struct {
  valk_gc_mark_queue_t *queue;
  valk_lval_t **vals;
  int count;
  int stolen;
} steal_ctx_t;

static void *stealer_thread(void *arg) {
  steal_ctx_t *ctx = arg;
  ctx->stolen = 0;
  for (int i = 0; i < ctx->count * 2; i++) {
    valk_lval_t *val = valk_gc_mark_queue_steal(ctx->queue);
    if (val != nullptr) {
      ctx->stolen++;
    }
  }
  return nullptr;
}

void test_gc_mark_queue_concurrent_steal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap_t *heap = valk_gc_heap_create(10 * 1024 * 1024);

  const int NUM_VALS = 100;
  valk_lval_t *vals[NUM_VALS];
  for (int i = 0; i < NUM_VALS; i++) {
    vals[i] = valk_gc_heap_alloc(heap, sizeof(valk_lval_t));
    vals[i]->flags = LVAL_NUM;
    vals[i]->num = i;
  }

  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);

  for (int i = 0; i < NUM_VALS; i++) {
    valk_gc_mark_queue_push(&queue, vals[i]);
  }

  const int NUM_STEALERS = 3;
  pthread_t threads[NUM_STEALERS];
  steal_ctx_t ctxs[NUM_STEALERS];

  for (int i = 0; i < NUM_STEALERS; i++) {
    ctxs[i].queue = &queue;
    ctxs[i].vals = vals;
    ctxs[i].count = NUM_VALS;
    ctxs[i].stolen = 0;
    pthread_create(&threads[i], nullptr, stealer_thread, &ctxs[i]);
  }

  int owner_popped = 0;
  while (true) {
    valk_lval_t *val = valk_gc_mark_queue_pop(&queue);
    if (val == nullptr) break;
    owner_popped++;
  }

  for (int i = 0; i < NUM_STEALERS; i++) {
    pthread_join(threads[i], nullptr);
  }

  int total_stolen = 0;
  for (int i = 0; i < NUM_STEALERS; i++) {
    total_stolen += ctxs[i].stolen;
  }

  int total = owner_popped + total_stolen;
  VALK_TEST_ASSERT(total == NUM_VALS, 
                   "Total processed should equal NUM_VALS (got %d, expected %d)", 
                   total, NUM_VALS);

  valk_gc_mark_queue_destroy(&queue);
  valk_gc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_phase_transitions(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_create(NULL);

  VALK_TEST_ASSERT(atomic_load(&valk_sys->phase) == VALK_GC_PHASE_IDLE,
                   "Should start IDLE");

  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  bool cas = atomic_compare_exchange_strong(&valk_sys->phase, &expected,
                                             VALK_GC_PHASE_STW_REQUESTED);
  VALK_TEST_ASSERT(cas, "CAS to STW_REQUESTED should succeed");
  VALK_TEST_ASSERT(atomic_load(&valk_sys->phase) == VALK_GC_PHASE_STW_REQUESTED,
                   "Phase should be STW_REQUESTED");

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_MARKING);
  VALK_TEST_ASSERT(atomic_load(&valk_sys->phase) == VALK_GC_PHASE_MARKING,
                   "Phase should be MARKING");

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_SWEEPING);
  VALK_TEST_ASSERT(atomic_load(&valk_sys->phase) == VALK_GC_PHASE_SWEEPING,
                   "Phase should be SWEEPING");

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);
  VALK_TEST_ASSERT(atomic_load(&valk_sys->phase) == VALK_GC_PHASE_IDLE,
                   "Phase should be IDLE again");

  VALK_PASS();
}

// Root-stack tests removed: the explicit root_stack mechanism was
// retired in favor of conservative native-stack scanning at safepoints
// (see src/gc_mark.c::scan_thread_native_stack). The runtime now
// discovers roots automatically by walking each registered thread's
// native C stack — no compiler cooperation, no manual push/pop, no
// per-thread root array. Coverage of the same scenarios moved to the
// LSP UAT 33_orange_repro stress test (real AOT under typing load) and
// test_gc_unit's precise mark/sweep tests (which opt out via
// gc_disable_stack_scan to test the marker primitives directly).

void test_gc_safe_point_with_stw(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_system_create(NULL);
  
  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);
  
  VALK_GC_SAFE_POINT();
  
  valk_gc_thread_unregister();
  
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_gc_coordinator_init", test_gc_coordinator_init);
  valk_testsuite_add_test(suite, "test_gc_barrier_basic", test_gc_barrier_basic);
  valk_testsuite_add_test(suite, "test_gc_barrier_multithread", test_gc_barrier_multithread);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_init", test_gc_mark_queue_init);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_push_pop", test_gc_mark_queue_push_pop);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_steal", test_gc_mark_queue_steal);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_dynamic_growth", test_gc_mark_queue_dynamic_growth);
  valk_testsuite_add_test(suite, "test_gc_thread_register_unregister", test_gc_thread_register_unregister);
  valk_testsuite_add_test(suite, "test_gc_safe_point_idle", test_gc_safe_point_idle);
  valk_testsuite_add_test(suite, "test_gc_mark_queue_concurrent_steal", test_gc_mark_queue_concurrent_steal);
  valk_testsuite_add_test(suite, "test_gc_phase_transitions", test_gc_phase_transitions);
  valk_testsuite_add_test(suite, "test_gc_safe_point_with_stw", test_gc_safe_point_with_stw);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
