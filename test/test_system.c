#include "testing.h"
#include "../src/gc.h"
#include "../src/memory.h"
#include "../src/aio/aio.h"

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>

static void alarm_handler(int sig) {
  (void)sig;
  fprintf(stderr, "TIMEOUT: test_system hung after 30s\n");
  _exit(1);
}

void test_system_create_sets_valk_sys(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);
  ASSERT_TRUE(valk_sys == sys);
  ASSERT_NOT_NULL(sys->heap);
  ASSERT_TRUE(sys->initialized);
  ASSERT_EQ(atomic_load(&sys->threads_registered), 1);
  ASSERT_TRUE(valk_thread_ctx.gc_registered);

  valk_system_destroy(sys);
  VALK_PASS();
}

static void *register_thread_fn(void *arg) {
  valk_system_t *sys = (valk_system_t *)arg;
  valk_system_register_thread(sys, nullptr, nullptr);
  u64 id = valk_thread_ctx.gc_thread_id;
  valk_system_unregister_thread(sys);
  return (void *)(uintptr_t)id;
}

void test_system_thread_register_gets_unique_slot(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);

  u64 main_id = valk_thread_ctx.gc_thread_id;
  ASSERT_EQ(atomic_load(&sys->threads_registered), 1);

  pthread_t t;
  pthread_create(&t, nullptr, register_thread_fn, sys);
  void *ret;
  pthread_join(t, &ret);
  u64 thread_id = (u64)(uintptr_t)ret;

  ASSERT_NE(main_id, thread_id);
  ASSERT_EQ(atomic_load(&sys->threads_registered), 1);

  valk_system_destroy(sys);
  VALK_PASS();
}

void test_system_heap_alloc_works_after_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);

  void *ptr = valk_gc_heap_alloc(sys->heap, 64);
  ASSERT_NOT_NULL(ptr);

  valk_system_destroy(sys);
  VALK_PASS();
}

void test_system_subsystem_add_remove(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);

  int ctx_a = 1;
  int ctx_b = 2;

  valk_system_add_subsystem(sys, nullptr, nullptr, nullptr, &ctx_a);
  ASSERT_EQ(sys->subsystem_count, 1);

  valk_system_add_subsystem(sys, nullptr, nullptr, nullptr, &ctx_b);
  ASSERT_EQ(sys->subsystem_count, 2);

  valk_system_remove_subsystem(sys, &ctx_a);
  ASSERT_EQ(sys->subsystem_count, 1);

  valk_system_remove_subsystem(sys, &ctx_b);
  ASSERT_EQ(sys->subsystem_count, 0);

  valk_system_destroy(sys);
  VALK_PASS();
}

typedef struct {
  _Atomic int seq;
  int stop_at;
  int wait_at;
  int destroy_at;
} subsystem_order_t;

static void order_stop(void *ctx) {
  subsystem_order_t *o = (subsystem_order_t *)ctx;
  o->stop_at = atomic_fetch_add(&o->seq, 1);
}

static void order_wait(void *ctx) {
  subsystem_order_t *o = (subsystem_order_t *)ctx;
  o->wait_at = atomic_fetch_add(&o->seq, 1);
}

static void order_destroy(void *ctx) {
  subsystem_order_t *o = (subsystem_order_t *)ctx;
  o->destroy_at = atomic_fetch_add(&o->seq, 1);
}

void test_system_shutdown_calls_subsystem_stop_wait_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);

  subsystem_order_t order = {.seq = 0, .stop_at = -1, .wait_at = -1, .destroy_at = -1};

  valk_system_add_subsystem(sys, order_stop, order_wait, order_destroy, &order);

  valk_system_shutdown(sys, 1000);

  ASSERT_EQ(order.stop_at, 0);
  ASSERT_EQ(order.wait_at, 1);
  ASSERT_EQ(order.destroy_at, 2);

  valk_system_destroy(sys);
  VALK_PASS();
}

void test_barrier_two_threads_no_deadlock(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);

  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.heap = heap;

  valk_aio_system_t *aio = valk_aio_start();
  ASSERT_NOT_NULL(aio);
  usleep(100000);

  for (int i = 0; i < 20; i++) {
    valk_gc_heap_collect(heap);
    usleep(1000);
  }

  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_checkpoint_does_not_deadlock_with_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);

  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.heap = heap;

  valk_mem_arena_t scratch;
  valk_mem_arena_init(&scratch, 1024 * 1024);
  valk_thread_ctx.scratch = &scratch;

  valk_aio_system_t *aio = valk_aio_start();
  ASSERT_NOT_NULL(aio);
  usleep(100000);

  for (int i = 0; i < 20; i++) {
    valk_checkpoint(&scratch, heap, nullptr);
    usleep(1000);
  }

  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  valk_thread_ctx.scratch = nullptr;
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_gc_phase_returns_to_idle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_system_t *sys = valk_system_create(nullptr);
  ASSERT_NOT_NULL(sys);

  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.heap = heap;

  valk_aio_system_t *aio = valk_aio_start();
  ASSERT_NOT_NULL(aio);
  usleep(100000);

  valk_gc_heap_collect(heap);

  valk_gc_phase_e phase = atomic_load(&valk_sys->phase);
  ASSERT_EQ(phase, VALK_GC_PHASE_IDLE);

  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  valk_system_destroy(sys);
  VALK_PASS();
}

int main(void) {
  signal(SIGALRM, alarm_handler);
  alarm(30);

  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_system_create_sets_valk_sys",
                          test_system_create_sets_valk_sys);
  valk_testsuite_add_test(suite, "test_system_thread_register_gets_unique_slot",
                          test_system_thread_register_gets_unique_slot);
  valk_testsuite_add_test(suite, "test_system_heap_alloc_works_after_create",
                          test_system_heap_alloc_works_after_create);
  valk_testsuite_add_test(suite, "test_system_subsystem_add_remove",
                          test_system_subsystem_add_remove);
  valk_testsuite_add_test(suite, "test_system_shutdown_calls_subsystem_stop_wait_destroy",
                          test_system_shutdown_calls_subsystem_stop_wait_destroy);
  valk_testsuite_add_test(suite, "test_barrier_two_threads_no_deadlock",
                          test_barrier_two_threads_no_deadlock);
  valk_testsuite_add_test(suite, "test_checkpoint_does_not_deadlock_with_aio",
                          test_checkpoint_does_not_deadlock_with_aio);
  valk_testsuite_add_test(suite, "test_gc_phase_returns_to_idle",
                          test_gc_phase_returns_to_idle);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
