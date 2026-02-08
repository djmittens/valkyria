#include "testing.h"
#include "gc.h"
#include "aio/aio_internal.h"
#include <signal.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>

static volatile sig_atomic_t timed_out = 0;

static void alarm_handler(int sig) {
  (void)sig;
  timed_out = 1;
  fprintf(stderr, "TIMEOUT: Test hung - GC/AIO coordination deadlock detected\n");
  _exit(1);
}

static void setup_timeout(int seconds) {
  alarm((unsigned)seconds);
  signal(SIGALRM, alarm_handler);
}

static valk_gc_malloc_heap_t *heap = NULL;
static valk_aio_system_t *sys = NULL;

static void setup_gc_and_aio(void) {
  valk_mem_init_malloc();
  valk_gc_coordinator_init();
  valk_gc_thread_register();

  heap = valk_gc_malloc_heap_init(0);
  valk_thread_ctx.heap = heap;

  sys = valk_aio_start();
  usleep(100000);
}

static void teardown_gc_and_aio(void) {
  if (sys) {
    valk_aio_stop(sys);
    valk_aio_wait_for_shutdown(sys);
    sys = NULL;
  }
}

void test_gc_after_aio_start(VALK_TEST_ARGS()) {
  VALK_TEST();

  setup_gc_and_aio();

  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  u64 registered = atomic_load(&valk_gc_coord.threads_registered);
  VALK_TEST_ASSERT(registered >= 2, "Expected at least 2 threads registered (main + event loop), got %llu", (unsigned long long)registered);

  sz reclaimed = valk_gc_malloc_collect(heap, NULL);
  (void)reclaimed;

  teardown_gc_and_aio();

  VALK_PASS();
}

void test_multiple_gc_cycles_with_aio(VALK_TEST_ARGS()) {
  VALK_TEST();

  setup_gc_and_aio();

  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  for (int i = 0; i < 5; i++) {
    valk_gc_malloc_collect(heap, NULL);
    usleep(10000);
  }

  teardown_gc_and_aio();

  VALK_PASS();
}

void test_allocation_triggers_auto_gc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_init_malloc();
  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_malloc_heap_t *small_heap = valk_gc_malloc_heap_init(1024 * 1024);
  valk_thread_ctx.heap = small_heap;

  valk_aio_system_t *local_sys = valk_aio_start();
  VALK_TEST_ASSERT(local_sys != NULL, "Failed to start AIO system");
  usleep(100000);

  u64 gc_cycles_before = atomic_load(&valk_gc_coord.parallel_cycles);

  for (int i = 0; i < 100; i++) {
    valk_gc_heap2_alloc(small_heap, 16384);
  }

  u64 gc_cycles_after = atomic_load(&valk_gc_coord.parallel_cycles);

  valk_aio_stop(local_sys);
  valk_aio_wait_for_shutdown(local_sys);

  VALK_TEST_ASSERT(gc_cycles_after >= gc_cycles_before, "GC cycles should not decrease");

  VALK_PASS();
}

void test_gc_coordination_thread_count(VALK_TEST_ARGS()) {
  VALK_TEST();

  setup_gc_and_aio();

  VALK_TEST_ASSERT(sys != NULL, "Failed to start AIO system");

  u64 registered = atomic_load(&valk_gc_coord.threads_registered);
  VALK_TEST_ASSERT(registered >= 2, "Expected at least 2 threads (main + event loop), got %llu", (unsigned long long)registered);

  u64 paused_before_gc = atomic_load(&valk_gc_coord.threads_paused);
  VALK_TEST_ASSERT(paused_before_gc == 0, "No threads should be paused before GC, got %llu", (unsigned long long)paused_before_gc);

  valk_gc_malloc_collect(heap, NULL);

  u64 paused_after_gc = atomic_load(&valk_gc_coord.threads_paused);
  VALK_TEST_ASSERT(paused_after_gc == 0, "No threads should be paused after GC completes, got %llu", (unsigned long long)paused_after_gc);

  teardown_gc_and_aio();

  VALK_PASS();
}

int main(void) {
  const char *env = getenv("VALK_TEST_TIMEOUT_SECONDS");
  setup_timeout(env ? atoi(env) : 10);

  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "gc_after_aio_start", test_gc_after_aio_start);
  valk_testsuite_add_test(suite, "multiple_gc_cycles_with_aio", test_multiple_gc_cycles_with_aio);
  valk_testsuite_add_test(suite, "allocation_triggers_auto_gc", test_allocation_triggers_auto_gc);
  valk_testsuite_add_test(suite, "gc_coordination_thread_count", test_gc_coordination_thread_count);

  int result = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return result;
}
