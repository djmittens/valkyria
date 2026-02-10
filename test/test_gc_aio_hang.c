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

int main(void) {
  alarm(5);
  signal(SIGALRM, alarm_handler);

  valk_mem_init_malloc();
  valk_gc_coordinator_init();
  valk_gc_thread_register();

  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.heap = heap;

  valk_aio_system_t *sys = valk_aio_start();
  if (!sys) {
    fprintf(stderr, "FAIL: Failed to start AIO system\n");
    return 1;
  }

  usleep(100000);

  valk_gc_heap_collect(heap);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  return 0;
}
