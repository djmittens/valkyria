#include "testing.h"
#include "gc.h"
#include "aio/aio_internal.h"
#include <unistd.h>
#include <stdio.h>

int main(void) {
  valk_mem_init_malloc();
  valk_system_create(NULL);
  
  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.heap = heap;
  
  printf("Main thread registered: threads_registered=%llu\n",
         (unsigned long long)atomic_load(&valk_sys->threads_registered));
  
  valk_aio_system_t *sys = valk_aio_start();
  if (!sys) {
    printf("Failed to start AIO system\n");
    return 1;
  }
  
  printf("AIO started: threads_registered=%llu\n",
         (unsigned long long)atomic_load(&valk_sys->threads_registered));
  
  // Small sleep to let event loop stabilize
  usleep(50000);
  
  printf("Before GC: threads_registered=%llu, phase=%d\n",
         (unsigned long long)atomic_load(&valk_sys->threads_registered),
         atomic_load(&valk_sys->phase));
  
  printf("Calling gc_collect...\n");
  fflush(stdout);
  
  // This should trigger parallel GC
  valk_gc_heap_collect(heap);
  
  printf("GC done!\n");
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  printf("Test passed\n");
  return 0;
}
