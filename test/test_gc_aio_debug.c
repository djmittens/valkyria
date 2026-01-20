#include "testing.h"
#include "gc.h"
#include "aio/aio_internal.h"
#include <unistd.h>
#include <stdio.h>

int main(void) {
  valk_mem_init_malloc();
  valk_gc_coordinator_init();
  valk_gc_thread_register();
  
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);
  valk_thread_ctx.heap = heap;
  
  printf("Main thread registered: threads_registered=%llu\n",
         (unsigned long long)atomic_load(&valk_gc_coord.threads_registered));
  
  valk_aio_system_t *sys = valk_aio_start();
  if (!sys) {
    printf("Failed to start AIO system\n");
    return 1;
  }
  
  printf("AIO started: threads_registered=%llu\n",
         (unsigned long long)atomic_load(&valk_gc_coord.threads_registered));
  
  // Small sleep to let event loop stabilize
  usleep(50000);
  
  printf("Before GC: threads_registered=%llu, threads_paused=%llu, phase=%d\n",
         (unsigned long long)atomic_load(&valk_gc_coord.threads_registered),
         (unsigned long long)atomic_load(&valk_gc_coord.threads_paused),
         atomic_load(&valk_gc_coord.phase));
  
  printf("Calling gc_collect...\n");
  fflush(stdout);
  
  // This should trigger parallel GC
  valk_gc_malloc_collect(heap, NULL);
  
  printf("GC done!\n");
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  printf("Test passed\n");
  return 0;
}
