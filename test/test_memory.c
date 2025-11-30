#include "test_memory.h"
#include "common.h"
#include "concurrency.h"
#include "gc.h"
#include "memory.h"
#include "testing.h"
#include <math.h>
#include <pthread.h>
#include <time.h>
#include <unistd.h>

const char *THREAD_FMT = "T%ldT%ldT%ld";

void test_implicit_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_thread_context_t ctxBackup = valk_thread_ctx;

  valk_mem_allocator_t alloc_old;
  valk_mem_allocator_t alloc_new;

  valk_thread_ctx.allocator = &alloc_old;
  valk_thread_context_t ctx = {.allocator = &alloc_new};
  VALK_WITH_CTX(ctx) {
    // The function gets context we set
    VALK_TEST_ASSERT(valk_thread_ctx.allocator == &alloc_new,
                     "expected some stuff %p", &alloc_new);
  }
  // VALK_WITH_CTX reset the context back to original
  VALK_TEST_ASSERT(valk_thread_ctx.allocator == &alloc_old,
                   "expected some stuff %d", &alloc_old);

  valk_thread_ctx = ctxBackup;
  VALK_PASS();
}

void test_slab_alloc(VALK_TEST_ARGS()) {

  const char msg[] = "Get fucked";

  VALK_TEST();

  int itemLen = sizeof(valk_arc_box) + sizeof(msg);
  size_t numItems = rand() % 1000;
  valk_slab_t *slab = valk_slab_new(itemLen, numItems);

  valk_arc_box *boxes[numItems];
  size_t slabIds[numItems];

  printf("Aquiring %ld boxes\n", numItems);
  // allocate everything
  for (size_t i = 0; i < numItems; ++i) {
    if (rand() % 2) {
      valk_slab_item_t *item = valk_slab_aquire(slab);
      boxes[i] = (valk_arc_box *)item->data;
      valk_arc_box_init(boxes[i], VALK_SUC, sizeof(msg));
      boxes[i]->allocator = (valk_mem_allocator_t *)slab;
      slabIds[i] = item->handle;
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
        boxes[i] = valk_arc_box_new(VALK_SUC, sizeof(msg));
        slabIds[i] =
            valk_container_of(boxes[i], valk_slab_item_t, data)->handle;
      }
    }

    printf("Aquired box i: %ld ::: slabId: %ld\n", i, slabIds[i]);
    strncpy(boxes[i]->item, msg, sizeof(msg));
  }

  for (size_t i = 0; i < numItems; ++i) {
    char *result = (char *)boxes[i]->item;
    VALK_TEST_ASSERT(strcmp(result, msg) == 0, "Shit got corrupted %d %s", i,
                     result);
  }

  VALK_TEST_ASSERT(slab->numFree == 0, "Shit should be full %d", slab->numFree);

  // ok now lets shuffle some dogshit
  // reap at most 80 % of the items
  size_t reapNum = rand() % lrint(numItems * .8);
  printf("Reaping total of %ld boxes:\n", reapNum);

  // should be smaller than the other messge
  const char newMsg[] = "XOXOXO";
  valk_arc_box *newBoxes[reapNum];

  for (size_t i = 0; i < reapNum; ++i) {
    do {
      // Find us a good id to reaperunny
      size_t reapId = rand() % numItems;
      if (boxes[reapId]) {
        printf("Reaping  box n: %ld : slabId: %ld\n", reapId, slabIds[reapId]);

        if (rand() % 2) {
          valk_slab_release_ptr(slab, boxes[reapId]);
        } else {
          VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
            valk_mem_free(boxes[reapId]);
          }
        }
        boxes[reapId] = nullptr;
        break;
      }
    } while (true);
  }

  // ok we are done with the context one, just to keep things simple lets just
  // do the normal api
  for (size_t i = 0; i < reapNum; ++i) {
    newBoxes[i] = (valk_arc_box *)valk_slab_aquire(slab)->data;
    valk_arc_box_init(newBoxes[i], VALK_SUC, sizeof(newMsg));
    newBoxes[i]->allocator = (valk_mem_allocator_t *)slab;
    strncpy(newBoxes[i]->item, newMsg, sizeof(newMsg));
  }

  for (size_t i = 0; i < reapNum; ++i) {
    char *result = (char *)newBoxes[i]->item;
    VALK_TEST_ASSERT(strcmp(result, newMsg) == 0, "Shit got corrupted %d %s", i,
                     result);
  }

  for (size_t i = 0; i < numItems; ++i) {
    if (boxes[i]) {
      char *result = (char *)boxes[i]->item;
      VALK_TEST_ASSERT(strcmp(result, msg) == 0,
                       "Shit got corrupted %ld :: slabId: %ld :: %s", i,
                       slabIds[i], result);
    }
  }

  VALK_TEST_ASSERT(slab->numFree == 0, "Shit should be full %d", slab->numFree);

  valk_mem_free(slab);
  VALK_PASS();
}

typedef struct {
  size_t id;
  valk_slab_t *slab;
  valk_arc_box **boxes;
  size_t numItems;
  size_t rand;
} shuffle_thread_arg_t;

static size_t __next_thread_rand(size_t *state) {
  // TODO(networking): i dont trust chatgpt what the heck does this do?
  size_t x = *state;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  *state = x;
  return x;
}

void test_slab_concurrency(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char msg[] = "Get fucked";
  int itemLen = sizeof(valk_arc_box) + sizeof(msg);
  size_t numItems = rand() % 1000;

  valk_slab_t *slab = valk_slab_new(itemLen, numItems);

  valk_arc_box *boxes[numItems];
  printf("Aquiring %ld boxes\n", numItems);

  size_t slabIds[numItems];

  // allocate everything
  for (size_t i = 0; i < numItems; ++i) {
    if (rand() % 2) {
      valk_slab_item_t *item = valk_slab_aquire(slab);
      boxes[i] = (valk_arc_box *)item->data;
      valk_arc_box_init(boxes[i], VALK_SUC, sizeof(msg));
      boxes[i]->allocator = (valk_mem_allocator_t *)slab;
      slabIds[i] = item->handle;
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
        boxes[i] = valk_arc_box_new(VALK_SUC, sizeof(msg));
        slabIds[i] =
            valk_container_of(boxes[i], valk_slab_item_t, data)->handle;
      }
    }

    printf("Aquired box i: %ld ::: slabId: %ld\n", i, slabIds[i]);
    strncpy(boxes[i]->item, msg, sizeof(msg));
  }
  VALK_TEST_ASSERT(slab->numFree == 0, "Shit should be full %d", slab->numFree);

  // Split the boxes randomly between threads
  size_t numThreads = 1 + rand() % 10;
  valk_arc_box *splitBoxes[numThreads][numItems];

  for (size_t i = 0; i < numThreads; ++i) {
    for (size_t j = 0; j < numItems; ++j) {
      splitBoxes[i][j] = nullptr;
    }
  }

  // TODO(networking): this is unix specific threading code using pthreads
  // Eventually want to support windows so should replace it with my own
  // conurrency

  for (size_t i = 0; i < numItems; ++i) {
    size_t tId = rand() % numThreads;
    do {
      size_t reapId = rand() % numItems;
      if (boxes[reapId] != nullptr) {
        printf("Select  box n: %ld : slabId: %ld : Tid: %ld\n", reapId,
               slabIds[reapId], tId);
        splitBoxes[tId][reapId] = boxes[reapId];
        int count = snprintf(nullptr, 0, THREAD_FMT, tId, tId, tId);
        snprintf(boxes[reapId]->item, count + 1, THREAD_FMT, tId, tId, tId);

        boxes[reapId] = nullptr;
        break;
      }
    } while (true);
  }

  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_t threadIds[numThreads];

  shuffle_thread_arg_t args[numThreads];
  for (size_t i = 0; i < numThreads; ++i) {
    args[i].id = i;
    args[i].boxes = splitBoxes[i];
    args[i].slab = slab;
    args[i].numItems = numItems;
    args[i].rand = rand();

    int res =
        pthread_create(&threadIds[i], &attr, slab_shuffle_thread, &args[i]);
    if (res) {
      printf("Failed creating thread [%ld]\n", i);
    }
  }

  for (size_t i = 0; i < numThreads; ++i) {
    void *foo;
    pthread_join(threadIds[i], &foo);
    VALK_TEST_ASSERT(foo == 0,
                     "Expected the result of a thread to be success %d",
                     (size_t)foo);
  }

  valk_mem_free(slab);
  VALK_PASS();
}

// Test arena statistics tracking
void test_arena_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a small test arena
  size_t arena_size = 64 * 1024;  // 64 KB
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  // Initial stats should be zero (except high_water_mark which starts at 0)
  VALK_TEST_ASSERT(arena->stats.total_allocations == 0,
                   "Initial total_allocations should be 0");
  VALK_TEST_ASSERT(arena->stats.num_resets == 0,
                   "Initial num_resets should be 0");

  // Allocate some memory
  void *ptr1 = valk_mem_arena_alloc(arena, 100);
  VALK_TEST_ASSERT(ptr1 != NULL, "First allocation should succeed");
  VALK_TEST_ASSERT(arena->stats.total_allocations == 1,
                   "total_allocations should be 1 after first alloc");

  void *ptr2 = valk_mem_arena_alloc(arena, 200);
  VALK_TEST_ASSERT(ptr2 != NULL, "Second allocation should succeed");
  VALK_TEST_ASSERT(arena->stats.total_allocations == 2,
                   "total_allocations should be 2 after second alloc");

  // Check high water mark was updated
  VALK_TEST_ASSERT(arena->stats.high_water_mark > 0,
                   "high_water_mark should be > 0");
  size_t hwm_before_reset = arena->stats.high_water_mark;

  // Reset the arena
  valk_mem_arena_reset(arena);
  VALK_TEST_ASSERT(arena->stats.num_resets == 1,
                   "num_resets should be 1 after reset");
  VALK_TEST_ASSERT(arena->offset == 0,
                   "Arena offset should be 0 after reset");
  // high_water_mark should be preserved
  VALK_TEST_ASSERT(arena->stats.high_water_mark >= hwm_before_reset,
                   "high_water_mark should be preserved after reset");

  // Test valk_ptr_in_arena
  void *ptr3 = valk_mem_arena_alloc(arena, 50);
  VALK_TEST_ASSERT(valk_ptr_in_arena(arena, ptr3),
                   "ptr3 should be in arena");
  VALK_TEST_ASSERT(!valk_ptr_in_arena(arena, (void *)0x12345678),
                   "Random pointer should not be in arena");
  VALK_TEST_ASSERT(!valk_ptr_in_arena(arena, NULL),
                   "NULL should not be in arena");

  // Test reset_stats
  valk_mem_arena_reset_stats(arena);
  VALK_TEST_ASSERT(arena->stats.total_allocations == 0,
                   "total_allocations should be 0 after reset_stats");
  VALK_TEST_ASSERT(arena->stats.num_resets == 0,
                   "num_resets should be 0 after reset_stats");
  // high_water_mark is intentionally NOT reset
  VALK_TEST_ASSERT(arena->stats.high_water_mark >= hwm_before_reset,
                   "high_water_mark should NOT be reset");

  free(arena);
  VALK_PASS();
}

// Test GC heap hard limit
void test_gc_heap_hard_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a GC heap with small threshold and hard limit
  size_t threshold = 1024 * 1024;  // 1 MB
  size_t hard_limit = 2 * 1024 * 1024;  // 2 MB
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, hard_limit);

  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  VALK_TEST_ASSERT(heap->gc_threshold == threshold,
                   "Threshold should match");
  VALK_TEST_ASSERT(heap->hard_limit == hard_limit,
                   "Hard limit should match");

  // Test default hard limit (2x threshold)
  valk_gc_malloc_heap_t *heap2 = valk_gc_malloc_heap_init(threshold, 0);
  VALK_TEST_ASSERT(heap2->hard_limit == threshold * 2,
                   "Default hard limit should be 2x threshold");

  // Test setting hard limit
  valk_gc_set_hard_limit(heap, hard_limit * 2);
  VALK_TEST_ASSERT(heap->hard_limit == hard_limit * 2,
                   "Hard limit should be updated");

  // Test stats initialization
  VALK_TEST_ASSERT(heap->stats.emergency_collections == 0,
                   "emergency_collections should start at 0");
  VALK_TEST_ASSERT(heap->stats.peak_usage == 0,
                   "peak_usage should start at 0");

  valk_gc_malloc_heap_destroy(heap);
  valk_gc_malloc_heap_destroy(heap2);
  VALK_PASS();
}

// Test GC heap statistics tracking
void test_gc_heap_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Allocate something that won't use the slab (not lval_t size)
  void *ptr = valk_gc_malloc_heap_alloc(heap, 123);
  VALK_TEST_ASSERT(ptr != NULL, "Allocation should succeed");
  VALK_TEST_ASSERT(heap->allocated_bytes > 0,
                   "allocated_bytes should be > 0");
  VALK_TEST_ASSERT(heap->stats.peak_usage > 0,
                   "peak_usage should be tracked");

  size_t peak = heap->stats.peak_usage;

  // Allocate more
  valk_gc_malloc_heap_alloc(heap, 456);  // result intentionally unused
  VALK_TEST_ASSERT(heap->stats.peak_usage >= peak,
                   "peak_usage should only increase");

  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test arena overflow fallback to heap
void test_arena_overflow_fallback(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a tiny arena that will overflow quickly
  size_t arena_size = 1024;  // 1 KB - very small
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  // Create a GC heap as the fallback
  size_t threshold = 1024 * 1024;  // 1 MB
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Set up thread context with fallback heap
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.heap = heap;

  // Initial state: no overflow
  VALK_TEST_ASSERT(arena->stats.overflow_fallbacks == 0,
                   "Initial overflow_fallbacks should be 0");
  VALK_TEST_ASSERT(arena->stats.overflow_bytes == 0,
                   "Initial overflow_bytes should be 0");

  // Fill up most of the arena with small allocations
  size_t alloc_count = 0;
  while (arena->offset < arena->capacity - 100) {
    void *p = valk_mem_arena_alloc(arena, 32);
    VALK_TEST_ASSERT(p != NULL, "Arena allocation should succeed");
    alloc_count++;
    if (alloc_count > 100) break;  // Safety limit
  }

  // Now try to allocate something larger than remaining space
  // This should trigger overflow fallback to heap
  size_t remaining = arena->capacity - arena->offset;
  size_t overflow_size = remaining + 100;  // Definitely won't fit

  void *overflow_ptr = valk_mem_arena_alloc(arena, overflow_size);
  VALK_TEST_ASSERT(overflow_ptr != NULL,
                   "Overflow allocation should succeed via heap fallback");
  VALK_TEST_ASSERT(arena->stats.overflow_fallbacks == 1,
                   "overflow_fallbacks should be 1");
  VALK_TEST_ASSERT(arena->stats.overflow_bytes == overflow_size,
                   "overflow_bytes should match requested size");

  // The overflow pointer should NOT be in the arena
  VALK_TEST_ASSERT(!valk_ptr_in_arena(arena, overflow_ptr),
                   "Overflow pointer should NOT be in arena");

  // warned_overflow should be set
  VALK_TEST_ASSERT(arena->warned_overflow == true,
                   "warned_overflow should be true after overflow");

  // Reset should clear warned_overflow
  valk_mem_arena_reset(arena);
  VALK_TEST_ASSERT(arena->warned_overflow == false,
                   "warned_overflow should be false after reset");

  // Restore thread context
  valk_thread_ctx = old_ctx;

  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test total_bytes_allocated tracking
void test_arena_total_bytes(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 64 * 1024;  // 64 KB
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  VALK_TEST_ASSERT(arena->stats.total_bytes_allocated == 0,
                   "Initial total_bytes_allocated should be 0");

  // Allocate various sizes
  valk_mem_arena_alloc(arena, 100);
  VALK_TEST_ASSERT(arena->stats.total_bytes_allocated == 100,
                   "total_bytes_allocated should be 100");

  valk_mem_arena_alloc(arena, 200);
  VALK_TEST_ASSERT(arena->stats.total_bytes_allocated == 300,
                   "total_bytes_allocated should be 300");

  valk_mem_arena_alloc(arena, 50);
  VALK_TEST_ASSERT(arena->stats.total_bytes_allocated == 350,
                   "total_bytes_allocated should be 350");

  // Reset arena - total_bytes should keep accumulating
  valk_mem_arena_reset(arena);
  valk_mem_arena_alloc(arena, 75);
  VALK_TEST_ASSERT(arena->stats.total_bytes_allocated == 425,
                   "total_bytes_allocated should accumulate across resets");

  free(arena);
  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  size_t seed;
#if 0
  // seed = 1746502782; // 8 threads with 1000 items
  // seed = 1746685013; // floating point exception
  seed = 1746685993; // crashig singlethreaded
#else

  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  seed = ts.tv_sec;
#endif
  srand(seed);

  printf("Seeding rand with %ld\n", seed);

  // Use malloc for now, by default
  // probably should think of how to add this by default everywhere
  valk_mem_init_malloc();

  // TODO(networking): Turns this into a real test
  // valk_ring_t *ring = valk_mem_alloc(sizeof(valk_ring_t) + 75);
  // valk_ring_init(ring, 64);
  //
  // const char *txt = "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "1234567890"
  //                   "TTXXTT";
  // int chunks = 4;
  // int chunklen = strlen(txt) / chunks;
  // char *offset = (void *)txt;
  //
  // while (chunks) {
  //   printf("\n TXt len %ld Capacity  %ld :: Offset  %ld :: len :: %d, %c\n",
  //          strlen(txt), ring->capacity, ring->offset, chunklen,
  //          *(offset + (chunklen - 1)));
  //   valk_ring_write(ring, (void *)(offset), chunklen);
  //   offset += chunklen;
  //   chunks--;
  // }
  //
  // // valk_ring_rewind(ring, 8);
  // printf("\nCapacity %ld :: Offset  %ld :: \n", ring->capacity,
  // ring->offset); valk_ring_fread(ring, 256, stdout);
  //
  // printf("\nCapacity %ld :: Offset  %ld :: \n", ring->capacity,
  // ring->offset);
  // ((char *)ring->items)[ring->capacity - 1] = '\0';
  // printf("\nFUUUCK: %s\n", (char *)ring->items);
  //

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_implicit_alloc", test_implicit_alloc);

  valk_testsuite_add_test(suite, "test_slab_alloc", test_slab_alloc);
  valk_testsuite_add_test(suite, "test_slab_concurrency",
                          test_slab_concurrency);

  // Phase 1 telemetry tests
  valk_testsuite_add_test(suite, "test_arena_stats", test_arena_stats);
  valk_testsuite_add_test(suite, "test_gc_heap_hard_limit", test_gc_heap_hard_limit);
  valk_testsuite_add_test(suite, "test_gc_heap_stats", test_gc_heap_stats);
  valk_testsuite_add_test(suite, "test_arena_overflow_fallback", test_arena_overflow_fallback);
  valk_testsuite_add_test(suite, "test_arena_total_bytes", test_arena_total_bytes);

  // load fixtures
  // valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  // valk_lenv_t *env = valk_lenv_empty();
  // valk_lenv_builtins(env); // load the builtins
  // valk_lval_t *r = valk_lval_eval(env, valk_lval_copy(ast));
  // valk_lval_free(r);
  //
  // valk_testsuite_fixture_add(suite, "prelude", ast,
  //                            (_fixture_copy_f *)valk_lval_copy,
  //                            (_fixture_free_f *)valk_lval_free);
  // valk_testsuite_fixture_add(suite, "env", env,
  //                            (_fixture_copy_f *)valk_lenv_copy,
  //                            (_fixture_free_f *)valk_lenv_free);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

void *slab_shuffle_thread(void *arg) {

  shuffle_thread_arg_t *params = arg;
  size_t numBoxes = 0;
  for (size_t j = 0; j < params->numItems; ++j) {
    if (params->boxes[j] != nullptr) {
      ++numBoxes;
    }
  }

  if (numBoxes > 0) {
    printf("[T%ld] Starting service thread with %ld boxes \n", params->id,
           numBoxes);

  } else {
    printf("[T%ld] Did not receive any boxes, shutting down\n", params->id);
    return nullptr;
  }

  // lets get to it
  valk_arc_box *myBoxes[numBoxes];
  for (size_t j = 0, remBoxes = numBoxes; j < params->numItems; ++j) {
    if (params->boxes[j] != nullptr) {
      myBoxes[--remBoxes] = params->boxes[j];
    }
  }

  int count =
      snprintf(nullptr, 0, THREAD_FMT, params->id, params->id, params->id);
  char msg[++count];
  memset(msg, 0, count);
  snprintf(msg, count, THREAD_FMT, params->id, params->id, params->id);

  for (size_t iteration = __next_thread_rand(&params->rand) % 1000000;
       iteration > 0; --iteration) {
    // randomly allocate / release the handles
    size_t randomBox = (__next_thread_rand(&params->rand)) % numBoxes;

    // Do something or skip it
    if ((__next_thread_rand(&params->rand)) % 2) {

      if (myBoxes[randomBox] == nullptr) {
        myBoxes[randomBox] =
            (valk_arc_box *)valk_slab_aquire(params->slab)->data;
        strncpy(myBoxes[randomBox]->item, msg, count);
      } else {
        // check if we have our message in this box, and then release it
        if (strcmp(myBoxes[randomBox]->item, msg) != 0) {
          printf("ERROR: Box did not contain our text: got: %s expected: %s\n",
                 (char *)myBoxes[randomBox]->item, msg);
          return (void *)1;
        }
        valk_slab_release_ptr(params->slab, myBoxes[randomBox]);
        myBoxes[randomBox] = nullptr;
      }
    }

    // TODO(networking): maybe should ald some logic to randomly pause for
    // microsecs
  }

  return 0;
}
