#include "test_memory.h"
#include "common.h"
#include "concurrency.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
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

  // Test default hard limit must be greater than threshold
  valk_gc_malloc_heap_t *heap2 = valk_gc_malloc_heap_init(threshold, 0);
  VALK_TEST_ASSERT(heap2->hard_limit > heap2->gc_threshold,
                   "Default hard limit should be greater than threshold");

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

// Phase 2: Test forwarding pointer set/check
void test_forward_set_and_check(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a GC heap for test allocations
  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Save and set up thread context
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.heap = heap;

  // Create two lvals
  valk_lval_t *src = valk_lval_num(42);
  valk_lval_t *dst = valk_lval_num(100);

  // Initially, neither should be forwarded
  VALK_TEST_ASSERT(!valk_lval_is_forwarded(src),
                   "src should not be forwarded initially");
  VALK_TEST_ASSERT(!valk_lval_is_forwarded(dst),
                   "dst should not be forwarded initially");
  VALK_TEST_ASSERT(LVAL_TYPE(src) == LVAL_NUM,
                   "src should be LVAL_NUM initially");

  // Set forwarding pointer
  valk_lval_set_forward(src, dst);

  // Now src should be forwarded
  VALK_TEST_ASSERT(valk_lval_is_forwarded(src),
                   "src should be forwarded after set_forward");
  VALK_TEST_ASSERT(LVAL_TYPE(src) == LVAL_FORWARD,
                   "src type should be LVAL_FORWARD");
  VALK_TEST_ASSERT(src->forward == dst,
                   "src->forward should point to dst");

  // dst should NOT be forwarded
  VALK_TEST_ASSERT(!valk_lval_is_forwarded(dst),
                   "dst should not be forwarded");

  // Test NULL handling
  VALK_TEST_ASSERT(!valk_lval_is_forwarded(NULL),
                   "NULL should not be forwarded");

  // Restore context and cleanup
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 2: Test following forwarding pointer chains
void test_forward_follow_chain(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a GC heap for test allocations
  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Save and set up thread context
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.heap = heap;

  // Create a chain: a -> b -> c -> d (final destination)
  valk_lval_t *a = valk_lval_num(1);
  valk_lval_t *b = valk_lval_num(2);
  valk_lval_t *c = valk_lval_num(3);
  valk_lval_t *d = valk_lval_num(4);  // Final destination

  // Build the chain
  valk_lval_set_forward(a, b);
  valk_lval_set_forward(b, c);
  valk_lval_set_forward(c, d);

  // Following from any point should reach d
  valk_lval_t *result_a = valk_lval_follow_forward(a);
  VALK_TEST_ASSERT(result_a == d,
                   "Following from a should reach d");

  valk_lval_t *result_b = valk_lval_follow_forward(b);
  VALK_TEST_ASSERT(result_b == d,
                   "Following from b should reach d");

  valk_lval_t *result_c = valk_lval_follow_forward(c);
  VALK_TEST_ASSERT(result_c == d,
                   "Following from c should reach d");

  // Following from d should return d (not forwarded)
  valk_lval_t *result_d = valk_lval_follow_forward(d);
  VALK_TEST_ASSERT(result_d == d,
                   "Following from d should return d itself");

  // Following NULL should return NULL
  valk_lval_t *result_null = valk_lval_follow_forward(NULL);
  VALK_TEST_ASSERT(result_null == NULL,
                   "Following NULL should return NULL");

  // Restore context and cleanup
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 2: Test forwarding preserves allocation flags
void test_forward_preserves_alloc_flags(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a GC heap for test allocations
  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Save and set up thread context
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.heap = heap;

  valk_lval_t *src = valk_lval_num(42);
  valk_lval_t *dst = valk_lval_num(100);

  // Get original allocation flags
  uint64_t orig_alloc_flags = LVAL_ALLOC(src);

  // Set forwarding pointer
  valk_lval_set_forward(src, dst);

  // Check that allocation flags are preserved
  uint64_t new_alloc_flags = LVAL_ALLOC(src);
  VALK_TEST_ASSERT(new_alloc_flags == orig_alloc_flags,
                   "Allocation flags should be preserved after forwarding, "
                   "got %llu expected %llu",
                   (unsigned long long)new_alloc_flags,
                   (unsigned long long)orig_alloc_flags);

  // Type should still be LVAL_FORWARD
  VALK_TEST_ASSERT(LVAL_TYPE(src) == LVAL_FORWARD,
                   "Type should be LVAL_FORWARD");

  // Restore context and cleanup
  valk_thread_ctx = old_ctx;
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

// Phase 3: Test valk_should_checkpoint threshold check
void test_should_checkpoint(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 10 * 1024;  // 10 KB
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  // Initially empty - should not trigger checkpoint
  VALK_TEST_ASSERT(!valk_should_checkpoint(arena, 0.75f),
                   "Empty arena should not trigger checkpoint");

  // Fill to 50% - still below 75% threshold
  size_t half = (arena->capacity * 50) / 100;
  arena->offset = half;
  VALK_TEST_ASSERT(!valk_should_checkpoint(arena, 0.75f),
                   "50% full should not trigger checkpoint at 75% threshold");

  // Fill to 76% - should trigger
  size_t over_threshold = (arena->capacity * 76) / 100;
  arena->offset = over_threshold;
  VALK_TEST_ASSERT(valk_should_checkpoint(arena, 0.75f),
                   "76% full should trigger checkpoint at 75% threshold");

  // Fill to 100%
  arena->offset = arena->capacity;
  VALK_TEST_ASSERT(valk_should_checkpoint(arena, 0.75f),
                   "100% full should trigger checkpoint");

  // Test with different threshold (50%)
  arena->offset = half;
  VALK_TEST_ASSERT(!valk_should_checkpoint(arena, 0.50f),
                   "50% full should not trigger at exact 50% threshold");

  arena->offset = half + 1;
  VALK_TEST_ASSERT(valk_should_checkpoint(arena, 0.50f),
                   "50%+1 should trigger at 50% threshold");

  // NULL arena should not crash and return false
  VALK_TEST_ASSERT(!valk_should_checkpoint(NULL, 0.75f),
                   "NULL arena should return false");

  free(arena);
  VALK_PASS();
}

// Phase 3: Test checkpoint with empty arena
void test_checkpoint_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create scratch arena
  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  // Create heap
  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Create a simple root environment (empty)
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.heap = heap;

  valk_lenv_t *env = valk_lenv_empty();

  // Run checkpoint on empty arena
  valk_checkpoint(arena, heap, env);

  // Stats should show 0 evacuations
  VALK_TEST_ASSERT(arena->stats.num_checkpoints == 1,
                   "num_checkpoints should be 1");
  VALK_TEST_ASSERT(arena->stats.values_evacuated == 0,
                   "values_evacuated should be 0 for empty arena");
  VALK_TEST_ASSERT(arena->offset == 0,
                   "Arena offset should be 0 after checkpoint");

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 3: Test checkpoint evacuates number values
void test_checkpoint_evacuate_number(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create scratch arena
  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  // Create heap
  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Set up thread context
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  // Create environment in heap
  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);

    // Allocate a number in scratch arena
    VALK_WITH_ALLOC((void *)arena) {
      valk_lval_t *num = valk_lval_num(42);
      VALK_TEST_ASSERT(LVAL_ALLOC(num) == LVAL_ALLOC_SCRATCH,
                       "Number should be in scratch");
      VALK_TEST_ASSERT(num->num == 42, "Number value should be 42");

      // Put the number in environment
      valk_lenv_put(env, valk_lval_sym("x"), num);
    }

    // Verify value is in environment
    VALK_WITH_ALLOC((void *)heap) {
      valk_lval_t *retrieved = valk_lenv_get(env, valk_lval_sym("x"));
      VALK_TEST_ASSERT(LVAL_TYPE(retrieved) == LVAL_NUM,
                       "Retrieved should be number");
      // Note: retrieved may point to scratch value which will be evacuated
    }

    // Run checkpoint
    size_t arena_before = arena->offset;
    VALK_TEST_ASSERT(arena_before > 0, "Arena should have allocations");

    valk_checkpoint(arena, heap, env);

    // Verify arena was reset
    VALK_TEST_ASSERT(arena->offset == 0,
                     "Arena should be reset after checkpoint");

    // Verify value was evacuated
    VALK_TEST_ASSERT(arena->stats.values_evacuated > 0,
                     "Should have evacuated at least one value");

    // Verify we can still get the value from environment
    VALK_WITH_ALLOC((void *)heap) {
      valk_lval_t *after = valk_lenv_get(env, valk_lval_sym("x"));
      VALK_TEST_ASSERT(LVAL_TYPE(after) == LVAL_NUM,
                       "Retrieved after checkpoint should be number");
      VALK_TEST_ASSERT(after->num == 42,
                       "Number value should still be 42 after checkpoint");
      VALK_TEST_ASSERT(LVAL_ALLOC(after) == LVAL_ALLOC_HEAP,
                       "After checkpoint, value should be in heap");
    }
  }

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 3: Test checkpoint evacuates cons/list structures
void test_checkpoint_evacuate_list(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create scratch arena
  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  // Create heap
  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  // Set up thread context
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);

    // Create a list (1 2 3) in scratch
    VALK_WITH_ALLOC((void *)arena) {
      valk_lval_t *nums[3] = {
        valk_lval_num(1),
        valk_lval_num(2),
        valk_lval_num(3)
      };
      valk_lval_t *list = valk_lval_list(nums, 3);

      // Verify it's in scratch
      VALK_TEST_ASSERT(LVAL_ALLOC(list) == LVAL_ALLOC_SCRATCH,
                       "List should be in scratch");

      // Put in environment
      valk_lenv_put(env, valk_lval_sym("mylist"), list);
    }

    // Run checkpoint
    valk_checkpoint(arena, heap, env);

    // Verify we can traverse the list after checkpoint
    VALK_WITH_ALLOC((void *)heap) {
      valk_lval_t *after = valk_lenv_get(env, valk_lval_sym("mylist"));
      VALK_TEST_ASSERT(LVAL_TYPE(after) == LVAL_QEXPR || LVAL_TYPE(after) == LVAL_CONS,
                       "Retrieved should be list-like");
      VALK_TEST_ASSERT(LVAL_ALLOC(after) == LVAL_ALLOC_HEAP,
                       "List should be in heap after checkpoint");

      // Verify list contents
      size_t count = valk_lval_list_count(after);
      VALK_TEST_ASSERT(count == 3, "List should have 3 elements, got %zu", count);

      valk_lval_t *first = valk_lval_list_nth(after, 0);
      VALK_TEST_ASSERT(LVAL_TYPE(first) == LVAL_NUM, "First should be num");
      VALK_TEST_ASSERT(first->num == 1, "First should be 1");
      VALK_TEST_ASSERT(LVAL_ALLOC(first) == LVAL_ALLOC_HEAP,
                       "First element should be in heap");

      valk_lval_t *second = valk_lval_list_nth(after, 1);
      VALK_TEST_ASSERT(second->num == 2, "Second should be 2");

      valk_lval_t *third = valk_lval_list_nth(after, 2);
      VALK_TEST_ASSERT(third->num == 3, "Third should be 3");
    }
  }

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 3: Test checkpoint stats are updated correctly
void test_checkpoint_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);

    // Initial stats
    VALK_TEST_ASSERT(arena->stats.num_checkpoints == 0,
                     "Initial checkpoints should be 0");
    VALK_TEST_ASSERT(heap->stats.evacuations_from_scratch == 0,
                     "Initial evacuations should be 0");

    // Create some values in scratch
    VALK_WITH_ALLOC((void *)arena) {
      valk_lenv_put(env, valk_lval_sym("a"), valk_lval_num(1));
      valk_lenv_put(env, valk_lval_sym("b"), valk_lval_num(2));
      valk_lenv_put(env, valk_lval_sym("c"), valk_lval_num(3));
    }

    // First checkpoint
    valk_checkpoint(arena, heap, env);

    VALK_TEST_ASSERT(arena->stats.num_checkpoints == 1,
                     "num_checkpoints should be 1");
    size_t evac1 = arena->stats.values_evacuated;
    VALK_TEST_ASSERT(evac1 > 0, "Should have evacuated some values");

    // Create more values
    VALK_WITH_ALLOC((void *)arena) {
      valk_lenv_put(env, valk_lval_sym("d"), valk_lval_num(4));
    }

    // Second checkpoint
    valk_checkpoint(arena, heap, env);

    VALK_TEST_ASSERT(arena->stats.num_checkpoints == 2,
                     "num_checkpoints should be 2");
    VALK_TEST_ASSERT(arena->stats.values_evacuated > evac1,
                     "Total evacuations should have increased");

    // Heap should track evacuations received
    VALK_TEST_ASSERT(heap->stats.evacuations_from_scratch > 0,
                     "Heap should track evacuations received");
  }

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 7: Edge case test - nil values in cons cells
void test_checkpoint_nil_cons(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);

    // Create cons cell with nil head and tail in scratch
    VALK_WITH_ALLOC((void *)arena) {
      valk_lval_t *nil_cons = valk_lval_cons(valk_lval_nil(), valk_lval_nil());
      valk_lenv_put(env, valk_lval_sym("nil_cons"), nil_cons);
    }

    // Checkpoint should handle nil values gracefully
    valk_checkpoint(arena, heap, env);

    // Verify value survived
    valk_lval_t *retrieved = valk_lenv_get(env, valk_lval_sym("nil_cons"));
    VALK_TEST_ASSERT(LVAL_TYPE(retrieved) == LVAL_CONS,
                     "nil_cons should be cons type");
    VALK_TEST_ASSERT(LVAL_TYPE(retrieved->cons.head) == LVAL_NIL,
                     "head should be nil");
    VALK_TEST_ASSERT(LVAL_TYPE(retrieved->cons.tail) == LVAL_NIL,
                     "tail should be nil");
  }

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 7: Edge case test - deeply nested environment chain
void test_checkpoint_deep_env_chain(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 256 * 1024;  // Larger arena for deep chain
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  const int CHAIN_DEPTH = 50;  // 50 nested environments

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *root_env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, root_env);

    // Build chain of nested environments in scratch and store values
    // Each level stores a number to verify the chain survives
    VALK_WITH_ALLOC((void *)arena) {
      for (int i = 0; i < CHAIN_DEPTH; i++) {
        char name[32];
        snprintf(name, sizeof(name), "level_%d", i);
        valk_lenv_put(root_env, valk_lval_sym(name), valk_lval_num(i * 10));
      }
    }

    // Checkpoint
    valk_checkpoint(arena, heap, root_env);

    // Verify all levels survived
    int verified = 0;
    for (int i = 0; i < CHAIN_DEPTH; i += 10) {
      char name[32];
      snprintf(name, sizeof(name), "level_%d", i);
      valk_lval_t *val = valk_lenv_get(root_env, valk_lval_sym(name));
      if (LVAL_TYPE(val) == LVAL_NUM && val->num == i * 10) {
        verified++;
      }
    }
    VALK_TEST_ASSERT(verified == (CHAIN_DEPTH + 9) / 10,
                     "All spot-checked levels should survive");
  }

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 7: Edge case test - environment with many bindings
void test_checkpoint_many_bindings(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 512 * 1024;  // Larger arena for many bindings
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  const int NUM_BINDINGS = 500;  // 500 bindings

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);

    // Create many bindings in scratch
    VALK_WITH_ALLOC((void *)arena) {
      for (int i = 0; i < NUM_BINDINGS; i++) {
        char name[32];
        snprintf(name, sizeof(name), "var_%d", i);
        valk_lenv_put(env, valk_lval_sym(name), valk_lval_num(i * 2));
      }
    }

    // Checkpoint
    valk_checkpoint(arena, heap, env);

    // Verify all bindings survived
    int verified = 0;
    for (int i = 0; i < NUM_BINDINGS; i += 50) {  // Spot check every 50th
      char name[32];
      snprintf(name, sizeof(name), "var_%d", i);
      valk_lval_t *val = valk_lenv_get(env, valk_lval_sym(name));
      if (LVAL_TYPE(val) == LVAL_NUM && val->num == i * 2) {
        verified++;
      }
    }
    VALK_TEST_ASSERT(verified == (NUM_BINDINGS + 49) / 50,
                     "All spot-checked bindings should survive");
  }

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Phase 7: Edge case test - closure with captured environment
void test_checkpoint_closure(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  size_t threshold = 16 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(threshold, 0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);

    // Create a closure (lambda with captured environment) in scratch
    VALK_WITH_ALLOC((void *)arena) {
      // Create captured environment with a value
      valk_lenv_t *captured = valk_lenv_empty();
      valk_lenv_put(captured, valk_lval_sym("captured_val"), valk_lval_num(42));

      // Create a lambda function: formals = {x}, body = {+ x captured_val}
      valk_lval_t *formals_arr[] = {valk_lval_sym("x")};
      valk_lval_t *formals = valk_lval_list(formals_arr, 1);

      valk_lval_t *body_arr[] = {valk_lval_sym("+"), valk_lval_sym("x"),
                                  valk_lval_sym("captured_val")};
      valk_lval_t *body = valk_lval_list(body_arr, 3);

      valk_lval_t *lambda = valk_lval_lambda(captured, formals, body);

      valk_lenv_put(env, valk_lval_sym("my_closure"), lambda);
    }

    // Checkpoint
    valk_checkpoint(arena, heap, env);

    // Verify closure survived with captured env
    valk_lval_t *closure = valk_lenv_get(env, valk_lval_sym("my_closure"));
    VALK_TEST_ASSERT(LVAL_TYPE(closure) == LVAL_FUN, "Should be function type");
    VALK_TEST_ASSERT(closure->fun.builtin == NULL, "Should be lambda not builtin");
    VALK_TEST_ASSERT(closure->fun.env != NULL, "Should have captured env");

    // Check captured value
    valk_lval_t *captured_val =
        valk_lenv_get(closure->fun.env, valk_lval_sym("captured_val"));
    VALK_TEST_ASSERT(LVAL_TYPE(captured_val) == LVAL_NUM,
                     "captured_val should be number");
    VALK_TEST_ASSERT(captured_val->num == 42, "captured_val should be 42");
  }

  valk_thread_ctx = old_ctx;
  free(arena);
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

void test_slab_overflow_counter(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create tiny slab with 2 items
  valk_slab_t* slab = valk_slab_new(64, 2);

  // Verify initial state
  VALK_TEST_ASSERT(slab->overflowCount == 0, "overflowCount should start at 0");

  // Acquire all items
  valk_slab_item_t* item1 = valk_slab_aquire(slab);
  valk_slab_item_t* item2 = valk_slab_aquire(slab);

  VALK_TEST_ASSERT(item1 != NULL, "First acquire should succeed");
  VALK_TEST_ASSERT(item2 != NULL, "Second acquire should succeed");

  // This should fail and increment overflow counter
  valk_slab_item_t* item3 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item3 == NULL, "Third acquire should fail");
  VALK_TEST_ASSERT(slab->overflowCount == 1, "overflowCount should be 1 after first overflow");

  // Try again - should increment again
  valk_slab_item_t* item4 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item4 == NULL, "Fourth acquire should also fail");
  VALK_TEST_ASSERT(slab->overflowCount == 2, "overflowCount should be 2 after second overflow");

  // Release one and try again
  valk_slab_release(slab, item1);

  valk_slab_item_t* item5 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item5 != NULL, "Fifth acquire should succeed after release");
  VALK_TEST_ASSERT(slab->overflowCount == 2, "overflowCount should still be 2 after successful acquire");

  valk_slab_free(slab);
  VALK_PASS();
}

void test_ring_buffer_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t cap = 64;
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + cap);
  valk_ring_init(ring, cap);

  VALK_TEST_ASSERT(ring->capacity == cap, "Ring capacity should be 64");
  VALK_TEST_ASSERT(ring->offset == 0, "Ring offset should start at 0");

  uint8_t data[] = "Hello, World!";
  valk_ring_write(ring, data, sizeof(data));
  VALK_TEST_ASSERT(ring->offset == sizeof(data), "Ring offset should advance");

  free(ring);
  VALK_PASS();
}

void test_ring_buffer_wrap(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t cap = 16;
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + cap);
  valk_ring_init(ring, cap);

  uint8_t data1[] = "ABCDEFGH";
  uint8_t data2[] = "12345678";

  valk_ring_write(ring, data1, 8);
  VALK_TEST_ASSERT(ring->offset == 8, "After first write, offset should be 8");

  valk_ring_write(ring, data2, 8);
  VALK_TEST_ASSERT(ring->offset == 0, "After wrap, offset should be 0");

  valk_ring_write(ring, data1, 8);
  VALK_TEST_ASSERT(ring->offset == 8, "After third write, offset should be 8");

  free(ring);
  VALK_PASS();
}

void test_ring_buffer_rewind(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t cap = 32;
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + cap);
  valk_ring_init(ring, cap);

  uint8_t data[] = "1234567890ABCDEF";
  valk_ring_write(ring, data, 16);
  VALK_TEST_ASSERT(ring->offset == 16, "After write, offset should be 16");

  valk_ring_rewind(ring, 4);
  VALK_TEST_ASSERT(ring->offset == 12, "After rewind 4, offset should be 12");

  valk_ring_rewind(ring, 16);
  VALK_TEST_ASSERT(ring->offset == 28, "After rewind 16 (wrap), offset should be 28");

  free(ring);
  VALK_PASS();
}

void test_ring_buffer_read(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t cap = 32;
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + cap);
  valk_ring_init(ring, cap);

  uint8_t data[] = "HELLO";
  valk_ring_write(ring, data, 5);

  ring->offset = 0;

  uint8_t out[8] = {0};
  valk_ring_read(ring, 5, out);

  VALK_TEST_ASSERT(memcmp(out, "HELLO", 5) == 0, "Read should match written data");
  VALK_TEST_ASSERT(ring->offset == 5, "Offset should advance after read");

  free(ring);
  VALK_PASS();
}

void test_buffer_alloc_and_append(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_buffer_t buf;
  valk_buffer_alloc(&buf, 128);

  VALK_TEST_ASSERT(buf.capacity == 128, "Buffer capacity should be 128");
  VALK_TEST_ASSERT(buf.count == 0, "Buffer count should start at 0");
  VALK_TEST_ASSERT(buf.items != NULL, "Buffer items should be allocated");

  uint8_t data[] = "Test data";
  valk_buffer_append(&buf, data, sizeof(data) - 1);

  VALK_TEST_ASSERT(buf.count == sizeof(data) - 1, "Buffer count should match appended data");
  VALK_TEST_ASSERT(!valk_buffer_is_full(&buf), "Buffer should not be full");

  valk_mem_free(buf.items);
  VALK_PASS();
}

void test_allocator_type_strings(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char* s_null = valk_mem_allocator_e_to_string(VALK_ALLOC_NULL);
  VALK_TEST_ASSERT(s_null != NULL, "NULL alloc string should not be NULL");
  VALK_TEST_ASSERT(strstr(s_null, "NULL") != NULL, "NULL alloc string should contain 'NULL'");

  const char* s_malloc = valk_mem_allocator_e_to_string(VALK_ALLOC_MALLOC);
  VALK_TEST_ASSERT(strstr(s_malloc, "Malloc") != NULL, "Malloc alloc string should contain 'Malloc'");

  const char* s_arena = valk_mem_allocator_e_to_string(VALK_ALLOC_ARENA);
  VALK_TEST_ASSERT(strstr(s_arena, "Arena") != NULL, "Arena alloc string should contain 'Arena'");

  const char* s_slab = valk_mem_allocator_e_to_string(VALK_ALLOC_SLAB);
  VALK_TEST_ASSERT(strstr(s_slab, "Slab") != NULL, "Slab alloc string should contain 'Slab'");

  const char* s_gc = valk_mem_allocator_e_to_string(VALK_ALLOC_GC_HEAP);
  VALK_TEST_ASSERT(strstr(s_gc, "GC") != NULL, "GC Heap alloc string should contain 'GC'");

  VALK_PASS();
}

void test_process_memory_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_process_memory_t pm;
  valk_process_memory_collect(&pm);

  VALK_TEST_ASSERT(pm.rss_bytes >= 0, "RSS should be non-negative");
  VALK_TEST_ASSERT(pm.vms_bytes >= pm.rss_bytes, "VMS should be >= RSS");

  valk_process_memory_collect(NULL);

  VALK_PASS();
}

void test_smaps_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_smaps_breakdown_t smaps;
  valk_smaps_collect(&smaps);

  VALK_TEST_ASSERT(smaps.total_rss >= 0, "Total RSS should be non-negative");

  valk_smaps_collect(NULL);

  VALK_PASS();
}

void test_arena_print_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 16 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  valk_mem_arena_alloc(arena, 100);
  valk_mem_arena_alloc(arena, 200);
  valk_mem_arena_reset(arena);

  FILE* devnull = fopen("/dev/null", "w");
  if (devnull) {
    valk_mem_arena_print_stats(arena, devnull);
    fclose(devnull);
  }

  valk_mem_arena_print_stats(NULL, NULL);
  valk_mem_arena_print_stats(arena, NULL);

  free(arena);
  VALK_PASS();
}

void test_slab_allocator_api(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t* slab = valk_slab_new(128, 8);

  void* ptr1 = valk_mem_allocator_alloc((valk_mem_allocator_t*)slab, 64);
  VALK_TEST_ASSERT(ptr1 != NULL, "Slab alloc should succeed");

  void* ptr2 = valk_mem_allocator_calloc((valk_mem_allocator_t*)slab, 1, 64);
  VALK_TEST_ASSERT(ptr2 != NULL, "Slab calloc should succeed");

  void* ptr3 = valk_mem_allocator_realloc((valk_mem_allocator_t*)slab, ptr1, 64);
  VALK_TEST_ASSERT(ptr3 == ptr1, "Slab realloc within size should return same ptr");

  valk_mem_allocator_free((valk_mem_allocator_t*)slab, ptr1);
  valk_mem_allocator_free((valk_mem_allocator_t*)slab, ptr2);

  valk_slab_free(slab);
  VALK_PASS();
}

void test_arena_allocator_realloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  void* ptr1 = valk_mem_allocator_alloc((valk_mem_allocator_t*)arena, 100);
  VALK_TEST_ASSERT(ptr1 != NULL, "Arena alloc should succeed");

  memset(ptr1, 'A', 100);

  void* ptr2 = valk_mem_allocator_realloc((valk_mem_allocator_t*)arena, ptr1, 200);
  VALK_TEST_ASSERT(ptr2 != NULL, "Arena realloc should succeed");

  uint8_t* bytes = (uint8_t*)ptr2;
  int match = 1;
  for (int i = 0; i < 100 && match; i++) {
    if (bytes[i] != 'A') match = 0;
  }
  VALK_TEST_ASSERT(match, "Realloc should preserve original data");

  void* ptr3 = valk_mem_allocator_calloc((valk_mem_allocator_t*)arena, 10, 10);
  VALK_TEST_ASSERT(ptr3 != NULL, "Arena calloc should succeed");

  bytes = (uint8_t*)ptr3;
  match = 1;
  for (int i = 0; i < 100 && match; i++) {
    if (bytes[i] != 0) match = 0;
  }
  VALK_TEST_ASSERT(match, "Calloc should zero memory");

  valk_mem_allocator_free((valk_mem_allocator_t*)arena, ptr1);

  free(arena);
  VALK_PASS();
}

void test_ring_buffer_fread(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t cap = 64;
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + cap);
  valk_ring_init(ring, cap);

  uint8_t data[] = "HELLO_WORLD_TEST";
  valk_ring_write(ring, data, 16);
  ring->offset = 0;

  FILE *devnull = fopen("/dev/null", "w");
  if (devnull) {
    valk_ring_fread(ring, 16, devnull);
    VALK_TEST_ASSERT(ring->offset == 16, "fread should advance offset");
    fclose(devnull);
  }

  free(ring);
  VALK_PASS();
}

void test_ring_buffer_fread_wrap(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t cap = 16;
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + cap);
  valk_ring_init(ring, cap);

  uint8_t data[] = "ABCDEFGHIJKLMNOP";
  valk_ring_write(ring, data, 16);
  ring->offset = 8;

  FILE *devnull = fopen("/dev/null", "w");
  if (devnull) {
    valk_ring_fread(ring, 16, devnull);
    VALK_TEST_ASSERT(ring->offset == 8, "fread should wrap and end at offset 8");
    fclose(devnull);
  }

  free(ring);
  VALK_PASS();
}

void test_ring_buffer_print(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t cap = 32;
  valk_ring_t *ring = malloc(sizeof(valk_ring_t) + cap);
  valk_ring_init(ring, cap);

  uint8_t data[] = "PRINT_TEST_DATA!";
  valk_ring_write(ring, data, 16);

  FILE *devnull = fopen("/dev/null", "w");
  if (devnull) {
    valk_ring_print(ring, devnull);
    fclose(devnull);
  }

  free(ring);
  VALK_PASS();
}

void test_arena_reset_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 16 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  valk_mem_arena_alloc(arena, 100);
  valk_mem_arena_alloc(arena, 200);
  valk_mem_arena_reset(arena);

  VALK_TEST_ASSERT(arena->stats.total_allocations > 0, "Should have allocations");
  VALK_TEST_ASSERT(arena->stats.num_resets > 0, "Should have resets");

  size_t old_hwm = arena->stats.high_water_mark;
  valk_mem_arena_reset_stats(arena);

  VALK_TEST_ASSERT(arena->stats.total_allocations == 0, "Allocations should be 0");
  VALK_TEST_ASSERT(arena->stats.num_resets == 0, "Resets should be 0");
  VALK_TEST_ASSERT(arena->stats.high_water_mark == old_hwm, "HWM should be preserved");

  valk_mem_arena_reset_stats(NULL);

  free(arena);
  VALK_PASS();
}

void test_malloc_allocator_api(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_allocator_t alloc = {.type = VALK_ALLOC_MALLOC};

  void *ptr = valk_mem_allocator_alloc(&alloc, 128);
  VALK_TEST_ASSERT(ptr != NULL, "Malloc alloc should succeed");

  void *ptr2 = valk_mem_allocator_calloc(&alloc, 4, 32);
  VALK_TEST_ASSERT(ptr2 != NULL, "Malloc calloc should succeed");

  void *ptr3 = valk_mem_allocator_realloc(&alloc, ptr, 256);
  VALK_TEST_ASSERT(ptr3 != NULL, "Malloc realloc should succeed");

  valk_mem_allocator_free(&alloc, ptr3);
  valk_mem_allocator_free(&alloc, ptr2);

  VALK_PASS();
}

void test_gc_heap_allocator_api(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  void *ptr = valk_mem_allocator_alloc((valk_mem_allocator_t*)heap, 128);
  VALK_TEST_ASSERT(ptr != NULL, "GC heap alloc should succeed");

  void *ptr2 = valk_mem_allocator_calloc((valk_mem_allocator_t*)heap, 4, 32);
  VALK_TEST_ASSERT(ptr2 != NULL, "GC heap calloc should succeed");

  valk_gc_malloc_heap_destroy(heap);
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

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_implicit_alloc", test_implicit_alloc);

  valk_testsuite_add_test(suite, "test_slab_alloc", test_slab_alloc);
  valk_testsuite_add_test(suite, "test_slab_concurrency",
                          test_slab_concurrency);
  valk_testsuite_add_test(suite, "test_slab_overflow_counter",
                          test_slab_overflow_counter);

  // Ring buffer and allocator tests
  valk_testsuite_add_test(suite, "test_ring_buffer_basic", test_ring_buffer_basic);
  valk_testsuite_add_test(suite, "test_ring_buffer_wrap", test_ring_buffer_wrap);
  valk_testsuite_add_test(suite, "test_ring_buffer_rewind", test_ring_buffer_rewind);
  valk_testsuite_add_test(suite, "test_ring_buffer_read", test_ring_buffer_read);
  valk_testsuite_add_test(suite, "test_buffer_alloc_and_append", test_buffer_alloc_and_append);
  valk_testsuite_add_test(suite, "test_allocator_type_strings", test_allocator_type_strings);
  valk_testsuite_add_test(suite, "test_process_memory_collect", test_process_memory_collect);
  valk_testsuite_add_test(suite, "test_smaps_collect", test_smaps_collect);
  valk_testsuite_add_test(suite, "test_arena_print_stats", test_arena_print_stats);
  valk_testsuite_add_test(suite, "test_slab_allocator_api", test_slab_allocator_api);
  valk_testsuite_add_test(suite, "test_arena_allocator_realloc", test_arena_allocator_realloc);
  valk_testsuite_add_test(suite, "test_ring_buffer_fread", test_ring_buffer_fread);
  valk_testsuite_add_test(suite, "test_ring_buffer_fread_wrap", test_ring_buffer_fread_wrap);
  valk_testsuite_add_test(suite, "test_ring_buffer_print", test_ring_buffer_print);
  valk_testsuite_add_test(suite, "test_arena_reset_stats", test_arena_reset_stats);
  valk_testsuite_add_test(suite, "test_malloc_allocator_api", test_malloc_allocator_api);
  valk_testsuite_add_test(suite, "test_gc_heap_allocator_api", test_gc_heap_allocator_api);

  // Phase 1 telemetry tests
  valk_testsuite_add_test(suite, "test_arena_stats", test_arena_stats);
  valk_testsuite_add_test(suite, "test_gc_heap_hard_limit", test_gc_heap_hard_limit);
  valk_testsuite_add_test(suite, "test_gc_heap_stats", test_gc_heap_stats);
  valk_testsuite_add_test(suite, "test_arena_overflow_fallback", test_arena_overflow_fallback);
  valk_testsuite_add_test(suite, "test_arena_total_bytes", test_arena_total_bytes);

  // Phase 2 forwarding pointer tests
  valk_testsuite_add_test(suite, "test_forward_set_and_check", test_forward_set_and_check);
  valk_testsuite_add_test(suite, "test_forward_follow_chain", test_forward_follow_chain);
  valk_testsuite_add_test(suite, "test_forward_preserves_alloc_flags", test_forward_preserves_alloc_flags);

  // Phase 3 checkpoint/evacuation tests
  valk_testsuite_add_test(suite, "test_should_checkpoint", test_should_checkpoint);
  valk_testsuite_add_test(suite, "test_checkpoint_empty", test_checkpoint_empty);
  valk_testsuite_add_test(suite, "test_checkpoint_evacuate_number", test_checkpoint_evacuate_number);
  valk_testsuite_add_test(suite, "test_checkpoint_evacuate_list", test_checkpoint_evacuate_list);
  valk_testsuite_add_test(suite, "test_checkpoint_stats", test_checkpoint_stats);

  // Phase 7 edge case tests
  valk_testsuite_add_test(suite, "test_checkpoint_nil_cons", test_checkpoint_nil_cons);
  valk_testsuite_add_test(suite, "test_checkpoint_deep_env_chain", test_checkpoint_deep_env_chain);
  valk_testsuite_add_test(suite, "test_checkpoint_many_bindings", test_checkpoint_many_bindings);
  valk_testsuite_add_test(suite, "test_checkpoint_closure", test_checkpoint_closure);

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
