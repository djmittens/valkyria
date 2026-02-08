#include "test_memory.h"
#include "common.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"
#include <math.h>
#include <pthread.h>
#include <time.h>
#include <unistd.h>

typedef struct test_box {
  valk_mem_allocator_t *allocator;
  u64 capacity;
  void *item;
} test_box_t;

static test_box_t *test_box_new(sz capacity) {
  test_box_t *box = valk_mem_alloc(sizeof(test_box_t) + capacity);
  memset(box, 0, sizeof(test_box_t) + capacity);
  box->allocator = valk_thread_ctx.allocator;
  box->capacity = capacity;
  box->item = (char*)box + sizeof(test_box_t);
  return box;
}

static void test_box_init(test_box_t *box, sz capacity) {
  memset(box, 0, sizeof(test_box_t) + capacity);
  box->capacity = capacity;
  box->item = (char*)box + sizeof(test_box_t);
}

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
  VALK_TEST();

  const char msg[] = "Get fucked";

  int itemLen = sizeof(test_box_t) + sizeof(msg);
  size_t numItems = rand() % 1000;
  valk_slab_t *slab = valk_slab_new(itemLen, numItems);

  test_box_t *boxes[numItems];
  size_t slabIds[numItems];

  printf("Aquiring %ld boxes\n", numItems);
  // allocate everything
  for (size_t i = 0; i < numItems; ++i) {
    if (rand() % 2) {
      valk_slab_item_t *item = valk_slab_aquire(slab);
      boxes[i] = (test_box_t *)item->data;
      test_box_init(boxes[i], sizeof(msg));
      boxes[i]->allocator = (valk_mem_allocator_t *)slab;
      slabIds[i] = item->handle;
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
        boxes[i] = test_box_new(sizeof(msg));
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
  test_box_t *newBoxes[reapNum];

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
    newBoxes[i] = (test_box_t *)valk_slab_aquire(slab)->data;
    test_box_init(newBoxes[i], sizeof(newMsg));
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

  valk_slab_free(slab);
  VALK_PASS();
}

typedef struct {
  size_t id;
  valk_slab_t *slab;
  test_box_t **boxes;
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
  int itemLen = sizeof(test_box_t) + sizeof(msg);
  size_t numItems = rand() % 1000;

  valk_slab_t *slab = valk_slab_new(itemLen, numItems);

  test_box_t *boxes[numItems];
  printf("Aquiring %ld boxes\n", numItems);

  size_t slabIds[numItems];

  // allocate everything
  for (size_t i = 0; i < numItems; ++i) {
    if (rand() % 2) {
      valk_slab_item_t *item = valk_slab_aquire(slab);
      boxes[i] = (test_box_t *)item->data;
      test_box_init(boxes[i], sizeof(msg));
      boxes[i]->allocator = (valk_mem_allocator_t *)slab;
      slabIds[i] = item->handle;
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
        boxes[i] = test_box_new(sizeof(msg));
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
  test_box_t *splitBoxes[numThreads][numItems];

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

  valk_slab_free(slab);
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
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) == 0,
                   "Initial total_allocations should be 0");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_resets) == 0,
                   "Initial num_resets should be 0");

  // Allocate some memory
  void *ptr1 = valk_mem_arena_alloc(arena, 100);
  VALK_TEST_ASSERT(ptr1 != nullptr, "First allocation should succeed");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) == 1,
                   "total_allocations should be 1 after first alloc");

  void *ptr2 = valk_mem_arena_alloc(arena, 200);
  VALK_TEST_ASSERT(ptr2 != nullptr, "Second allocation should succeed");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) == 2,
                   "total_allocations should be 2 after second alloc");

  // Check high water mark was updated
  VALK_TEST_ASSERT(atomic_load(&arena->stats.high_water_mark) > 0,
                   "high_water_mark should be > 0");
  size_t hwm_before_reset = atomic_load(&arena->stats.high_water_mark);

  // Reset the arena
  valk_mem_arena_reset(arena);
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_resets) == 1,
                   "num_resets should be 1 after reset");
  VALK_TEST_ASSERT(arena->offset == 0,
                   "Arena offset should be 0 after reset");
  // high_water_mark should be preserved
  VALK_TEST_ASSERT(atomic_load(&arena->stats.high_water_mark) >= hwm_before_reset,
                   "high_water_mark should be preserved after reset");

  // Test valk_ptr_in_arena
  void *ptr3 = valk_mem_arena_alloc(arena, 50);
  VALK_TEST_ASSERT(valk_ptr_in_arena(arena, ptr3),
                   "ptr3 should be in arena");
  VALK_TEST_ASSERT(!valk_ptr_in_arena(arena, (void *)0x12345678),
                   "Random pointer should not be in arena");
  VALK_TEST_ASSERT(!valk_ptr_in_arena(arena, nullptr),
                   "nullptr should not be in arena");

  // Test reset_stats
  valk_mem_arena_reset_stats(arena);
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) == 0,
                   "total_allocations should be 0 after reset_stats");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_resets) == 0,
                   "num_resets should be 0 after reset_stats");
  // high_water_mark is intentionally NOT reset
  VALK_TEST_ASSERT(atomic_load(&arena->stats.high_water_mark) >= hwm_before_reset,
                   "high_water_mark should NOT be reset");

  free(arena);
  VALK_PASS();
}

// Test GC heap hard limit
void test_gc_heap_hard_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  sz hard_limit = 2 * 1024 * 1024;
  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(hard_limit);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  VALK_TEST_ASSERT(heap->hard_limit == hard_limit, "Hard limit should match");

  valk_gc_set_hard_limit(heap, hard_limit * 2);
  VALK_TEST_ASSERT(heap->hard_limit == hard_limit * 2, "Hard limit should be updated");

  VALK_TEST_ASSERT(heap->stats.peak_usage == 0, "peak_usage should start at 0");

  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test GC heap statistics tracking
void test_gc_heap_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  // Allocate something
  void *ptr = valk_gc_malloc_heap_alloc(heap, 123);
  VALK_TEST_ASSERT(ptr != nullptr, "Allocation should succeed");
  VALK_TEST_ASSERT(valk_gc_heap2_used_bytes(heap) > 0,
                   "used_bytes should be > 0");
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  // Set up thread context with fallback heap
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.heap = heap;

  // Initial state: no overflow
  VALK_TEST_ASSERT(atomic_load(&arena->stats.overflow_fallbacks) == 0,
                   "Initial overflow_fallbacks should be 0");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.overflow_bytes) == 0,
                   "Initial overflow_bytes should be 0");

  // Fill up most of the arena with small allocations
  size_t alloc_count = 0;
  while (arena->offset < arena->capacity - 100) {
    void *p = valk_mem_arena_alloc(arena, 32);
    VALK_TEST_ASSERT(p != nullptr, "Arena allocation should succeed");
    alloc_count++;
    if (alloc_count > 100) break;  // Safety limit
  }

  // Now try to allocate something larger than remaining space
  // This should trigger overflow fallback to heap
  size_t remaining = arena->capacity - arena->offset;
  size_t overflow_size = remaining + 100;  // Definitely won't fit

  void *overflow_ptr = valk_mem_arena_alloc(arena, overflow_size);
  VALK_TEST_ASSERT(overflow_ptr != nullptr,
                   "Overflow allocation should succeed via heap fallback");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.overflow_fallbacks) == 1,
                   "overflow_fallbacks should be 1");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.overflow_bytes) == overflow_size,
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

  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_bytes_allocated) == 0,
                   "Initial total_bytes_allocated should be 0");

  // Allocate various sizes
  valk_mem_arena_alloc(arena, 100);
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_bytes_allocated) == 100,
                   "total_bytes_allocated should be 100");

  valk_mem_arena_alloc(arena, 200);
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_bytes_allocated) == 300,
                   "total_bytes_allocated should be 300");

  valk_mem_arena_alloc(arena, 50);
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_bytes_allocated) == 350,
                   "total_bytes_allocated should be 350");

  // Reset arena - total_bytes should keep accumulating
  valk_mem_arena_reset(arena);
  valk_mem_arena_alloc(arena, 75);
  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_bytes_allocated) == 425,
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

  // nullptr arena should not crash and return false
  VALK_TEST_ASSERT(!valk_should_checkpoint(nullptr, 0.75f),
                   "nullptr arena should return false");

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.heap = heap;

  valk_lenv_t *env = valk_lenv_empty();

  // Run checkpoint on empty arena
  valk_checkpoint(arena, heap, env);

  // Stats should show 0 evacuations
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_checkpoints) == 1,
                   "num_checkpoints should be 1");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.values_evacuated) == 0,
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;
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
    VALK_TEST_ASSERT(atomic_load(&arena->stats.values_evacuated) > 0,
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);
    VALK_TEST_ASSERT(atomic_load(&arena->stats.num_checkpoints) == 0,
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

    VALK_TEST_ASSERT(atomic_load(&arena->stats.num_checkpoints) == 1,
                     "num_checkpoints should be 1");
    size_t evac1 = atomic_load(&arena->stats.values_evacuated);
    VALK_TEST_ASSERT(evac1 > 0, "Should have evacuated some values");

    // Create more values
    VALK_WITH_ALLOC((void *)arena) {
      valk_lenv_put(env, valk_lval_sym("d"), valk_lval_num(4));
    }

    // Second checkpoint
    valk_checkpoint(arena, heap, env);

    VALK_TEST_ASSERT(atomic_load(&arena->stats.num_checkpoints) == 2,
                     "num_checkpoints should be 2");
    VALK_TEST_ASSERT(atomic_load(&arena->stats.values_evacuated) > evac1,
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  const int CHAIN_DEPTH = 50;

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  const int NUM_BINDINGS = 500;

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

// Slab bitmap tests
void test_slab_bitmap_snapshot(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 16);
  ASSERT_NOT_NULL(slab);
  ASSERT_NOT_NULL(slab->usage_bitmap);

  valk_slab_item_t *item1 = valk_slab_aquire(slab);
  valk_slab_item_t *item2 = valk_slab_aquire(slab);

  valk_slab_bitmap_t snapshot;
  valk_slab_bitmap_snapshot(slab, &snapshot);

  ASSERT_NOT_NULL(snapshot.data);
  ASSERT_GT(snapshot.bytes, 0);
  ASSERT_GT(snapshot.version, 0);

  valk_slab_bitmap_free(&snapshot);
  ASSERT_NULL(snapshot.data);
  ASSERT_EQ(snapshot.bytes, 0);

  valk_slab_release(slab, item1);
  valk_slab_release(slab, item2);
  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_bitmap_snapshot_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_bitmap_t snapshot = {0};

  valk_slab_bitmap_snapshot(nullptr, &snapshot);
  ASSERT_NULL(snapshot.data);
  ASSERT_EQ(snapshot.bytes, 0);

  valk_slab_t *slab = valk_slab_new(64, 16);
  valk_slab_bitmap_snapshot(slab, nullptr);

  valk_slab_free(slab);

  VALK_PASS();
}

void test_bitmap_delta_init_free(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_bitmap_delta_t delta;

  valk_bitmap_delta_init(&delta);
  ASSERT_NULL(delta.runs);
  ASSERT_EQ(delta.run_count, 0);
  ASSERT_EQ(delta.run_capacity, 0);

  valk_bitmap_delta_free(&delta);
  ASSERT_NULL(delta.runs);

  valk_bitmap_delta_init(nullptr);
  valk_bitmap_delta_free(nullptr);

  VALK_PASS();
}

void test_bitmap_delta_compute_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 32);
  ASSERT_NOT_NULL(slab);

  valk_slab_bitmap_t prev;
  valk_slab_bitmap_snapshot(slab, &prev);

  valk_slab_item_t *item1 = valk_slab_aquire(slab);
  valk_slab_item_t *item2 = valk_slab_aquire(slab);

  valk_slab_bitmap_t curr;
  valk_slab_bitmap_snapshot(slab, &curr);

  valk_bitmap_delta_t delta;
  bool ok = valk_bitmap_delta_compute(&curr, &prev, &delta);
  ASSERT_TRUE(ok);
  ASSERT_GT(delta.run_count, 0);

  valk_bitmap_delta_free(&delta);
  valk_slab_bitmap_free(&prev);
  valk_slab_bitmap_free(&curr);

  valk_slab_release(slab, item1);
  valk_slab_release(slab, item2);
  valk_slab_free(slab);

  VALK_PASS();
}

void test_bitmap_delta_compute_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_bitmap_t bmp = {.data = malloc(8), .bytes = 8, .version = 1};
  memset(bmp.data, 0, 8);
  valk_bitmap_delta_t delta;

  bool ok1 = valk_bitmap_delta_compute(nullptr, &bmp, &delta);
  ASSERT_FALSE(ok1);

  bool ok2 = valk_bitmap_delta_compute(&bmp, nullptr, &delta);
  ASSERT_FALSE(ok2);

  bool ok3 = valk_bitmap_delta_compute(&bmp, &bmp, nullptr);
  ASSERT_FALSE(ok3);

  valk_slab_bitmap_t empty = {.data = nullptr, .bytes = 0, .version = 0};
  bool ok4 = valk_bitmap_delta_compute(&empty, &bmp, &delta);
  ASSERT_FALSE(ok4);

  valk_slab_bitmap_t diff_size = {.data = malloc(4), .bytes = 4, .version = 1};
  bool ok5 = valk_bitmap_delta_compute(&diff_size, &bmp, &delta);
  ASSERT_FALSE(ok5);

  free(bmp.data);
  free(diff_size.data);

  VALK_PASS();
}

void test_bitmap_delta_to_rle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 64);
  ASSERT_NOT_NULL(slab);

  valk_slab_bitmap_t prev;
  valk_slab_bitmap_snapshot(slab, &prev);

  for (int i = 0; i < 8; i++) {
    valk_slab_aquire(slab);
  }

  valk_slab_bitmap_t curr;
  valk_slab_bitmap_snapshot(slab, &curr);

  valk_bitmap_delta_t delta;
  bool ok = valk_bitmap_delta_compute(&curr, &prev, &delta);
  ASSERT_TRUE(ok);

  char buf[256];
  sz len = valk_bitmap_delta_to_rle(&delta, buf, sizeof(buf));
  ASSERT_GT(len, 0);
  ASSERT_TRUE(buf[0] != '\0');

  valk_bitmap_delta_free(&delta);
  valk_slab_bitmap_free(&prev);
  valk_slab_bitmap_free(&curr);
  valk_slab_free(slab);

  VALK_PASS();
}

void test_bitmap_delta_to_rle_edge_cases(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buf[16];

  sz len1 = valk_bitmap_delta_to_rle(nullptr, buf, sizeof(buf));
  ASSERT_EQ(len1, 0);

  valk_bitmap_delta_t empty = {0};
  sz len2 = valk_bitmap_delta_to_rle(&empty, nullptr, 0);
  ASSERT_EQ(len2, 0);

  sz len3 = valk_bitmap_delta_to_rle(&empty, buf, 2);
  ASSERT_EQ(len3, 0);

  VALK_PASS();
}

void test_slab_bitmap_buckets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 100);
  ASSERT_NOT_NULL(slab);

  for (int i = 0; i < 30; i++) {
    valk_slab_aquire(slab);
  }

  valk_bitmap_bucket_t buckets[10];
  sz result = valk_slab_bitmap_buckets(slab, 0, 100, 10, buckets);
  ASSERT_EQ(result, 10);

  u64 total_used = 0;
  u64 total_free = 0;
  for (int i = 0; i < 10; i++) {
    total_used += buckets[i].used;
    total_free += buckets[i].free;
  }
  ASSERT_EQ(total_used, 30);
  ASSERT_EQ(total_free, 70);

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_bitmap_buckets_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_bitmap_bucket_t buckets[10];

  sz r1 = valk_slab_bitmap_buckets(nullptr, 0, 100, 10, buckets);
  ASSERT_EQ(r1, 0);

  valk_slab_t *slab = valk_slab_new(64, 100);
  sz r2 = valk_slab_bitmap_buckets(slab, 0, 100, 10, nullptr);
  ASSERT_EQ(r2, 0);

  sz r3 = valk_slab_bitmap_buckets(slab, 0, 100, 0, buckets);
  ASSERT_EQ(r3, 0);

  sz r4 = valk_slab_bitmap_buckets(slab, 50, 50, 10, buckets);
  ASSERT_EQ(r4, 0);

  sz r5 = valk_slab_bitmap_buckets(slab, 100, 50, 10, buckets);
  ASSERT_EQ(r5, 0);

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_bitmap_buckets_partial_range(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 100);
  ASSERT_NOT_NULL(slab);

  for (int i = 0; i < 50; i++) {
    valk_slab_aquire(slab);
  }

  valk_bitmap_bucket_t buckets[5];
  sz result = valk_slab_bitmap_buckets(slab, 20, 80, 5, buckets);
  ASSERT_EQ(result, 5);

  u64 total = 0;
  for (int i = 0; i < 5; i++) {
    total += buckets[i].used + buckets[i].free;
  }
  ASSERT_EQ(total, 60);

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_peak_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(64, 20);
  ASSERT_NOT_NULL(slab);
  ASSERT_EQ(slab->peakUsed, 0);

  valk_slab_item_t *items[10];
  for (int i = 0; i < 10; i++) {
    items[i] = valk_slab_aquire(slab);
  }
  ASSERT_EQ(slab->peakUsed, 10);

  for (int i = 0; i < 5; i++) {
    valk_slab_release(slab, items[i]);
  }
  ASSERT_EQ(slab->peakUsed, 10);

  for (int i = 0; i < 8; i++) {
    valk_slab_aquire(slab);
  }
  ASSERT_EQ(slab->peakUsed, 13);

  valk_slab_free(slab);

  VALK_PASS();
}

void test_slab_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_free(nullptr);

  VALK_PASS();
}

void test_slab_bitmap_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_bitmap_free(nullptr);

  valk_slab_bitmap_t bmp = {0};
  valk_slab_bitmap_free(&bmp);
  ASSERT_NULL(bmp.data);

  VALK_PASS();
}

// Phase 7: Edge case test - closure with captured environment
void test_checkpoint_closure(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 64 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)arena;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_gc_malloc_set_root(heap, env);
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
    VALK_TEST_ASSERT(closure->fun.builtin == nullptr, "Should be lambda not builtin");
    VALK_TEST_ASSERT(closure->fun.env != nullptr, "Should have captured env");

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

  VALK_TEST_ASSERT(item1 != nullptr, "First acquire should succeed");
  VALK_TEST_ASSERT(item2 != nullptr, "Second acquire should succeed");

  // This should fail and increment overflow counter
  valk_slab_item_t* item3 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item3 == nullptr, "Third acquire should fail");
  VALK_TEST_ASSERT(slab->overflowCount == 1, "overflowCount should be 1 after first overflow");

  // Try again - should increment again
  valk_slab_item_t* item4 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item4 == nullptr, "Fourth acquire should also fail");
  VALK_TEST_ASSERT(slab->overflowCount == 2, "overflowCount should be 2 after second overflow");

  // Release one and try again
  valk_slab_release(slab, item1);

  valk_slab_item_t* item5 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item5 != nullptr, "Fifth acquire should succeed after release");
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

  u8 data[] = "Hello, World!";
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

  u8 data1[] = "ABCDEFGH";
  u8 data2[] = "12345678";

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

  u8 data[] = "1234567890ABCDEF";
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

  u8 data[] = "HELLO";
  valk_ring_write(ring, data, 5);

  ring->offset = 0;

  u8 out[8] = {0};
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
  VALK_TEST_ASSERT(buf.items != nullptr, "Buffer items should be allocated");

  u8 data[] = "Test data";
  valk_buffer_append(&buf, data, sizeof(data) - 1);

  VALK_TEST_ASSERT(buf.count == sizeof(data) - 1, "Buffer count should match appended data");
  VALK_TEST_ASSERT(!valk_buffer_is_full(&buf), "Buffer should not be full");

  valk_mem_free(buf.items);
  VALK_PASS();
}

void test_allocator_type_strings(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char* s_null = valk_mem_allocator_e_to_string(VALK_ALLOC_NULL);
  VALK_TEST_ASSERT(s_null != nullptr, "nullptr alloc string should not be nullptr");
  VALK_TEST_ASSERT(strstr(s_null, "nullptr") != nullptr, "nullptr alloc string should contain 'nullptr'");

  const char* s_malloc = valk_mem_allocator_e_to_string(VALK_ALLOC_MALLOC);
  VALK_TEST_ASSERT(strstr(s_malloc, "Malloc") != nullptr, "Malloc alloc string should contain 'Malloc'");

  const char* s_arena = valk_mem_allocator_e_to_string(VALK_ALLOC_ARENA);
  VALK_TEST_ASSERT(strstr(s_arena, "Arena") != nullptr, "Arena alloc string should contain 'Arena'");

  const char* s_slab = valk_mem_allocator_e_to_string(VALK_ALLOC_SLAB);
  VALK_TEST_ASSERT(strstr(s_slab, "Slab") != nullptr, "Slab alloc string should contain 'Slab'");

  const char* s_gc = valk_mem_allocator_e_to_string(VALK_ALLOC_GC_HEAP);
  VALK_TEST_ASSERT(strstr(s_gc, "GC") != nullptr, "GC Heap alloc string should contain 'GC'");

  VALK_PASS();
}

void test_process_memory_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_process_memory_t pm;
  valk_process_memory_collect(&pm);

  VALK_TEST_ASSERT(pm.rss_bytes >= 0, "RSS should be non-negative");
  VALK_TEST_ASSERT(pm.vms_bytes >= pm.rss_bytes, "VMS should be >= RSS");

  valk_process_memory_collect(nullptr);

  VALK_PASS();
}

void test_smaps_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_smaps_breakdown_t smaps;
  valk_smaps_collect(&smaps);

  VALK_TEST_ASSERT(smaps.total_rss >= 0, "Total RSS should be non-negative");

  valk_smaps_collect(nullptr);

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

  valk_mem_arena_print_stats(nullptr, nullptr);
  valk_mem_arena_print_stats(arena, nullptr);

  free(arena);
  VALK_PASS();
}

void test_slab_allocator_api(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t* slab = valk_slab_new(128, 8);

  void* ptr1 = valk_mem_allocator_alloc((valk_mem_allocator_t*)slab, 64);
  VALK_TEST_ASSERT(ptr1 != nullptr, "Slab alloc should succeed");

  void* ptr2 = valk_mem_allocator_calloc((valk_mem_allocator_t*)slab, 1, 64);
  VALK_TEST_ASSERT(ptr2 != nullptr, "Slab calloc should succeed");

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
  VALK_TEST_ASSERT(ptr1 != nullptr, "Arena alloc should succeed");

  memset(ptr1, 'A', 100);

  void* ptr2 = valk_mem_allocator_realloc((valk_mem_allocator_t*)arena, ptr1, 200);
  VALK_TEST_ASSERT(ptr2 != nullptr, "Arena realloc should succeed");

  u8* bytes = (u8*)ptr2;
  int match = 1;
  for (int i = 0; i < 100 && match; i++) {
    if (bytes[i] != 'A') match = 0;
  }
  VALK_TEST_ASSERT(match, "Realloc should preserve original data");

  void* ptr3 = valk_mem_allocator_calloc((valk_mem_allocator_t*)arena, 10, 10);
  VALK_TEST_ASSERT(ptr3 != nullptr, "Arena calloc should succeed");

  bytes = (u8*)ptr3;
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

  u8 data[] = "HELLO_WORLD_TEST";
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

  u8 data[] = "ABCDEFGHIJKLMNOP";
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

  u8 data[] = "PRINT_TEST_DATA!";
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

  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) > 0, "Should have allocations");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_resets) > 0, "Should have resets");

  size_t old_hwm = atomic_load(&arena->stats.high_water_mark);
  valk_mem_arena_reset_stats(arena);

  VALK_TEST_ASSERT(atomic_load(&arena->stats.total_allocations) == 0, "Allocations should be 0");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.num_resets) == 0, "Resets should be 0");
  VALK_TEST_ASSERT(atomic_load(&arena->stats.high_water_mark) == old_hwm, "HWM should be preserved");

  valk_mem_arena_reset_stats(nullptr);

  free(arena);
  VALK_PASS();
}

void test_malloc_allocator_api(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_allocator_t alloc = {.type = VALK_ALLOC_MALLOC};

  void *ptr = valk_mem_allocator_alloc(&alloc, 128);
  VALK_TEST_ASSERT(ptr != nullptr, "Malloc alloc should succeed");

  void *ptr2 = valk_mem_allocator_calloc(&alloc, 4, 32);
  VALK_TEST_ASSERT(ptr2 != nullptr, "Malloc calloc should succeed");

  void *ptr3 = valk_mem_allocator_realloc(&alloc, ptr, 256);
  VALK_TEST_ASSERT(ptr3 != nullptr, "Malloc realloc should succeed");

  valk_mem_allocator_free(&alloc, ptr3);
  valk_mem_allocator_free(&alloc, ptr2);

  VALK_PASS();
}

void test_gc_heap_allocator_api(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  void *ptr = valk_mem_allocator_alloc((valk_mem_allocator_t*)heap, 128);
  VALK_TEST_ASSERT(ptr != nullptr, "GC heap alloc should succeed");

  void *ptr2 = valk_mem_allocator_calloc((valk_mem_allocator_t*)heap, 4, 32);
  VALK_TEST_ASSERT(ptr2 != nullptr, "GC heap calloc should succeed");

  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

void test_region_create_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  valk_region_t *region = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  ASSERT_NOT_NULL(region);
  ASSERT_EQ(region->type, VALK_ALLOC_REGION);
  ASSERT_EQ(region->lifetime, VALK_LIFETIME_REQUEST);
  ASSERT_NOT_NULL(region->arena);
  ASSERT_TRUE(region->owns_arena);
  
  valk_region_destroy(region);
  
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_stats_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  valk_region_t *region = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  ASSERT_NOT_NULL(region);
  
  ASSERT_EQ(atomic_load(&region->stats.bytes_allocated), 0);
  ASSERT_EQ(atomic_load(&region->stats.alloc_count), 0);
  
  void *ptr1 = valk_region_alloc(region, 100);
  ASSERT_NOT_NULL(ptr1);
  ASSERT_EQ(atomic_load(&region->stats.bytes_allocated), 100);
  ASSERT_EQ(atomic_load(&region->stats.alloc_count), 1);
  
  void *ptr2 = valk_region_alloc(region, 200);
  ASSERT_NOT_NULL(ptr2);
  ASSERT_EQ(atomic_load(&region->stats.bytes_allocated), 300);
  ASSERT_EQ(atomic_load(&region->stats.alloc_count), 2);
  
  valk_region_stats_t stats;
  valk_region_get_stats(region, &stats);
  ASSERT_EQ(atomic_load(&stats.bytes_allocated), 300);
  ASSERT_EQ(atomic_load(&stats.alloc_count), 2);
  
  valk_region_destroy(region);
  
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_memory_limit(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  valk_region_t *parent = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *child = valk_region_create(VALK_LIFETIME_REQUEST, parent);
  ASSERT_NOT_NULL(child);
  
  bool set_ok = valk_region_set_limit(child, 500);
  ASSERT_TRUE(set_ok);
  ASSERT_EQ(child->stats.bytes_limit, 500);
  
  void *ptr1 = valk_region_alloc(child, 200);
  ASSERT_NOT_NULL(ptr1);
  ASSERT_EQ(atomic_load(&child->stats.bytes_allocated), 200);
  
  void *ptr2 = valk_region_alloc(child, 200);
  ASSERT_NOT_NULL(ptr2);
  ASSERT_EQ(atomic_load(&child->stats.bytes_allocated), 400);
  
  void *ptr3 = valk_region_alloc(child, 200);
  ASSERT_NOT_NULL(ptr3);
  ASSERT_EQ(atomic_load(&child->stats.overflow_count), 1);
  
  valk_region_destroy(child);
  valk_region_destroy(parent);
  
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_reset_preserves_limit(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  valk_region_t *region = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  ASSERT_NOT_NULL(region);
  
  valk_region_set_limit(region, 1000);
  
  valk_region_alloc(region, 100);
  ASSERT_EQ(atomic_load(&region->stats.bytes_allocated), 100);
  
  valk_region_reset(region);
  
  ASSERT_EQ(atomic_load(&region->stats.bytes_allocated), 0);
  ASSERT_EQ(atomic_load(&region->stats.alloc_count), 0);
  ASSERT_EQ(region->stats.bytes_limit, 1000);
  
  valk_region_destroy(region);
  
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_lifetime_reference_rules(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  // IMMORTAL (longest-lived, enum=0) can only reference IMMORTAL
  // because it lives forever and must not hold refs to shorter-lived objects
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_IMMORTAL, VALK_LIFETIME_IMMORTAL));
  ASSERT_FALSE(valk_lifetime_can_reference(VALK_LIFETIME_IMMORTAL, VALK_LIFETIME_SESSION));
  ASSERT_FALSE(valk_lifetime_can_reference(VALK_LIFETIME_IMMORTAL, VALK_LIFETIME_REQUEST));
  ASSERT_FALSE(valk_lifetime_can_reference(VALK_LIFETIME_IMMORTAL, VALK_LIFETIME_SCRATCH));
  
  // SESSION can reference IMMORTAL and SESSION
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_SESSION, VALK_LIFETIME_IMMORTAL));
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_SESSION, VALK_LIFETIME_SESSION));
  ASSERT_FALSE(valk_lifetime_can_reference(VALK_LIFETIME_SESSION, VALK_LIFETIME_REQUEST));
  ASSERT_FALSE(valk_lifetime_can_reference(VALK_LIFETIME_SESSION, VALK_LIFETIME_SCRATCH));
  
  // REQUEST can reference IMMORTAL, SESSION, REQUEST
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_REQUEST, VALK_LIFETIME_IMMORTAL));
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_REQUEST, VALK_LIFETIME_SESSION));
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_REQUEST, VALK_LIFETIME_REQUEST));
  ASSERT_FALSE(valk_lifetime_can_reference(VALK_LIFETIME_REQUEST, VALK_LIFETIME_SCRATCH));
  
  // SCRATCH (shortest-lived, enum=3) can reference anything
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_SCRATCH, VALK_LIFETIME_IMMORTAL));
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_SCRATCH, VALK_LIFETIME_SESSION));
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_SCRATCH, VALK_LIFETIME_REQUEST));
  ASSERT_TRUE(valk_lifetime_can_reference(VALK_LIFETIME_SCRATCH, VALK_LIFETIME_SCRATCH));
  
  VALK_PASS();
}

void test_allocator_lifetime_detection(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  valk_region_t *session_region = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request_region = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  
  ASSERT_EQ(valk_allocator_lifetime(session_region), VALK_LIFETIME_SESSION);
  ASSERT_EQ(valk_allocator_lifetime(request_region), VALK_LIFETIME_REQUEST);
  ASSERT_EQ(valk_allocator_lifetime(nullptr), VALK_LIFETIME_SCRATCH);
  ASSERT_EQ(valk_allocator_lifetime(&valk_malloc_allocator), VALK_LIFETIME_IMMORTAL);
  
  valk_region_destroy(request_region);
  valk_region_destroy(session_region);
  
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_write_barrier(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  valk_region_t *session = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  
  // REQUEST can safely reference SESSION (shorter-lived -> longer-lived)
  ASSERT_TRUE(valk_region_write_barrier(request, session, false));
  
  // SESSION cannot safely reference REQUEST (would create dangling pointer)
  ASSERT_FALSE(valk_region_write_barrier(session, request, false));
  
  // Same lifetime is always safe
  ASSERT_TRUE(valk_region_write_barrier(session, session, false));
  ASSERT_TRUE(valk_region_write_barrier(request, request, false));
  
  valk_region_destroy(request);
  valk_region_destroy(session);
  
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_promote_lval(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  valk_region_t *session = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request = valk_region_create(VALK_LIFETIME_REQUEST, session);
  
  VALK_WITH_ALLOC((valk_mem_allocator_t *)request) {
    valk_lval_t *num = valk_lval_num(42);
    ASSERT_NOT_NULL(num);
    ASSERT_LVAL_NUM(num, 42);
    
    valk_lval_t *promoted = valk_region_promote_lval(session, num);
    ASSERT_NOT_NULL(promoted);
    ASSERT_LVAL_NUM(promoted, 42);
    
    ASSERT_EQ(promoted->origin_allocator, session);
    ASSERT_GT(atomic_load(&session->stats.promotion_count), 0);
  }
  
  valk_region_destroy(request);
  valk_region_destroy(session);
  
  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_promote_lval_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *session = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request = valk_region_create(VALK_LIFETIME_REQUEST, session);

  VALK_WITH_ALLOC((valk_mem_allocator_t *)request) {
    valk_lval_t *str = valk_lval_str("hello world");
    ASSERT_NOT_NULL(str);

    valk_lval_t *promoted = valk_region_promote_lval(session, str);
    ASSERT_NOT_NULL(promoted);
    ASSERT_LVAL_STR(promoted, "hello world");
    ASSERT_EQ(promoted->origin_allocator, session);
  }

  valk_region_destroy(request);
  valk_region_destroy(session);

  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_promote_lval_symbol(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *session = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request = valk_region_create(VALK_LIFETIME_REQUEST, session);

  VALK_WITH_ALLOC((valk_mem_allocator_t *)request) {
    valk_lval_t *sym = valk_lval_sym("my-symbol");
    ASSERT_NOT_NULL(sym);

    valk_lval_t *promoted = valk_region_promote_lval(session, sym);
    ASSERT_NOT_NULL(promoted);
    ASSERT_EQ(LVAL_TYPE(promoted), LVAL_SYM);
    ASSERT_STR_CONTAINS(promoted->str, "my-symbol");
    ASSERT_EQ(promoted->origin_allocator, session);
  }

  valk_region_destroy(request);
  valk_region_destroy(session);

  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_promote_lval_cons(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *session = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request = valk_region_create(VALK_LIFETIME_REQUEST, session);

  VALK_WITH_ALLOC((valk_mem_allocator_t *)request) {
    valk_lval_t *list = valk_lval_cons(valk_lval_num(1),
                          valk_lval_cons(valk_lval_num(2), valk_lval_nil()));
    ASSERT_NOT_NULL(list);

    valk_lval_t *promoted = valk_region_promote_lval(session, list);
    ASSERT_NOT_NULL(promoted);
    ASSERT_EQ(LVAL_TYPE(promoted), LVAL_CONS);
    ASSERT_EQ(promoted->origin_allocator, session);

    valk_lval_t *head = promoted->cons.head;
    ASSERT_NOT_NULL(head);
    ASSERT_LVAL_NUM(head, 1);
  }

  valk_region_destroy(request);
  valk_region_destroy(session);

  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_promote_lval_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *session = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request = valk_region_create(VALK_LIFETIME_REQUEST, session);

  VALK_WITH_ALLOC((valk_mem_allocator_t *)request) {
    valk_lval_t *err = valk_lval_err("test error message");
    ASSERT_NOT_NULL(err);

    valk_lval_t *promoted = valk_region_promote_lval(session, err);
    ASSERT_NOT_NULL(promoted);
    ASSERT_EQ(LVAL_TYPE(promoted), LVAL_ERR);
    ASSERT_STR_CONTAINS(promoted->str, "test error message");
    ASSERT_EQ(promoted->origin_allocator, session);
  }

  valk_region_destroy(request);
  valk_region_destroy(session);

  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_promote_lval_lambda(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *session = valk_region_create(VALK_LIFETIME_SESSION, nullptr);
  valk_region_t *request = valk_region_create(VALK_LIFETIME_REQUEST, session);

  VALK_WITH_ALLOC((valk_mem_allocator_t *)request) {
    valk_lenv_t *env = valk_lenv_empty();
    valk_lval_t *formals = valk_lval_qcons(valk_lval_sym("x"), valk_lval_nil());
    valk_lval_t *body = valk_lval_cons(valk_lval_sym("+"), valk_lval_cons(valk_lval_sym("x"), valk_lval_cons(valk_lval_num(1), valk_lval_nil())));
    valk_lval_t *lambda = valk_lval_lambda(env, formals, body);
    ASSERT_NOT_NULL(lambda);
    ASSERT_EQ(LVAL_TYPE(lambda), LVAL_FUN);

    valk_lval_t *promoted = valk_region_promote_lval(session, lambda);
    ASSERT_NOT_NULL(promoted);
    ASSERT_EQ(LVAL_TYPE(promoted), LVAL_FUN);
    ASSERT_EQ(promoted->origin_allocator, session);
  }

  valk_region_destroy(request);
  valk_region_destroy(session);

  valk_runtime_shutdown();
  VALK_PASS();
}

void test_region_init_embedded(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);
  
  sz arena_size = sizeof(valk_mem_arena_t) + 4096;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);
  
  valk_region_t region;
  valk_region_init(&region, VALK_LIFETIME_REQUEST, nullptr, arena);
  
  ASSERT_EQ(region.type, VALK_ALLOC_REGION);
  ASSERT_EQ(region.lifetime, VALK_LIFETIME_REQUEST);
  ASSERT_EQ(region.arena, arena);
  ASSERT_FALSE(region.owns_arena);
  ASSERT_EQ(region.stats.bytes_allocated, 0);
  
  void *ptr = valk_region_alloc(&region, 100);
  ASSERT_NOT_NULL(ptr);
  ASSERT_EQ(region.stats.bytes_allocated, 100);
  
  free(arena);

  valk_runtime_shutdown();
  VALK_PASS();
}

// Test VALK_ALLOC_REGION string conversion (branch coverage for switch case)
void test_allocator_type_string_region(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char* s_region = valk_mem_allocator_e_to_string(VALK_ALLOC_REGION);
  VALK_TEST_ASSERT(s_region != nullptr, "Region alloc string should not be nullptr");
  VALK_TEST_ASSERT(strstr(s_region, "Region") != nullptr, "Region alloc string should contain 'Region'");

  VALK_PASS();
}

// Test region allocator API via valk_mem_allocator_* functions (for switch branch coverage)
void test_region_allocator_api(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *region = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  ASSERT_NOT_NULL(region);

  // Test alloc via allocator API
  void *ptr1 = valk_mem_allocator_alloc((valk_mem_allocator_t*)region, 64);
  ASSERT_NOT_NULL(ptr1);

  // Test calloc via allocator API
  void *ptr2 = valk_mem_allocator_calloc((valk_mem_allocator_t*)region, 4, 32);
  ASSERT_NOT_NULL(ptr2);

  // Verify calloc zeroed memory
  u8 *bytes = (u8*)ptr2;
  bool all_zero = true;
  for (int i = 0; i < 128 && all_zero; i++) {
    if (bytes[i] != 0) all_zero = false;
  }
  ASSERT_TRUE(all_zero);

  // Test realloc via allocator API - should do copy-alloc semantics for arena-backed regions
  memset(ptr1, 'X', 64);
  void *ptr3 = valk_mem_allocator_realloc((valk_mem_allocator_t*)region, ptr1, 128);
  ASSERT_NOT_NULL(ptr3);

  // Verify original data preserved in realloc
  bytes = (u8*)ptr3;
  bool preserved = true;
  for (int i = 0; i < 64 && preserved; i++) {
    if (bytes[i] != 'X') preserved = false;
  }
  ASSERT_TRUE(preserved);

  // Test free via allocator API - should be a no-op for regions
  valk_mem_allocator_free((valk_mem_allocator_t*)region, ptr1);

  valk_region_destroy(region);
  valk_runtime_shutdown();
  VALK_PASS();
}

// Test region realloc with nullptr pointer (covers realloc ptr==null branch)
void test_region_allocator_realloc_null_ptr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *region = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  ASSERT_NOT_NULL(region);

  // Test realloc with nullptr ptr - should behave like alloc
  void *ptr = valk_mem_allocator_realloc((valk_mem_allocator_t*)region, nullptr, 100);
  ASSERT_NOT_NULL(ptr);

  valk_region_destroy(region);
  valk_runtime_shutdown();
  VALK_PASS();
}

// Test region with gc_heap backing (non-arena path for realloc)
void test_region_gc_heap_realloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  // Create a region with gc_heap backing instead of arena
  valk_region_t region;
  memset(&region, 0, sizeof(region));
  region.type = VALK_ALLOC_REGION;
  region.lifetime = VALK_LIFETIME_SESSION;
  region.gc_heap = (struct valk_gc_heap2*)valk_gc_malloc_heap_init(0);
  region.arena = nullptr;
  region.owns_arena = false;

  // Test alloc via gc_heap path
  void *ptr1 = valk_region_alloc(&region, 64);
  ASSERT_NOT_NULL(ptr1);

  // Test realloc via gc_heap path
  memset(ptr1, 'Y', 64);
  void *ptr2 = valk_mem_allocator_realloc((valk_mem_allocator_t*)&region, ptr1, 128);
  ASSERT_NOT_NULL(ptr2);

  // Verify data preserved
  u8 *bytes = (u8*)ptr2;
  bool preserved = true;
  for (int i = 0; i < 64 && preserved; i++) {
    if (bytes[i] != 'Y') preserved = false;
  }
  ASSERT_TRUE(preserved);

  // Clean up gc_heap manually
  if (region.gc_heap) {
    valk_gc_malloc_heap_destroy((valk_gc_malloc_heap_t*)region.gc_heap);
  }

  valk_runtime_shutdown();
  VALK_PASS();
}

// Test bitmap delta with run length > 1 (covers run extension path)
void test_bitmap_delta_compute_runs(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create two bitmaps with consecutive differences
  valk_slab_bitmap_t prev = {0};
  valk_slab_bitmap_t curr = {0};

  prev.bytes = 8;
  curr.bytes = 8;
  prev.version = 1;
  curr.version = 2;
  prev.data = calloc(8, 1);
  curr.data = calloc(8, 1);
  ASSERT_NOT_NULL(prev.data);
  ASSERT_NOT_NULL(curr.data);

  // Set up consecutive bytes with same XOR pattern to trigger run extension
  prev.data[0] = 0x00;
  prev.data[1] = 0x00;
  prev.data[2] = 0x00;
  prev.data[3] = 0xFF;  // Different pattern here

  curr.data[0] = 0x0F;  // XOR = 0x0F
  curr.data[1] = 0x0F;  // XOR = 0x0F (same as prev, triggers run)
  curr.data[2] = 0x0F;  // XOR = 0x0F (extends run)
  curr.data[3] = 0xFF;  // No change

  valk_bitmap_delta_t delta;
  bool result = valk_bitmap_delta_compute(&curr, &prev, &delta);
  ASSERT_TRUE(result);

  // Should have one run with count >= 3
  ASSERT_TRUE(delta.run_count >= 1);
  if (delta.run_count > 0) {
    ASSERT_TRUE(delta.runs[0].count >= 1);
  }

  valk_bitmap_delta_free(&delta);
  free(prev.data);
  free(curr.data);
  VALK_PASS();
}

// Test RLE encoding with buffer too small (covers truncation path)
void test_bitmap_delta_to_rle_truncation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_bitmap_delta_t delta;
  valk_bitmap_delta_init(&delta);

  // Manually add some runs
  delta.runs = malloc(3 * sizeof(valk_bitmap_delta_run_t));
  ASSERT_NOT_NULL(delta.runs);
  delta.run_count = 3;
  delta.run_capacity = 3;

  delta.runs[0].offset = 0;
  delta.runs[0].count = 2;
  delta.runs[0].byte = 0xAB;

  delta.runs[1].offset = 10;
  delta.runs[1].count = 1;
  delta.runs[1].byte = 0xCD;

  delta.runs[2].offset = 20;
  delta.runs[2].count = 5;
  delta.runs[2].byte = 0xEF;

  // Test with very small buffer that will truncate
  char small_buf[10];
  sz len = valk_bitmap_delta_to_rle(&delta, small_buf, sizeof(small_buf));
  ASSERT_TRUE(len < sizeof(small_buf));
  ASSERT_TRUE(small_buf[len] == '\0');

  // Test with nullptr delta
  char buf[32];
  len = valk_bitmap_delta_to_rle(nullptr, buf, sizeof(buf));
  ASSERT_EQ(len, 0);

  // Test with buf_size too small
  len = valk_bitmap_delta_to_rle(&delta, buf, 2);
  ASSERT_EQ(len, 0);

  valk_bitmap_delta_free(&delta);
  VALK_PASS();
}

// Test chunked_ptrs with malloc-backed chunks
void test_chunked_ptrs_malloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chunked_ptrs_t ptrs;
  valk_chunked_ptrs_init(&ptrs);

  ASSERT_EQ(ptrs.count, 0);
  ASSERT_TRUE(ptrs.head == nullptr);

  // Push items without alloc_ctx (will use malloc)
  for (int i = 0; i < 10; i++) {
    bool ok = valk_chunked_ptrs_push(&ptrs, (void*)(uintptr_t)(i + 1), nullptr);
    ASSERT_TRUE(ok);
  }

  ASSERT_EQ(ptrs.count, 10);
  ASSERT_TRUE(ptrs.malloc_chunks);

  // Verify retrieval
  for (int i = 0; i < 10; i++) {
    void* item = valk_chunked_ptrs_get(&ptrs, i);
    ASSERT_EQ((uintptr_t)item, (uintptr_t)(i + 1));
  }

  // Test out of bounds
  void* oob = valk_chunked_ptrs_get(&ptrs, 100);
  ASSERT_TRUE(oob == nullptr);

  valk_chunked_ptrs_free(&ptrs);
  ASSERT_EQ(ptrs.count, 0);

  VALK_PASS();
}

// Test chunked_ptrs with region-backed allocation
void test_chunked_ptrs_region(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_runtime_config_t cfg = valk_runtime_config_default();
  valk_runtime_init(&cfg);

  valk_region_t *region = valk_region_create(VALK_LIFETIME_REQUEST, nullptr);
  ASSERT_NOT_NULL(region);

  valk_chunked_ptrs_t ptrs;
  valk_chunked_ptrs_init(&ptrs);

  // Push items with region allocation context
  for (int i = 0; i < 5; i++) {
    bool ok = valk_chunked_ptrs_push(&ptrs, (void*)(uintptr_t)(i + 100), region);
    ASSERT_TRUE(ok);
  }

  ASSERT_EQ(ptrs.count, 5);
  ASSERT_FALSE(ptrs.malloc_chunks);  // Using region, not malloc

  // Verify retrieval
  for (int i = 0; i < 5; i++) {
    void* item = valk_chunked_ptrs_get(&ptrs, i);
    ASSERT_EQ((uintptr_t)item, (uintptr_t)(i + 100));
  }

  // Free should be no-op since not malloc-backed
  valk_chunked_ptrs_free(&ptrs);

  valk_region_destroy(region);
  valk_runtime_shutdown();
  VALK_PASS();
}

// Test buffer_is_full edge case
void test_buffer_is_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_buffer_t buf;
  buf.capacity = 100;
  buf.count = 50;
  buf.items = nullptr;

  ASSERT_FALSE(valk_buffer_is_full(&buf));

  buf.count = 100;
  ASSERT_TRUE(valk_buffer_is_full(&buf));

  buf.count = 99;
  ASSERT_FALSE(valk_buffer_is_full(&buf));

  VALK_PASS();
}

// Test slab bitmap snapshot when no usage_bitmap exists
void test_slab_bitmap_snapshot_no_bitmap(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create slab manually with no bitmap
  valk_slab_t fake_slab;
  memset(&fake_slab, 0, sizeof(fake_slab));
  fake_slab.numItems = 10;
  fake_slab.usage_bitmap = nullptr;

  valk_slab_bitmap_t out;
  valk_slab_bitmap_snapshot(&fake_slab, &out);

  // Should return empty snapshot when no bitmap
  ASSERT_TRUE(out.data == nullptr);
  ASSERT_EQ(out.bytes, 0);
  ASSERT_EQ(out.version, 0);

  VALK_PASS();
}

// Test bitmap delta compute with mismatched sizes
void test_bitmap_delta_compute_size_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_bitmap_t prev = {0};
  valk_slab_bitmap_t curr = {0};

  prev.bytes = 8;
  curr.bytes = 16;  // Different size
  prev.data = calloc(8, 1);
  curr.data = calloc(16, 1);

  valk_bitmap_delta_t delta;
  bool result = valk_bitmap_delta_compute(&curr, &prev, &delta);

  // Should fail due to size mismatch
  ASSERT_FALSE(result);

  free(prev.data);
  free(curr.data);
  VALK_PASS();
}

// ============================================================================
// Coverage Gap Tests: gc_stats.c per-class usage loop
// ============================================================================

void test_gc_heap_print_stats_with_allocations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_heap2_create(1024 * 1024);
  ASSERT_NOT_NULL(heap);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.heap = heap;

  VALK_WITH_ALLOC((void *)heap) {
    for (int i = 0; i < 10; i++) {
      void *p = valk_gc_heap2_alloc(heap, 32);
      ASSERT_NOT_NULL(p);
    }
  }

  valk_gc_malloc_print_stats(heap);

  valk_thread_ctx = old_ctx;
  valk_gc_heap2_destroy(heap);
  VALK_PASS();
}

// ============================================================================
// Coverage Gap Tests: gc_heap.c large object realloc
// ============================================================================

void test_gc_heap_large_object_realloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_heap2_create(4 * 1024 * 1024);
  ASSERT_NOT_NULL(heap);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.heap = heap;

  void *large = valk_gc_heap2_alloc(heap, 64 * 1024);
  ASSERT_NOT_NULL(large);
  memset(large, 0xAB, 64 * 1024);

  void *resized = valk_gc_heap2_realloc(heap, large, 128 * 1024);
  ASSERT_NOT_NULL(resized);

  u8 *bytes = (u8 *)resized;
  ASSERT_EQ(bytes[0], 0xAB);
  ASSERT_EQ(bytes[1000], 0xAB);

  valk_thread_ctx = old_ctx;
  valk_gc_heap2_destroy(heap);
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

  // Slab bitmap and delta tests
  valk_testsuite_add_test(suite, "test_slab_bitmap_snapshot", test_slab_bitmap_snapshot);
  valk_testsuite_add_test(suite, "test_slab_bitmap_snapshot_null", test_slab_bitmap_snapshot_null);
  valk_testsuite_add_test(suite, "test_bitmap_delta_init_free", test_bitmap_delta_init_free);
  valk_testsuite_add_test(suite, "test_bitmap_delta_compute_basic", test_bitmap_delta_compute_basic);
  valk_testsuite_add_test(suite, "test_bitmap_delta_compute_null", test_bitmap_delta_compute_null);
  valk_testsuite_add_test(suite, "test_bitmap_delta_to_rle", test_bitmap_delta_to_rle);
  valk_testsuite_add_test(suite, "test_bitmap_delta_to_rle_edge_cases", test_bitmap_delta_to_rle_edge_cases);
  valk_testsuite_add_test(suite, "test_slab_bitmap_buckets", test_slab_bitmap_buckets);
  valk_testsuite_add_test(suite, "test_slab_bitmap_buckets_null", test_slab_bitmap_buckets_null);
  valk_testsuite_add_test(suite, "test_slab_bitmap_buckets_partial_range", test_slab_bitmap_buckets_partial_range);
  valk_testsuite_add_test(suite, "test_slab_peak_tracking", test_slab_peak_tracking);
  valk_testsuite_add_test(suite, "test_slab_free_null", test_slab_free_null);
  valk_testsuite_add_test(suite, "test_slab_bitmap_free_null", test_slab_bitmap_free_null);

  // Region API tests
  valk_testsuite_add_test(suite, "test_region_create_destroy", test_region_create_destroy);
  valk_testsuite_add_test(suite, "test_region_stats_tracking", test_region_stats_tracking);
  valk_testsuite_add_test(suite, "test_region_memory_limit", test_region_memory_limit);
  valk_testsuite_add_test(suite, "test_region_reset_preserves_limit", test_region_reset_preserves_limit);
  valk_testsuite_add_test(suite, "test_lifetime_reference_rules", test_lifetime_reference_rules);
  valk_testsuite_add_test(suite, "test_allocator_lifetime_detection", test_allocator_lifetime_detection);
  valk_testsuite_add_test(suite, "test_region_write_barrier", test_region_write_barrier);
  valk_testsuite_add_test(suite, "test_region_promote_lval", test_region_promote_lval);
  valk_testsuite_add_test(suite, "test_region_promote_lval_string", test_region_promote_lval_string);
  valk_testsuite_add_test(suite, "test_region_promote_lval_symbol", test_region_promote_lval_symbol);
  valk_testsuite_add_test(suite, "test_region_promote_lval_cons", test_region_promote_lval_cons);
  valk_testsuite_add_test(suite, "test_region_promote_lval_error", test_region_promote_lval_error);
  valk_testsuite_add_test(suite, "test_region_promote_lval_lambda", test_region_promote_lval_lambda);
  valk_testsuite_add_test(suite, "test_region_init_embedded", test_region_init_embedded);

  // Branch coverage improvement tests
  valk_testsuite_add_test(suite, "test_allocator_type_string_region", test_allocator_type_string_region);
  valk_testsuite_add_test(suite, "test_region_allocator_api", test_region_allocator_api);
  valk_testsuite_add_test(suite, "test_region_allocator_realloc_null_ptr", test_region_allocator_realloc_null_ptr);
  valk_testsuite_add_test(suite, "test_region_gc_heap_realloc", test_region_gc_heap_realloc);
  valk_testsuite_add_test(suite, "test_bitmap_delta_compute_runs", test_bitmap_delta_compute_runs);
  valk_testsuite_add_test(suite, "test_bitmap_delta_to_rle_truncation", test_bitmap_delta_to_rle_truncation);
  valk_testsuite_add_test(suite, "test_chunked_ptrs_malloc", test_chunked_ptrs_malloc);
  valk_testsuite_add_test(suite, "test_chunked_ptrs_region", test_chunked_ptrs_region);
  valk_testsuite_add_test(suite, "test_buffer_is_full", test_buffer_is_full);
  valk_testsuite_add_test(suite, "test_slab_bitmap_snapshot_no_bitmap", test_slab_bitmap_snapshot_no_bitmap);
  valk_testsuite_add_test(suite, "test_bitmap_delta_compute_size_mismatch", test_bitmap_delta_compute_size_mismatch);

  // Coverage gap tests
  valk_testsuite_add_test(suite, "test_gc_heap_print_stats_with_allocations", test_gc_heap_print_stats_with_allocations);
  valk_testsuite_add_test(suite, "test_gc_heap_large_object_realloc", test_gc_heap_large_object_realloc);

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
  test_box_t *myBoxes[numBoxes];
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
            (test_box_t *)valk_slab_aquire(params->slab)->data;
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
