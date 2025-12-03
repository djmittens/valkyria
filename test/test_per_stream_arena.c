#include "testing.h"
#include "common.h"
#include "memory.h"
#include <stdio.h>
#include <string.h>

// Test 1: Arena isolation - allocations on one stream don't affect another
void test_stream_arena_isolation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(
      sizeof(valk_mem_arena_t) + 4096, 2);

  // Acquire two stream arenas
  valk_slab_item_t *item1 = valk_slab_aquire(slab);
  valk_slab_item_t *item2 = valk_slab_aquire(slab);

  VALK_TEST_ASSERT(item1 != NULL, "First arena item should be allocated");
  VALK_TEST_ASSERT(item2 != NULL, "Second arena item should be allocated");

  valk_mem_arena_t *arena1 = (valk_mem_arena_t *)item1->data;
  valk_mem_arena_t *arena2 = (valk_mem_arena_t *)item2->data;

  valk_mem_arena_init(arena1, 4096);
  valk_mem_arena_init(arena2, 4096);

  // Fill arena1 nearly full
  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena1) {
    void *p = valk_mem_alloc(3000);
    VALK_TEST_ASSERT(p != NULL, "Arena1 allocation should succeed");
  }

  // Arena2 should still have full capacity
  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena2) {
    void *p = valk_mem_alloc(3000);
    VALK_TEST_ASSERT(p != NULL, "Arena2 should have space independent of arena1");
  }

  // Release arena1, arena2 unaffected
  valk_slab_release(slab, item1);

  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena2) {
    void *p = valk_mem_alloc(500);
    VALK_TEST_ASSERT(p != NULL, "Arena2 should still work after arena1 released");
  }

  valk_slab_release(slab, item2);
  valk_slab_free(slab);
  VALK_PASS();
}

// Test 2: Arena reuse after release
void test_stream_arena_reuse(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(
      sizeof(valk_mem_arena_t) + 4096, 1);  // Only 1 arena

  // Acquire, use, release, reacquire
  valk_slab_item_t *item1 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item1 != NULL, "First acquire should succeed");

  valk_mem_arena_t *arena = (valk_mem_arena_t *)item1->data;
  valk_mem_arena_init(arena, 4096);

  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    void *p = valk_mem_alloc(3000);
    VALK_TEST_ASSERT(p != NULL, "Initial allocation should succeed");
  }
  VALK_TEST_ASSERT(arena->offset > 3000, "Arena should be partially used");

  valk_slab_release(slab, item1);

  // Reacquire - should get same slot
  valk_slab_item_t *item2 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item2 != NULL, "Reacquire should succeed");
  VALK_TEST_ASSERT(item1 == item2, "Should reuse same slab item");

  arena = (valk_mem_arena_t *)item2->data;
  valk_mem_arena_init(arena, 4096);  // Reinitialize

  // Should have full capacity again
  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    void *p = valk_mem_alloc(3500);
    VALK_TEST_ASSERT(p != NULL, "Reused arena should have full capacity");
  }

  valk_slab_release(slab, item2);
  valk_slab_free(slab);
  VALK_PASS();
}

// Test 3: Pool exhaustion handling
void test_stream_arena_exhaustion(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_slab_t *slab = valk_slab_new(
      sizeof(valk_mem_arena_t) + 1024, 2);

  valk_slab_item_t *item1 = valk_slab_aquire(slab);
  valk_slab_item_t *item2 = valk_slab_aquire(slab);
  valk_slab_item_t *item3 = valk_slab_aquire(slab);  // Should fail

  VALK_TEST_ASSERT(item1 != NULL, "First acquire should succeed");
  VALK_TEST_ASSERT(item2 != NULL, "Second acquire should succeed");
  VALK_TEST_ASSERT(item3 == NULL, "Third acquire should fail (pool exhausted)");

  // Release one, then acquire should work
  valk_slab_release(slab, item1);
  item3 = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item3 != NULL, "Acquire after release should succeed");

  valk_slab_release(slab, item2);
  valk_slab_release(slab, item3);
  valk_slab_free(slab);
  VALK_PASS();
}

// Test 4: Multiple arenas in sequence (simulating sequential requests)
void test_stream_arena_sequential(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Simulate HTTP/2 config: 64KB arenas, 16 in pool
  valk_slab_t *slab = valk_slab_new(
      sizeof(valk_mem_arena_t) + (64 * 1024), 16);

  // Process 100 sequential "requests", each acquiring and releasing an arena
  for (int i = 0; i < 100; i++) {
    valk_slab_item_t *item = valk_slab_aquire(slab);
    VALK_TEST_ASSERT(item != NULL, "Request %d: arena acquire should succeed", i);

    valk_mem_arena_t *arena = (valk_mem_arena_t *)item->data;
    valk_mem_arena_init(arena, 64 * 1024);

    // Simulate request processing - allocate some data
    VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
      char *data = valk_mem_alloc(1024);
      VALK_TEST_ASSERT(data != NULL, "Request %d: data allocation should succeed", i);
      memset(data, 'X', 1024);
    }

    // Release immediately (simulating stream close)
    valk_slab_release(slab, item);
  }

  // Slab should be fully available again
  VALK_TEST_ASSERT(slab->numFree == 16, "All arenas should be available after sequential processing");

  valk_slab_free(slab);
  VALK_PASS();
}

// Test 5: Concurrent streams (simulating multiple active HTTP/2 streams)
void test_stream_arena_concurrent(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Simulate 8 concurrent streams
  const int NUM_STREAMS = 8;
  valk_slab_t *slab = valk_slab_new(
      sizeof(valk_mem_arena_t) + (64 * 1024), NUM_STREAMS);

  valk_slab_item_t *items[NUM_STREAMS];
  valk_mem_arena_t *arenas[NUM_STREAMS];

  // Acquire all streams
  for (int i = 0; i < NUM_STREAMS; i++) {
    items[i] = valk_slab_aquire(slab);
    VALK_TEST_ASSERT(items[i] != NULL, "Stream %d arena should be acquired", i);
    arenas[i] = (valk_mem_arena_t *)items[i]->data;
    valk_mem_arena_init(arenas[i], 64 * 1024);
  }

  // All arenas should be used
  VALK_TEST_ASSERT(slab->numFree == 0, "All arenas should be in use");

  // Allocate data on each stream
  for (int i = 0; i < NUM_STREAMS; i++) {
    VALK_WITH_ALLOC((valk_mem_allocator_t*)arenas[i]) {
      char *data = valk_mem_alloc(4096);
      VALK_TEST_ASSERT(data != NULL, "Stream %d data allocation should succeed", i);
      // Mark the data with stream id to verify isolation
      memset(data, 'A' + i, 4096);
    }
  }

  // Release streams in reverse order (simulating different completion times)
  for (int i = NUM_STREAMS - 1; i >= 0; i--) {
    valk_slab_release(slab, items[i]);
  }

  VALK_TEST_ASSERT(slab->numFree == NUM_STREAMS, "All arenas should be released");

  valk_slab_free(slab);
  VALK_PASS();
}

// Test 6: Memory bounded after many acquire/release cycles
void test_stream_arena_no_memory_growth(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Simulate 10000 stream open/close cycles
  valk_slab_t *slab = valk_slab_new(
      sizeof(valk_mem_arena_t) + (64 * 1024), 16);

  for (int i = 0; i < 10000; i++) {
    valk_slab_item_t *item = valk_slab_aquire(slab);
    if (!item) {
      VALK_FAIL("Slab exhausted at iteration %d", i);
    }

    valk_mem_arena_t *arena = (valk_mem_arena_t *)item->data;
    valk_mem_arena_init(arena, 64 * 1024);

    // Allocate some data
    VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
      void *p = valk_mem_alloc(30000);
      VALK_TEST_ASSERT(p != NULL, "Iteration %d allocation should succeed", i);
    }

    // Release immediately
    valk_slab_release(slab, item);
  }

  // Verify slab is back to initial state
  VALK_TEST_ASSERT(slab->numFree == 16, "All arenas should be free after 10000 cycles");

  valk_slab_free(slab);
  VALK_PASS();
}

// Test 7: Arena size appropriate for typical HTTP request
void test_stream_arena_size_adequate(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Test with 64KB arena - should be enough for typical request
  const size_t ARENA_SIZE = 64 * 1024;
  valk_slab_t *slab = valk_slab_new(sizeof(valk_mem_arena_t) + ARENA_SIZE, 1);

  valk_slab_item_t *item = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(item != NULL, "Should acquire arena");

  valk_mem_arena_t *arena = (valk_mem_arena_t *)item->data;
  valk_mem_arena_init(arena, ARENA_SIZE);

  VALK_WITH_ALLOC((valk_mem_allocator_t*)arena) {
    // Simulate typical HTTP/2 request allocations:
    // - 4 pseudo-headers (~100 bytes each)
    // - 20 regular headers (~50 bytes each name/value)
    // - Request body (8KB)
    // - Lisp qexpr representation (couple KB)

    // Pseudo-headers
    for (int i = 0; i < 4; i++) {
      char *hdr = valk_mem_alloc(100);
      VALK_TEST_ASSERT(hdr != NULL, "Pseudo-header %d should allocate", i);
    }

    // Regular headers (20 x 2 strings)
    for (int i = 0; i < 20; i++) {
      char *name = valk_mem_alloc(50);
      char *value = valk_mem_alloc(50);
      VALK_TEST_ASSERT(name != NULL && value != NULL, "Header %d should allocate", i);
    }

    // Request body
    char *body = valk_mem_alloc(8192);
    VALK_TEST_ASSERT(body != NULL, "Request body should allocate");

    // Qexpr overhead
    char *qexpr = valk_mem_alloc(4096);
    VALK_TEST_ASSERT(qexpr != NULL, "Qexpr should allocate");

    // Response body
    char *response = valk_mem_alloc(16384);
    VALK_TEST_ASSERT(response != NULL, "Response body should allocate");
  }

  // Should still have room to spare
  VALK_TEST_ASSERT(arena->offset < arena->capacity,
                   "Arena should have room to spare for typical request");

  valk_slab_release(slab, item);
  valk_slab_free(slab);
  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_stream_arena_isolation", test_stream_arena_isolation);
  valk_testsuite_add_test(suite, "test_stream_arena_reuse", test_stream_arena_reuse);
  valk_testsuite_add_test(suite, "test_stream_arena_exhaustion", test_stream_arena_exhaustion);
  valk_testsuite_add_test(suite, "test_stream_arena_sequential", test_stream_arena_sequential);
  valk_testsuite_add_test(suite, "test_stream_arena_concurrent", test_stream_arena_concurrent);
  valk_testsuite_add_test(suite, "test_stream_arena_no_memory_growth", test_stream_arena_no_memory_growth);
  valk_testsuite_add_test(suite, "test_stream_arena_size_adequate", test_stream_arena_size_adequate);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
