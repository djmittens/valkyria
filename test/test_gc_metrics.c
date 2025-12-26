#include "testing.h"
#include "gc.h"
#include "parser.h"
#include "memory.h"
#include <stdio.h>
#include <unistd.h>

// Test that GC metrics initialize to zero
void test_gc_metrics_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t threshold = 1024 * 1024;  // 1 MB
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");

  // Get metrics
  uint64_t cycles = 999;
  uint64_t pause_us_total = 999;
  uint64_t pause_us_max = 999;
  uint64_t reclaimed = 999;
  size_t heap_used = 999;
  size_t heap_total = 999;

  valk_gc_get_runtime_metrics(heap, &cycles, &pause_us_total, &pause_us_max,
                               &reclaimed, &heap_used, &heap_total);

  // Verify initial values
  VALK_TEST_ASSERT(cycles == 0, "Initial cycles should be 0, got %llu",
                   (unsigned long long)cycles);
  VALK_TEST_ASSERT(pause_us_total == 0, "Initial pause_us_total should be 0, got %llu",
                   (unsigned long long)pause_us_total);
  VALK_TEST_ASSERT(pause_us_max == 0, "Initial pause_us_max should be 0, got %llu",
                   (unsigned long long)pause_us_max);
  VALK_TEST_ASSERT(reclaimed == 0, "Initial reclaimed should be 0, got %llu",
                   (unsigned long long)reclaimed);
  // heap_total now includes slab capacity (256K objects * ~80 bytes each) + malloc hard_limit
  // The slab adds about 256MB capacity, malloc limit is threshold * 2 (default when hard_limit=0)
  size_t expected_malloc_limit = threshold * 2;  // Default hard_limit = 2x threshold
  VALK_TEST_ASSERT(heap_total > expected_malloc_limit,
                   "heap_total should include slab capacity (got %zu, expected > %zu)",
                   heap_total, expected_malloc_limit);

  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that cycles increment after collection
void test_gc_metrics_after_collection(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  // Set up thread context
  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;

  // Create a simple environment
  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // Add some data
  valk_lenv_put(env, valk_lval_sym("x"), valk_lval_num(42));
  valk_lenv_put(env, valk_lval_sym("y"), valk_lval_num(100));

  // Run collection
  valk_gc_malloc_collect(heap, NULL);

  // Get metrics
  uint64_t cycles = 0;
  valk_gc_get_runtime_metrics(heap, &cycles, NULL, NULL, NULL, NULL, NULL);

  VALK_TEST_ASSERT(cycles == 1, "cycles should be 1 after first collection, got %llu",
                   (unsigned long long)cycles);

  // Run another collection
  valk_gc_malloc_collect(heap, NULL);
  valk_gc_get_runtime_metrics(heap, &cycles, NULL, NULL, NULL, NULL, NULL);

  VALK_TEST_ASSERT(cycles == 2, "cycles should be 2 after second collection, got %llu",
                   (unsigned long long)cycles);

  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that pause time is recorded
void test_gc_pause_time_recorded(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;

  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // Add some data to make GC do work
  for (int i = 0; i < 100; i++) {
    char name[32];
    snprintf(name, sizeof(name), "var_%d", i);
    valk_lenv_put(env, valk_lval_sym(name), valk_lval_num(i));
  }

  // Run collection
  valk_gc_malloc_collect(heap, NULL);

  // Get pause time metrics
  uint64_t pause_us_total = 0;
  uint64_t pause_us_max = 0;
  valk_gc_get_runtime_metrics(heap, NULL, &pause_us_total, &pause_us_max,
                               NULL, NULL, NULL);

  // Pause time should be greater than 0 (GC takes some time)
  VALK_TEST_ASSERT(pause_us_total > 0,
                   "pause_us_total should be > 0 after collection, got %llu",
                   (unsigned long long)pause_us_total);
  VALK_TEST_ASSERT(pause_us_max > 0,
                   "pause_us_max should be > 0 after collection, got %llu",
                   (unsigned long long)pause_us_max);
  VALK_TEST_ASSERT(pause_us_max == pause_us_total,
                   "pause_us_max should equal pause_us_total after first collection");

  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that reclaimed bytes are tracked
void test_gc_reclaimed_bytes(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;

  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // Allocate objects that will become garbage
  // Use non-lval size to avoid slab allocator (so bytes are tracked)
  for (int i = 0; i < 10; i++) {
    void* ptr = valk_gc_malloc_heap_alloc(heap, 1024);  // 1KB each
    VALK_TEST_ASSERT(ptr != NULL, "Allocation should succeed");
    // Don't add to environment - these will be garbage
  }

  size_t allocated_before = heap->allocated_bytes;

  // Run collection - should reclaim the unreferenced allocations
  valk_gc_malloc_collect(heap, NULL);

  size_t allocated_after = heap->allocated_bytes;

  // Get reclaimed bytes metric
  uint64_t reclaimed = 0;
  valk_gc_get_runtime_metrics(heap, NULL, NULL, NULL, &reclaimed, NULL, NULL);

  // Should have reclaimed some bytes
  VALK_TEST_ASSERT(reclaimed > 0, "reclaimed should be > 0, got %llu",
                   (unsigned long long)reclaimed);
  VALK_TEST_ASSERT(allocated_after < allocated_before,
                   "allocated_bytes should decrease after GC");

  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that max pause tracks worst case
void test_gc_max_pause_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t threshold = 16 * 1024 * 1024;  // 16 MB
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;

  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // First collection with minimal work
  valk_gc_malloc_collect(heap, NULL);

  uint64_t pause_us_max_1 = 0;
  valk_gc_get_runtime_metrics(heap, NULL, NULL, &pause_us_max_1, NULL, NULL, NULL);

  // Add lots of objects for second collection
  for (int i = 0; i < 1000; i++) {
    char name[32];
    snprintf(name, sizeof(name), "var_%d", i);
    valk_lenv_put(env, valk_lval_sym(name), valk_lval_num(i));
  }

  // Second collection with more work - might be slower
  valk_gc_malloc_collect(heap, NULL);

  uint64_t pause_us_max_2 = 0;
  uint64_t pause_us_total = 0;
  valk_gc_get_runtime_metrics(heap, NULL, &pause_us_total, &pause_us_max_2,
                               NULL, NULL, NULL);

  // Max should be >= first pause
  VALK_TEST_ASSERT(pause_us_max_2 >= pause_us_max_1,
                   "pause_us_max should not decrease, was %llu now %llu",
                   (unsigned long long)pause_us_max_1,
                   (unsigned long long)pause_us_max_2);

  // Total should be sum of both pauses
  VALK_TEST_ASSERT(pause_us_total >= pause_us_max_2,
                   "pause_us_total should be >= pause_us_max");

  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test NULL heap handling
void test_gc_metrics_null_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  uint64_t cycles = 999;
  uint64_t pause_us_total = 999;
  uint64_t pause_us_max = 999;
  uint64_t reclaimed = 999;
  size_t heap_used = 999;
  size_t heap_total = 999;

  // Should not crash with NULL heap
  valk_gc_get_runtime_metrics(NULL, &cycles, &pause_us_total, &pause_us_max,
                               &reclaimed, &heap_used, &heap_total);

  // Values should be unchanged
  VALK_TEST_ASSERT(cycles == 999, "cycles should be unchanged with NULL heap");
  VALK_TEST_ASSERT(pause_us_total == 999, "pause_us_total should be unchanged");

  VALK_PASS();
}

// Test NULL output parameters
void test_gc_metrics_null_outputs(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t threshold = 1024 * 1024;
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  // Should not crash with NULL output parameters
  valk_gc_get_runtime_metrics(heap, NULL, NULL, NULL, NULL, NULL, NULL);

  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

int main(int argc, const char** argv) {
  (void)argc;
  (void)argv;

  // Initialize memory subsystem
  valk_mem_init_malloc();

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_gc_metrics_init", test_gc_metrics_init);
  valk_testsuite_add_test(suite, "test_gc_metrics_after_collection",
                          test_gc_metrics_after_collection);
  valk_testsuite_add_test(suite, "test_gc_pause_time_recorded",
                          test_gc_pause_time_recorded);
  valk_testsuite_add_test(suite, "test_gc_reclaimed_bytes",
                          test_gc_reclaimed_bytes);
  valk_testsuite_add_test(suite, "test_gc_max_pause_tracking",
                          test_gc_max_pause_tracking);
  valk_testsuite_add_test(suite, "test_gc_metrics_null_heap",
                          test_gc_metrics_null_heap);
  valk_testsuite_add_test(suite, "test_gc_metrics_null_outputs",
                          test_gc_metrics_null_outputs);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
