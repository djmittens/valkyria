#include "testing.h"
#include "gc.h"
#include "parser.h"
#include "memory.h"
#include <stdio.h>
#include <unistd.h>

// Test that GC metrics initialize to zero
void test_gc_metrics_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  VALK_TEST_ASSERT(heap != nullptr, "Heap should be created");

  // Get metrics
  u64 cycles = 999;
  u64 pause_us_total = 999;
  u64 pause_us_max = 999;
  sz reclaimed = 999;
  sz heap_used = 999;
  sz heap_total = 999;

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
  VALK_TEST_ASSERT(heap_total > 0,
                   "heap_total should be positive (got %zu)",
                   heap_total);

  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that cycles increment after collection
void test_gc_metrics_after_collection(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;
  valk_gc_thread_register();

  // Create a simple environment
  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // Add some data
  valk_lenv_put(env, valk_lval_sym("x"), valk_lval_num(42));
  valk_lenv_put(env, valk_lval_sym("y"), valk_lval_num(100));

  // Run collection
  valk_gc_malloc_collect(heap, nullptr);

  // Get metrics
  u64 cycles = 0;
  valk_gc_get_runtime_metrics(heap, &cycles, nullptr, nullptr, nullptr, nullptr, nullptr);

  VALK_TEST_ASSERT(cycles == 1, "cycles should be 1 after first collection, got %llu",
                   (unsigned long long)cycles);

  // Run another collection
  valk_gc_malloc_collect(heap, nullptr);
  valk_gc_get_runtime_metrics(heap, &cycles, nullptr, nullptr, nullptr, nullptr, nullptr);

  VALK_TEST_ASSERT(cycles == 2, "cycles should be 2 after second collection, got %llu",
                   (unsigned long long)cycles);

  valk_gc_thread_unregister();
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that pause time is recorded
void test_gc_pause_time_recorded(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;
  valk_gc_thread_register();

  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);
  for (int i = 0; i < 100; i++) {
    char name[32];
    snprintf(name, sizeof(name), "var_%d", i);
    valk_lenv_put(env, valk_lval_sym(name), valk_lval_num(i));
  }

  // Run collection
  valk_gc_malloc_collect(heap, nullptr);

  // Get pause time metrics
  u64 pause_us_total = 0;
  u64 pause_us_max = 0;
  valk_gc_get_runtime_metrics(heap, nullptr, &pause_us_total, &pause_us_max,
                               nullptr, nullptr, nullptr);

  // Pause time should be greater than 0 (GC takes some time)
  VALK_TEST_ASSERT(pause_us_total > 0,
                   "pause_us_total should be > 0 after collection, got %llu",
                   (unsigned long long)pause_us_total);
  VALK_TEST_ASSERT(pause_us_max > 0,
                   "pause_us_max should be > 0 after collection, got %llu",
                   (unsigned long long)pause_us_max);
  VALK_TEST_ASSERT(pause_us_max == pause_us_total,
                   "pause_us_max should equal pause_us_total after first collection");

  valk_gc_thread_unregister();
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that reclaimed bytes are tracked
void test_gc_reclaimed_bytes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;
  valk_gc_thread_register();

  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);
  // Use non-lval size to avoid slab allocator (so bytes are tracked)
  for (int i = 0; i < 10; i++) {
    void* ptr = valk_gc_malloc_heap_alloc(heap, 1024);  // 1KB each
    VALK_TEST_ASSERT(ptr != nullptr, "Allocation should succeed");
    // Don't add to environment - these will be garbage
  }

  size_t allocated_before = valk_gc_heap2_used_bytes(heap);

  // Run collection - should reclaim the unreferenced allocations
  valk_gc_malloc_collect(heap, nullptr);

  size_t allocated_after = valk_gc_heap2_used_bytes(heap);

  // Get reclaimed bytes metric
  sz reclaimed = 0;
  valk_gc_get_runtime_metrics(heap, nullptr, nullptr, nullptr, &reclaimed, nullptr, nullptr);

  // Should have reclaimed some bytes
  VALK_TEST_ASSERT(reclaimed > 0, "reclaimed should be > 0, got %zu", reclaimed);
  VALK_TEST_ASSERT(allocated_after < allocated_before,
                   "allocated_bytes should decrease after GC");

  valk_gc_thread_unregister();
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test that max pause tracks worst case
void test_gc_max_pause_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (void*)heap;
  valk_thread_ctx.heap = heap;
  valk_gc_thread_register();

  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // First collection with minimal work
  valk_gc_malloc_collect(heap, nullptr);

  u64 pause_us_max_1 = 0;
  valk_gc_get_runtime_metrics(heap, nullptr, nullptr, &pause_us_max_1, nullptr, nullptr, nullptr);

  // Add lots of objects for second collection
  for (int i = 0; i < 1000; i++) {
    char name[32];
    snprintf(name, sizeof(name), "var_%d", i);
    valk_lenv_put(env, valk_lval_sym(name), valk_lval_num(i));
  }

  // Second collection with more work - might be slower
  valk_gc_malloc_collect(heap, nullptr);

  u64 pause_us_max_2 = 0;
  u64 pause_us_total = 0;
  valk_gc_get_runtime_metrics(heap, nullptr, &pause_us_total, &pause_us_max_2,
                               nullptr, nullptr, nullptr);

  // Max should be >= first pause
  VALK_TEST_ASSERT(pause_us_max_2 >= pause_us_max_1,
                   "pause_us_max should not decrease, was %llu now %llu",
                   (unsigned long long)pause_us_max_1,
                   (unsigned long long)pause_us_max_2);

  // Total should be sum of both pauses
  VALK_TEST_ASSERT(pause_us_total >= pause_us_max_2,
                   "pause_us_total should be >= pause_us_max");

  valk_gc_thread_unregister();
  valk_thread_ctx = old_ctx;
  valk_gc_malloc_heap_destroy(heap);
  VALK_PASS();
}

// Test nullptr heap handling
void test_gc_metrics_null_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 cycles = 999;
  u64 pause_us_total = 999;
  u64 pause_us_max = 999;
  sz reclaimed = 999;
  sz heap_used = 999;
  sz heap_total = 999;

  // Should not crash with nullptr heap
  valk_gc_get_runtime_metrics(nullptr, &cycles, &pause_us_total, &pause_us_max,
                               &reclaimed, &heap_used, &heap_total);

  // Values should be unchanged
  VALK_TEST_ASSERT(cycles == 999, "cycles should be unchanged with nullptr heap");
  VALK_TEST_ASSERT(pause_us_total == 999, "pause_us_total should be unchanged");

  VALK_PASS();
}

// Test nullptr output parameters
void test_gc_metrics_null_outputs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(0);

  // Should not crash with nullptr output parameters
  valk_gc_get_runtime_metrics(heap, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr);

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
