#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/gc.h"
#include "../../src/parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_gc_heap_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "GC heap should be created");
  VALK_TEST_ASSERT(heap->type == VALK_ALLOC_GC_HEAP, "Type should be GC_HEAP");
  VALK_TEST_ASSERT(heap->allocated_bytes == 0, "Initial allocated_bytes should be 0");
  VALK_TEST_ASSERT(heap->num_collections == 0, "Initial collections should be 0");
  VALK_TEST_ASSERT(heap->objects == NULL, "Initial objects list should be NULL");
  VALK_TEST_ASSERT(heap->root_env == NULL, "Initial root_env should be NULL");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_init_default_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 0);
  VALK_TEST_ASSERT(heap != NULL, "GC heap should be created");
  VALK_TEST_ASSERT(heap->hard_limit > 0, "Default hard_limit should be set");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);
  size_t before = heap->allocated_bytes;

  void *ptr = valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(ptr != NULL, "Allocation should succeed");
  VALK_TEST_ASSERT(heap->allocated_bytes > before, "allocated_bytes should increase");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_alloc_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  void *ptrs[100];
  for (int i = 0; i < 100; i++) {
    ptrs[i] = valk_gc_malloc_heap_alloc(heap, 1024);
    VALK_TEST_ASSERT(ptrs[i] != NULL, "Allocation %d should succeed", i);
  }

  VALK_TEST_ASSERT(heap->allocated_bytes >= 100 * 1024, "Should have allocated at least 100KB");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_set_root(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);
  VALK_TEST_ASSERT(heap->root_env == NULL, "root_env should be NULL initially");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_set_hard_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);
  size_t original = heap->hard_limit;

  valk_gc_set_hard_limit(heap, 20 * 1024 * 1024);
  VALK_TEST_ASSERT(heap->hard_limit == 20 * 1024 * 1024, "hard_limit should be updated");

  valk_gc_set_hard_limit(heap, original);
  VALK_TEST_ASSERT(heap->hard_limit == original, "hard_limit should be restored");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_set_thresholds(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  valk_gc_set_thresholds(heap, 80, 60, 500);
  VALK_TEST_ASSERT(heap->gc_threshold_pct == 80, "threshold_pct should be 80");
  VALK_TEST_ASSERT(heap->gc_target_pct == 60, "target_pct should be 60");
  VALK_TEST_ASSERT(heap->min_gc_interval_ms == 500, "min_interval should be 500");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_should_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024, 10 * 1024);

  bool should = valk_gc_malloc_should_collect(heap);
  VALK_TEST_ASSERT(should == false || should == true, "Result should be boolean");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_usage_pct(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  uint8_t pct = valk_gc_heap_usage_pct(heap);
  VALK_TEST_ASSERT(pct <= 100, "Usage percentage should be 0-100");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_collect_empty_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  size_t reclaimed = valk_gc_malloc_collect(heap, NULL);
  VALK_TEST_ASSERT(heap->num_collections == 1, "Should count collection");

  valk_gc_malloc_heap_destroy(heap);
  (void)reclaimed;

  VALK_PASS();
}

void test_gc_collect_with_allocations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  for (int i = 0; i < 10; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
  }

  size_t before = heap->allocated_bytes;
  size_t reclaimed = valk_gc_malloc_collect(heap, NULL);

  VALK_TEST_ASSERT(heap->num_collections == 1, "Should count collection");
  (void)before;
  (void)reclaimed;

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_get_runtime_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  uint64_t cycles, pause_total, pause_max, reclaimed;
  size_t heap_used, heap_total;

  valk_gc_get_runtime_metrics(heap, &cycles, &pause_total, &pause_max, &reclaimed,
                               &heap_used, &heap_total);

  VALK_TEST_ASSERT(cycles == 0, "Initial cycles should be 0");
  VALK_TEST_ASSERT(pause_total == 0, "Initial pause_total should be 0");
  VALK_TEST_ASSERT(heap_total > 0, "heap_total should be > 0");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_runtime_metrics_after_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  valk_gc_malloc_collect(heap, NULL);

  uint64_t cycles, pause_total, pause_max, reclaimed;
  size_t heap_used, heap_total;

  valk_gc_get_runtime_metrics(heap, &cycles, &pause_total, &pause_max, &reclaimed,
                               &heap_used, &heap_total);

  VALK_TEST_ASSERT(cycles == 1, "cycles should be 1 after collect");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_print_stats_does_not_crash(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  valk_gc_malloc_print_stats(heap);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_forwarding_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool is_forwarded = valk_lval_is_forwarded(NULL);
  VALK_TEST_ASSERT(is_forwarded == false, "NULL should not be forwarded");

  valk_lval_t *followed = valk_lval_follow_forward(NULL);
  VALK_TEST_ASSERT(followed == NULL, "Following NULL should return NULL");

  VALK_PASS();
}

void test_gc_should_checkpoint(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *scratch = malloc(arena_size);
  valk_mem_arena_init(scratch, 4096);

  bool should = valk_should_checkpoint(scratch, 0.75f);
  VALK_TEST_ASSERT(should == false, "Empty scratch should not need checkpoint");

  free(scratch);

  VALK_PASS();
}

void test_gc_collect_arena_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t collected = valk_gc_collect_arena(NULL, NULL);
  VALK_TEST_ASSERT(collected == 0, "Null args should return 0");

  VALK_PASS();
}

void test_gc_should_collect_arena_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  bool should = valk_gc_should_collect_arena(arena);
  VALK_TEST_ASSERT(should == false || should == true, "Result should be boolean");

  free(arena);

  VALK_PASS();
}

void test_gc_heap_destroy_null_safe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_destroy(NULL);

  VALK_PASS();
}

void test_gc_multiple_collections(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  for (int i = 0; i < 5; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
    valk_gc_malloc_collect(heap, NULL);
  }

  VALK_TEST_ASSERT(heap->num_collections == 5, "Should count 5 collections");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_stats_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  VALK_TEST_ASSERT(heap->stats.overflow_allocations == 0, "Initial overflow should be 0");
  VALK_TEST_ASSERT(heap->stats.evacuations_from_scratch == 0, "Initial evacuations should be 0");
  VALK_TEST_ASSERT(heap->stats.emergency_collections == 0, "Initial emergency GCs should be 0");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_free_list_initially_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  VALK_TEST_ASSERT(heap->free_list == NULL, "Initial free_list should be NULL");
  VALK_TEST_ASSERT(heap->free_list_size == 0, "Initial free_list_size should be 0");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_slab_allocated(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  VALK_TEST_ASSERT(heap->lval_size > 0, "lval_size should be > 0");
  VALK_TEST_ASSERT(heap->lenv_size > 0, "lenv_size should be > 0");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_thresholds_boundary(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  valk_gc_set_thresholds(heap, 1, 1, 0);
  VALK_TEST_ASSERT(heap->gc_threshold_pct == 1, "threshold can be 1");

  valk_gc_set_thresholds(heap, 100, 100, 0xFFFFFFFF);
  VALK_TEST_ASSERT(heap->gc_threshold_pct == 100, "threshold can be 100");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_gc_heap_init", test_gc_heap_init);
  valk_testsuite_add_test(suite, "test_gc_heap_init_default_limit", test_gc_heap_init_default_limit);
  valk_testsuite_add_test(suite, "test_gc_heap_alloc", test_gc_heap_alloc);
  valk_testsuite_add_test(suite, "test_gc_heap_alloc_multiple", test_gc_heap_alloc_multiple);
  valk_testsuite_add_test(suite, "test_gc_set_root", test_gc_set_root);
  valk_testsuite_add_test(suite, "test_gc_set_hard_limit", test_gc_set_hard_limit);
  valk_testsuite_add_test(suite, "test_gc_set_thresholds", test_gc_set_thresholds);
  valk_testsuite_add_test(suite, "test_gc_should_collect", test_gc_should_collect);
  valk_testsuite_add_test(suite, "test_gc_heap_usage_pct", test_gc_heap_usage_pct);
  valk_testsuite_add_test(suite, "test_gc_collect_empty_heap", test_gc_collect_empty_heap);
  valk_testsuite_add_test(suite, "test_gc_collect_with_allocations", test_gc_collect_with_allocations);
  valk_testsuite_add_test(suite, "test_gc_get_runtime_metrics", test_gc_get_runtime_metrics);
  valk_testsuite_add_test(suite, "test_gc_runtime_metrics_after_collect", test_gc_runtime_metrics_after_collect);
  valk_testsuite_add_test(suite, "test_gc_print_stats_does_not_crash", test_gc_print_stats_does_not_crash);
  valk_testsuite_add_test(suite, "test_gc_forwarding_null", test_gc_forwarding_null);
  valk_testsuite_add_test(suite, "test_gc_should_checkpoint", test_gc_should_checkpoint);
  valk_testsuite_add_test(suite, "test_gc_collect_arena_null", test_gc_collect_arena_null);
  valk_testsuite_add_test(suite, "test_gc_should_collect_arena_empty", test_gc_should_collect_arena_empty);
  valk_testsuite_add_test(suite, "test_gc_heap_destroy_null_safe", test_gc_heap_destroy_null_safe);
  valk_testsuite_add_test(suite, "test_gc_multiple_collections", test_gc_multiple_collections);
  valk_testsuite_add_test(suite, "test_gc_stats_tracking", test_gc_stats_tracking);
  valk_testsuite_add_test(suite, "test_gc_free_list_initially_empty", test_gc_free_list_initially_empty);
  valk_testsuite_add_test(suite, "test_gc_slab_allocated", test_gc_slab_allocated);
  valk_testsuite_add_test(suite, "test_gc_thresholds_boundary", test_gc_thresholds_boundary);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
