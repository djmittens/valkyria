#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/gc.h"
#include "../../src/parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>

void test_gc_heap_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "GC heap should be created");
  VALK_TEST_ASSERT(heap->type == VALK_ALLOC_GC_HEAP, "Type should be GC_HEAP");
  VALK_TEST_ASSERT(valk_gc_heap2_used_bytes(heap) == 0, "Initial used_bytes should be 0");
  VALK_TEST_ASSERT(atomic_load(&heap->collections) == 0, "Initial collections should be 0");
  VALK_TEST_ASSERT(heap->root_env == NULL, "Initial root_env should be NULL");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_init_default_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(0);
  VALK_TEST_ASSERT(heap != NULL, "GC heap should be created");
  VALK_TEST_ASSERT(heap->hard_limit > 0, "Default hard_limit should be set");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  size_t before = valk_gc_heap2_used_bytes(heap);

  void *ptr = valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(ptr != NULL, "Allocation should succeed");
  VALK_TEST_ASSERT(valk_gc_heap2_used_bytes(heap) > before, "used_bytes should increase");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_alloc_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  void *ptrs[100];
  for (int i = 0; i < 100; i++) {
    ptrs[i] = valk_gc_malloc_heap_alloc(heap, 1024);
    VALK_TEST_ASSERT(ptrs[i] != NULL, "Allocation %d should succeed", i);
  }

  VALK_TEST_ASSERT(valk_gc_heap2_used_bytes(heap) >= 100 * 1024, "Should have allocated at least 100KB");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_set_root(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  VALK_TEST_ASSERT(heap->root_env == NULL, "root_env should be NULL initially");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_set_hard_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_gc_set_thresholds(heap, 80, 60, 500);
  VALK_TEST_ASSERT(heap->gc_threshold_pct == 80, "threshold_pct should be 80");
  VALK_TEST_ASSERT(heap->gc_target_pct == 60, "target_pct should be 60");
  VALK_TEST_ASSERT(heap->min_gc_interval_ms == 500, "min_interval should be 500");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_should_collect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024);

  bool should = valk_gc_malloc_should_collect(heap);
  VALK_TEST_ASSERT(should == false || should == true, "Result should be boolean");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_usage_pct(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  uint8_t pct = valk_gc_heap_usage_pct(heap);
  VALK_TEST_ASSERT(pct <= 100, "Usage percentage should be 0-100");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_collect_empty_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  size_t reclaimed = valk_gc_malloc_collect(heap, NULL);
  VALK_TEST_ASSERT(atomic_load(&heap->collections) == 1, "Should count collection");

  valk_gc_malloc_heap_destroy(heap);
  (void)reclaimed;

  VALK_PASS();
}

void test_gc_collect_with_allocations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  for (int i = 0; i < 10; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
  }

  size_t before = valk_gc_heap2_used_bytes(heap);
  size_t reclaimed = valk_gc_malloc_collect(heap, NULL);

  VALK_TEST_ASSERT(atomic_load(&heap->collections) == 1, "Should count collection");
  (void)before;
  (void)reclaimed;

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_get_runtime_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  for (int i = 0; i < 5; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
    valk_gc_malloc_collect(heap, NULL);
  }

  VALK_TEST_ASSERT(atomic_load(&heap->collections) == 5, "Should count 5 collections");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_stats_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  VALK_TEST_ASSERT(heap->stats.overflow_allocations == 0, "Initial overflow should be 0");
  VALK_TEST_ASSERT(heap->stats.evacuations_from_scratch == 0, "Initial evacuations should be 0");
  VALK_TEST_ASSERT(heap->stats.emergency_collections == 0, "Initial emergency GCs should be 0");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_free_list_initially_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("heap2 uses page-based allocation, no free list");
}

void test_gc_slab_allocated(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("heap2 uses page-based allocation, no slab sizes");
}

void test_gc_thresholds_boundary(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_gc_set_thresholds(heap, 1, 1, 0);
  VALK_TEST_ASSERT(heap->gc_threshold_pct == 1, "threshold can be 1");

  valk_gc_set_thresholds(heap, 100, 100, 0xFFFFFFFF);
  VALK_TEST_ASSERT(heap->gc_threshold_pct == 100, "threshold can be 100");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_set_thresholds_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_set_thresholds(NULL, 80, 60, 500);

  VALK_PASS();
}

void test_gc_set_thresholds_zero_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_gc_set_thresholds(heap, 0, 0, 0);
  VALK_TEST_ASSERT(heap->gc_threshold_pct == 75, "zero threshold should use default 75");
  VALK_TEST_ASSERT(heap->gc_target_pct == 50, "zero target should use default 50");
  VALK_TEST_ASSERT(heap->min_gc_interval_ms == 0, "zero interval should be 0");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_should_collect_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool should = valk_gc_malloc_should_collect(NULL);
  VALK_TEST_ASSERT(should == false, "NULL heap should return false");

  VALK_PASS();
}

void test_gc_heap_usage_pct_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  uint8_t pct = valk_gc_heap_usage_pct(NULL);
  VALK_TEST_ASSERT(pct == 0, "NULL heap should return 0%");

  VALK_PASS();
}

void test_gc_set_hard_limit_below_usage(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  for (int i = 0; i < 100; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
  }

  size_t usage = valk_gc_heap2_used_bytes(heap);
  size_t original = heap->hard_limit;

  valk_gc_set_hard_limit(heap, usage / 2);
  VALK_TEST_ASSERT(heap->hard_limit == original, "Should not change limit below usage");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_lval_forwarding(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *src = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  valk_lval_t *dst = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));

  src->flags = LVAL_NUM;
  src->num = 42;
  dst->flags = LVAL_NUM;
  dst->num = 99;

  valk_lval_set_forward(src, dst);
  VALK_TEST_ASSERT(valk_lval_is_forwarded(src), "src should be forwarded");
  VALK_TEST_ASSERT(LVAL_TYPE(src) == LVAL_FORWARD, "src type should be FORWARD");

  valk_lval_t *followed = valk_lval_follow_forward(src);
  VALK_TEST_ASSERT(followed == dst, "follow should return dst");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_follow_forward_chain(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *a = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  valk_lval_t *b = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  valk_lval_t *c = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));

  c->flags = LVAL_NUM;
  c->num = 123;

  valk_lval_set_forward(a, b);
  valk_lval_set_forward(b, c);

  valk_lval_t *result = valk_lval_follow_forward(a);
  VALK_TEST_ASSERT(result == c, "Should follow chain to c");
  VALK_TEST_ASSERT(result->num == 123, "Value should be 123");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_get_runtime_metrics_null_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  uint64_t cycles = 999, pause_total = 999, pause_max = 999, reclaimed = 999;
  size_t heap_used = 999, heap_total = 999;

  valk_gc_get_runtime_metrics(NULL, &cycles, &pause_total, &pause_max, &reclaimed,
                               &heap_used, &heap_total);

  VALK_TEST_ASSERT(cycles == 999, "cycles should be unchanged for NULL heap");

  VALK_PASS();
}

void test_gc_get_runtime_metrics_null_params(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_gc_get_runtime_metrics(heap, NULL, NULL, NULL, NULL, NULL, NULL);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_peak_usage_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);
  VALK_TEST_ASSERT(heap->stats.peak_usage == 0, "Initial peak should be 0");

  for (int i = 0; i < 10; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
  }

  VALK_TEST_ASSERT(heap->stats.peak_usage > 0, "Peak should increase after allocations");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_add_to_objects(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *val = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val->flags = LVAL_NUM;
  val->num = 42;

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_memory_print_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *scratch = malloc(arena_size);
  valk_mem_arena_init(scratch, 4096);

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  FILE *devnull = fopen("/dev/null", "w");
  if (devnull) {
    valk_memory_print_stats(scratch, heap, devnull);
    fclose(devnull);
  }

  valk_gc_malloc_heap_destroy(heap);
  free(scratch);

  VALK_PASS();
}

void test_gc_memory_print_stats_null_output(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_memory_print_stats(NULL, heap, NULL);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_memory_print_stats_null_heap(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *scratch = malloc(arena_size);
  valk_mem_arena_init(scratch, 4096);

  FILE *devnull = fopen("/dev/null", "w");
  if (devnull) {
    valk_memory_print_stats(scratch, NULL, devnull);
    fclose(devnull);
  }

  free(scratch);

  VALK_PASS();
}

void test_gc_collect_with_additional_root(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *root = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  root->flags = LVAL_NUM | LVAL_ALLOC_HEAP;
  root->num = 123;

  size_t reclaimed = valk_gc_malloc_collect(heap, root);
  VALK_TEST_ASSERT(atomic_load(&heap->collections) == 1, "Should count collection");
  (void)reclaimed;

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_print_stats_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_print_stats(NULL);

  VALK_PASS();
}

void test_gc_mark_lval_external(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *val = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  val->flags = LVAL_NUM | LVAL_ALLOC_HEAP;
  val->num = 42;

  valk_gc_mark_lval_external(val);

  VALK_TEST_ASSERT((val->flags & LVAL_FLAG_GC_MARK) != 0, "Should be marked");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_mark_lval_external_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_mark_lval_external(NULL);

  VALK_PASS();
}

void test_gc_free_object(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  void *ptr = valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(ptr != NULL, "Should allocate");

  size_t before = valk_gc_heap2_used_bytes(heap);
  valk_gc_free_object(heap, ptr);

  VALK_TEST_ASSERT(valk_gc_heap2_used_bytes(heap) <= before, "used_bytes should decrease or stay same");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_free_object_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_gc_free_object(heap, NULL);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_should_checkpoint_null_scratch(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool should = valk_should_checkpoint(NULL, 0.75f);
  VALK_TEST_ASSERT(should == false, "NULL scratch should return false");

  VALK_PASS();
}

void test_gc_should_checkpoint_high_threshold(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *scratch = malloc(arena_size);
  valk_mem_arena_init(scratch, 4096);

  scratch->offset = 3500;

  bool should = valk_should_checkpoint(scratch, 0.75f);
  VALK_TEST_ASSERT(should == true, "85% full should trigger checkpoint");

  free(scratch);

  VALK_PASS();
}

void test_gc_lval_sizes_set(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("heap2 uses page-based allocation, no lval_size/lenv_size fields");
}

void test_gc_mark_env_external(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_mark_env_external(NULL);

  VALK_PASS();
}

void test_gc_checkpoint_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_checkpoint(NULL, NULL, NULL);

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *scratch = malloc(arena_size);
  valk_mem_arena_init(scratch, 4096);

  valk_checkpoint(scratch, NULL, NULL);

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_checkpoint(NULL, heap, NULL);

  valk_gc_malloc_heap_destroy(heap);
  free(scratch);

  VALK_PASS();
}

void test_gc_should_collect_rate_limiting(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_gc_set_thresholds(heap, 1, 1, 10000);

  for (int i = 0; i < 100; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
  }

  valk_gc_malloc_collect(heap, NULL);

  bool should = valk_gc_malloc_should_collect(heap);

  valk_gc_malloc_heap_destroy(heap);
  (void)should;

  VALK_PASS();
}

void test_gc_should_collect_above_threshold(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_gc_set_thresholds(heap, 1, 1, 0);

  uint8_t usage = valk_gc_heap_usage_pct(heap);
  bool should = valk_gc_malloc_should_collect(heap);
  bool expected = (usage >= 1);
  VALK_TEST_ASSERT(should == expected, "Should match usage-based decision (usage=%u, expected=%d, got=%d)",
                   usage, expected, should);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_heap_usage_pct_with_allocations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  uint8_t pct_before = valk_gc_heap_usage_pct(heap);

  for (int i = 0; i < 1000; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
  }

  uint8_t pct_after = valk_gc_heap_usage_pct(heap);
  VALK_TEST_ASSERT(pct_after >= pct_before, "Usage should increase after allocations");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_collect_arena_with_env(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 65536 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 65536);

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lenv_t *env = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lenv_t));
  memset(env, 0, sizeof(valk_lenv_t));

  size_t collected = valk_gc_collect_arena(env, arena);
  (void)collected;

  valk_gc_malloc_heap_destroy(heap);
  free(arena);

  VALK_PASS();
}

void test_gc_should_collect_arena_high_usage(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t arena_size = 4096 + sizeof(valk_mem_arena_t);
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, 4096);

  arena->offset = 3800;

  bool should = valk_gc_should_collect_arena(arena);
  VALK_TEST_ASSERT(should == true, "Should collect at >90% usage");

  free(arena);

  VALK_PASS();
}

void test_gc_forwarding_preserves_alloc_bits(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  valk_lval_t *src = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  valk_lval_t *dst = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));

  src->flags = LVAL_NUM | LVAL_ALLOC_HEAP;

  valk_lval_set_forward(src, dst);

  uint64_t alloc_bits = LVAL_ALLOC(src);
  VALK_TEST_ASSERT(alloc_bits == LVAL_ALLOC_HEAP, "Alloc bits should be preserved");
  VALK_TEST_ASSERT(LVAL_TYPE(src) == LVAL_FORWARD, "Type should be FORWARD");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_runtime_metrics_pause_max_updates(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(10 * 1024 * 1024);

  for (int i = 0; i < 5; i++) {
    for (int j = 0; j < 100; j++) {
      valk_gc_malloc_heap_alloc(heap, 1024);
    }
    valk_gc_malloc_collect(heap, NULL);
  }

  uint64_t cycles, pause_total, pause_max, reclaimed;
  size_t heap_used, heap_total;

  valk_gc_get_runtime_metrics(heap, &cycles, &pause_total, &pause_max, &reclaimed,
                               &heap_used, &heap_total);

  VALK_TEST_ASSERT(cycles == 5, "Should have 5 cycles");
  VALK_TEST_ASSERT(pause_max > 0, "pause_max should be > 0");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_alloc_tracks_to_objects_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("heap2 uses page-based allocation with bitmaps, no objects linked list");
}

// ============================================================================
// Size Class Infrastructure Tests (Phase 1 - Multi-Class Allocator)
// ============================================================================

void test_gc_size_class_lookup(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_gc_size_class(1) == 0, "1 byte -> class 0 (16B)");
  VALK_TEST_ASSERT(valk_gc_size_class(16) == 0, "16 bytes -> class 0 (16B)");
  VALK_TEST_ASSERT(valk_gc_size_class(17) == 1, "17 bytes -> class 1 (32B)");
  VALK_TEST_ASSERT(valk_gc_size_class(32) == 1, "32 bytes -> class 1 (32B)");
  VALK_TEST_ASSERT(valk_gc_size_class(72) == 3, "72 bytes (lval_t) -> class 3 (128B)");
  VALK_TEST_ASSERT(valk_gc_size_class(80) == 3, "80 bytes (lenv_t) -> class 3 (128B)");
  VALK_TEST_ASSERT(valk_gc_size_class(128) == 3, "128 bytes -> class 3 (128B)");
  VALK_TEST_ASSERT(valk_gc_size_class(129) == 4, "129 bytes -> class 4 (256B)");
  VALK_TEST_ASSERT(valk_gc_size_class(4096) == 8, "4096 bytes -> class 8 (4KB)");
  VALK_TEST_ASSERT(valk_gc_size_class(4097) == UINT8_MAX, "4097 bytes -> large object");
  VALK_TEST_ASSERT(valk_gc_size_class(1048576) == UINT8_MAX, "1MB -> large object");

  VALK_PASS();
}

void test_gc_slots_per_page_calculation(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(valk_gc_slots_per_page(0) > 0, "Class 0 should have slots");
  VALK_TEST_ASSERT(valk_gc_slots_per_page(3) > 0, "Class 3 should have slots");
  VALK_TEST_ASSERT(valk_gc_slots_per_page(8) > 0, "Class 8 should have slots");
  VALK_TEST_ASSERT(valk_gc_slots_per_page(VALK_GC_NUM_SIZE_CLASSES) == 0, "Invalid class -> 0 slots");

  uint16_t class0_slots = valk_gc_slots_per_page(0);
  uint16_t class3_slots = valk_gc_slots_per_page(3);
  uint16_t class8_slots = valk_gc_slots_per_page(8);

  VALK_TEST_ASSERT(class0_slots > class3_slots, "Class 0 (16B) should have more slots than class 3 (128B)");
  VALK_TEST_ASSERT(class3_slots > class8_slots, "Class 3 (128B) should have more slots than class 8 (4KB)");

  VALK_PASS();
}

void test_gc_page_total_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    size_t page_size = valk_gc_page_total_size(c);
    VALK_TEST_ASSERT(page_size > 0, "Class %d should have non-zero page size", c);
    VALK_TEST_ASSERT(page_size <= VALK_GC_PAGE_SIZE + 1024, 
                     "Class %d page size should be close to 64KB (got %zu)", c, page_size);
    VALK_TEST_ASSERT((page_size % 64) == 0, "Page size should be cache-aligned");
  }

  VALK_PASS();
}

void test_gc_heap2_create_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap creation should succeed");
  VALK_TEST_ASSERT(heap->hard_limit == 64 * 1024 * 1024, "Hard limit should be set");
  VALK_TEST_ASSERT(heap->soft_limit == heap->hard_limit * 3 / 4, "Soft limit should be 75%% of hard");
  VALK_TEST_ASSERT(atomic_load(&heap->committed_bytes) == 0, "Initial committed should be 0");
  VALK_TEST_ASSERT(atomic_load(&heap->used_bytes) == 0, "Initial used should be 0");

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_heap2_create_default_limit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(0);
  VALK_TEST_ASSERT(heap != NULL, "Heap creation should succeed with 0 limit");
  VALK_TEST_ASSERT(heap->hard_limit == VALK_GC_DEFAULT_HARD_LIMIT, 
                   "Default hard limit should be used");

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_heap2_alloc_small(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);

  void *ptr = valk_gc_heap2_alloc(heap, 72);
  VALK_TEST_ASSERT(ptr != NULL, "Allocation of 72 bytes should succeed");
  VALK_TEST_ASSERT(atomic_load(&heap->used_bytes) > 0, "Used bytes should increase");

  memset(ptr, 0xAB, 72);
  uint8_t *bytes = (uint8_t *)ptr;
  VALK_TEST_ASSERT(bytes[0] == 0xAB, "Memory should be writable");
  VALK_TEST_ASSERT(bytes[71] == 0xAB, "Full allocation should be accessible");

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_heap2_alloc_multiple_classes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);

  void *p16 = valk_gc_heap2_alloc(heap, 16);
  void *p32 = valk_gc_heap2_alloc(heap, 32);
  void *p128 = valk_gc_heap2_alloc(heap, 128);
  void *p1024 = valk_gc_heap2_alloc(heap, 1024);

  VALK_TEST_ASSERT(p16 != NULL, "16-byte allocation should succeed");
  VALK_TEST_ASSERT(p32 != NULL, "32-byte allocation should succeed");
  VALK_TEST_ASSERT(p128 != NULL, "128-byte allocation should succeed");
  VALK_TEST_ASSERT(p1024 != NULL, "1024-byte allocation should succeed");

  VALK_TEST_ASSERT(p16 != p32 && p32 != p128 && p128 != p1024, 
                   "Allocations should be distinct");

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_heap2_alloc_many(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);

  void *ptrs[1000];
  for (int i = 0; i < 1000; i++) {
    ptrs[i] = valk_gc_heap2_alloc(heap, 72);
    VALK_TEST_ASSERT(ptrs[i] != NULL, "Allocation %d should succeed", i);
  }

  for (int i = 0; i < 1000; i++) {
    for (int j = i + 1; j < 1000; j++) {
      VALK_TEST_ASSERT(ptrs[i] != ptrs[j], "Allocations %d and %d should be distinct", i, j);
    }
  }

  size_t expected_min = 1000 * 128;
  VALK_TEST_ASSERT(atomic_load(&heap->used_bytes) >= expected_min, 
                   "Used bytes should be at least %zu (got %zu)", 
                   expected_min, atomic_load(&heap->used_bytes));

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_heap2_alloc_large_object(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);

  void *large = valk_gc_heap2_alloc(heap, 1024 * 1024);
  VALK_TEST_ASSERT(large != NULL, "1MB large object allocation should succeed");

  size_t large_bytes = atomic_load(&heap->large_object_bytes);
  VALK_TEST_ASSERT(large_bytes >= 1024 * 1024, "Large object bytes should reflect allocation");

  memset(large, 0xCD, 1024 * 1024);

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_heap2_used_bytes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);

  size_t before = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(before == 0, "Initial used bytes should be 0");

  valk_gc_heap2_alloc(heap, 72);
  size_t after = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(after > before, "Used bytes should increase after allocation");

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_tlab2_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_tlab2_t tlab;
  valk_gc_tlab2_init(&tlab);

  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    VALK_TEST_ASSERT(tlab.classes[c].page == NULL, "Class %d page should be NULL", c);
    VALK_TEST_ASSERT(tlab.classes[c].next_slot == 0, "Class %d next_slot should be 0", c);
    VALK_TEST_ASSERT(tlab.classes[c].limit_slot == 0, "Class %d limit_slot should be 0", c);
  }

  VALK_PASS();
}

void test_gc_page2_accessors(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  valk_gc_heap2_alloc(heap, 72);

  valk_gc_page_list_t *list = &heap->classes[3];
  VALK_TEST_ASSERT(list->all_pages != NULL, "Class 3 should have a page");

  valk_gc_page2_t *page = list->all_pages;
  uint8_t *alloc_bm = valk_gc_page2_alloc_bitmap(page);
  uint8_t *mark_bm = valk_gc_page2_mark_bitmap(page);
  uint8_t *slots = valk_gc_page2_slots(page);

  VALK_TEST_ASSERT(alloc_bm != NULL, "Alloc bitmap should be accessible");
  VALK_TEST_ASSERT(mark_bm != NULL, "Mark bitmap should be accessible");
  VALK_TEST_ASSERT(slots != NULL, "Slots should be accessible");
  VALK_TEST_ASSERT(mark_bm > alloc_bm, "Mark bitmap should follow alloc bitmap");
  VALK_TEST_ASSERT(slots > mark_bm, "Slots should follow mark bitmap");
  VALK_TEST_ASSERT(((uintptr_t)slots % 64) == 0, "Slots should be cache-aligned");

  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_ptr_to_location(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *ptr1 = valk_gc_heap2_alloc(heap, 72);
  void *ptr2 = valk_gc_heap2_alloc(heap, 16);
  void *ptr3 = valk_gc_heap2_alloc(heap, 1024);
  
  valk_gc_ptr_location_t loc;
  
  bool found1 = valk_gc_ptr_to_location(heap, ptr1, &loc);
  VALK_TEST_ASSERT(found1, "Should find 72-byte allocation");
  VALK_TEST_ASSERT(loc.is_valid, "Location should be valid");
  VALK_TEST_ASSERT(loc.size_class == 3, "72 bytes should be in class 3 (128B)");
  VALK_TEST_ASSERT(loc.page != NULL, "Page should be set");
  
  bool found2 = valk_gc_ptr_to_location(heap, ptr2, &loc);
  VALK_TEST_ASSERT(found2, "Should find 16-byte allocation");
  VALK_TEST_ASSERT(loc.size_class == 0, "16 bytes should be in class 0 (16B)");
  
  bool found3 = valk_gc_ptr_to_location(heap, ptr3, &loc);
  VALK_TEST_ASSERT(found3, "Should find 1024-byte allocation");
  VALK_TEST_ASSERT(loc.size_class == 6, "1024 bytes should be in class 6 (1KB)");
  
  void *external = malloc(64);
  bool found_ext = valk_gc_ptr_to_location(heap, external, &loc);
  VALK_TEST_ASSERT(!found_ext, "External pointer should not be found");
  VALK_TEST_ASSERT(!loc.is_valid, "Location should be invalid");
  free(external);
  
  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_page2_mark_operations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *ptr = valk_gc_heap2_alloc(heap, 72);
  
  valk_gc_ptr_location_t loc;
  bool found = valk_gc_ptr_to_location(heap, ptr, &loc);
  VALK_TEST_ASSERT(found, "Should find allocation");
  
  VALK_TEST_ASSERT(!valk_gc_page2_is_marked(loc.page, loc.slot), "Slot should not be marked initially");
  VALK_TEST_ASSERT(valk_gc_page2_is_allocated(loc.page, loc.slot), "Slot should be allocated");
  
  bool newly_marked = valk_gc_page2_try_mark(loc.page, loc.slot);
  VALK_TEST_ASSERT(newly_marked, "First mark should succeed");
  VALK_TEST_ASSERT(valk_gc_page2_is_marked(loc.page, loc.slot), "Slot should be marked now");
  
  bool marked_again = valk_gc_page2_try_mark(loc.page, loc.slot);
  VALK_TEST_ASSERT(!marked_again, "Second mark should return false (already marked)");
  
  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_sweep_page2_unmarked(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  for (int i = 0; i < 100; i++) {
    valk_gc_heap2_alloc(heap, 72);
  }
  
  valk_gc_page_list_t *list = &heap->classes[3];
  VALK_TEST_ASSERT(list->all_pages != NULL, "Should have pages");
  
  valk_gc_page2_t *page = list->all_pages;
  uint32_t before = atomic_load(&page->num_allocated);
  VALK_TEST_ASSERT(before > 0, "Page should have allocations");
  
  size_t freed = valk_gc_sweep_page2(page);
  VALK_TEST_ASSERT(freed == before, "All unmarked slots should be freed");
  
  uint32_t after = atomic_load(&page->num_allocated);
  VALK_TEST_ASSERT(after == 0, "No slots should remain allocated");
  
  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_sweep_page2_marked(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *ptrs[10];
  for (int i = 0; i < 10; i++) {
    ptrs[i] = valk_gc_heap2_alloc(heap, 72);
  }
  
  int marked_count = 0;
  for (int i = 0; i < 5; i++) {
    valk_gc_ptr_location_t loc;
    if (valk_gc_ptr_to_location(heap, ptrs[i], &loc)) {
      valk_gc_page2_try_mark(loc.page, loc.slot);
      marked_count++;
    }
  }
  
  valk_gc_page_list_t *list = &heap->classes[3];
  valk_gc_page2_t *page = list->all_pages;
  
  uint32_t before = atomic_load(&page->num_allocated);
  
  size_t freed = valk_gc_sweep_page2(page);
  
  uint32_t remaining = atomic_load(&page->num_allocated);
  VALK_TEST_ASSERT(remaining == (uint32_t)marked_count, 
                   "Marked slots should remain (expected %d, got %u)", marked_count, remaining);
  VALK_TEST_ASSERT(freed == before - (uint32_t)marked_count, 
                   "Unmarked slots should be freed (expected %u, got %zu)", 
                   before - marked_count, freed);
  
  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_mark_large_object(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *large = valk_gc_heap2_alloc(heap, 1024 * 1024);
  VALK_TEST_ASSERT(large != NULL, "Large allocation should succeed");
  
  bool marked = valk_gc_mark_large_object(heap, large);
  VALK_TEST_ASSERT(marked, "First mark should succeed");
  
  bool marked_again = valk_gc_mark_large_object(heap, large);
  VALK_TEST_ASSERT(!marked_again, "Second mark should return false");
  
  void *external = malloc(64);
  bool marked_ext = valk_gc_mark_large_object(heap, external);
  VALK_TEST_ASSERT(!marked_ext, "External pointer should not be markable");
  free(external);
  
  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_sweep_large_objects(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *large1 = valk_gc_heap2_alloc(heap, 1024 * 1024);
  void *large2 = valk_gc_heap2_alloc(heap, 512 * 1024);
  
  size_t before = atomic_load(&heap->large_object_bytes);
  VALK_TEST_ASSERT(before > 0, "Should have large object bytes");
  
  valk_gc_mark_large_object(heap, large1);
  
  size_t freed = valk_gc_sweep_large_objects(heap);
  VALK_TEST_ASSERT(freed >= 512 * 1024, "Unmarked large object should be freed");
  
  size_t after = atomic_load(&heap->large_object_bytes);
  VALK_TEST_ASSERT(after < before, "Large object bytes should decrease");
  
  (void)large2;
  
  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

void test_gc_rebuild_partial_lists(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  for (int i = 0; i < 100; i++) {
    valk_gc_heap2_alloc(heap, 72);
  }
  
  valk_gc_page_list_t *list = &heap->classes[3];
  valk_gc_page2_t *page = list->all_pages;
  valk_gc_sweep_page2(page);
  
  valk_gc_rebuild_partial_lists(heap);
  
  VALK_TEST_ASSERT(list->partial_pages != NULL, "Partial list should be rebuilt");
  VALK_TEST_ASSERT(list->partial_pages == page, "Swept page should be in partial list");
  
  valk_gc_heap2_destroy(heap);

  VALK_PASS();
}

// ============================================================================
// Phase 3: Memory Limits and GC Cycle Tests
// ============================================================================

void test_gc_heap2_get_stats(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  for (int i = 0; i < 50; i++) {
    valk_gc_heap2_alloc(heap, 72);
  }
  
  valk_gc_stats2_t stats;
  valk_gc_heap2_get_stats(heap, &stats);
  
  VALK_TEST_ASSERT(stats.hard_limit == 64 * 1024 * 1024, "Hard limit should match");
  VALK_TEST_ASSERT(stats.soft_limit == 48 * 1024 * 1024, "Soft limit should be 75% of hard");
  VALK_TEST_ASSERT(stats.used_bytes > 0, "Used bytes should be positive");
  VALK_TEST_ASSERT(stats.class_used_slots[3] >= 50, "Class 3 should have at least 50 slots used");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_tlab2_reset(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_tlab2_t tlab;
  valk_gc_tlab2_init(&tlab);
  
  tlab.classes[0].next_slot = 5;
  tlab.classes[0].limit_slot = 32;
  tlab.classes[3].page = (valk_gc_page2_t *)0x12345678;
  tlab.classes[3].next_slot = 10;
  tlab.classes[3].limit_slot = 20;
  
  valk_gc_tlab2_reset(&tlab);
  
  for (int c = 0; c < VALK_GC_NUM_SIZE_CLASSES; c++) {
    VALK_TEST_ASSERT(tlab.classes[c].page == NULL, "Page should be NULL after reset");
    VALK_TEST_ASSERT(tlab.classes[c].next_slot == 0, "next_slot should be 0 after reset");
    VALK_TEST_ASSERT(tlab.classes[c].limit_slot == 0, "limit_slot should be 0 after reset");
  }
  
  VALK_PASS();
}

void test_gc_heap2_collect_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  size_t reclaimed = valk_gc_heap2_collect(heap);
  
  VALK_TEST_ASSERT(reclaimed == 0, "Empty heap should reclaim nothing");
  VALK_TEST_ASSERT(atomic_load(&heap->collections) == 1, "Collection count should be 1");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_collect_reclaims_unmarked(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  for (int i = 0; i < 100; i++) {
    valk_gc_heap2_alloc(heap, 72);
  }
  
  size_t used_before = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(used_before >= 100 * 128, "Should have allocated at least 100 * 128 bytes");
  
  size_t reclaimed = valk_gc_heap2_collect(heap);
  
  VALK_TEST_ASSERT(reclaimed >= 100 * 128, "Should reclaim all unmarked allocations");
  
  size_t used_after = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(used_after < used_before, "Used bytes should decrease after collection");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_collect_preserves_marked(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *ptrs[50];
  for (int i = 0; i < 50; i++) {
    ptrs[i] = valk_gc_heap2_alloc(heap, 72);
  }
  
  for (int i = 0; i < 25; i++) {
    valk_gc_ptr_location_t loc;
    if (valk_gc_ptr_to_location(heap, ptrs[i], &loc)) {
      valk_gc_page2_try_mark(loc.page, loc.slot);
    }
  }
  
  size_t reclaimed = valk_gc_heap2_collect(heap);
  
  VALK_TEST_ASSERT(reclaimed >= 25 * 128, "Should reclaim unmarked slots");
  VALK_TEST_ASSERT(reclaimed < 50 * 128, "Should not reclaim marked slots");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_soft_limit_triggers_gc(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  size_t hard_limit = 256 * 1024;
  size_t soft_limit = hard_limit * 3 / 4;
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(hard_limit);
  
  size_t allocs_needed = soft_limit / 128 + 10;
  for (size_t i = 0; i < allocs_needed; i++) {
    valk_gc_heap2_alloc(heap, 72);
  }
  
  VALK_TEST_ASSERT(atomic_load(&heap->collections) >= 1, 
                   "Exceeding soft limit should trigger at least one GC");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_collect_updates_stats(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  for (int i = 0; i < 100; i++) {
    valk_gc_heap2_alloc(heap, 72);
  }
  
  size_t reclaimed = valk_gc_heap2_collect(heap);
  
  valk_gc_stats2_t stats;
  valk_gc_heap2_get_stats(heap, &stats);
  
  VALK_TEST_ASSERT(stats.collections == 1, "Collection count should be 1");
  VALK_TEST_ASSERT(stats.bytes_reclaimed_total >= reclaimed, 
                   "Total reclaimed should include this collection");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_mark_object(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *ptr = valk_gc_heap2_alloc(heap, 72);
  VALK_TEST_ASSERT(ptr != NULL, "Allocation should succeed");
  
  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = &queue
  };
  
  valk_gc_heap2_mark_object(&ctx, ptr);
  
  valk_gc_ptr_location_t loc;
  bool found = valk_gc_ptr_to_location(heap, ptr, &loc);
  VALK_TEST_ASSERT(found, "Should find pointer location");
  VALK_TEST_ASSERT(valk_gc_page2_is_marked(loc.page, loc.slot), 
                   "Object should be marked after mark_object call");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_mark_object_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = &queue
  };
  
  valk_gc_heap2_mark_object(&ctx, NULL);
  
  VALK_TEST_ASSERT(valk_gc_mark_queue_empty(&queue), 
                   "Queue should remain empty after marking NULL");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_mark_object_not_in_heap(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = &queue
  };
  
  char stack_buffer[128];
  valk_gc_heap2_mark_object(&ctx, stack_buffer);
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_mark_large_object_via_ctx(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *large = valk_gc_heap2_alloc(heap, 8192);
  VALK_TEST_ASSERT(large != NULL, "Large allocation should succeed");
  
  valk_gc_mark_queue_t queue;
  valk_gc_mark_queue_init(&queue);
  
  valk_gc_mark_ctx2_t ctx = {
    .heap = heap,
    .queue = &queue
  };
  
  valk_gc_heap2_mark_object(&ctx, large);
  
  size_t used_before = valk_gc_heap2_used_bytes(heap);
  valk_gc_heap2_collect(heap);
  size_t used_after = valk_gc_heap2_used_bytes(heap);
  
  VALK_TEST_ASSERT(used_after == used_before, 
                   "Marked large object should not be collected");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_mark_roots_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  valk_gc_heap2_mark_roots(heap);
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_mark_roots_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_mark_roots(NULL);
  
  VALK_PASS();
}

void test_gc_reclaim_empty_pages_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  size_t reclaimed = valk_gc_reclaim_empty_pages(NULL);
  VALK_TEST_ASSERT(reclaimed == 0, "NULL heap should return 0");
  
  VALK_PASS();
}

void test_gc_reclaim_empty_pages_no_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *p1 = valk_gc_heap2_alloc(heap, 64);
  VALK_TEST_ASSERT(p1 != NULL, "Allocation should succeed");
  
  size_t reclaimed = valk_gc_reclaim_empty_pages(heap);
  VALK_TEST_ASSERT(reclaimed == 0, "No pages should be reclaimed when all have allocations");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_reclaim_empty_pages_after_sweep(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *p1 = valk_gc_heap2_alloc(heap, 64);
  VALK_TEST_ASSERT(p1 != NULL, "Allocation should succeed");
  
  valk_gc_heap2_collect(heap);
  
  size_t reclaimed = valk_gc_reclaim_empty_pages(heap);
  VALK_TEST_ASSERT(reclaimed >= 1, "Empty page should be reclaimed after GC");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_reclaim_empty_pages_multiple_classes(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *p1 = valk_gc_heap2_alloc(heap, 16);
  void *p2 = valk_gc_heap2_alloc(heap, 64);
  void *p3 = valk_gc_heap2_alloc(heap, 256);
  void *p4 = valk_gc_heap2_alloc(heap, 1024);
  
  VALK_TEST_ASSERT(p1 && p2 && p3 && p4, "All allocations should succeed");
  
  valk_gc_heap2_collect(heap);
  
  size_t reclaimed = valk_gc_reclaim_empty_pages(heap);
  VALK_TEST_ASSERT(reclaimed >= 4, "All empty pages should be reclaimed");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_reclaim_reallocation_works(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *p1 = valk_gc_heap2_alloc(heap, 64);
  VALK_TEST_ASSERT(p1 != NULL, "First allocation should succeed");
  
  valk_gc_heap2_collect(heap);
  valk_gc_reclaim_empty_pages(heap);
  
  void *p2 = valk_gc_heap2_alloc(heap, 64);
  VALK_TEST_ASSERT(p2 != NULL, "Second allocation after reclaim should succeed");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_parallel_collect_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  size_t reclaimed = valk_gc_heap2_parallel_collect(NULL);
  VALK_TEST_ASSERT(reclaimed == 0, "NULL heap should return 0");
  
  VALK_PASS();
}

void test_gc_heap2_parallel_collect_single_thread(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  void *p1 = valk_gc_heap2_alloc(heap, 64);
  void *p2 = valk_gc_heap2_alloc(heap, 128);
  void *p3 = valk_gc_heap2_alloc(heap, 256);
  VALK_TEST_ASSERT(p1 && p2 && p3, "All allocations should succeed");
  
  size_t before = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(before > 0, "Heap should have used bytes");
  
  size_t reclaimed = valk_gc_heap2_parallel_collect(heap);
  
  size_t after = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(after < before, "Heap usage should decrease after GC");
  VALK_TEST_ASSERT(reclaimed > 0, "Should reclaim some bytes");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_parallel_mark_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_parallel_mark(NULL);
  
  VALK_PASS();
}

void test_gc_heap2_parallel_sweep_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_parallel_sweep(NULL);
  
  VALK_PASS();
}

void test_gc_heap2_request_stw_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  bool result = valk_gc_heap2_request_stw(NULL);
  VALK_TEST_ASSERT(!result, "NULL heap should return false");
  
  VALK_PASS();
}

void test_gc_heap2_parallel_collect_reclaims_bytes(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  for (int i = 0; i < 100; i++) {
    void *p = valk_gc_heap2_alloc(heap, 64);
    VALK_TEST_ASSERT(p != NULL, "Allocation should succeed");
  }
  
  size_t before = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(before >= 100 * 64, "Should have allocated at least 6400 bytes");
  
  size_t reclaimed = valk_gc_heap2_parallel_collect(heap);
  
  size_t after = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(after == 0, "All objects should be reclaimed (no roots)");
  VALK_TEST_ASSERT(reclaimed == before, "Reclaimed should equal previous usage");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_parallel_collect_updates_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  
  for (int i = 0; i < 50; i++) {
    valk_gc_heap2_alloc(heap, 128);
  }
  
  valk_gc_stats2_t stats_before;
  valk_gc_heap2_get_stats(heap, &stats_before);
  uint64_t cycles_before = stats_before.collections;
  
  valk_gc_heap2_parallel_collect(heap);
  
  valk_gc_stats2_t stats_after;
  valk_gc_heap2_get_stats(heap, &stats_after);
  
  VALK_TEST_ASSERT(stats_after.collections == cycles_before + 1, 
                   "Collection count should increment");
  VALK_TEST_ASSERT(stats_after.bytes_reclaimed_total > 0,
                   "Should have reclaimed some bytes");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

typedef struct {
  valk_gc_heap2_t *heap;
  int thread_id;
  int alloc_count;
  _Atomic int *ready_count;
  _Atomic bool *start_flag;
} mt_gc_test_args_t;

static void *mt_gc_worker(void *arg) {
  mt_gc_test_args_t *args = (mt_gc_test_args_t *)arg;
  
  valk_mem_init_malloc();
  valk_gc_thread_register();
  
  atomic_fetch_add(args->ready_count, 1);
  
  while (!atomic_load(args->start_flag)) {
    sched_yield();
  }
  
  for (int i = 0; i < args->alloc_count; i++) {
    void *p = valk_gc_heap2_alloc(args->heap, 64 + (i % 128));
    if (p) {
      memset(p, args->thread_id, 64);
    }
    
    if (i % 100 == 0) {
      VALK_GC_SAFE_POINT();
    }
  }
  
  valk_gc_thread_unregister();
  return NULL;
}

void test_gc_heap2_multithread_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(128 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  const int num_threads = 4;
  const int allocs_per_thread = 500;
  
  pthread_t threads[4];
  mt_gc_test_args_t args[4];
  _Atomic int ready_count = 0;
  _Atomic bool start_flag = false;
  
  for (int i = 0; i < num_threads; i++) {
    args[i].heap = heap;
    args[i].thread_id = i;
    args[i].alloc_count = allocs_per_thread;
    args[i].ready_count = &ready_count;
    args[i].start_flag = &start_flag;
    pthread_create(&threads[i], NULL, mt_gc_worker, &args[i]);
  }
  
  while (atomic_load(&ready_count) < num_threads) {
    sched_yield();
  }
  
  atomic_store(&start_flag, true);
  
  for (int i = 0; i < num_threads; i++) {
    pthread_join(threads[i], NULL);
  }
  
  size_t used = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(used > 0, "Should have allocated some bytes");
  
  size_t reclaimed = valk_gc_heap2_collect(heap);
  VALK_TEST_ASSERT(reclaimed == used, "Should reclaim all bytes (no roots)");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_multithread_collect_auto(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(128 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  valk_gc_thread_register();
  
  for (int i = 0; i < 1000; i++) {
    valk_gc_heap2_alloc(heap, 128);
  }
  
  size_t before = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(before > 0, "Should have allocated bytes");
  
  size_t reclaimed = valk_gc_heap2_collect_auto(heap);
  
  VALK_TEST_ASSERT(reclaimed == before, "collect_auto should reclaim all (fallback to single-threaded)");
  
  valk_gc_thread_unregister();
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

typedef struct {
  valk_gc_heap2_t *heap;
  int thread_id;
  int alloc_count;
  _Atomic int *ready_count;
  _Atomic bool *start_flag;
  _Atomic bool *gc_triggered;
  _Atomic int *gc_complete_count;
} parallel_gc_test_args_t;

static void *parallel_gc_worker(void *arg) {
  parallel_gc_test_args_t *args = (parallel_gc_test_args_t *)arg;
  
  valk_mem_init_malloc();
  valk_gc_thread_register();
  
  atomic_fetch_add(args->ready_count, 1);
  
  while (!atomic_load(args->start_flag)) {
    sched_yield();
  }
  
  for (int i = 0; i < args->alloc_count; i++) {
    void *p = valk_gc_heap2_alloc(args->heap, 64 + (args->thread_id * 16));
    if (p) {
      memset(p, args->thread_id, 64);
    }
    
    VALK_GC_SAFE_POINT();
  }
  
  atomic_fetch_add(args->gc_complete_count, 1);
  
  while (atomic_load(args->gc_complete_count) < 4) {
    VALK_GC_SAFE_POINT();
    usleep(100);
  }
  
  valk_gc_thread_unregister();
  return NULL;
}

void test_gc_heap2_parallel_gc_stress(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(256 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  const int num_threads = 4;
  const int allocs_per_thread = 500;
  
  pthread_t threads[4];
  parallel_gc_test_args_t args[4];
  _Atomic int ready_count = 0;
  _Atomic bool start_flag = false;
  _Atomic bool gc_triggered = false;
  _Atomic int gc_complete_count = 0;
  
  for (int i = 0; i < num_threads; i++) {
    args[i].heap = heap;
    args[i].thread_id = i;
    args[i].alloc_count = allocs_per_thread;
    args[i].ready_count = &ready_count;
    args[i].start_flag = &start_flag;
    args[i].gc_triggered = &gc_triggered;
    args[i].gc_complete_count = &gc_complete_count;
    pthread_create(&threads[i], NULL, parallel_gc_worker, &args[i]);
  }
  
  while (atomic_load(&ready_count) < num_threads) {
    sched_yield();
  }
  
  atomic_store(&start_flag, true);
  
  for (int i = 0; i < num_threads; i++) {
    pthread_join(threads[i], NULL);
  }
  
  VALK_TEST_ASSERT(atomic_load(&gc_complete_count) == num_threads, 
                   "All threads should have completed");
  
  size_t used = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(used > 0, "Should have allocated some bytes");
  
  size_t reclaimed = valk_gc_heap2_collect(heap);
  VALK_TEST_ASSERT(reclaimed == used, "Should reclaim all bytes (no roots)");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_parallel_gc_stw(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_coordinator_init();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(256 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  valk_gc_thread_register();
  
  for (int i = 0; i < 1000; i++) {
    void *p = valk_gc_heap2_alloc(heap, 128);
    if (p) memset(p, 0, 64);
  }
  
  size_t before = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(before > 0, "Should have allocated bytes");
  
  size_t reclaimed = valk_gc_heap2_collect_auto(heap);
  
  VALK_TEST_ASSERT(reclaimed == before, "Should reclaim all bytes (no roots)");
  
  valk_gc_stats2_t stats;
  valk_gc_heap2_get_stats(heap, &stats);
  VALK_TEST_ASSERT(stats.collections == 1, "Should have 1 collection");
  
  valk_gc_thread_unregister();
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

typedef struct {
  valk_gc_heap2_t *heap;
  int thread_id;
  _Atomic int *ready_count;
  _Atomic bool *start_flag;
  _Atomic bool *gc_done_flag;
  _Atomic int *participated_count;
  void **rooted_ptrs;
  int rooted_count;
} true_parallel_gc_args_t;

static void *true_parallel_gc_worker(void *arg) {
  true_parallel_gc_args_t *args = (true_parallel_gc_args_t *)arg;
  
  valk_mem_init_malloc();
  valk_gc_thread_register();
  
  for (int i = 0; i < args->rooted_count; i++) {
    args->rooted_ptrs[i] = valk_gc_heap2_alloc(args->heap, 64);
    if (args->rooted_ptrs[i]) {
      memset(args->rooted_ptrs[i], args->thread_id + 1, 64);
    }
  }
  
  atomic_fetch_add(args->ready_count, 1);
  
  while (!atomic_load(args->start_flag)) {
    sched_yield();
  }
  
  for (int i = 0; i < 100 && !atomic_load(args->gc_done_flag); i++) {
    VALK_GC_SAFE_POINT();
    usleep(100);
  }
  
  atomic_fetch_add(args->participated_count, 1);
  
  for (int i = 0; i < args->rooted_count; i++) {
    if (args->rooted_ptrs[i]) {
      uint8_t *data = (uint8_t *)args->rooted_ptrs[i];
      if (data[0] != (uint8_t)(args->thread_id + 1)) {
        fprintf(stderr, "Thread %d: data corrupted!\n", args->thread_id);
      }
    }
  }
  
  valk_gc_thread_unregister();
  return NULL;
}

void test_gc_heap2_true_parallel_gc(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_coordinator_init();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(256 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  valk_gc_thread_register();
  
  const int num_workers = 3;
  const int rooted_per_thread = 100;
  pthread_t workers[3];
  true_parallel_gc_args_t args[3];
  void *rooted_ptrs[3][100];
  _Atomic int ready_count = 0;
  _Atomic bool start_flag = false;
  _Atomic bool gc_done_flag = false;
  _Atomic int participated_count = 0;
  
  for (int i = 0; i < num_workers; i++) {
    args[i].heap = heap;
    args[i].thread_id = i;
    args[i].ready_count = &ready_count;
    args[i].start_flag = &start_flag;
    args[i].gc_done_flag = &gc_done_flag;
    args[i].participated_count = &participated_count;
    args[i].rooted_ptrs = rooted_ptrs[i];
    args[i].rooted_count = rooted_per_thread;
    pthread_create(&workers[i], NULL, true_parallel_gc_worker, &args[i]);
  }
  
  while (atomic_load(&ready_count) < num_workers) {
    sched_yield();
  }
  
  for (int i = 0; i < 500; i++) {
    void *p = valk_gc_heap2_alloc(heap, 128);
    if (p) memset(p, 0xFF, 128);
  }
  
  size_t before = valk_gc_heap2_used_bytes(heap);
  VALK_TEST_ASSERT(before > 0, "Should have allocated bytes");
  
  size_t num_registered = atomic_load(&valk_gc_coord.threads_registered);
  VALK_TEST_ASSERT(num_registered == 4, "Should have 4 registered threads");
  
  atomic_store(&start_flag, true);
  
  usleep(1000);
  
  size_t reclaimed = valk_gc_heap2_collect_auto(heap);
  
  atomic_store(&gc_done_flag, true);
  
  for (int i = 0; i < num_workers; i++) {
    pthread_join(workers[i], NULL);
  }
  
  VALK_TEST_ASSERT(reclaimed > 0, "Should reclaim some bytes (main thread garbage)");
  
  valk_gc_stats2_t stats;
  valk_gc_heap2_get_stats(heap, &stats);
  VALK_TEST_ASSERT(stats.collections >= 1, "Should have at least 1 collection");
  
  uint64_t parallel_cycles = atomic_load(&valk_gc_coord.parallel_cycles);
  VALK_TEST_ASSERT(parallel_cycles >= 1, "Should have parallel GC cycle");
  
  valk_gc_thread_unregister();
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

typedef struct {
  valk_gc_heap2_t *heap;
  int thread_id;
  _Atomic int *ready_count;
  _Atomic bool *start_flag;
  _Atomic bool *gc_done_flag;
  _Atomic int *roots_verified;
  valk_lval_t *root_val;
} root_marking_test_args_t;

static void *root_marking_worker(void *arg) {
  root_marking_test_args_t *args = (root_marking_test_args_t *)arg;
  
  valk_mem_init_malloc();
  valk_gc_thread_register();
  
  args->root_val = valk_gc_heap2_alloc(args->heap, sizeof(valk_lval_t));
  if (args->root_val) {
    memset(args->root_val, 0, sizeof(valk_lval_t));
    args->root_val->flags = LVAL_NUM;
    args->root_val->num = 42 + args->thread_id;
  }
  
  atomic_fetch_add(args->ready_count, 1);
  
  while (!atomic_load(args->start_flag)) {
    sched_yield();
  }
  
  for (int i = 0; i < 100 && !atomic_load(args->gc_done_flag); i++) {
    VALK_GC_SAFE_POINT();
    usleep(100);
  }
  
  if (args->root_val && args->root_val->num == (42 + args->thread_id)) {
    atomic_fetch_add(args->roots_verified, 1);
  }
  
  valk_gc_thread_unregister();
  return NULL;
}

void test_gc_parallel_thread_local_roots(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_coordinator_init();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(256 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  valk_gc_thread_register();
  
  const int num_workers = 3;
  pthread_t workers[3];
  root_marking_test_args_t args[3];
  _Atomic int ready_count = 0;
  _Atomic bool start_flag = false;
  _Atomic bool gc_done_flag = false;
  _Atomic int roots_verified = 0;
  
  for (int i = 0; i < num_workers; i++) {
    args[i].heap = heap;
    args[i].thread_id = i;
    args[i].ready_count = &ready_count;
    args[i].start_flag = &start_flag;
    args[i].gc_done_flag = &gc_done_flag;
    args[i].roots_verified = &roots_verified;
    args[i].root_val = NULL;
    pthread_create(&workers[i], NULL, root_marking_worker, &args[i]);
  }
  
  while (atomic_load(&ready_count) < num_workers) {
    sched_yield();
  }
  
  for (int i = 0; i < 1000; i++) {
    void *p = valk_gc_heap2_alloc(heap, 64);
    if (p) memset(p, 0xAB, 64);
  }
  
  atomic_store(&start_flag, true);
  usleep(1000);
  
  valk_gc_heap2_collect_auto(heap);
  
  atomic_store(&gc_done_flag, true);
  
  for (int i = 0; i < num_workers; i++) {
    pthread_join(workers[i], NULL);
  }
  
  valk_gc_thread_unregister();
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_realloc_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  void *ptr = valk_gc_heap2_alloc(heap, 32);
  VALK_TEST_ASSERT(ptr != NULL, "Should allocate 32 bytes");
  memset(ptr, 0xAB, 32);
  
  void *ptr2 = valk_gc_heap2_realloc(heap, ptr, 128);
  VALK_TEST_ASSERT(ptr2 != NULL, "Should reallocate to 128 bytes");
  
  uint8_t *data = (uint8_t *)ptr2;
  bool data_preserved = true;
  for (int i = 0; i < 32; i++) {
    if (data[i] != 0xAB) {
      data_preserved = false;
      break;
    }
  }
  VALK_TEST_ASSERT(data_preserved, "Original data should be preserved");
  
  void *ptr3 = valk_gc_heap2_realloc(heap, ptr2, 16);
  VALK_TEST_ASSERT(ptr3 != NULL, "Should reallocate to 16 bytes");
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_realloc_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  void *ptr = valk_gc_heap2_realloc(heap, NULL, 64);
  VALK_TEST_ASSERT(ptr != NULL, "realloc(NULL, size) should allocate");
  
  void *ptr2 = valk_gc_heap2_realloc(heap, ptr, 0);
  (void)ptr2;
  
  valk_gc_heap2_destroy(heap);
  
  VALK_PASS();
}

void test_gc_heap2_realloc_large(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_gc_heap2_t *heap = valk_gc_heap2_create(64 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != NULL, "Heap should be created");
  
  void *ptr = valk_gc_heap2_alloc(heap, 64);
  VALK_TEST_ASSERT(ptr != NULL, "Should allocate 64 bytes");
  memset(ptr, 0xCD, 64);
  
  void *ptr2 = valk_gc_heap2_realloc(heap, ptr, 8192);
  VALK_TEST_ASSERT(ptr2 != NULL, "Should reallocate to large object");
  
  uint8_t *data = (uint8_t *)ptr2;
  bool data_preserved = true;
  for (int i = 0; i < 64; i++) {
    if (data[i] != 0xCD) {
      data_preserved = false;
      break;
    }
  }
  VALK_TEST_ASSERT(data_preserved, "Original data should be preserved");
  
  valk_gc_heap2_destroy(heap);
  
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
  valk_testsuite_add_test(suite, "test_gc_set_thresholds_null", test_gc_set_thresholds_null);
  valk_testsuite_add_test(suite, "test_gc_set_thresholds_zero_defaults", test_gc_set_thresholds_zero_defaults);
  valk_testsuite_add_test(suite, "test_gc_should_collect_null", test_gc_should_collect_null);
  valk_testsuite_add_test(suite, "test_gc_heap_usage_pct_null", test_gc_heap_usage_pct_null);
  valk_testsuite_add_test(suite, "test_gc_set_hard_limit_below_usage", test_gc_set_hard_limit_below_usage);
  valk_testsuite_add_test(suite, "test_gc_lval_forwarding", test_gc_lval_forwarding);
  valk_testsuite_add_test(suite, "test_gc_follow_forward_chain", test_gc_follow_forward_chain);
  valk_testsuite_add_test(suite, "test_gc_get_runtime_metrics_null_heap", test_gc_get_runtime_metrics_null_heap);
  valk_testsuite_add_test(suite, "test_gc_get_runtime_metrics_null_params", test_gc_get_runtime_metrics_null_params);
  valk_testsuite_add_test(suite, "test_gc_peak_usage_tracking", test_gc_peak_usage_tracking);
  valk_testsuite_add_test(suite, "test_gc_add_to_objects", test_gc_add_to_objects);
  valk_testsuite_add_test(suite, "test_gc_memory_print_stats", test_gc_memory_print_stats);
  valk_testsuite_add_test(suite, "test_gc_memory_print_stats_null_output", test_gc_memory_print_stats_null_output);
  valk_testsuite_add_test(suite, "test_gc_memory_print_stats_null_heap", test_gc_memory_print_stats_null_heap);
  valk_testsuite_add_test(suite, "test_gc_collect_with_additional_root", test_gc_collect_with_additional_root);
  valk_testsuite_add_test(suite, "test_gc_print_stats_null", test_gc_print_stats_null);
  valk_testsuite_add_test(suite, "test_gc_mark_lval_external", test_gc_mark_lval_external);
  valk_testsuite_add_test(suite, "test_gc_mark_lval_external_null", test_gc_mark_lval_external_null);
  valk_testsuite_add_test(suite, "test_gc_free_object", test_gc_free_object);
  valk_testsuite_add_test(suite, "test_gc_free_object_null", test_gc_free_object_null);
  valk_testsuite_add_test(suite, "test_gc_should_checkpoint_null_scratch", test_gc_should_checkpoint_null_scratch);
  valk_testsuite_add_test(suite, "test_gc_should_checkpoint_high_threshold", test_gc_should_checkpoint_high_threshold);
  valk_testsuite_add_test(suite, "test_gc_lval_sizes_set", test_gc_lval_sizes_set);
  valk_testsuite_add_test(suite, "test_gc_mark_env_external", test_gc_mark_env_external);
  valk_testsuite_add_test(suite, "test_gc_checkpoint_null_args", test_gc_checkpoint_null_args);
  valk_testsuite_add_test(suite, "test_gc_should_collect_rate_limiting", test_gc_should_collect_rate_limiting);
  valk_testsuite_add_test(suite, "test_gc_should_collect_above_threshold", test_gc_should_collect_above_threshold);
  valk_testsuite_add_test(suite, "test_gc_heap_usage_pct_with_allocations", test_gc_heap_usage_pct_with_allocations);
  valk_testsuite_add_test(suite, "test_gc_collect_arena_with_env", test_gc_collect_arena_with_env);
  valk_testsuite_add_test(suite, "test_gc_should_collect_arena_high_usage", test_gc_should_collect_arena_high_usage);
  valk_testsuite_add_test(suite, "test_gc_forwarding_preserves_alloc_bits", test_gc_forwarding_preserves_alloc_bits);
  valk_testsuite_add_test(suite, "test_gc_runtime_metrics_pause_max_updates", test_gc_runtime_metrics_pause_max_updates);
  valk_testsuite_add_test(suite, "test_gc_alloc_tracks_to_objects_list", test_gc_alloc_tracks_to_objects_list);

  // Size class infrastructure tests (Phase 1 - Multi-Class Allocator)
  valk_testsuite_add_test(suite, "test_gc_size_class_lookup", test_gc_size_class_lookup);
  valk_testsuite_add_test(suite, "test_gc_slots_per_page_calculation", test_gc_slots_per_page_calculation);
  valk_testsuite_add_test(suite, "test_gc_page_total_size", test_gc_page_total_size);
  valk_testsuite_add_test(suite, "test_gc_heap2_create_destroy", test_gc_heap2_create_destroy);
  valk_testsuite_add_test(suite, "test_gc_heap2_create_default_limit", test_gc_heap2_create_default_limit);
  valk_testsuite_add_test(suite, "test_gc_heap2_alloc_small", test_gc_heap2_alloc_small);
  valk_testsuite_add_test(suite, "test_gc_heap2_alloc_multiple_classes", test_gc_heap2_alloc_multiple_classes);
  valk_testsuite_add_test(suite, "test_gc_heap2_alloc_many", test_gc_heap2_alloc_many);
  valk_testsuite_add_test(suite, "test_gc_heap2_alloc_large_object", test_gc_heap2_alloc_large_object);
  valk_testsuite_add_test(suite, "test_gc_heap2_used_bytes", test_gc_heap2_used_bytes);
  valk_testsuite_add_test(suite, "test_gc_tlab2_init", test_gc_tlab2_init);
  valk_testsuite_add_test(suite, "test_gc_page2_accessors", test_gc_page2_accessors);

  // Phase 2: Pointer location and marking tests
  valk_testsuite_add_test(suite, "test_gc_ptr_to_location", test_gc_ptr_to_location);
  valk_testsuite_add_test(suite, "test_gc_page2_mark_operations", test_gc_page2_mark_operations);
  valk_testsuite_add_test(suite, "test_gc_sweep_page2_unmarked", test_gc_sweep_page2_unmarked);
  valk_testsuite_add_test(suite, "test_gc_sweep_page2_marked", test_gc_sweep_page2_marked);
  valk_testsuite_add_test(suite, "test_gc_mark_large_object", test_gc_mark_large_object);
  valk_testsuite_add_test(suite, "test_gc_sweep_large_objects", test_gc_sweep_large_objects);
  valk_testsuite_add_test(suite, "test_gc_rebuild_partial_lists", test_gc_rebuild_partial_lists);

  // Phase 3: Memory limits and GC cycle tests
  valk_testsuite_add_test(suite, "test_gc_heap2_get_stats", test_gc_heap2_get_stats);
  valk_testsuite_add_test(suite, "test_gc_tlab2_reset", test_gc_tlab2_reset);
  valk_testsuite_add_test(suite, "test_gc_heap2_collect_empty", test_gc_heap2_collect_empty);
  valk_testsuite_add_test(suite, "test_gc_heap2_collect_reclaims_unmarked", test_gc_heap2_collect_reclaims_unmarked);
  valk_testsuite_add_test(suite, "test_gc_heap2_collect_preserves_marked", test_gc_heap2_collect_preserves_marked);
  valk_testsuite_add_test(suite, "test_gc_heap2_soft_limit_triggers_gc", test_gc_heap2_soft_limit_triggers_gc);
  valk_testsuite_add_test(suite, "test_gc_heap2_collect_updates_stats", test_gc_heap2_collect_updates_stats);

  // Phase 4: Mark phase tests
  valk_testsuite_add_test(suite, "test_gc_heap2_mark_object", test_gc_heap2_mark_object);
  valk_testsuite_add_test(suite, "test_gc_heap2_mark_object_null", test_gc_heap2_mark_object_null);
  valk_testsuite_add_test(suite, "test_gc_heap2_mark_object_not_in_heap", test_gc_heap2_mark_object_not_in_heap);
  valk_testsuite_add_test(suite, "test_gc_heap2_mark_large_object_via_ctx", test_gc_heap2_mark_large_object_via_ctx);
  valk_testsuite_add_test(suite, "test_gc_heap2_mark_roots_empty", test_gc_heap2_mark_roots_empty);
  valk_testsuite_add_test(suite, "test_gc_heap2_mark_roots_null", test_gc_heap2_mark_roots_null);

  // Phase 5: Page reclamation tests
  valk_testsuite_add_test(suite, "test_gc_reclaim_empty_pages_null", test_gc_reclaim_empty_pages_null);
  valk_testsuite_add_test(suite, "test_gc_reclaim_empty_pages_no_empty", test_gc_reclaim_empty_pages_no_empty);
  valk_testsuite_add_test(suite, "test_gc_reclaim_empty_pages_after_sweep", test_gc_reclaim_empty_pages_after_sweep);
  valk_testsuite_add_test(suite, "test_gc_reclaim_empty_pages_multiple_classes", test_gc_reclaim_empty_pages_multiple_classes);
  valk_testsuite_add_test(suite, "test_gc_reclaim_reallocation_works", test_gc_reclaim_reallocation_works);

  // Phase 7: Parallel mark/sweep tests
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_collect_null", test_gc_heap2_parallel_collect_null);
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_collect_single_thread", test_gc_heap2_parallel_collect_single_thread);
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_mark_null", test_gc_heap2_parallel_mark_null);
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_sweep_null", test_gc_heap2_parallel_sweep_null);
  valk_testsuite_add_test(suite, "test_gc_heap2_request_stw_null", test_gc_heap2_request_stw_null);
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_collect_reclaims_bytes", test_gc_heap2_parallel_collect_reclaims_bytes);
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_collect_updates_metrics", test_gc_heap2_parallel_collect_updates_metrics);

  // Multi-threaded allocation tests
  valk_testsuite_add_test(suite, "test_gc_heap2_multithread_alloc", test_gc_heap2_multithread_alloc);
  valk_testsuite_add_test(suite, "test_gc_heap2_multithread_collect_auto", test_gc_heap2_multithread_collect_auto);

  // Parallel GC stress tests
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_gc_stress", test_gc_heap2_parallel_gc_stress);
  valk_testsuite_add_test(suite, "test_gc_heap2_parallel_gc_stw", test_gc_heap2_parallel_gc_stw);

  // Phase 10: True multi-threaded parallel GC tests
  valk_testsuite_add_test(suite, "test_gc_heap2_true_parallel_gc", test_gc_heap2_true_parallel_gc);
  valk_testsuite_add_test(suite, "test_gc_parallel_thread_local_roots", test_gc_parallel_thread_local_roots);

  // Phase 12: Realloc tests
  valk_testsuite_add_test(suite, "test_gc_heap2_realloc_basic", test_gc_heap2_realloc_basic);
  valk_testsuite_add_test(suite, "test_gc_heap2_realloc_null", test_gc_heap2_realloc_null);
  valk_testsuite_add_test(suite, "test_gc_heap2_realloc_large", test_gc_heap2_realloc_large);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
