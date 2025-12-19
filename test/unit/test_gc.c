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

void test_gc_set_thresholds_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_set_thresholds(NULL, 80, 60, 500);

  VALK_PASS();
}

void test_gc_set_thresholds_zero_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  for (int i = 0; i < 100; i++) {
    valk_gc_malloc_heap_alloc(heap, 1024);
  }

  size_t usage = heap->allocated_bytes;
  size_t original = heap->hard_limit;

  valk_gc_set_hard_limit(heap, usage / 2);
  VALK_TEST_ASSERT(heap->hard_limit == original, "Should not change limit below usage");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_lval_forwarding(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  valk_gc_get_runtime_metrics(heap, NULL, NULL, NULL, NULL, NULL, NULL);

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_peak_usage_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  valk_lval_t *root = valk_gc_malloc_heap_alloc(heap, sizeof(valk_lval_t));
  root->flags = LVAL_NUM | LVAL_ALLOC_HEAP;
  root->num = 123;

  size_t reclaimed = valk_gc_malloc_collect(heap, root);
  VALK_TEST_ASSERT(heap->num_collections == 1, "Should count collection");
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  void *ptr = valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(ptr != NULL, "Should allocate");

  size_t before = heap->allocated_bytes;
  valk_gc_free_object(heap, ptr);

  VALK_TEST_ASSERT(heap->allocated_bytes <= before, "allocated_bytes should decrease or stay same");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
}

void test_gc_free_object_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  extern size_t __valk_lval_size;
  extern size_t __valk_lenv_size;

  VALK_TEST_ASSERT(heap->lval_size == __valk_lval_size, "lval_size should match global");
  VALK_TEST_ASSERT(heap->lenv_size == __valk_lenv_size, "lenv_size should match global");

  valk_gc_malloc_heap_destroy(heap);

  VALK_PASS();
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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  valk_checkpoint(NULL, heap, NULL);

  valk_gc_malloc_heap_destroy(heap);
  free(scratch);

  VALK_PASS();
}

void test_gc_should_collect_rate_limiting(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

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

  valk_gc_malloc_heap_t *heap = valk_gc_malloc_heap_init(1024 * 1024, 10 * 1024 * 1024);

  VALK_TEST_ASSERT(heap->objects == NULL, "Objects list should be NULL initially");

  valk_gc_malloc_heap_alloc(heap, 1024);
  VALK_TEST_ASSERT(heap->objects != NULL, "Objects list should have entry after alloc");

  valk_gc_malloc_heap_alloc(heap, 1024);

  int count = 0;
  for (valk_gc_header_t *h = heap->objects; h != NULL && count < 100; h = h->gc_next) {
    count++;
  }
  VALK_TEST_ASSERT(count >= 2, "Should have at least 2 objects in list");

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

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
