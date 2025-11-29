#include "../src/gc.h"
#include "../src/memory.h"
#include "../src/parser.h"
#include "testing.h"
#include <stdio.h>
#include <stdlib.h>

// Test 1: Basic freeze functionality
void test_freeze_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t* v = valk_lval_nil();

  // Should not be frozen initially
  VALK_TEST_ASSERT(!LVAL_IS_FROZEN(v), "Value should not be frozen initially");

  // Freeze the value
  valk_lval_freeze(v);

  // Should be frozen now
  VALK_TEST_ASSERT(LVAL_IS_FROZEN(v), "Value should be frozen after freeze");
  VALK_PASS();
}

// Test 2: Construction before freeze works
void test_construction_before_freeze(VALK_TEST_ARGS()) {
  VALK_TEST();
  // valk_lval_t* v = valk_lval_qexpr_empty();
  // valk_lval_add(v, valk_lval_num(1));
  // valk_lval_add(v, valk_lval_num(2));
  // valk_lval_add(v, valk_lval_num(3));
  //
  // // Should have 3 elements
  // VALK_TEST_ASSERT(valk_lval_list_count(v) == 3, "Should have 3 elements");
  // VALK_TEST_ASSERT(valk_lval_list_nth(v, 0)->num == 1, "First element should be 1");
  // VALK_TEST_ASSERT(valk_lval_list_nth(v, 1)->num == 2, "Second element should be 2");
  // VALK_TEST_ASSERT(valk_lval_list_nth(v, 2)->num == 3, "Third element should be 3");
  //
  // // Now freeze
  // valk_lval_freeze(v);
  //
  // // Should still have 3 elements and data intact
  // VALK_TEST_ASSERT(valk_lval_list_count(v) == 3, "Still have 3 elements after freeze");
  // VALK_TEST_ASSERT(valk_lval_list_nth(v, 0)->num == 1, "Data preserved after freeze");
  // VALK_TEST_ASSERT(LVAL_IS_FROZEN(v), "Should be frozen");
  // VALK_PASS();
  VALK_SKIP("NOT implemented");
}

// Test 3: Recursive freeze
void test_recursive_freeze(VALK_TEST_ARGS()) {
  VALK_TEST();
  // // Create nested structure: {{1 2} {3 4}}
  // valk_lval_t* inner1 = valk_lval_qexpr_empty();
  // valk_lval_add(inner1, valk_lval_num(1));
  // valk_lval_add(inner1, valk_lval_num(2));
  //
  // valk_lval_t* inner2 = valk_lval_qexpr_empty();
  // valk_lval_add(inner2, valk_lval_num(3));
  // valk_lval_add(inner2, valk_lval_num(4));
  //
  // valk_lval_t* outer = valk_lval_qexpr_empty();
  // valk_lval_add(outer, inner1);
  // valk_lval_add(outer, inner2);
  //
  // // Freeze outer (should recursively freeze inner)
  // valk_lval_freeze(outer);
  //
  // // All should be frozen
  // VALK_TEST_ASSERT(LVAL_IS_FROZEN(outer), "Outer should be frozen");
  // VALK_TEST_ASSERT(LVAL_IS_FROZEN(inner1), "Inner1 should be frozen");
  // VALK_TEST_ASSERT(LVAL_IS_FROZEN(inner2), "Inner2 should be frozen");
  // VALK_TEST_ASSERT(LVAL_IS_FROZEN(valk_lval_list_nth(inner1, 0)),
  //                  "Nested elements should be frozen");
  // VALK_TEST_ASSERT(LVAL_IS_FROZEN(valk_lval_list_nth(inner2, 0)),
  //                  "All nested elements should be frozen");
  // VALK_PASS();
  VALK_SKIP("NOT implemented");
}

// Test 4: Cons list freeze
void test_cons_freeze(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Create cons list: (1 2 3)
  valk_lval_t* list = valk_lval_cons(
      valk_lval_num(1),
      valk_lval_cons(
          valk_lval_num(2),
          valk_lval_cons(
              valk_lval_num(3),
              valk_lval_nil())));

  // Freeze the list
  valk_lval_freeze(list);

  // All cons cells should be frozen
  VALK_TEST_ASSERT(LVAL_IS_FROZEN(list), "Cons list should be frozen");
  VALK_TEST_ASSERT(LVAL_IS_FROZEN(list->cons.head), "Head should be frozen");
  VALK_TEST_ASSERT(LVAL_IS_FROZEN(list->cons.tail), "Tail should be frozen");
  VALK_PASS();
}

// Test 5: Freeze doesn't affect reading
void test_freeze_allows_reading(VALK_TEST_ARGS()) {
  VALK_TEST();
  // valk_lval_t* v = valk_lval_qexpr_empty();
  // valk_lval_add(v, valk_lval_num(42));
  // valk_lval_freeze(v);
  //
  // // Should be able to read frozen values
  // VALK_TEST_ASSERT(valk_lval_list_count(v) == 1, "Can read count after freeze");
  // VALK_TEST_ASSERT(valk_lval_list_nth(v, 0)->num == 42, "Can read values after freeze");
  // VALK_PASS();
  VALK_SKIP("NOT implemented");
}

int main(int argc, const char** argv) {
  (void)argc;
  (void)argv;

  // Use GC heap for everything, including test suite
  size_t const GC_THRESHOLD_BYTES = 16 * 1024 * 1024;  // 16 MiB
  valk_gc_malloc_heap_t *gc_heap = valk_gc_malloc_heap_init(GC_THRESHOLD_BYTES);
  valk_thread_ctx.allocator = (void *)gc_heap;

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_freeze_basic", test_freeze_basic);
  valk_testsuite_add_test(suite, "test_construction_before_freeze",
                          test_construction_before_freeze);
  valk_testsuite_add_test(suite, "test_recursive_freeze", test_recursive_freeze);
  valk_testsuite_add_test(suite, "test_cons_freeze", test_cons_freeze);
  valk_testsuite_add_test(suite, "test_freeze_allows_reading",
                          test_freeze_allows_reading);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_testsuite_free(suite);

  // Clean up GC heap to avoid memory leaks
  valk_gc_malloc_heap_destroy(gc_heap);

  return res;
}
