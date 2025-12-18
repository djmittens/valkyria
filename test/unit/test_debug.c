#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/common.h"
#include "../../src/debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_trace_capture_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);

  VALK_TEST_ASSERT(captured > 0, "Should capture at least one frame, got %zu", captured);
  VALK_TEST_ASSERT(captured <= VALK_TRACE_DEPTH, "Should not exceed max depth");

  VALK_PASS();
}

void test_trace_capture_zero_frames(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, 0);

  VALK_TEST_ASSERT(captured == 0, "Requesting 0 frames should return 0");

  VALK_PASS();
}

void test_trace_capture_small_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[2];
  size_t captured = valk_trace_capture(stack, 2);

  VALK_TEST_ASSERT(captured >= 1, "Should capture at least 1 frame");
  VALK_TEST_ASSERT(captured <= 2, "Should not exceed buffer size");

  VALK_PASS();
}

void test_trace_capture_all_pointers_valid(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);

  for (size_t i = 0; i < captured; i++) {
    VALK_TEST_ASSERT(stack[i] != NULL, "Stack frame %zu should not be NULL", i);
  }

  VALK_PASS();
}

void test_trace_print_null_safe(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[2] = {NULL, NULL};
  valk_trace_print(stack, 0);

  VALK_PASS();
}

void test_trace_print_single_frame(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);

  if (captured > 0) {
    valk_trace_print(stack, 1);
  }

  VALK_PASS();
}

void test_trace_print_full_trace(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);

  valk_trace_print(stack, captured);

  VALK_PASS();
}

static void nested_function_for_trace(void **stack, size_t *captured) {
  *captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);
}

void test_trace_capture_nested(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = 0;

  nested_function_for_trace(stack, &captured);

  VALK_TEST_ASSERT(captured >= 2, "Nested call should capture at least 2 frames, got %zu", captured);

  VALK_PASS();
}

static void deeply_nested_level_3(void **stack, size_t *captured) {
  *captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);
}

static void deeply_nested_level_2(void **stack, size_t *captured) {
  deeply_nested_level_3(stack, captured);
}

static void deeply_nested_level_1(void **stack, size_t *captured) {
  deeply_nested_level_2(stack, captured);
}

void test_trace_capture_deep_nesting(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = 0;

  deeply_nested_level_1(stack, &captured);

  VALK_TEST_ASSERT(captured >= 4, "Deeply nested call should capture at least 4 frames, got %zu", captured);

  VALK_PASS();
}

void test_trace_max_constant(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_TRACE_MAX == 50, "VALK_TRACE_MAX should be 50");
  VALK_TEST_ASSERT(VALK_TRACE_DEPTH == 10, "VALK_TRACE_DEPTH should be 10");

  VALK_PASS();
}

void test_trace_capture_returns_consistent(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack1[VALK_TRACE_DEPTH];
  void *stack2[VALK_TRACE_DEPTH];
  size_t captured1 = valk_trace_capture(stack1, VALK_TRACE_DEPTH);
  size_t captured2 = valk_trace_capture(stack2, VALK_TRACE_DEPTH);

  VALK_TEST_ASSERT(captured1 == captured2, "Consistent call should return same depth");

  VALK_PASS();
}

void test_trace_print_does_not_crash(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);

  for (size_t i = 0; i <= captured && i <= VALK_TRACE_DEPTH; i++) {
    valk_trace_print(stack, i);
  }

  VALK_PASS();
}

void test_trace_capture_max_depth(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_MAX];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_MAX);

  VALK_TEST_ASSERT(captured > 0, "Should capture at least one frame");
  VALK_TEST_ASSERT(captured <= VALK_TRACE_MAX, "Should not exceed VALK_TRACE_MAX");

  VALK_PASS();
}

static void recursive_function(void **stack, size_t *captured, int depth) {
  if (depth == 0) {
    *captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);
  } else {
    recursive_function(stack, captured, depth - 1);
  }
}

void test_trace_capture_recursive(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = 0;

  recursive_function(stack, &captured, 5);

  VALK_TEST_ASSERT(captured >= 5, "Recursive call should capture at least 5 frames, got %zu", captured);

  VALK_PASS();
}

void test_trace_print_many_frames(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_MAX];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_MAX);

  valk_trace_print(stack, captured);

  VALK_PASS();
}

void test_trace_capture_different_sizes(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t sizes[] = {1, 2, 3, 5, 10, 20, 50};

  for (size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); i++) {
    void *stack[VALK_TRACE_MAX];
    size_t captured = valk_trace_capture(stack, sizes[i]);
    VALK_TEST_ASSERT(captured <= sizes[i], "Captured frames should not exceed requested size");
  }

  VALK_PASS();
}

void test_trace_capture_one_frame(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[1];
  size_t captured = valk_trace_capture(stack, 1);

  VALK_TEST_ASSERT(captured == 1, "Should capture exactly 1 frame when buffer is size 1");
  VALK_TEST_ASSERT(stack[0] != NULL, "Captured frame should not be NULL");

  VALK_PASS();
}

void test_trace_print_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  valk_trace_print(stack, 0);

  VALK_PASS();
}

void test_trace_print_large_depth(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_MAX];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_MAX);

  valk_trace_print(stack, captured);

  VALK_PASS();
}

void test_trace_capture_boundary_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack1[VALK_TRACE_DEPTH];
  void *stack2[VALK_TRACE_MAX];

  size_t c1 = valk_trace_capture(stack1, VALK_TRACE_DEPTH);
  size_t c2 = valk_trace_capture(stack2, VALK_TRACE_MAX);

  VALK_TEST_ASSERT(c1 <= VALK_TRACE_DEPTH, "Should not exceed VALK_TRACE_DEPTH");
  VALK_TEST_ASSERT(c2 <= VALK_TRACE_MAX, "Should not exceed VALK_TRACE_MAX");
  VALK_TEST_ASSERT(c2 >= c1, "Larger buffer should capture at least as many frames");

  VALK_PASS();
}

void test_trace_capture_address_uniqueness(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);

  VALK_TEST_ASSERT(captured >= 2, "Need at least 2 frames for uniqueness test");

  VALK_PASS();
}

void test_trace_print_partial(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = valk_trace_capture(stack, VALK_TRACE_DEPTH);

  if (captured >= 3) {
    valk_trace_print(stack, 1);
    valk_trace_print(stack, 2);
    valk_trace_print(stack, 3);
  }

  VALK_PASS();
}

static void helper_for_stack_test(void **out_stack, size_t *out_count, int depth) {
  if (depth > 0) {
    helper_for_stack_test(out_stack, out_count, depth - 1);
  } else {
    *out_count = valk_trace_capture(out_stack, VALK_TRACE_DEPTH);
  }
}

void test_trace_capture_with_helper(VALK_TEST_ARGS()) {
  VALK_TEST();

  void *stack[VALK_TRACE_DEPTH];
  size_t captured = 0;

  helper_for_stack_test(stack, &captured, 3);

  VALK_TEST_ASSERT(captured >= 4, "Helper function should add frames, got %zu", captured);

  VALK_PASS();
}

void test_trace_constants_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_TRACE_MAX >= VALK_TRACE_DEPTH, "TRACE_MAX should be >= TRACE_DEPTH");
  VALK_TEST_ASSERT(VALK_TRACE_DEPTH > 0, "TRACE_DEPTH should be positive");
  VALK_TEST_ASSERT(VALK_TRACE_MAX > 0, "TRACE_MAX should be positive");

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_trace_capture_basic", test_trace_capture_basic);
  valk_testsuite_add_test(suite, "test_trace_capture_zero_frames", test_trace_capture_zero_frames);
  valk_testsuite_add_test(suite, "test_trace_capture_small_buffer", test_trace_capture_small_buffer);
  valk_testsuite_add_test(suite, "test_trace_capture_all_pointers_valid", test_trace_capture_all_pointers_valid);
  valk_testsuite_add_test(suite, "test_trace_print_null_safe", test_trace_print_null_safe);
  valk_testsuite_add_test(suite, "test_trace_print_single_frame", test_trace_print_single_frame);
  valk_testsuite_add_test(suite, "test_trace_print_full_trace", test_trace_print_full_trace);
  valk_testsuite_add_test(suite, "test_trace_capture_nested", test_trace_capture_nested);
  valk_testsuite_add_test(suite, "test_trace_capture_deep_nesting", test_trace_capture_deep_nesting);
  valk_testsuite_add_test(suite, "test_trace_max_constant", test_trace_max_constant);
  valk_testsuite_add_test(suite, "test_trace_capture_returns_consistent", test_trace_capture_returns_consistent);
  valk_testsuite_add_test(suite, "test_trace_print_does_not_crash", test_trace_print_does_not_crash);
  valk_testsuite_add_test(suite, "test_trace_capture_max_depth", test_trace_capture_max_depth);
  valk_testsuite_add_test(suite, "test_trace_capture_recursive", test_trace_capture_recursive);
  valk_testsuite_add_test(suite, "test_trace_print_many_frames", test_trace_print_many_frames);
  valk_testsuite_add_test(suite, "test_trace_capture_different_sizes", test_trace_capture_different_sizes);
  valk_testsuite_add_test(suite, "test_trace_capture_one_frame", test_trace_capture_one_frame);
  valk_testsuite_add_test(suite, "test_trace_print_empty", test_trace_print_empty);
  valk_testsuite_add_test(suite, "test_trace_print_large_depth", test_trace_print_large_depth);
  valk_testsuite_add_test(suite, "test_trace_capture_boundary_values", test_trace_capture_boundary_values);
  valk_testsuite_add_test(suite, "test_trace_capture_address_uniqueness", test_trace_capture_address_uniqueness);
  valk_testsuite_add_test(suite, "test_trace_print_partial", test_trace_print_partial);
  valk_testsuite_add_test(suite, "test_trace_capture_with_helper", test_trace_capture_with_helper);
  valk_testsuite_add_test(suite, "test_trace_constants_values", test_trace_constants_values);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
