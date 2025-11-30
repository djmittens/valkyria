#include <stdio.h>
#include <stdlib.h>

#include "../src/gc.h"
#include "../src/memory.h"
#include "../src/parser.h"
#include "testing.h"

// Escape analysis tests - placeholder for future implementation
// These tests were removed as part of escape analysis cleanup

void test_escape_placeholder(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Escape analysis tests removed - to be reimplemented");
}

int main(int argc, const char** argv) {
  (void)argc;
  (void)argv;

  // Use GC heap for everything, including test suite
  size_t const GC_THRESHOLD_BYTES = 16 * 1024 * 1024;  // 16 MiB
  valk_gc_malloc_heap_t* gc_heap = valk_gc_malloc_heap_init(GC_THRESHOLD_BYTES);
  valk_thread_ctx.allocator = (void*)gc_heap;

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_escape_placeholder",
                          test_escape_placeholder);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_testsuite_free(suite);

  // Clean up GC heap to avoid memory leaks
  valk_gc_malloc_heap_destroy(gc_heap);

  return res;
}
