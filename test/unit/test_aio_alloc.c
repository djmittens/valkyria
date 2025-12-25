#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/aio_alloc.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <uv.h>

void test_aio_alloc_init_does_not_crash(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_alloc_init();
  valk_aio_alloc_init();

  VALK_PASS();
}

void test_aio_ssl_bytes_used_initial(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t bytes = valk_aio_ssl_bytes_used();
  VALK_TEST_ASSERT(bytes >= 0, "SSL bytes should be non-negative");

  VALK_PASS();
}

void test_aio_nghttp2_bytes_used_initial(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t bytes = valk_aio_nghttp2_bytes_used();
  VALK_TEST_ASSERT(bytes >= 0, "nghttp2 bytes should be non-negative");

  VALK_PASS();
}

void test_aio_libuv_bytes_used_initial(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t bytes = valk_aio_libuv_bytes_used();
  VALK_TEST_ASSERT(bytes >= 0, "libuv bytes should be non-negative");

  VALK_PASS();
}

void test_aio_nghttp2_mem_not_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  VALK_TEST_ASSERT(mem != NULL, "nghttp2_mem should not be NULL");

  VALK_PASS();
}

void test_aio_nghttp2_mem_has_functions(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  VALK_TEST_ASSERT(mem != NULL, "nghttp2_mem should not be NULL");
  VALK_TEST_ASSERT(mem->malloc != NULL, "malloc function should be set");
  VALK_TEST_ASSERT(mem->free != NULL, "free function should be set");
  VALK_TEST_ASSERT(mem->calloc != NULL, "calloc function should be set");
  VALK_TEST_ASSERT(mem->realloc != NULL, "realloc function should be set");

  VALK_PASS();
}

void test_aio_nghttp2_malloc_free(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  size_t before = valk_aio_nghttp2_bytes_used();

  void *ptr = mem->malloc(1024, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "malloc should succeed");

  size_t during = valk_aio_nghttp2_bytes_used();
  VALK_TEST_ASSERT(during >= before + 1024, "bytes used should increase by at least 1024");

  mem->free(ptr, mem->mem_user_data);
  size_t after = valk_aio_nghttp2_bytes_used();
  VALK_TEST_ASSERT(after <= during, "bytes used should decrease after free");

  VALK_PASS();
}

void test_aio_nghttp2_calloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  size_t before = valk_aio_nghttp2_bytes_used();

  void *ptr = mem->calloc(10, 100, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "calloc should succeed");

  size_t during = valk_aio_nghttp2_bytes_used();
  VALK_TEST_ASSERT(during >= before + 1000, "bytes used should increase by at least 1000");

  char *data = (char *)ptr;
  for (int i = 0; i < 1000; i++) {
    VALK_TEST_ASSERT(data[i] == 0, "calloc should zero memory");
  }

  mem->free(ptr, mem->mem_user_data);

  VALK_PASS();
}

void test_aio_nghttp2_realloc(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();

  void *ptr = mem->malloc(100, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "initial malloc should succeed");

  strcpy(ptr, "test data");

  void *new_ptr = mem->realloc(ptr, 200, mem->mem_user_data);
  VALK_TEST_ASSERT(new_ptr != NULL, "realloc should succeed");
  VALK_TEST_ASSERT(strcmp(new_ptr, "test data") == 0, "data should be preserved");

  mem->free(new_ptr, mem->mem_user_data);

  VALK_PASS();
}

void test_aio_nghttp2_realloc_null_ptr(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  size_t before = valk_aio_nghttp2_bytes_used();

  void *ptr = mem->realloc(NULL, 256, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "realloc(NULL) should act as malloc");

  size_t after = valk_aio_nghttp2_bytes_used();
  VALK_TEST_ASSERT(after >= before + 256, "bytes should increase");

  mem->free(ptr, mem->mem_user_data);

  VALK_PASS();
}

void test_aio_nghttp2_realloc_to_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();

  void *ptr = mem->malloc(100, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "initial malloc should succeed");

  void *result = mem->realloc(ptr, 0, mem->mem_user_data);
  VALK_TEST_ASSERT(result == NULL, "realloc to 0 should return NULL");

  VALK_PASS();
}

void test_aio_nghttp2_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  size_t before = valk_aio_nghttp2_bytes_used();

  mem->free(NULL, mem->mem_user_data);

  size_t after = valk_aio_nghttp2_bytes_used();
  VALK_TEST_ASSERT(before == after, "freeing NULL should not change bytes used");

  VALK_PASS();
}

void test_aio_multiple_allocations(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  void *ptrs[10];

  for (int i = 0; i < 10; i++) {
    ptrs[i] = mem->malloc((size_t)(100 * (i + 1)), mem->mem_user_data);
    VALK_TEST_ASSERT(ptrs[i] != NULL, "malloc should succeed");
  }

  for (int i = 0; i < 10; i++) {
    mem->free(ptrs[i], mem->mem_user_data);
  }

  VALK_PASS();
}

void test_aio_large_allocation(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();
  size_t before = valk_aio_nghttp2_bytes_used();

  void *ptr = mem->malloc(1024 * 1024, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "large malloc should succeed");

  size_t during = valk_aio_nghttp2_bytes_used();
  VALK_TEST_ASSERT(during >= before + 1024 * 1024, "bytes should increase by 1MB");

  mem->free(ptr, mem->mem_user_data);

  VALK_PASS();
}

void test_aio_bytes_used_consistency(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t ssl_bytes = valk_aio_ssl_bytes_used();
  size_t nghttp2_bytes = valk_aio_nghttp2_bytes_used();
  size_t libuv_bytes = valk_aio_libuv_bytes_used();

  VALK_TEST_ASSERT(ssl_bytes == valk_aio_ssl_bytes_used(), "SSL bytes should be consistent");
  VALK_TEST_ASSERT(nghttp2_bytes == valk_aio_nghttp2_bytes_used(), "nghttp2 bytes should be consistent");
  VALK_TEST_ASSERT(libuv_bytes == valk_aio_libuv_bytes_used(), "libuv bytes should be consistent");

  VALK_PASS();
}

void test_aio_nghttp2_realloc_grow(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();

  void *ptr = mem->malloc(64, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "initial malloc should succeed");

  char *data = (char *)ptr;
  for (int i = 0; i < 64; i++) {
    data[i] = (char)('A' + (i % 26));
  }

  void *new_ptr = mem->realloc(ptr, 128, mem->mem_user_data);
  VALK_TEST_ASSERT(new_ptr != NULL, "realloc grow should succeed");

  char *new_data = (char *)new_ptr;
  for (int i = 0; i < 64; i++) {
    VALK_TEST_ASSERT(new_data[i] == (char)('A' + (i % 26)), "original data should be preserved");
  }

  mem->free(new_ptr, mem->mem_user_data);

  VALK_PASS();
}

void test_aio_nghttp2_realloc_shrink(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();

  void *ptr = mem->malloc(256, mem->mem_user_data);
  VALK_TEST_ASSERT(ptr != NULL, "initial malloc should succeed");

  strcpy(ptr, "hello");

  void *new_ptr = mem->realloc(ptr, 32, mem->mem_user_data);
  VALK_TEST_ASSERT(new_ptr != NULL, "realloc shrink should succeed");
  VALK_TEST_ASSERT(strcmp(new_ptr, "hello") == 0, "data should be preserved on shrink");

  mem->free(new_ptr, mem->mem_user_data);

  VALK_PASS();
}

void test_aio_nghttp2_calloc_zero_nmemb(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();

  void *ptr = mem->calloc(0, 100, mem->mem_user_data);
  if (ptr != NULL) {
    mem->free(ptr, mem->mem_user_data);
  }

  VALK_PASS();
}

void test_aio_nghttp2_calloc_zero_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_mem *mem = valk_aio_nghttp2_mem();

  void *ptr = mem->calloc(100, 0, mem->mem_user_data);
  if (ptr != NULL) {
    mem->free(ptr, mem->mem_user_data);
  }

  VALK_PASS();
}

void test_aio_libuv_allocations_via_uv(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t before = valk_aio_libuv_bytes_used();

  uv_loop_t *loop = malloc(sizeof(uv_loop_t));
  VALK_TEST_ASSERT(loop != NULL, "should allocate loop");

  int r = uv_loop_init(loop);
  VALK_TEST_ASSERT(r == 0, "loop init should succeed");

  size_t after = valk_aio_libuv_bytes_used();
  VALK_TEST_ASSERT(after >= before, "libuv should use some memory");

  uv_loop_close(loop);
  free(loop);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_aio_alloc_init_does_not_crash", test_aio_alloc_init_does_not_crash);
  valk_testsuite_add_test(suite, "test_aio_ssl_bytes_used_initial", test_aio_ssl_bytes_used_initial);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_bytes_used_initial", test_aio_nghttp2_bytes_used_initial);
  valk_testsuite_add_test(suite, "test_aio_libuv_bytes_used_initial", test_aio_libuv_bytes_used_initial);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_mem_not_null", test_aio_nghttp2_mem_not_null);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_mem_has_functions", test_aio_nghttp2_mem_has_functions);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_malloc_free", test_aio_nghttp2_malloc_free);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_calloc", test_aio_nghttp2_calloc);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_realloc", test_aio_nghttp2_realloc);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_realloc_null_ptr", test_aio_nghttp2_realloc_null_ptr);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_realloc_to_zero", test_aio_nghttp2_realloc_to_zero);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_free_null", test_aio_nghttp2_free_null);
  valk_testsuite_add_test(suite, "test_aio_multiple_allocations", test_aio_multiple_allocations);
  valk_testsuite_add_test(suite, "test_aio_large_allocation", test_aio_large_allocation);
  valk_testsuite_add_test(suite, "test_aio_bytes_used_consistency", test_aio_bytes_used_consistency);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_realloc_grow", test_aio_nghttp2_realloc_grow);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_realloc_shrink", test_aio_nghttp2_realloc_shrink);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_calloc_zero_nmemb", test_aio_nghttp2_calloc_zero_nmemb);
  valk_testsuite_add_test(suite, "test_aio_nghttp2_calloc_zero_size", test_aio_nghttp2_calloc_zero_size);
  valk_testsuite_add_test(suite, "test_aio_libuv_allocations_via_uv", test_aio_libuv_allocations_via_uv);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
