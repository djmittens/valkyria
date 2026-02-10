#include "testing.h"
#include "../src/memory.h"
#include "../src/gc.h"
#include "../src/parser.h"

#include <string.h>
#include <stdlib.h>

void test_2mb_string_concat(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_gc_heap_t *heap = valk_gc_heap_create(64 * 1024 * 1024);
  VALK_TEST_ASSERT(heap != nullptr, "GC heap should be created");

  valk_thread_context_t old_ctx = valk_thread_ctx;
  valk_thread_ctx.allocator = (valk_mem_allocator_t *)heap;
  valk_thread_ctx.heap = heap;

  char kb_buf[1025];
  for (int i = 0; i < 1024; i++) {
    kb_buf[i] = 'A' + (i % 26);
  }
  kb_buf[1024] = '\0';

  valk_lval_t* kb = valk_lval_str(kb_buf);
  VALK_TEST_ASSERT(strlen(kb->str) == 1024, "1KB string should be 1024 bytes");

  size_t kb4_len = 4096;
  char *kb4_buf = malloc(kb4_len + 1);
  for (int i = 0; i < 4; i++) {
    memcpy(kb4_buf + (i * 1024), kb_buf, 1024);
  }
  kb4_buf[kb4_len] = '\0';

  valk_lval_t* kb4 = valk_lval_str(kb4_buf);
  VALK_TEST_ASSERT(LVAL_TYPE(kb4) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(kb4->str) == 4096, "4KB string should be 4096 bytes");

  size_t kb64_len = 65536;
  char *kb64_buf = malloc(kb64_len + 1);
  for (int i = 0; i < 16; i++) {
    memcpy(kb64_buf + (i * 4096), kb4_buf, 4096);
  }
  kb64_buf[kb64_len] = '\0';

  valk_lval_t* kb64 = valk_lval_str(kb64_buf);
  VALK_TEST_ASSERT(LVAL_TYPE(kb64) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(kb64->str) == 65536, "64KB string should be 65536 bytes");

  size_t kb256_len = 262144;
  char *kb256_buf = malloc(kb256_len + 1);
  for (int i = 0; i < 4; i++) {
    memcpy(kb256_buf + (i * 65536), kb64_buf, 65536);
  }
  kb256_buf[kb256_len] = '\0';

  valk_lval_t* kb256 = valk_lval_str(kb256_buf);
  VALK_TEST_ASSERT(LVAL_TYPE(kb256) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(kb256->str) == 262144, "256KB string should be 262144 bytes");

  size_t mb1_len = 1048576;
  char *mb1_buf = malloc(mb1_len + 1);
  for (int i = 0; i < 4; i++) {
    memcpy(mb1_buf + (i * 262144), kb256_buf, 262144);
  }
  mb1_buf[mb1_len] = '\0';

  valk_lval_t* mb1 = valk_lval_str(mb1_buf);
  VALK_TEST_ASSERT(LVAL_TYPE(mb1) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(mb1->str) == 1048576, "1MB string should be 1048576 bytes");

  size_t mb2_len = 2097152;
  char *mb2_buf = malloc(mb2_len + 1);
  memcpy(mb2_buf, mb1_buf, 1048576);
  memcpy(mb2_buf + 1048576, mb1_buf, 1048576);
  mb2_buf[mb2_len] = '\0';

  valk_lval_t* mb2 = valk_lval_str(mb2_buf);
  VALK_TEST_ASSERT(LVAL_TYPE(mb2) == LVAL_STR, "Result should be string");
  VALK_TEST_ASSERT(strlen(mb2->str) == 2097152, "2MB string should be 2097152 bytes");

  printf("SUCCESS: Created 2MB string (%zu bytes)\n", strlen(mb2->str));

  free(kb4_buf);
  free(kb64_buf);
  free(kb256_buf);
  free(mb1_buf);
  free(mb2_buf);

  valk_thread_ctx = old_ctx;
  valk_gc_heap_destroy(heap);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_2mb_string_concat", test_2mb_string_concat);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
