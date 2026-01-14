#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/common.h"
#include "../../src/concurrency.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_arc_box_new(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 64);
  VALK_TEST_ASSERT(box != nullptr, "arc_box_new should return non-nullptr");
  VALK_TEST_ASSERT(box->type == VALK_SUC, "type should be VALK_SUC");
  VALK_TEST_ASSERT(box->refcount == 1, "refcount should be 1");
  VALK_TEST_ASSERT(box->capacity == 64, "capacity should be 64");
  VALK_TEST_ASSERT(box->item != nullptr, "item pointer should be set");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buffer[sizeof(valk_arc_box) + 64];
  valk_arc_box *box = (valk_arc_box *)buffer;
  valk_arc_box_init(box, VALK_ERR, 64);

  VALK_TEST_ASSERT(box->type == VALK_ERR, "type should be VALK_ERR");
  VALK_TEST_ASSERT(box->refcount == 1, "refcount should be 1");
  VALK_TEST_ASSERT(box->capacity == 64, "capacity should be 64");
  VALK_TEST_ASSERT(box->allocator == nullptr, "allocator should be nullptr after init");
  VALK_TEST_ASSERT(box->free == nullptr, "free should be nullptr after init");

  VALK_PASS();
}

void test_arc_box_err(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *msg = "Test error message";
  valk_arc_box *box = valk_arc_box_err(msg);

  VALK_TEST_ASSERT(box != nullptr, "arc_box_err should return non-nullptr");
  VALK_TEST_ASSERT(box->type == VALK_ERR, "type should be VALK_ERR");
  VALK_TEST_ASSERT(box->refcount == 1, "refcount should be 1");
  VALK_TEST_ASSERT(strcmp(box->item, msg) == 0, "item should contain error message");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_retain_release(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 32);
  VALK_TEST_ASSERT(box->refcount == 1, "Initial refcount should be 1");

  valk_arc_retain(box);
  VALK_TEST_ASSERT(box->refcount == 2, "Refcount after retain should be 2");

  valk_arc_retain(box);
  VALK_TEST_ASSERT(box->refcount == 3, "Refcount after second retain should be 3");

  valk_arc_release(box);
  VALK_TEST_ASSERT(box->refcount == 2, "Refcount after release should be 2");

  valk_arc_release(box);
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount after second release should be 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_res_type_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_SUC == 0, "VALK_SUC should be 0");
  VALK_TEST_ASSERT(VALK_ERR == 1, "VALK_ERR should be 1");

  VALK_PASS();
}

void test_arc_box_refcount_boundary(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 16);
  VALK_TEST_ASSERT(box->refcount == 1, "Initial refcount should be 1");

  for (int i = 0; i < 100; i++) {
    valk_arc_retain(box);
  }
  VALK_TEST_ASSERT(box->refcount == 101, "Refcount should be 101");

  for (int i = 0; i < 100; i++) {
    valk_arc_release(box);
  }
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount should be back to 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_with_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 256);

  char *data = (char *)box->item;
  strcpy(data, "Hello, World!");

  VALK_TEST_ASSERT(strcmp(data, "Hello, World!") == 0, "Data should be preserved");
  VALK_TEST_ASSERT(box->capacity == 256, "Capacity should be 256");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_err_empty_message(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_err("");

  VALK_TEST_ASSERT(box != nullptr, "Should create box for empty message");
  VALK_TEST_ASSERT(box->type == VALK_ERR, "Type should be VALK_ERR");
  VALK_TEST_ASSERT(strlen(box->item) == 0, "Message should be empty");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_err_long_message(VALK_TEST_ARGS()) {
  VALK_TEST();

  char long_msg[1024];
  memset(long_msg, 'A', sizeof(long_msg) - 1);
  long_msg[sizeof(long_msg) - 1] = '\0';

  valk_arc_box *box = valk_arc_box_err(long_msg);

  VALK_TEST_ASSERT(box != nullptr, "Should create box for long message");
  VALK_TEST_ASSERT(box->type == VALK_ERR, "Type should be VALK_ERR");
  VALK_TEST_ASSERT(strcmp(box->item, long_msg) == 0, "Message should match");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_zero_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 0);

  VALK_TEST_ASSERT(box != nullptr, "Should create box with zero capacity");
  VALK_TEST_ASSERT(box->capacity == 0, "Capacity should be 0");
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount should be 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_large_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 1024 * 1024);

  VALK_TEST_ASSERT(box != nullptr, "Should create box with large capacity");
  VALK_TEST_ASSERT(box->capacity == 1024 * 1024, "Capacity should be 1MB");
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount should be 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_type_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *suc_box = valk_arc_box_new(VALK_SUC, 16);
  valk_arc_box *err_box = valk_arc_box_new(VALK_ERR, 16);

  VALK_TEST_ASSERT(suc_box->type == VALK_SUC, "Type should be VALK_SUC");
  VALK_TEST_ASSERT(err_box->type == VALK_ERR, "Type should be VALK_ERR");

  valk_arc_release(suc_box);
  valk_arc_release(err_box);

  VALK_PASS();
}

void test_arc_box_item_pointer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 128);

  VALK_TEST_ASSERT(box->item != nullptr, "Item pointer should be set");
  VALK_TEST_ASSERT((char *)box->item > (char *)box, "Item should be after box header");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_retain_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 16);
  VALK_TEST_ASSERT(box != nullptr, "Box should be created");

  valk_arc_retain(box);
  VALK_TEST_ASSERT(box->refcount == 2, "Refcount after retain should be 2");

  valk_arc_release(box);
  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_new_large_allocation(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t large_size = 10 * 1024 * 1024;
  valk_arc_box *box = valk_arc_box_new(VALK_SUC, large_size);

  VALK_TEST_ASSERT(box != nullptr, "Should allocate large box");
  VALK_TEST_ASSERT(box->capacity == large_size, "Capacity should match");

  memset(box->item, 0xAB, large_size);

  valk_arc_release(box);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_arc_box_new", test_arc_box_new);
  valk_testsuite_add_test(suite, "test_arc_box_init", test_arc_box_init);
  valk_testsuite_add_test(suite, "test_arc_box_err", test_arc_box_err);
  valk_testsuite_add_test(suite, "test_arc_retain_release", test_arc_retain_release);
  valk_testsuite_add_test(suite, "test_res_type_enum", test_res_type_enum);
  valk_testsuite_add_test(suite, "test_arc_box_refcount_boundary", test_arc_box_refcount_boundary);
  valk_testsuite_add_test(suite, "test_arc_box_with_data", test_arc_box_with_data);
  valk_testsuite_add_test(suite, "test_arc_box_err_empty_message", test_arc_box_err_empty_message);
  valk_testsuite_add_test(suite, "test_arc_box_err_long_message", test_arc_box_err_long_message);
  valk_testsuite_add_test(suite, "test_arc_box_zero_capacity", test_arc_box_zero_capacity);
  valk_testsuite_add_test(suite, "test_arc_box_large_capacity", test_arc_box_large_capacity);
  valk_testsuite_add_test(suite, "test_arc_box_type_values", test_arc_box_type_values);
  valk_testsuite_add_test(suite, "test_arc_box_item_pointer", test_arc_box_item_pointer);
  valk_testsuite_add_test(suite, "test_arc_retain_null", test_arc_retain_null);
  valk_testsuite_add_test(suite, "test_arc_box_new_large_allocation", test_arc_box_new_large_allocation);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
