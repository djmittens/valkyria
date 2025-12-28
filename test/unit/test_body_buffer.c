#include "../testing.h"
#include "../../src/aio/aio_body_buffer.h"
#include "../../src/memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TEST_ARENA_SIZE (64 * 1024)

static valk_mem_arena_t *create_test_arena(void) {
  size_t size = sizeof(valk_mem_arena_t) + TEST_ARENA_SIZE;
  valk_mem_arena_t *arena = malloc(size);
  valk_mem_arena_init(arena, TEST_ARENA_SIZE);
  return arena;
}

static void free_test_arena(valk_mem_arena_t *arena) {
  free(arena);
}

void test_init_sets_arena(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;

  valk_body_buffer_init(&bb, arena);

  ASSERT_EQ((void*)bb.arena, (void*)arena);
  ASSERT_NULL(bb.data);
  ASSERT_EQ(bb.len, 0);
  ASSERT_EQ(bb.capacity, 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_append_single_chunk(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  u8 data[] = "Hello, World!";
  valk_body_chunk_t chunk = {
    .data = data,
    .len = sizeof(data) - 1,
    .status = VALK_BODY_CONTINUE,
  };

  bool result = valk_body_buffer_append(&bb, &chunk);
  ASSERT_TRUE(result);
  ASSERT_EQ(bb.len, sizeof(data) - 1);

  u64 len;
  const u8 *got = valk_body_buffer_get(&bb, &len);
  ASSERT_NOT_NULL(got);
  ASSERT_EQ(len, sizeof(data) - 1);
  ASSERT_EQ(memcmp(got, data, len), 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_append_multiple_chunks(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  u8 data1[] = "Hello, ";
  u8 data2[] = "World!";

  valk_body_chunk_t chunk1 = { .data = data1, .len = 7, .status = VALK_BODY_CONTINUE };
  valk_body_chunk_t chunk2 = { .data = data2, .len = 6, .status = VALK_BODY_COMPLETE };

  ASSERT_TRUE(valk_body_buffer_append(&bb, &chunk1));
  ASSERT_TRUE(valk_body_buffer_append(&bb, &chunk2));
  ASSERT_EQ(bb.len, 13);

  u64 len;
  const u8 *got = valk_body_buffer_get(&bb, &len);
  ASSERT_EQ(len, 13);
  ASSERT_EQ(memcmp(got, "Hello, World!", 13), 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_append_grows_buffer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  u8 small[] = "A";
  valk_body_chunk_t chunk = { .data = small, .len = 1, .status = VALK_BODY_CONTINUE };

  ASSERT_TRUE(valk_body_buffer_append(&bb, &chunk));
  size_t initial_capacity = bb.capacity;
  ASSERT_GT(initial_capacity, 0);

  u8 large[5000];
  memset(large, 'X', sizeof(large));
  valk_body_chunk_t large_chunk = { .data = large, .len = sizeof(large), .status = VALK_BODY_CONTINUE };

  ASSERT_TRUE(valk_body_buffer_append(&bb, &large_chunk));
  ASSERT_GT(bb.capacity, initial_capacity);
  ASSERT_EQ(bb.len, 1 + sizeof(large));

  free_test_arena(arena);
  VALK_PASS();
}

void test_get_empty_returns_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  u64 len = 999;
  const u8 *got = valk_body_buffer_get(&bb, &len);
  ASSERT_NULL(got);
  ASSERT_EQ(len, 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_reset_keeps_arena(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  u8 data[] = "test data";
  valk_body_chunk_t chunk = { .data = data, .len = 9, .status = VALK_BODY_CONTINUE };
  valk_body_buffer_append(&bb, &chunk);

  ASSERT_EQ(bb.len, 9);

  valk_body_buffer_reset(&bb);

  ASSERT_EQ((void*)bb.arena, (void*)arena);
  ASSERT_EQ(bb.len, 0);
  ASSERT_GT(bb.capacity, 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_append_empty_chunk(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  valk_body_chunk_t empty = { .data = nullptr, .len = 0, .status = VALK_BODY_CONTINUE };
  ASSERT_TRUE(valk_body_buffer_append(&bb, &empty));
  ASSERT_EQ(bb.len, 0);

  u8 data[] = "x";
  valk_body_chunk_t zero_len = { .data = data, .len = 0, .status = VALK_BODY_CONTINUE };
  ASSERT_TRUE(valk_body_buffer_append(&bb, &zero_len));
  ASSERT_EQ(bb.len, 0);

  ASSERT_TRUE(valk_body_buffer_append(&bb, nullptr));
  ASSERT_EQ(bb.len, 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_append_bytes_directly(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  u8 data[] = "direct bytes";
  ASSERT_TRUE(valk_body_buffer_append_bytes(&bb, data, sizeof(data) - 1));
  ASSERT_EQ(bb.len, 12);

  u64 len;
  const u8 *got = valk_body_buffer_get(&bb, &len);
  ASSERT_EQ(len, 12);
  ASSERT_EQ(memcmp(got, "direct bytes", 12), 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_append_bytes_null_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  ASSERT_TRUE(valk_body_buffer_append_bytes(&bb, nullptr, 10));
  ASSERT_EQ(bb.len, 0);

  ASSERT_TRUE(valk_body_buffer_append_bytes(&bb, nullptr, 0));
  ASSERT_EQ(bb.len, 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_get_with_null_len(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  u8 data[] = "test data";
  valk_body_buffer_append_bytes(&bb, data, sizeof(data) - 1);

  const u8 *got = valk_body_buffer_get(&bb, nullptr);
  ASSERT_NOT_NULL(got);
  ASSERT_EQ(memcmp(got, "test data", 9), 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_remaining_calculation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  size_t max_size = 1000;
  ASSERT_EQ(valk_body_buffer_remaining(&bb, max_size), 1000);

  u8 data[500];
  memset(data, 'X', sizeof(data));
  valk_body_buffer_append_bytes(&bb, data, 500);

  ASSERT_EQ(valk_body_buffer_remaining(&bb, max_size), 500);

  valk_body_buffer_append_bytes(&bb, data, 500);
  ASSERT_EQ(valk_body_buffer_remaining(&bb, max_size), 0);

  valk_body_buffer_append_bytes(&bb, data, 100);
  ASSERT_EQ(valk_body_buffer_remaining(&bb, max_size), 0);

  free_test_arena(arena);
  VALK_PASS();
}

void test_large_append_multiple_grows(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mem_arena_t *arena = create_test_arena();
  valk_body_buffer_t bb;
  valk_body_buffer_init(&bb, arena);

  size_t total = 0;
  for (int i = 0; i < 20; i++) {
    u8 chunk_data[1000];
    memset(chunk_data, 'A' + i, sizeof(chunk_data));
    ASSERT_TRUE(valk_body_buffer_append_bytes(&bb, chunk_data, sizeof(chunk_data)));
    total += sizeof(chunk_data);
  }

  ASSERT_EQ(bb.len, total);
  ASSERT_GE(bb.capacity, total);

  u64 len;
  const u8 *data = valk_body_buffer_get(&bb, &len);
  ASSERT_NOT_NULL(data);
  ASSERT_EQ(len, total);

  for (int i = 0; i < 20; i++) {
    ASSERT_EQ(data[i * 1000], 'A' + i);
  }

  free_test_arena(arena);
  VALK_PASS();
}

int main(int argc, const char *argv[]) {
  (void)argc;
  (void)argv;

  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_init_sets_arena", test_init_sets_arena);
  valk_testsuite_add_test(suite, "test_append_single_chunk", test_append_single_chunk);
  valk_testsuite_add_test(suite, "test_append_multiple_chunks", test_append_multiple_chunks);
  valk_testsuite_add_test(suite, "test_append_grows_buffer", test_append_grows_buffer);
  valk_testsuite_add_test(suite, "test_get_empty_returns_null", test_get_empty_returns_null);
  valk_testsuite_add_test(suite, "test_reset_keeps_arena", test_reset_keeps_arena);
  valk_testsuite_add_test(suite, "test_append_empty_chunk", test_append_empty_chunk);
  valk_testsuite_add_test(suite, "test_append_bytes_directly", test_append_bytes_directly);
  valk_testsuite_add_test(suite, "test_append_bytes_null_data", test_append_bytes_null_data);
  valk_testsuite_add_test(suite, "test_get_with_null_len", test_get_with_null_len);
  valk_testsuite_add_test(suite, "test_remaining_calculation", test_remaining_calculation);
  valk_testsuite_add_test(suite, "test_large_append_multiple_grows", test_large_append_multiple_grows);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
