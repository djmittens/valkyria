#include "../testing.h"
#include "../../src/aio_conn_buffer.h"
#include "../../src/memory.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_init_zeroes_counters(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  buf.encrypted_len = 999;
  buf.encrypted_consumed = 888;
  buf.decrypted_len = 777;
  buf.decrypted_consumed = 666;

  valk_conn_read_buf_init(&buf);

  ASSERT_EQ(buf.encrypted_len, 0);
  ASSERT_EQ(buf.encrypted_consumed, 0);
  ASSERT_EQ(buf.decrypted_len, 0);
  ASSERT_EQ(buf.decrypted_consumed, 0);

  VALK_PASS();
}

void test_encrypted_ptr_returns_buffer_start(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  size_t available;
  uint8_t *ptr = valk_conn_read_buf_get_encrypted_ptr(&buf, &available);

  ASSERT_NOT_NULL(ptr);
  ASSERT_EQ(ptr, buf.encrypted);
  ASSERT_EQ(available, VALK_CONN_ENCRYPTED_SIZE);

  VALK_PASS();
}

void test_encrypted_ptr_advances_after_commit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  size_t available;
  valk_conn_read_buf_get_encrypted_ptr(&buf, &available);
  ASSERT_EQ(available, VALK_CONN_ENCRYPTED_SIZE);

  valk_conn_read_buf_commit_encrypted(&buf, 1000);

  uint8_t *ptr = valk_conn_read_buf_get_encrypted_ptr(&buf, &available);
  ASSERT_NOT_NULL(ptr);
  ASSERT_EQ(ptr, buf.encrypted + 1000);
  ASSERT_EQ(available, VALK_CONN_ENCRYPTED_SIZE - 1000);

  VALK_PASS();
}

void test_encrypted_ptr_null_when_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  valk_conn_read_buf_commit_encrypted(&buf, VALK_CONN_ENCRYPTED_SIZE);

  size_t available;
  uint8_t *ptr = valk_conn_read_buf_get_encrypted_ptr(&buf, &available);

  ASSERT_NULL(ptr);
  ASSERT_EQ(available, 0);

  VALK_PASS();
}

void test_commit_updates_len(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  ASSERT_EQ(buf.encrypted_len, 0);

  valk_conn_read_buf_commit_encrypted(&buf, 500);
  ASSERT_EQ(buf.encrypted_len, 500);

  valk_conn_read_buf_commit_encrypted(&buf, 300);
  ASSERT_EQ(buf.encrypted_len, 800);

  VALK_PASS();
}

void test_get_encrypted_returns_correct_slice(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  memset(buf.encrypted, 'A', 100);
  buf.encrypted_len = 100;

  size_t len;
  const uint8_t *data = valk_conn_read_buf_get_encrypted(&buf, &len);

  ASSERT_NOT_NULL(data);
  ASSERT_EQ(len, 100);
  ASSERT_EQ(data[0], 'A');
  ASSERT_EQ(data[99], 'A');

  VALK_PASS();
}

void test_consume_encrypted_advances_consumed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  buf.encrypted_len = 1000;

  valk_conn_read_buf_consume_encrypted(&buf, 200);
  ASSERT_EQ(buf.encrypted_consumed, 200);

  size_t len;
  const uint8_t *data = valk_conn_read_buf_get_encrypted(&buf, &len);
  ASSERT_EQ(data, buf.encrypted + 200);
  ASSERT_EQ(len, 800);

  VALK_PASS();
}

void test_decrypted_ptr_returns_buffer_start(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  size_t available;
  uint8_t *ptr = valk_conn_read_buf_get_decrypted_ptr(&buf, &available);

  ASSERT_NOT_NULL(ptr);
  ASSERT_EQ(ptr, buf.decrypted);
  ASSERT_EQ(available, VALK_CONN_DECRYPTED_SIZE);

  VALK_PASS();
}

void test_decrypted_commit_updates_len(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  ASSERT_EQ(buf.decrypted_len, 0);

  valk_conn_read_buf_commit_decrypted(&buf, 700);
  ASSERT_EQ(buf.decrypted_len, 700);

  VALK_PASS();
}

void test_get_decrypted_returns_correct_slice(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  memset(buf.decrypted, 'B', 200);
  buf.decrypted_len = 200;

  size_t len;
  const uint8_t *data = valk_conn_read_buf_get_decrypted(&buf, &len);

  ASSERT_NOT_NULL(data);
  ASSERT_EQ(len, 200);
  ASSERT_EQ(data[0], 'B');

  VALK_PASS();
}

void test_consume_decrypted_advances_consumed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  buf.decrypted_len = 500;

  valk_conn_read_buf_consume_decrypted(&buf, 150);
  ASSERT_EQ(buf.decrypted_consumed, 150);

  size_t len;
  const uint8_t *data = valk_conn_read_buf_get_decrypted(&buf, &len);
  ASSERT_EQ(data, buf.decrypted + 150);
  ASSERT_EQ(len, 350);

  VALK_PASS();
}

void test_compact_moves_unconsumed_to_start(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  for (int i = 0; i < 100; i++) {
    buf.encrypted[i] = (uint8_t)('A' + (i % 26));
  }
  buf.encrypted_len = 100;
  buf.encrypted_consumed = 50;

  for (int i = 0; i < 80; i++) {
    buf.decrypted[i] = (uint8_t)('a' + (i % 26));
  }
  buf.decrypted_len = 80;
  buf.decrypted_consumed = 30;

  valk_conn_read_buf_compact(&buf);

  ASSERT_EQ(buf.encrypted_len, 50);
  ASSERT_EQ(buf.encrypted_consumed, 0);
  ASSERT_EQ(buf.encrypted[0], 'A' + (50 % 26));

  ASSERT_EQ(buf.decrypted_len, 50);
  ASSERT_EQ(buf.decrypted_consumed, 0);
  ASSERT_EQ(buf.decrypted[0], 'a' + (30 % 26));

  VALK_PASS();
}

void test_compact_resets_counters(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  buf.encrypted_len = 100;
  buf.encrypted_consumed = 100;
  buf.decrypted_len = 50;
  buf.decrypted_consumed = 50;

  valk_conn_read_buf_compact(&buf);

  ASSERT_EQ(buf.encrypted_len, 0);
  ASSERT_EQ(buf.encrypted_consumed, 0);
  ASSERT_EQ(buf.decrypted_len, 0);
  ASSERT_EQ(buf.decrypted_consumed, 0);

  VALK_PASS();
}

void test_full_cycle_encrypt_decrypt(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  size_t available;
  uint8_t *write_ptr = valk_conn_read_buf_get_encrypted_ptr(&buf, &available);
  ASSERT_NOT_NULL(write_ptr);

  memcpy(write_ptr, "encrypted data here", 19);
  valk_conn_read_buf_commit_encrypted(&buf, 19);

  size_t encrypted_len;
  const uint8_t *encrypted = valk_conn_read_buf_get_encrypted(&buf, &encrypted_len);
  ASSERT_EQ(encrypted_len, 19);

  valk_conn_read_buf_consume_encrypted(&buf, 19);

  uint8_t *decrypt_ptr = valk_conn_read_buf_get_decrypted_ptr(&buf, &available);
  memcpy(decrypt_ptr, "decrypted data here", 19);
  valk_conn_read_buf_commit_decrypted(&buf, 19);

  size_t decrypted_len;
  const uint8_t *decrypted = valk_conn_read_buf_get_decrypted(&buf, &decrypted_len);
  ASSERT_EQ(decrypted_len, 19);
  ASSERT_EQ(memcmp(decrypted, "decrypted data here", 19), 0);

  valk_conn_read_buf_consume_decrypted(&buf, 19);

  size_t remaining;
  valk_conn_read_buf_get_decrypted(&buf, &remaining);
  ASSERT_EQ(remaining, 0);

  VALK_PASS();
}

void test_partial_consume_then_more_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  size_t available;
  uint8_t *ptr = valk_conn_read_buf_get_encrypted_ptr(&buf, &available);
  memcpy(ptr, "AAAAAABBBBBB", 12);
  valk_conn_read_buf_commit_encrypted(&buf, 12);

  valk_conn_read_buf_consume_encrypted(&buf, 6);

  size_t len;
  const uint8_t *data = valk_conn_read_buf_get_encrypted(&buf, &len);
  ASSERT_EQ(len, 6);
  ASSERT_EQ(memcmp(data, "BBBBBB", 6), 0);

  ptr = valk_conn_read_buf_get_encrypted_ptr(&buf, &available);
  memcpy(ptr, "CCCCCC", 6);
  valk_conn_read_buf_commit_encrypted(&buf, 6);

  ASSERT_EQ(buf.encrypted_len, 18);

  valk_conn_read_buf_compact(&buf);

  ASSERT_EQ(buf.encrypted_len, 12);
  ASSERT_EQ(buf.encrypted_consumed, 0);
  ASSERT_EQ(memcmp(buf.encrypted, "BBBBBBCCCCCC", 12), 0);

  VALK_PASS();
}

void test_available_helpers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  ASSERT_EQ(valk_conn_read_buf_encrypted_available(&buf), 0);
  ASSERT_EQ(valk_conn_read_buf_decrypted_available(&buf), 0);

  buf.encrypted_len = 100;
  buf.encrypted_consumed = 30;
  ASSERT_EQ(valk_conn_read_buf_encrypted_available(&buf), 70);

  buf.decrypted_len = 200;
  buf.decrypted_consumed = 50;
  ASSERT_EQ(valk_conn_read_buf_decrypted_available(&buf), 150);

  VALK_PASS();
}

void test_commit_clamps_to_max(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  buf.encrypted_len = VALK_CONN_ENCRYPTED_SIZE - 10;
  valk_conn_read_buf_commit_encrypted(&buf, 100);
  ASSERT_EQ(buf.encrypted_len, VALK_CONN_ENCRYPTED_SIZE);

  buf.decrypted_len = VALK_CONN_DECRYPTED_SIZE - 5;
  valk_conn_read_buf_commit_decrypted(&buf, 50);
  ASSERT_EQ(buf.decrypted_len, VALK_CONN_DECRYPTED_SIZE);

  VALK_PASS();
}

void test_consume_clamps_to_len(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_conn_read_buf_t buf;
  valk_conn_read_buf_init(&buf);

  buf.encrypted_len = 100;
  valk_conn_read_buf_consume_encrypted(&buf, 200);
  ASSERT_EQ(buf.encrypted_consumed, 100);

  buf.decrypted_len = 50;
  valk_conn_read_buf_consume_decrypted(&buf, 100);
  ASSERT_EQ(buf.decrypted_consumed, 50);

  VALK_PASS();
}

int main(int argc, const char *argv[]) {
  (void)argc;
  (void)argv;

  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_init_zeroes_counters", test_init_zeroes_counters);
  valk_testsuite_add_test(suite, "test_encrypted_ptr_returns_buffer_start", test_encrypted_ptr_returns_buffer_start);
  valk_testsuite_add_test(suite, "test_encrypted_ptr_advances_after_commit", test_encrypted_ptr_advances_after_commit);
  valk_testsuite_add_test(suite, "test_encrypted_ptr_null_when_full", test_encrypted_ptr_null_when_full);
  valk_testsuite_add_test(suite, "test_commit_updates_len", test_commit_updates_len);
  valk_testsuite_add_test(suite, "test_get_encrypted_returns_correct_slice", test_get_encrypted_returns_correct_slice);
  valk_testsuite_add_test(suite, "test_consume_encrypted_advances_consumed", test_consume_encrypted_advances_consumed);
  valk_testsuite_add_test(suite, "test_decrypted_ptr_returns_buffer_start", test_decrypted_ptr_returns_buffer_start);
  valk_testsuite_add_test(suite, "test_decrypted_commit_updates_len", test_decrypted_commit_updates_len);
  valk_testsuite_add_test(suite, "test_get_decrypted_returns_correct_slice", test_get_decrypted_returns_correct_slice);
  valk_testsuite_add_test(suite, "test_consume_decrypted_advances_consumed", test_consume_decrypted_advances_consumed);
  valk_testsuite_add_test(suite, "test_compact_moves_unconsumed_to_start", test_compact_moves_unconsumed_to_start);
  valk_testsuite_add_test(suite, "test_compact_resets_counters", test_compact_resets_counters);
  valk_testsuite_add_test(suite, "test_full_cycle_encrypt_decrypt", test_full_cycle_encrypt_decrypt);
  valk_testsuite_add_test(suite, "test_partial_consume_then_more_data", test_partial_consume_then_more_data);
  valk_testsuite_add_test(suite, "test_available_helpers", test_available_helpers);
  valk_testsuite_add_test(suite, "test_commit_clamps_to_max", test_commit_clamps_to_max);
  valk_testsuite_add_test(suite, "test_consume_clamps_to_len", test_consume_clamps_to_len);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
