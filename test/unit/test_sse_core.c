#include "../testing.h"
#include "../../src/memory.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/aio_sse.h"

#include <stdio.h>
#include <string.h>

void test_sse_is_writable_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool result = valk_sse_is_writable(nullptr);
  VALK_TEST_ASSERT(result == false, "NULL stream should not be writable");

  VALK_PASS();
}

void test_sse_queue_len_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t len = valk_sse_queue_len(nullptr);
  VALK_TEST_ASSERT(len == 0, "NULL stream should have queue_len 0");

  VALK_PASS();
}

void test_sse_send_null_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send(nullptr, "test", 4);
  VALK_TEST_ASSERT(result == -1, "NULL stream should return -1");

  VALK_PASS();
}

void test_sse_send_null_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_OPEN;

  int result = valk_sse_send(&fake_stream, nullptr, 0);
  VALK_TEST_ASSERT(result == -1, "NULL data should return -1");

  VALK_PASS();
}

void test_sse_send_event_null_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send_event(nullptr, "message", "test", 4, 0);
  VALK_TEST_ASSERT(result == -1, "NULL stream should return -1");

  VALK_PASS();
}

void test_sse_send_event_null_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_OPEN;

  int result = valk_sse_send_event(&fake_stream, "message", nullptr, 0, 0);
  VALK_TEST_ASSERT(result == -1, "NULL data should return -1");

  VALK_PASS();
}

void test_sse_send_retry_null_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send_retry(nullptr, 1000);
  VALK_TEST_ASSERT(result == -1, "NULL stream should return -1");

  VALK_PASS();
}

void test_sse_stream_close_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_close(nullptr);

  VALK_PASS();
}

void test_sse_state_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_SSE_INIT == 0, "INIT should be 0");
  VALK_TEST_ASSERT(VALK_SSE_OPEN == 1, "OPEN should be 1");
  VALK_TEST_ASSERT(VALK_SSE_CLOSING == 2, "CLOSING should be 2");
  VALK_TEST_ASSERT(VALK_SSE_CLOSED == 3, "CLOSED should be 3");

  VALK_PASS();
}

void test_sse_send_closed_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_CLOSED;

  int result = valk_sse_send(&fake_stream, "test", 4);
  VALK_TEST_ASSERT(result == -1, "Closed stream should return -1");

  VALK_PASS();
}

void test_sse_send_event_closed_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_CLOSED;

  int result = valk_sse_send_event(&fake_stream, "message", "test", 4, 0);
  VALK_TEST_ASSERT(result == -1, "Closed stream should return -1");

  VALK_PASS();
}

void test_sse_send_retry_closed_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_CLOSED;

  int result = valk_sse_send_retry(&fake_stream, 1000);
  VALK_TEST_ASSERT(result == -1, "Closed stream should return -1");

  VALK_PASS();
}

void test_sse_is_writable_open_empty_queue(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_OPEN;
  fake_stream.queue_len = 0;
  fake_stream.queue_max = 100;

  bool result = valk_sse_is_writable(&fake_stream);
  VALK_TEST_ASSERT(result == true, "Empty queue should be writable");

  VALK_PASS();
}

void test_sse_is_writable_full_queue(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_OPEN;
  fake_stream.queue_len = 100;
  fake_stream.queue_max = 100;

  bool result = valk_sse_is_writable(&fake_stream);
  VALK_TEST_ASSERT(result == false, "Full queue should not be writable");

  VALK_PASS();
}

void test_sse_is_writable_near_full_queue(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_OPEN;
  fake_stream.queue_len = 99;
  fake_stream.queue_max = 100;

  bool result = valk_sse_is_writable(&fake_stream);
  VALK_TEST_ASSERT(result == true, "Near-full queue should be writable");

  VALK_PASS();
}

void test_sse_queue_len_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.queue_len = 0;

  size_t len = valk_sse_queue_len(&fake_stream);
  VALK_TEST_ASSERT(len == 0, "Empty queue should have len 0");

  VALK_PASS();
}

void test_sse_queue_len_with_items(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.queue_len = 42;

  size_t len = valk_sse_queue_len(&fake_stream);
  VALK_TEST_ASSERT(len == 42, "Queue should have len 42");

  VALK_PASS();
}

void test_sse_stream_new_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;
  valk_sse_stream_t *stream = valk_sse_stream_new(nullptr, nullptr, 1, &data_prd);
  VALK_TEST_ASSERT(stream == nullptr, "NULL conn should return NULL");

  VALK_PASS();
}

void test_sse_stream_new_null_data_prd(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new((valk_aio_handle_t*)0x1, 
                                                   (nghttp2_session*)0x1, 
                                                   1, nullptr);
  VALK_TEST_ASSERT(stream == nullptr, "NULL data_prd should return NULL");

  VALK_PASS();
}

void test_sse_close_already_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_CLOSED;

  valk_sse_stream_close(&fake_stream);

  VALK_TEST_ASSERT(fake_stream.state == VALK_SSE_CLOSED, "State should remain CLOSED");

  VALK_PASS();
}

void test_sse_send_init_state(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_INIT;

  int result = valk_sse_send(&fake_stream, "test", 4);
  VALK_TEST_ASSERT(result == -1, "INIT state stream should return -1");

  VALK_PASS();
}

void test_sse_send_closing_state(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_CLOSING;

  int result = valk_sse_send(&fake_stream, "test", 4);
  VALK_TEST_ASSERT(result == -1, "CLOSING state stream should return -1");

  VALK_PASS();
}

void test_sse_is_writable_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_CLOSED;
  fake_stream.queue_len = 0;
  fake_stream.queue_max = 100;

  bool result = valk_sse_is_writable(&fake_stream);
  VALK_TEST_ASSERT(result == true, "Closed stream with empty queue is technically writable by impl");

  VALK_PASS();
}

void test_sse_queue_len_large_value(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.queue_len = 1000000;

  size_t len = valk_sse_queue_len(&fake_stream);
  VALK_TEST_ASSERT(len == 1000000, "Queue should report large value");

  VALK_PASS();
}

void test_sse_is_writable_zero_max(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t fake_stream = {0};
  fake_stream.state = VALK_SSE_OPEN;
  fake_stream.queue_len = 0;
  fake_stream.queue_max = 0;

  bool result = valk_sse_is_writable(&fake_stream);
  VALK_TEST_ASSERT(result == false, "Zero max queue should not be writable");

  VALK_PASS();
}

#else

void test_sse_core_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("SSE core tests require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_sse_is_writable_null", test_sse_is_writable_null);
  valk_testsuite_add_test(suite, "test_sse_queue_len_null", test_sse_queue_len_null);
  valk_testsuite_add_test(suite, "test_sse_send_null_stream", test_sse_send_null_stream);
  valk_testsuite_add_test(suite, "test_sse_send_null_data", test_sse_send_null_data);
  valk_testsuite_add_test(suite, "test_sse_send_event_null_stream", test_sse_send_event_null_stream);
  valk_testsuite_add_test(suite, "test_sse_send_event_null_data", test_sse_send_event_null_data);
  valk_testsuite_add_test(suite, "test_sse_send_retry_null_stream", test_sse_send_retry_null_stream);
  valk_testsuite_add_test(suite, "test_sse_stream_close_null", test_sse_stream_close_null);
  valk_testsuite_add_test(suite, "test_sse_state_enum", test_sse_state_enum);
  valk_testsuite_add_test(suite, "test_sse_send_closed_stream", test_sse_send_closed_stream);
  valk_testsuite_add_test(suite, "test_sse_send_event_closed_stream", test_sse_send_event_closed_stream);
  valk_testsuite_add_test(suite, "test_sse_send_retry_closed_stream", test_sse_send_retry_closed_stream);
  valk_testsuite_add_test(suite, "test_sse_is_writable_open_empty_queue", test_sse_is_writable_open_empty_queue);
  valk_testsuite_add_test(suite, "test_sse_is_writable_full_queue", test_sse_is_writable_full_queue);
  valk_testsuite_add_test(suite, "test_sse_is_writable_near_full_queue", test_sse_is_writable_near_full_queue);
  valk_testsuite_add_test(suite, "test_sse_queue_len_empty", test_sse_queue_len_empty);
  valk_testsuite_add_test(suite, "test_sse_queue_len_with_items", test_sse_queue_len_with_items);
  valk_testsuite_add_test(suite, "test_sse_stream_new_null_args", test_sse_stream_new_null_args);
  valk_testsuite_add_test(suite, "test_sse_stream_new_null_data_prd", test_sse_stream_new_null_data_prd);
  valk_testsuite_add_test(suite, "test_sse_close_already_closed", test_sse_close_already_closed);
  valk_testsuite_add_test(suite, "test_sse_send_init_state", test_sse_send_init_state);
  valk_testsuite_add_test(suite, "test_sse_send_closing_state", test_sse_send_closing_state);
  valk_testsuite_add_test(suite, "test_sse_is_writable_closed", test_sse_is_writable_closed);
  valk_testsuite_add_test(suite, "test_sse_queue_len_large_value", test_sse_queue_len_large_value);
  valk_testsuite_add_test(suite, "test_sse_is_writable_zero_max", test_sse_is_writable_zero_max);
#else
  valk_testsuite_add_test(suite, "test_sse_core_disabled", test_sse_core_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
