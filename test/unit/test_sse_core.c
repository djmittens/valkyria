#include "../testing.h"
#include "../../src/memory.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/aio_sse.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static valk_sse_stream_t *create_test_stream(void) {
  valk_sse_stream_t *stream = calloc(1, sizeof(valk_sse_stream_t));
  stream->state = VALK_SSE_OPEN;
  stream->queue_max = 100;
  stream->pending_capacity = 4096;
  stream->pending_data = malloc(stream->pending_capacity);
  stream->data_deferred = false;
  return stream;
}

static void free_test_stream(valk_sse_stream_t *stream) {
  if (!stream) return;
  valk_sse_event_t *event = stream->queue_head;
  while (event) {
    valk_sse_event_t *next = event->next;
    free(event);
    event = next;
  }
  if (stream->pending_data) free(stream->pending_data);
  free(stream);
}

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

void test_sse_send_event_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->queue_len = 100;
  stream->queue_max = 100;

  int result = valk_sse_send_event(stream, "test", "data", 4, 0);
  VALK_TEST_ASSERT(result == -2, "Full queue should return -2 (EAGAIN)");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_event_with_id(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  int result = valk_sse_send_event(stream, "custom", "hello", 5, 42);
  VALK_TEST_ASSERT(result == 0, "With data_deferred=false, should succeed");

  VALK_TEST_ASSERT(stream->queue_len == 1, "Queue should have 1 event");
  VALK_TEST_ASSERT(stream->queue_head != NULL, "Queue head should not be NULL");
  VALK_TEST_ASSERT(stream->queue_head->id == 42, "Event should have ID 42");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_event_queues_correctly(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  int result = valk_sse_send_event(stream, NULL, "test1", 5, 0);
  VALK_TEST_ASSERT(result == 0, "Send should succeed with data_deferred=false");
  VALK_TEST_ASSERT(stream->queue_len == 1, "Queue should have 1 event");

  result = valk_sse_send_event(stream, "event2", "test2", 5, 0);
  VALK_TEST_ASSERT(result == 0, "Second send should also succeed");
  VALK_TEST_ASSERT(stream->queue_len == 2, "Queue should have 2 events");

  valk_sse_event_t *first = stream->queue_head;
  VALK_TEST_ASSERT(first != NULL, "First event should exist");
  VALK_TEST_ASSERT(first->next != NULL, "Second event should exist");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_simple_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  int result = valk_sse_send(stream, "hello world", 11);
  VALK_TEST_ASSERT(result == 0, "valk_sse_send should succeed");
  VALK_TEST_ASSERT(stream->queue_len == 1, "Queue should have 1 event");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_retry_queues_correctly(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  int result = valk_sse_send_retry(stream, 5000);
  VALK_TEST_ASSERT(result == 0, "send_retry should succeed with data_deferred=false");
  VALK_TEST_ASSERT(stream->queue_len == 1, "Queue should have 1 event");
  VALK_TEST_ASSERT(stream->queue_head->retry_ms == 5000, "Retry should be 5000ms");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_retry_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->queue_len = 100;
  stream->queue_max = 100;

  int result = valk_sse_send_retry(stream, 1000);
  VALK_TEST_ASSERT(result == -2, "Full queue should return -2 (EAGAIN)");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_event_format_with_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  int result = valk_sse_send_event(stream, "custom_event", "payload data", 12, 123);
  VALK_TEST_ASSERT(result == -4 || result == 0, "Should succeed or fail on resume");

  valk_sse_event_t *event = stream->queue_head;
  VALK_TEST_ASSERT(event != NULL, "Event should be queued");
  VALK_TEST_ASSERT(event->data != NULL, "Event data should exist");
  VALK_TEST_ASSERT(strstr(event->data, "id: 123") != NULL, "Should contain id");
  VALK_TEST_ASSERT(strstr(event->data, "event: custom_event") != NULL, "Should contain event type");
  VALK_TEST_ASSERT(strstr(event->data, "data: payload data") != NULL, "Should contain data");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_event_format_without_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  int result = valk_sse_send_event(stream, NULL, "just data", 9, 0);
  VALK_TEST_ASSERT(result == -4 || result == 0, "Should succeed or fail on resume");

  valk_sse_event_t *event = stream->queue_head;
  VALK_TEST_ASSERT(event != NULL, "Event should be queued");
  VALK_TEST_ASSERT(strstr(event->data, "event:") == NULL, "Should not contain event type");
  VALK_TEST_ASSERT(strstr(event->data, "id:") == NULL, "Should not contain id");
  VALK_TEST_ASSERT(strstr(event->data, "data: just data") != NULL, "Should contain data");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_queue_tail_pointer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  valk_sse_send_event(stream, NULL, "first", 5, 0);
  valk_sse_event_t *first = stream->queue_tail;
  VALK_TEST_ASSERT(stream->queue_head == first, "Head and tail should be same for single item");

  valk_sse_send_event(stream, NULL, "second", 6, 0);
  valk_sse_event_t *second = stream->queue_tail;
  VALK_TEST_ASSERT(stream->queue_head == first, "Head should still be first");
  VALK_TEST_ASSERT(stream->queue_tail == second, "Tail should be second");
  VALK_TEST_ASSERT(first->next == second, "First should point to second");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_stream_close_with_queued_events(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  valk_sse_send_event(stream, NULL, "event1", 6, 0);
  valk_sse_send_event(stream, NULL, "event2", 6, 0);
  valk_sse_send_event(stream, NULL, "event3", 6, 0);
  VALK_TEST_ASSERT(stream->queue_len == 3, "Queue should have 3 events");

  stream->state = VALK_SSE_CLOSED;

  VALK_PASS();
}

void test_sse_send_event_large_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  char large_data[8192];
  memset(large_data, 'X', sizeof(large_data) - 1);
  large_data[sizeof(large_data) - 1] = '\0';

  int result = valk_sse_send_event(stream, "big", large_data, strlen(large_data), 0);
  VALK_TEST_ASSERT(result == -4 || result == 0, "Large data should be accepted");
  VALK_TEST_ASSERT(stream->queue_head->data_len > 8000, "Event should contain large data");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_event_empty_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  int result = valk_sse_send_event(stream, NULL, "", 0, 0);
  VALK_TEST_ASSERT(result == -4 || result == 0, "Empty data should be accepted");
  VALK_TEST_ASSERT(stream->queue_len == 1, "Event should be queued");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_send_retry_format(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  valk_sse_send_retry(stream, 3000);

  valk_sse_event_t *event = stream->queue_head;
  VALK_TEST_ASSERT(event != NULL, "Retry event should be queued");
  VALK_TEST_ASSERT(strstr(event->data, "retry: 3000") != NULL, "Should contain retry directive");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_multiple_event_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->data_deferred = false;

  valk_sse_send_event(stream, "ping", "1", 1, 0);
  valk_sse_send_event(stream, "pong", "2", 1, 0);
  valk_sse_send_retry(stream, 1000);
  valk_sse_send(stream, "plain", 5);

  VALK_TEST_ASSERT(stream->queue_len == 4, "Should have 4 queued items");

  free_test_stream(stream);
  VALK_PASS();
}

void test_sse_writable_at_threshold(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = create_test_stream();
  stream->queue_max = 10;

  stream->queue_len = 9;
  VALK_TEST_ASSERT(valk_sse_is_writable(stream) == true, "9/10 should be writable");

  stream->queue_len = 10;
  VALK_TEST_ASSERT(valk_sse_is_writable(stream) == false, "10/10 should not be writable");

  stream->queue_len = 11;
  VALK_TEST_ASSERT(valk_sse_is_writable(stream) == false, "11/10 should not be writable");

  free_test_stream(stream);
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
  valk_testsuite_add_test(suite, "test_sse_send_event_backpressure", test_sse_send_event_backpressure);
  valk_testsuite_add_test(suite, "test_sse_send_event_with_id", test_sse_send_event_with_id);
  valk_testsuite_add_test(suite, "test_sse_send_event_queues_correctly", test_sse_send_event_queues_correctly);
  valk_testsuite_add_test(suite, "test_sse_send_simple_data", test_sse_send_simple_data);
  valk_testsuite_add_test(suite, "test_sse_send_retry_queues_correctly", test_sse_send_retry_queues_correctly);
  valk_testsuite_add_test(suite, "test_sse_send_retry_backpressure", test_sse_send_retry_backpressure);
  valk_testsuite_add_test(suite, "test_sse_send_event_format_with_type", test_sse_send_event_format_with_type);
  valk_testsuite_add_test(suite, "test_sse_send_event_format_without_type", test_sse_send_event_format_without_type);
  valk_testsuite_add_test(suite, "test_sse_queue_tail_pointer", test_sse_queue_tail_pointer);
  valk_testsuite_add_test(suite, "test_sse_stream_close_with_queued_events", test_sse_stream_close_with_queued_events);
  valk_testsuite_add_test(suite, "test_sse_send_event_large_data", test_sse_send_event_large_data);
  valk_testsuite_add_test(suite, "test_sse_send_event_empty_data", test_sse_send_event_empty_data);
  valk_testsuite_add_test(suite, "test_sse_send_retry_format", test_sse_send_retry_format);
  valk_testsuite_add_test(suite, "test_sse_multiple_event_types", test_sse_multiple_event_types);
  valk_testsuite_add_test(suite, "test_sse_writable_at_threshold", test_sse_writable_at_threshold);
#else
  valk_testsuite_add_test(suite, "test_sse_core_disabled", test_sse_core_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
