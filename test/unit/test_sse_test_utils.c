#include "../testing.h"
#include "../../src/memory.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/aio/sse/sse_test.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_sse_test_create(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);
  ASSERT_EQ(stream->state, VALK_SSE_OPEN);
  ASSERT_NULL(stream->conn);
  ASSERT_NULL(stream->session);
  ASSERT_EQ(stream->queue_len, 0);
  ASSERT_NOT_NULL(stream->pending_data);

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_create_initial_counts(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  ASSERT_EQ(valk_test_sse_bytes_written(stream), 0);
  ASSERT_EQ(valk_test_sse_events_count(stream), 0);

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_test_sse_free(nullptr);

  VALK_PASS();
}

void test_sse_test_capture_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  char *output = valk_test_sse_capture_output(stream);
  ASSERT_NOT_NULL(output);
  ASSERT_STR_EQ(output, "");

  free(output);
  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_capture_single_event(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  int result = valk_test_sse_send_event(stream, "message", "hello", 5, 0);
  ASSERT_EQ(result, 0);

  char *output = valk_test_sse_capture_output(stream);
  ASSERT_NOT_NULL(output);
  ASSERT_STR_CONTAINS(output, "event: message");
  ASSERT_STR_CONTAINS(output, "data: hello");

  ASSERT_EQ(valk_test_sse_events_count(stream), 1);
  ASSERT_GT(valk_test_sse_bytes_written(stream), 0);

  free(output);
  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_capture_multiple_events(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  valk_test_sse_send_event(stream, "ping", "1", 1, 0);
  valk_test_sse_send_event(stream, "pong", "2", 1, 0);
  valk_test_sse_send_event(stream, nullptr, "plain", 5, 0);

  char *output = valk_test_sse_capture_output(stream);
  ASSERT_NOT_NULL(output);
  ASSERT_STR_CONTAINS(output, "event: ping");
  ASSERT_STR_CONTAINS(output, "event: pong");
  ASSERT_STR_CONTAINS(output, "data: 1");
  ASSERT_STR_CONTAINS(output, "data: 2");
  ASSERT_STR_CONTAINS(output, "data: plain");

  ASSERT_EQ(valk_test_sse_events_count(stream), 3);

  free(output);
  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_capture_with_id(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  int result = valk_test_sse_send_event(stream, "update", "data", 4, 42);
  ASSERT_EQ(result, 0);

  char *output = valk_test_sse_capture_output(stream);
  ASSERT_NOT_NULL(output);
  ASSERT_STR_CONTAINS(output, "id: 42");
  ASSERT_STR_CONTAINS(output, "event: update");
  ASSERT_STR_CONTAINS(output, "data: data");

  free(output);
  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_has_event_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  valk_test_sse_send_event(stream, "custom", "payload", 7, 0);

  ASSERT_TRUE(valk_test_sse_has_event(stream, "custom", "payload"));

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_has_event_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  valk_test_sse_send_event(stream, "custom", "payload", 7, 0);

  ASSERT_FALSE(valk_test_sse_has_event(stream, "other", "payload"));
  ASSERT_FALSE(valk_test_sse_has_event(stream, "custom", "other"));
  ASSERT_FALSE(valk_test_sse_has_event(stream, "other", "other"));

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_has_event_null_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  valk_test_sse_send_event(stream, nullptr, "data", 4, 0);

  ASSERT_TRUE(valk_test_sse_has_event(stream, nullptr, "data"));
  ASSERT_FALSE(valk_test_sse_has_event(stream, "message", "data"));

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_reset_capture(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  valk_test_sse_send_event(stream, "test", "data", 4, 0);
  ASSERT_EQ(valk_test_sse_events_count(stream), 1);
  ASSERT_GT(valk_test_sse_bytes_written(stream), 0);

  valk_test_sse_reset_capture(stream);

  ASSERT_EQ(valk_test_sse_events_count(stream), 0);
  ASSERT_EQ(valk_test_sse_bytes_written(stream), 0);

  char *output = valk_test_sse_capture_output(stream);
  ASSERT_NOT_NULL(output);
  ASSERT_STR_EQ(output, "");

  ASSERT_FALSE(valk_test_sse_has_event(stream, "test", "data"));

  free(output);
  valk_test_sse_free(stream);
  VALK_PASS();
}

static bool g_drain_called = false;
static void test_drain_callback(valk_sse_stream_t *stream, void *user_data) {
  (void)stream;
  (void)user_data;
  g_drain_called = true;
}

void test_sse_test_simulate_drain(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  g_drain_called = false;
  stream->on_drain = test_drain_callback;

  valk_test_sse_simulate_drain(stream);

  ASSERT_TRUE(g_drain_called);

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_simulate_drain_no_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  stream->on_drain = nullptr;

  valk_test_sse_simulate_drain(stream);

  valk_test_sse_free(stream);
  VALK_PASS();
}

static bool g_close_called = false;
static void test_close_callback(valk_sse_stream_t *stream, void *user_data) {
  (void)stream;
  (void)user_data;
  g_close_called = true;
}

void test_sse_test_simulate_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  g_close_called = false;
  stream->on_close = test_close_callback;

  ASSERT_EQ(stream->state, VALK_SSE_OPEN);

  valk_test_sse_simulate_close(stream);

  ASSERT_EQ(stream->state, VALK_SSE_CLOSED);
  ASSERT_TRUE(g_close_called);

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_simulate_close_no_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  stream->on_close = nullptr;

  valk_test_sse_simulate_close(stream);

  ASSERT_EQ(stream->state, VALK_SSE_CLOSED);

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_send_to_closed_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  valk_test_sse_simulate_close(stream);

  int result = valk_test_sse_send_event(stream, "test", "data", 4, 0);
  ASSERT_EQ(result, -1);

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_send_null_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  int result = valk_test_sse_send_event(stream, "test", nullptr, 0, 0);
  ASSERT_EQ(result, -1);

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_bytes_written_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t result = valk_test_sse_bytes_written(nullptr);
  ASSERT_EQ(result, 0);

  VALK_PASS();
}

void test_sse_test_events_count_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t result = valk_test_sse_events_count(nullptr);
  ASSERT_EQ(result, 0);

  VALK_PASS();
}

void test_sse_test_capture_output_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  char *result = valk_test_sse_capture_output(nullptr);
  ASSERT_NULL(result);

  VALK_PASS();
}

void test_sse_test_reset_capture_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_test_sse_reset_capture(nullptr);

  VALK_PASS();
}

void test_sse_test_has_event_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool result = valk_test_sse_has_event(nullptr, "type", "data");
  ASSERT_FALSE(result);

  VALK_PASS();
}

void test_sse_test_simulate_drain_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_test_sse_simulate_drain(nullptr);

  VALK_PASS();
}

void test_sse_test_simulate_close_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_test_sse_simulate_close(nullptr);

  VALK_PASS();
}

void test_sse_test_large_event(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  char large_data[8192];
  memset(large_data, 'X', sizeof(large_data) - 1);
  large_data[sizeof(large_data) - 1] = '\0';

  int result = valk_test_sse_send_event(stream, "big", large_data, strlen(large_data), 0);
  ASSERT_EQ(result, 0);

  ASSERT_EQ(valk_test_sse_events_count(stream), 1);
  ASSERT_GT(valk_test_sse_bytes_written(stream), 8000);

  ASSERT_TRUE(valk_test_sse_has_event(stream, "big", large_data));

  valk_test_sse_free(stream);
  VALK_PASS();
}

void test_sse_test_stream_stats_updated(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_test_sse_create();
  ASSERT_NOT_NULL(stream);

  ASSERT_EQ(stream->events_sent, 0);
  ASSERT_EQ(stream->bytes_sent, 0);

  valk_test_sse_send_event(stream, "test", "data", 4, 0);

  ASSERT_EQ(stream->events_sent, 1);
  ASSERT_GT(stream->bytes_sent, 0);

  valk_test_sse_free(stream);
  VALK_PASS();
}

#else

void test_sse_test_utils_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("SSE test utils require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_sse_test_create", test_sse_test_create);
  valk_testsuite_add_test(suite, "test_sse_test_create_initial_counts", test_sse_test_create_initial_counts);
  valk_testsuite_add_test(suite, "test_sse_test_free_null", test_sse_test_free_null);
  valk_testsuite_add_test(suite, "test_sse_test_capture_empty", test_sse_test_capture_empty);
  valk_testsuite_add_test(suite, "test_sse_test_capture_single_event", test_sse_test_capture_single_event);
  valk_testsuite_add_test(suite, "test_sse_test_capture_multiple_events", test_sse_test_capture_multiple_events);
  valk_testsuite_add_test(suite, "test_sse_test_capture_with_id", test_sse_test_capture_with_id);
  valk_testsuite_add_test(suite, "test_sse_test_has_event_found", test_sse_test_has_event_found);
  valk_testsuite_add_test(suite, "test_sse_test_has_event_not_found", test_sse_test_has_event_not_found);
  valk_testsuite_add_test(suite, "test_sse_test_has_event_null_type", test_sse_test_has_event_null_type);
  valk_testsuite_add_test(suite, "test_sse_test_reset_capture", test_sse_test_reset_capture);
  valk_testsuite_add_test(suite, "test_sse_test_simulate_drain", test_sse_test_simulate_drain);
  valk_testsuite_add_test(suite, "test_sse_test_simulate_drain_no_callback", test_sse_test_simulate_drain_no_callback);
  valk_testsuite_add_test(suite, "test_sse_test_simulate_close", test_sse_test_simulate_close);
  valk_testsuite_add_test(suite, "test_sse_test_simulate_close_no_callback", test_sse_test_simulate_close_no_callback);
  valk_testsuite_add_test(suite, "test_sse_test_send_to_closed_stream", test_sse_test_send_to_closed_stream);
  valk_testsuite_add_test(suite, "test_sse_test_send_null_data", test_sse_test_send_null_data);
  valk_testsuite_add_test(suite, "test_sse_test_bytes_written_null", test_sse_test_bytes_written_null);
  valk_testsuite_add_test(suite, "test_sse_test_events_count_null", test_sse_test_events_count_null);
  valk_testsuite_add_test(suite, "test_sse_test_capture_output_null", test_sse_test_capture_output_null);
  valk_testsuite_add_test(suite, "test_sse_test_reset_capture_null", test_sse_test_reset_capture_null);
  valk_testsuite_add_test(suite, "test_sse_test_has_event_null", test_sse_test_has_event_null);
  valk_testsuite_add_test(suite, "test_sse_test_simulate_drain_null", test_sse_test_simulate_drain_null);
  valk_testsuite_add_test(suite, "test_sse_test_simulate_close_null", test_sse_test_simulate_close_null);
  valk_testsuite_add_test(suite, "test_sse_test_large_event", test_sse_test_large_event);
  valk_testsuite_add_test(suite, "test_sse_test_stream_stats_updated", test_sse_test_stream_stats_updated);
#else
  valk_testsuite_add_test(suite, "test_sse_test_utils_disabled", test_sse_test_utils_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
