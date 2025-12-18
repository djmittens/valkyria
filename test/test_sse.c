#include "testing.h"
#include "memory.h"
#include "common.h"
#include "aio_sse.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// ============================================================================
// Test Helpers
// ============================================================================

static valk_sse_stream_t *valk_sse_stream_new_for_test(size_t queue_max) {
  valk_sse_stream_t *stream = calloc(1, sizeof(valk_sse_stream_t));
  if (!stream) {
    return NULL;
  }

  stream->state = VALK_SSE_OPEN;
  stream->queue_max = queue_max;
  stream->pending_capacity = 1024;
  stream->pending_data = malloc(stream->pending_capacity);

  if (!stream->pending_data) {
    free(stream);
    return NULL;
  }

  return stream;
}

static void valk_sse_stream_test_free(valk_sse_stream_t *stream) {
  if (!stream) {
    return;
  }

  valk_sse_event_t *event = stream->queue_head;
  while (event) {
    valk_sse_event_t *next = event->next;
    free(event);
    event = next;
  }

  if (stream->pending_data) {
    free(stream->pending_data);
  }

  free(stream);
}

// ============================================================================
// Stream Lifecycle Tests
// ============================================================================

void test_sse_stream_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;
  valk_sse_stream_t *stream = valk_sse_stream_new(NULL, NULL, 1, &data_prd);
  VALK_TEST_ASSERT(stream == NULL, "Should return NULL with invalid arguments");

  VALK_PASS();
}

void test_sse_stream_state_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_close(NULL);

  VALK_PASS();
}

void test_sse_event_queue_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");
  VALK_TEST_ASSERT(stream->queue_len == 0, "Queue should start empty");

  int result = valk_sse_send_event(NULL, "test", "data", 4, 1);
  VALK_TEST_ASSERT(result == -1, "Should reject NULL stream");

  result = valk_sse_send_event(stream, "test", NULL, 4, 1);
  VALK_TEST_ASSERT(result == -1, "Should reject NULL data");

  stream->state = VALK_SSE_CLOSED;
  result = valk_sse_send_event(stream, "test", "data", 4, 1);
  VALK_TEST_ASSERT(result == -1, "Should reject closed stream");

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_sse_event_queue_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(5);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");

  stream->queue_len = 5;

  int result = valk_sse_send_event(stream, "test", "data", 4, 1);
  VALK_TEST_ASSERT(result == -2, "Should return -2 (EAGAIN) when queue full, got %d", result);

  bool writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(!writable, "Stream should not be writable when queue full");

  stream->queue_len = 2;

  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(writable, "Stream should be writable when queue not full");

  size_t len = valk_sse_queue_len(stream);
  VALK_TEST_ASSERT(len == 2, "Queue len should be 2, got %zu", len);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

// ============================================================================
// Backpressure Tests
// ============================================================================

void test_sse_is_writable(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool writable = valk_sse_is_writable(NULL);
  VALK_TEST_ASSERT(!writable, "NULL stream should not be writable");

  size_t len = valk_sse_queue_len(NULL);
  VALK_TEST_ASSERT(len == 0, "NULL stream should return 0 queue len");

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");

  stream->queue_len = 0;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(writable, "Empty queue should be writable");

  stream->queue_len = 5;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(writable, "Partially filled queue should be writable");

  stream->queue_len = 10;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(!writable, "Full queue should not be writable");

  stream->queue_len = 11;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(!writable, "Over-full queue should not be writable");

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

// ============================================================================
// Event Format Tests
// ============================================================================

void test_sse_event_format_manual(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Test SSE format manually (since we can't easily test the actual
  // valk_sse_send_event without a full HTTP/2 setup)

  // Verify format with id, event type, and data
  const char *event_type = "update";
  const char *data = "Hello, SSE!";
  uint64_t id = 42;

  char buf[512];
  int len = snprintf(buf, sizeof(buf), "id: %lu\nevent: %s\ndata: %s\n\n",
                     id, event_type, data);

  VALK_TEST_ASSERT(len > 0, "Failed to format SSE event");
  VALK_TEST_ASSERT(strstr(buf, "id: 42\n") != NULL, "Missing id field");
  VALK_TEST_ASSERT(strstr(buf, "event: update\n") != NULL, "Missing event field");
  VALK_TEST_ASSERT(strstr(buf, "data: Hello, SSE!\n") != NULL, "Missing data field");
  VALK_TEST_ASSERT(strstr(buf, "\n\n") != NULL, "Missing double newline terminator");

  // Verify format without id (id=0)
  len = snprintf(buf, sizeof(buf), "event: %s\ndata: %s\n\n", event_type, data);
  VALK_TEST_ASSERT(len > 0, "Failed to format SSE event without id");
  VALK_TEST_ASSERT(strstr(buf, "id: ") == NULL, "Should not have id field when id=0");
  VALK_TEST_ASSERT(strstr(buf, "event: update\n") != NULL, "Missing event field");

  // Verify format without event type (NULL)
  len = snprintf(buf, sizeof(buf), "data: %s\n\n", data);
  VALK_TEST_ASSERT(len > 0, "Failed to format SSE event without type");
  VALK_TEST_ASSERT(strstr(buf, "event: ") == NULL, "Should not have event field when NULL");
  VALK_TEST_ASSERT(strstr(buf, "data: Hello, SSE!\n") != NULL, "Missing data field");

  // Verify retry format
  uint32_t retry_ms = 5000;
  len = snprintf(buf, sizeof(buf), "retry: %u\n\n", retry_ms);
  VALK_TEST_ASSERT(len > 0, "Failed to format retry directive");
  VALK_TEST_ASSERT(strstr(buf, "retry: 5000\n") != NULL, "Missing retry field");

  VALK_PASS();
}

void test_sse_send_retry(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send_retry(NULL, 5000);
  VALK_TEST_ASSERT(result == -1, "Should reject NULL stream");

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");

  stream->state = VALK_SSE_CLOSED;
  result = valk_sse_send_retry(stream, 5000);
  VALK_TEST_ASSERT(result == -1, "Should reject closed stream");

  stream->state = VALK_SSE_OPEN;
  stream->queue_len = 10;
  result = valk_sse_send_retry(stream, 5000);
  VALK_TEST_ASSERT(result == -2, "Should return -2 (EAGAIN) when queue full");

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

// ============================================================================
// State Tests
// ============================================================================

void test_sse_state_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Verify enum values are in expected order
  VALK_TEST_ASSERT(VALK_SSE_INIT == 0, "INIT should be 0");
  VALK_TEST_ASSERT(VALK_SSE_OPEN == 1, "OPEN should be 1");
  VALK_TEST_ASSERT(VALK_SSE_CLOSING == 2, "CLOSING should be 2");
  VALK_TEST_ASSERT(VALK_SSE_CLOSED == 3, "CLOSED should be 3");

  VALK_PASS();
}

// ============================================================================
// Test Main
// ============================================================================

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_sse_stream_lifecycle", test_sse_stream_lifecycle);
  valk_testsuite_add_test(suite, "test_sse_stream_state_closed", test_sse_stream_state_closed);
  valk_testsuite_add_test(suite, "test_sse_event_queue_basic", test_sse_event_queue_basic);
  valk_testsuite_add_test(suite, "test_sse_event_queue_backpressure", test_sse_event_queue_backpressure);
  valk_testsuite_add_test(suite, "test_sse_is_writable", test_sse_is_writable);
  valk_testsuite_add_test(suite, "test_sse_event_format_manual", test_sse_event_format_manual);
  valk_testsuite_add_test(suite, "test_sse_send_retry", test_sse_send_retry);
  valk_testsuite_add_test(suite, "test_sse_state_enum", test_sse_state_enum);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
