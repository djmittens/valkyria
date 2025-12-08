#include "testing.h"
#include "memory.h"
#include "common.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef VALK_METRICS_ENABLED
#include "aio_sse.h"

// ============================================================================
// Stream Lifecycle Tests
// ============================================================================

void test_sse_stream_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Test NULL argument handling
  nghttp2_data_provider2 data_prd;
  valk_sse_stream_t *stream = valk_sse_stream_new(NULL, NULL, 1, &data_prd);
  VALK_TEST_ASSERT(stream == NULL, "Should return NULL with invalid arguments");

  // Note: We can't create a real stream without a valid nghttp2_session and
  // connection handle, which require a full HTTP/2 setup. The actual lifecycle
  // is tested in integration tests. Here we verify NULL handling.

  VALK_PASS();
}

void test_sse_stream_state_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Test that valk_sse_stream_close handles NULL gracefully
  valk_sse_stream_close(NULL);

  // Note: Testing actual state transitions requires a valid stream, which
  // needs a full HTTP/2 context. This is covered in integration tests.

  VALK_PASS();
}

// ============================================================================
// Event Queue Tests (with mock stream)
// ============================================================================

// Create a minimal mock stream for queue testing
static valk_sse_stream_t *__mock_stream_new(size_t queue_max) {
  valk_sse_stream_t *stream = calloc(1, sizeof(valk_sse_stream_t));
  if (!stream) {
    return NULL;
  }

  stream->state = VALK_SSE_OPEN;
  stream->queue_max = queue_max;
  stream->queue_len = 0;
  stream->queue_head = NULL;
  stream->queue_tail = NULL;
  stream->pending_capacity = 1024;
  stream->pending_data = malloc(stream->pending_capacity);

  if (!stream->pending_data) {
    free(stream);
    return NULL;
  }

  return stream;
}

static void __mock_stream_free(valk_sse_stream_t *stream) {
  if (!stream) {
    return;
  }

  // Free queued events
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

void test_sse_event_queue_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create mock stream with small queue
  valk_sse_stream_t *stream = __mock_stream_new(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create mock stream");
  VALK_TEST_ASSERT(stream->queue_len == 0, "Queue should start empty");

  // Note: valk_sse_send_event needs a real nghttp2_session to resume the stream.
  // Since we can't mock that without complex setup, we'll test the NULL checks
  // and basic validation instead.

  // Test NULL stream handling
  int result = valk_sse_send_event(NULL, "test", "data", 4, 1);
  VALK_TEST_ASSERT(result == -1, "Should reject NULL stream");

  // Test NULL data handling
  result = valk_sse_send_event(stream, "test", NULL, 4, 1);
  VALK_TEST_ASSERT(result == -1, "Should reject NULL data");

  // Test closed stream
  stream->state = VALK_SSE_CLOSED;
  result = valk_sse_send_event(stream, "test", "data", 4, 1);
  VALK_TEST_ASSERT(result == -1, "Should reject closed stream");

  __mock_stream_free(stream);
  VALK_PASS();
}

void test_sse_event_queue_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create mock stream with small queue for backpressure testing
  valk_sse_stream_t *stream = __mock_stream_new(5);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create mock stream");

  // Simulate filling the queue by setting queue_len manually
  // (we can't actually enqueue without a valid nghttp2_session)
  stream->queue_len = 5;

  // Test backpressure when queue is full
  int result = valk_sse_send_event(stream, "test", "data", 4, 1);
  VALK_TEST_ASSERT(result == -2, "Should return -2 (EAGAIN) when queue full, got %d", result);

  // Test is_writable returns false when full
  bool writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(!writable, "Stream should not be writable when queue full");

  // Simulate draining the queue
  stream->queue_len = 2;

  // Test is_writable returns true when not full
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(writable, "Stream should be writable when queue not full");

  // Test queue_len accessor
  size_t len = valk_sse_queue_len(stream);
  VALK_TEST_ASSERT(len == 2, "Queue len should be 2, got %zu", len);

  __mock_stream_free(stream);
  VALK_PASS();
}

// ============================================================================
// Backpressure Tests
// ============================================================================

void test_sse_is_writable(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Test NULL handling
  bool writable = valk_sse_is_writable(NULL);
  VALK_TEST_ASSERT(!writable, "NULL stream should not be writable");

  size_t len = valk_sse_queue_len(NULL);
  VALK_TEST_ASSERT(len == 0, "NULL stream should return 0 queue len");

  // Create mock stream and test writable states
  valk_sse_stream_t *stream = __mock_stream_new(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create mock stream");

  // Empty queue should be writable
  stream->queue_len = 0;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(writable, "Empty queue should be writable");

  // Partially filled queue should be writable
  stream->queue_len = 5;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(writable, "Partially filled queue should be writable");

  // Full queue should not be writable
  stream->queue_len = 10;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(!writable, "Full queue should not be writable");

  // Over-full queue should not be writable (defensive check)
  stream->queue_len = 11;
  writable = valk_sse_is_writable(stream);
  VALK_TEST_ASSERT(!writable, "Over-full queue should not be writable");

  __mock_stream_free(stream);
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

  // Test NULL handling
  int result = valk_sse_send_retry(NULL, 5000);
  VALK_TEST_ASSERT(result == -1, "Should reject NULL stream");

  // Create mock stream
  valk_sse_stream_t *stream = __mock_stream_new(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create mock stream");

  // Test closed stream
  stream->state = VALK_SSE_CLOSED;
  result = valk_sse_send_retry(stream, 5000);
  VALK_TEST_ASSERT(result == -1, "Should reject closed stream");

  // Test backpressure with full queue
  stream->state = VALK_SSE_OPEN;
  stream->queue_len = 10;
  result = valk_sse_send_retry(stream, 5000);
  VALK_TEST_ASSERT(result == -2, "Should return -2 (EAGAIN) when queue full");

  __mock_stream_free(stream);
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

#else // !VALK_METRICS_ENABLED

void test_sse_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("SSE tests require VALK_METRICS_ENABLED");
}

#endif // VALK_METRICS_ENABLED

// ============================================================================
// Test Main
// ============================================================================

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  // Lifecycle tests
  valk_testsuite_add_test(suite, "test_sse_stream_lifecycle", test_sse_stream_lifecycle);
  valk_testsuite_add_test(suite, "test_sse_stream_state_closed", test_sse_stream_state_closed);

  // Event queue tests
  valk_testsuite_add_test(suite, "test_sse_event_queue_basic", test_sse_event_queue_basic);
  valk_testsuite_add_test(suite, "test_sse_event_queue_backpressure", test_sse_event_queue_backpressure);

  // Backpressure tests
  valk_testsuite_add_test(suite, "test_sse_is_writable", test_sse_is_writable);

  // Event format tests
  valk_testsuite_add_test(suite, "test_sse_event_format_manual", test_sse_event_format_manual);
  valk_testsuite_add_test(suite, "test_sse_send_retry", test_sse_send_retry);

  // State enum tests
  valk_testsuite_add_test(suite, "test_sse_state_enum", test_sse_state_enum);
#else
  valk_testsuite_add_test(suite, "test_sse_disabled", test_sse_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
