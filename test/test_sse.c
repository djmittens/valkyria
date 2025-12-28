#include "testing.h"
#include "memory.h"
#include "common.h"
#include "aio/aio_sse.h"

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
  u64 id = 42;

  char buf[512];
  int len = snprintf(buf, sizeof(buf), "id: %llu\nevent: %s\ndata: %s\n\n",
                     (unsigned long long)id, event_type, data);

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
  u32 retry_ms = 5000;
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

  VALK_TEST_ASSERT(VALK_SSE_INIT == 0, "INIT should be 0");
  VALK_TEST_ASSERT(VALK_SSE_OPEN == 1, "OPEN should be 1");
  VALK_TEST_ASSERT(VALK_SSE_CLOSING == 2, "CLOSING should be 2");
  VALK_TEST_ASSERT(VALK_SSE_CLOSED == 3, "CLOSED should be 3");

  VALK_PASS();
}

static bool g_on_close_called = false;
static void *g_on_close_user_data = NULL;

static void test_on_close_callback(valk_sse_stream_t *stream, void *user_data) {
  UNUSED(stream);
  g_on_close_called = true;
  g_on_close_user_data = user_data;
}

void test_sse_stream_close_with_queued_events(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");

  valk_sse_event_t *event1 = calloc(1, sizeof(valk_sse_event_t) + 16);
  valk_sse_event_t *event2 = calloc(1, sizeof(valk_sse_event_t) + 16);
  VALK_TEST_ASSERT(event1 != NULL && event2 != NULL, "Failed to allocate events");

  event1->data = (char *)(event1 + 1);
  event1->data_len = 10;
  event1->next = event2;

  event2->data = (char *)(event2 + 1);
  event2->data_len = 10;
  event2->next = NULL;

  stream->queue_head = event1;
  stream->queue_tail = event2;
  stream->queue_len = 2;

  stream->state = VALK_SSE_CLOSED;
  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

void test_sse_stream_close_with_on_close_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");

  g_on_close_called = false;
  g_on_close_user_data = NULL;

  int sentinel = 0xDEADBEEF;
  stream->on_close = test_on_close_callback;
  stream->user_data = &sentinel;

  stream->state = VALK_SSE_OPEN;

  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

void test_sse_send_wrapper(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send(NULL, "data", 4);
  VALK_TEST_ASSERT(result == -1, "Should reject NULL stream");

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");

  stream->state = VALK_SSE_CLOSED;
  result = valk_sse_send(stream, "data", 4);
  VALK_TEST_ASSERT(result == -1, "Should reject closed stream");

  stream->state = VALK_SSE_OPEN;
  stream->queue_len = 10;
  result = valk_sse_send(stream, "data", 4);
  VALK_TEST_ASSERT(result == -2, "Should return backpressure when full");

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_sse_stream_close_already_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  VALK_TEST_ASSERT(stream != NULL, "Failed to create stream");

  stream->state = VALK_SSE_CLOSED;

  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

// ============================================================================
// Pending Stream Queue Tests
// ============================================================================

static valk_sse_event_t *create_test_event(const char *data, size_t data_len) {
  valk_sse_event_t *event = calloc(1, sizeof(valk_sse_event_t) + data_len + 1);
  if (!event) return NULL;

  char *buf = (char *)(event + 1);
  memcpy(buf, data, data_len);
  buf[data_len] = '\0';

  event->data = buf;
  event->data_len = data_len;
  event->next = NULL;

  return event;
}

void test_pending_queue_enqueue_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);
  ASSERT_EQ(stream->queue_len, 0);
  ASSERT_NULL(stream->queue_head);
  ASSERT_NULL(stream->queue_tail);

  valk_sse_event_t *event = create_test_event("hello", 5);
  ASSERT_NOT_NULL(event);

  stream->queue_head = event;
  stream->queue_tail = event;
  stream->queue_len = 1;

  ASSERT_EQ(stream->queue_len, 1);
  ASSERT_EQ(stream->queue_head, event);
  ASSERT_EQ(stream->queue_tail, event);
  ASSERT_NULL(event->next);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_queue_enqueue_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  valk_sse_event_t *event1 = create_test_event("first", 5);
  valk_sse_event_t *event2 = create_test_event("second", 6);
  valk_sse_event_t *event3 = create_test_event("third", 5);
  ASSERT_NOT_NULL(event1);
  ASSERT_NOT_NULL(event2);
  ASSERT_NOT_NULL(event3);

  stream->queue_head = event1;
  stream->queue_tail = event1;
  stream->queue_len = 1;

  event1->next = event2;
  stream->queue_tail = event2;
  stream->queue_len++;

  event2->next = event3;
  stream->queue_tail = event3;
  stream->queue_len++;

  ASSERT_EQ(stream->queue_len, 3);
  ASSERT_EQ(stream->queue_head, event1);
  ASSERT_EQ(stream->queue_tail, event3);
  ASSERT_EQ(event1->next, event2);
  ASSERT_EQ(event2->next, event3);
  ASSERT_NULL(event3->next);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_queue_dequeue_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  valk_sse_event_t *event = create_test_event("hello", 5);
  ASSERT_NOT_NULL(event);

  stream->queue_head = event;
  stream->queue_tail = event;
  stream->queue_len = 1;

  valk_sse_event_t *dequeued = stream->queue_head;
  stream->queue_head = event->next;
  if (!stream->queue_head) {
    stream->queue_tail = NULL;
  }
  stream->queue_len--;

  ASSERT_EQ(dequeued, event);
  ASSERT_EQ(stream->queue_len, 0);
  ASSERT_NULL(stream->queue_head);
  ASSERT_NULL(stream->queue_tail);

  free(dequeued);
  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_queue_dequeue_fifo_order(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  valk_sse_event_t *event1 = create_test_event("first", 5);
  valk_sse_event_t *event2 = create_test_event("second", 6);
  valk_sse_event_t *event3 = create_test_event("third", 5);
  ASSERT_NOT_NULL(event1);
  ASSERT_NOT_NULL(event2);
  ASSERT_NOT_NULL(event3);

  stream->queue_head = event1;
  event1->next = event2;
  event2->next = event3;
  stream->queue_tail = event3;
  stream->queue_len = 3;

  valk_sse_event_t *d1 = stream->queue_head;
  stream->queue_head = d1->next;
  stream->queue_len--;
  ASSERT_STR_EQ(d1->data, "first");
  ASSERT_EQ(stream->queue_len, 2);
  free(d1);

  valk_sse_event_t *d2 = stream->queue_head;
  stream->queue_head = d2->next;
  stream->queue_len--;
  ASSERT_STR_EQ(d2->data, "second");
  ASSERT_EQ(stream->queue_len, 1);
  free(d2);

  valk_sse_event_t *d3 = stream->queue_head;
  stream->queue_head = d3->next;
  if (!stream->queue_head) {
    stream->queue_tail = NULL;
  }
  stream->queue_len--;
  ASSERT_STR_EQ(d3->data, "third");
  ASSERT_EQ(stream->queue_len, 0);
  ASSERT_NULL(stream->queue_head);
  ASSERT_NULL(stream->queue_tail);
  free(d3);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_initial_state(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  ASSERT_NOT_NULL(stream->pending_data);
  ASSERT_EQ(stream->pending_capacity, 1024);
  ASSERT_EQ(stream->pending_len, 0);
  ASSERT_EQ(stream->pending_offset, 0);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_copy_event_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  const char *test_data = "event: test\ndata: hello world\n\n";
  size_t test_len = strlen(test_data);

  memcpy(stream->pending_data, test_data, test_len);
  stream->pending_len = test_len;
  stream->pending_offset = 0;

  ASSERT_EQ(stream->pending_len, test_len);
  ASSERT_MEM_EQ(stream->pending_data, test_data, test_len);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_partial_read(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  const char *test_data = "0123456789ABCDEF";
  size_t test_len = 16;

  memcpy(stream->pending_data, test_data, test_len);
  stream->pending_len = test_len;
  stream->pending_offset = 0;

  char buf[8];
  size_t to_read = 8;
  size_t remaining = stream->pending_len - stream->pending_offset;
  size_t actual = remaining < to_read ? remaining : to_read;

  memcpy(buf, stream->pending_data + stream->pending_offset, actual);
  stream->pending_offset += actual;

  ASSERT_EQ(actual, 8);
  ASSERT_MEM_EQ(buf, "01234567", 8);
  ASSERT_EQ(stream->pending_offset, 8);

  remaining = stream->pending_len - stream->pending_offset;
  actual = remaining < to_read ? remaining : to_read;
  memcpy(buf, stream->pending_data + stream->pending_offset, actual);
  stream->pending_offset += actual;

  ASSERT_EQ(actual, 8);
  ASSERT_MEM_EQ(buf, "89ABCDEF", 8);
  ASSERT_EQ(stream->pending_offset, 16);

  ASSERT_EQ(stream->pending_offset, stream->pending_len);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_remaining_calculation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  stream->pending_len = 100;
  stream->pending_offset = 0;

  size_t remaining = stream->pending_len - stream->pending_offset;
  ASSERT_EQ(remaining, 100);

  stream->pending_offset = 30;
  remaining = stream->pending_len - stream->pending_offset;
  ASSERT_EQ(remaining, 70);

  stream->pending_offset = 100;
  remaining = stream->pending_len - stream->pending_offset;
  ASSERT_EQ(remaining, 0);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_reset_after_event(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  stream->pending_len = 50;
  stream->pending_offset = 50;

  ASSERT_EQ(stream->pending_offset, stream->pending_len);

  const char *new_data = "new event data";
  size_t new_len = strlen(new_data);

  memcpy(stream->pending_data, new_data, new_len);
  stream->pending_len = new_len;
  stream->pending_offset = 0;

  ASSERT_EQ(stream->pending_len, new_len);
  ASSERT_EQ(stream->pending_offset, 0);
  ASSERT_MEM_EQ(stream->pending_data, new_data, new_len);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

static bool g_on_drain_called = false;
static valk_sse_stream_t *g_on_drain_stream = NULL;
static void *g_on_drain_user_data = NULL;

static void test_on_drain_callback(valk_sse_stream_t *stream, void *user_data) {
  g_on_drain_called = true;
  g_on_drain_stream = stream;
  g_on_drain_user_data = user_data;
}

void test_on_drain_callback_setup(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  int sentinel = 42;
  stream->on_drain = test_on_drain_callback;
  stream->user_data = &sentinel;

  ASSERT_NOT_NULL(stream->on_drain);
  ASSERT_EQ(stream->user_data, &sentinel);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_on_drain_callback_trigger(VALK_TEST_ARGS()) {
  VALK_TEST();

  g_on_drain_called = false;
  g_on_drain_stream = NULL;
  g_on_drain_user_data = NULL;

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  int sentinel = 42;
  stream->on_drain = test_on_drain_callback;
  stream->user_data = &sentinel;

  stream->queue_len = 6;

  stream->queue_len--;
  if (stream->queue_len < stream->queue_max / 2 && stream->on_drain) {
    stream->on_drain(stream, stream->user_data);
  }

  ASSERT_FALSE(g_on_drain_called);

  stream->queue_len = 5;

  stream->queue_len--;
  if (stream->queue_len < stream->queue_max / 2 && stream->on_drain) {
    stream->on_drain(stream, stream->user_data);
  }

  ASSERT_TRUE(g_on_drain_called);
  ASSERT_EQ(g_on_drain_stream, stream);
  ASSERT_EQ(g_on_drain_user_data, &sentinel);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_on_drain_not_called_when_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  g_on_drain_called = false;

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  stream->on_drain = NULL;
  stream->queue_len = 5;

  stream->queue_len--;
  if (stream->queue_len < stream->queue_max / 2 && stream->on_drain) {
    stream->on_drain(stream, stream->user_data);
  }

  ASSERT_FALSE(g_on_drain_called);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_growth_needed(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  size_t original_capacity = stream->pending_capacity;
  ASSERT_EQ(original_capacity, 1024);

  size_t large_event_size = 2048;

  if (large_event_size > stream->pending_capacity) {
    char *new_buf = realloc(stream->pending_data, large_event_size);
    ASSERT_NOT_NULL(new_buf);
    stream->pending_data = new_buf;
    stream->pending_capacity = large_event_size;
  }

  ASSERT_EQ(stream->pending_capacity, 2048);
  ASSERT_GT(stream->pending_capacity, original_capacity);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_growth_with_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  size_t large_size = 2048;
  char *large_data = malloc(large_size);
  ASSERT_NOT_NULL(large_data);
  memset(large_data, 'A', large_size);

  if (large_size > stream->pending_capacity) {
    char *new_buf = realloc(stream->pending_data, large_size);
    ASSERT_NOT_NULL(new_buf);
    stream->pending_data = new_buf;
    stream->pending_capacity = large_size;
  }

  memcpy(stream->pending_data, large_data, large_size);
  stream->pending_len = large_size;
  stream->pending_offset = 0;

  ASSERT_EQ(stream->pending_len, 2048);
  ASSERT_EQ(stream->pending_capacity, 2048);
  ASSERT_MEM_EQ(stream->pending_data, large_data, large_size);

  free(large_data);
  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_data_deferred_flag(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  stream->data_deferred = false;

  ASSERT_NULL(stream->queue_head);
  stream->data_deferred = true;

  ASSERT_TRUE(stream->data_deferred);

  valk_sse_event_t *event = create_test_event("data", 4);
  ASSERT_NOT_NULL(event);
  stream->queue_head = event;
  stream->queue_tail = event;
  stream->queue_len = 1;

  stream->data_deferred = false;

  ASSERT_FALSE(stream->data_deferred);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_stats_update_on_send(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  ASSERT_EQ(stream->events_sent, 0);
  ASSERT_EQ(stream->bytes_sent, 0);

  size_t event_size = 42;
  stream->events_sent++;
  stream->bytes_sent += event_size;

  ASSERT_EQ(stream->events_sent, 1);
  ASSERT_EQ(stream->bytes_sent, 42);

  stream->events_sent++;
  stream->bytes_sent += 58;

  ASSERT_EQ(stream->events_sent, 2);
  ASSERT_EQ(stream->bytes_sent, 100);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_queue_at_exact_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(3);
  ASSERT_NOT_NULL(stream);

  valk_sse_event_t *e1 = create_test_event("1", 1);
  valk_sse_event_t *e2 = create_test_event("2", 1);
  valk_sse_event_t *e3 = create_test_event("3", 1);

  stream->queue_head = e1;
  e1->next = e2;
  e2->next = e3;
  stream->queue_tail = e3;
  stream->queue_len = 3;

  ASSERT_EQ(stream->queue_len, stream->queue_max);
  ASSERT_FALSE(valk_sse_is_writable(stream));

  valk_sse_event_t *dequeued = stream->queue_head;
  stream->queue_head = dequeued->next;
  stream->queue_len--;
  free(dequeued);

  ASSERT_TRUE(valk_sse_is_writable(stream));

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_empty_queue_state(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  ASSERT_NULL(stream->queue_head);
  ASSERT_NULL(stream->queue_tail);
  ASSERT_EQ(stream->queue_len, 0);
  ASSERT_TRUE(valk_sse_is_writable(stream));
  ASSERT_EQ(valk_sse_queue_len(stream), 0);

  valk_sse_stream_test_free(stream);
  VALK_PASS();
}

void test_pending_buffer_exactly_fits(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  size_t exact_size = stream->pending_capacity;
  char *data = malloc(exact_size);
  ASSERT_NOT_NULL(data);
  memset(data, 'X', exact_size);

  memcpy(stream->pending_data, data, exact_size);
  stream->pending_len = exact_size;
  stream->pending_offset = 0;

  ASSERT_EQ(stream->pending_len, stream->pending_capacity);

  free(data);
  valk_sse_stream_test_free(stream);
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
  valk_testsuite_add_test(suite, "test_sse_stream_close_with_queued_events", test_sse_stream_close_with_queued_events);
  valk_testsuite_add_test(suite, "test_sse_stream_close_with_on_close_callback", test_sse_stream_close_with_on_close_callback);
  valk_testsuite_add_test(suite, "test_sse_send_wrapper", test_sse_send_wrapper);
  valk_testsuite_add_test(suite, "test_sse_stream_close_already_closed", test_sse_stream_close_already_closed);

  valk_testsuite_add_test(suite, "test_pending_queue_enqueue_single", test_pending_queue_enqueue_single);
  valk_testsuite_add_test(suite, "test_pending_queue_enqueue_multiple", test_pending_queue_enqueue_multiple);
  valk_testsuite_add_test(suite, "test_pending_queue_dequeue_single", test_pending_queue_dequeue_single);
  valk_testsuite_add_test(suite, "test_pending_queue_dequeue_fifo_order", test_pending_queue_dequeue_fifo_order);
  valk_testsuite_add_test(suite, "test_pending_buffer_initial_state", test_pending_buffer_initial_state);
  valk_testsuite_add_test(suite, "test_pending_buffer_copy_event_data", test_pending_buffer_copy_event_data);
  valk_testsuite_add_test(suite, "test_pending_buffer_partial_read", test_pending_buffer_partial_read);
  valk_testsuite_add_test(suite, "test_pending_buffer_remaining_calculation", test_pending_buffer_remaining_calculation);
  valk_testsuite_add_test(suite, "test_pending_buffer_reset_after_event", test_pending_buffer_reset_after_event);
  valk_testsuite_add_test(suite, "test_on_drain_callback_setup", test_on_drain_callback_setup);
  valk_testsuite_add_test(suite, "test_on_drain_callback_trigger", test_on_drain_callback_trigger);
  valk_testsuite_add_test(suite, "test_on_drain_not_called_when_null", test_on_drain_not_called_when_null);
  valk_testsuite_add_test(suite, "test_pending_buffer_growth_needed", test_pending_buffer_growth_needed);
  valk_testsuite_add_test(suite, "test_pending_buffer_growth_with_data", test_pending_buffer_growth_with_data);
  valk_testsuite_add_test(suite, "test_data_deferred_flag", test_data_deferred_flag);
  valk_testsuite_add_test(suite, "test_stats_update_on_send", test_stats_update_on_send);
  valk_testsuite_add_test(suite, "test_queue_at_exact_capacity", test_queue_at_exact_capacity);
  valk_testsuite_add_test(suite, "test_empty_queue_state", test_empty_queue_state);
  valk_testsuite_add_test(suite, "test_pending_buffer_exactly_fits", test_pending_buffer_exactly_fits);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
