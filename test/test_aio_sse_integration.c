#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_sse.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

typedef struct {
  int connectedCount;
  int disconnectedCount;
} valk_srv_state_t;

static void cb_onConnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
}

static void cb_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->disconnectedCount, 1, __ATOMIC_RELAXED);
}

static void cb_onHeader(void *arg, valk_aio_handle_t *conn, u64 stream, char *name,
                 char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void cb_onBody(void *arg, valk_aio_handle_t *conn, u64 stream, u8 flags,
               valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

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

static void test_sse_stream_new_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;
  valk_sse_stream_t *stream = valk_sse_stream_new(NULL, NULL, 1, &data_prd);
  ASSERT_NULL(stream);

  VALK_PASS();
}

static void test_sse_stream_close_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_close(NULL);

  VALK_PASS();
}

static void test_sse_is_writable_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool writable = valk_sse_is_writable(NULL);
  ASSERT_FALSE(writable);

  VALK_PASS();
}

static void test_sse_queue_len_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t len = valk_sse_queue_len(NULL);
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

static void test_sse_send_event_null_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send_event(NULL, "test", "data", 4, 1);
  ASSERT_EQ(result, -1);

  VALK_PASS();
}

static void test_sse_send_event_null_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  int result = valk_sse_send_event(stream, "test", NULL, 4, 1);
  ASSERT_EQ(result, -1);

  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

static void test_sse_send_event_closed_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  stream->state = VALK_SSE_CLOSED;

  int result = valk_sse_send_event(stream, "test", "data", 4, 1);
  ASSERT_EQ(result, -1);

  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

static void test_sse_backpressure_queue_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(5);
  ASSERT_NOT_NULL(stream);

  stream->queue_len = 5;

  int result = valk_sse_send_event(stream, "test", "data", 4, 1);
  ASSERT_EQ(result, -2);

  bool writable = valk_sse_is_writable(stream);
  ASSERT_FALSE(writable);

  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

static void test_sse_is_writable_open_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  stream->queue_len = 0;
  bool writable = valk_sse_is_writable(stream);
  ASSERT_TRUE(writable);

  stream->queue_len = 5;
  writable = valk_sse_is_writable(stream);
  ASSERT_TRUE(writable);

  stream->queue_len = 10;
  writable = valk_sse_is_writable(stream);
  ASSERT_FALSE(writable);

  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

static void test_sse_send_retry_null_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send_retry(NULL, 5000);
  ASSERT_EQ(result, -1);

  VALK_PASS();
}

static void test_sse_send_null_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  int result = valk_sse_send(NULL, "data", 4);
  ASSERT_EQ(result, -1);

  VALK_PASS();
}

static void test_sse_queue_len_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_stream_t *stream = valk_sse_stream_new_for_test(10);
  ASSERT_NOT_NULL(stream);

  size_t len = valk_sse_queue_len(stream);
  ASSERT_EQ(len, 0);

  stream->queue_len = 3;
  len = valk_sse_queue_len(stream);
  ASSERT_EQ(len, 3);

  stream->queue_len = 10;
  len = valk_sse_queue_len(stream);
  ASSERT_EQ(len, 10);

  valk_sse_stream_test_free(stream);

  VALK_PASS();
}

static void test_sse_stream_state_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_EQ(VALK_SSE_INIT, 0);
  ASSERT_EQ(VALK_SSE_OPEN, 1);
  ASSERT_EQ(VALK_SSE_CLOSING, 2);
  ASSERT_EQ(VALK_SSE_CLOSED, 3);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
static void test_sse_registry_init_shutdown(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  valk_aio_http_server *srv = result->ref.ptr;
  (void)valk_aio_http2_server_get_port(srv);

  valk_sse_stream_registry_t *registry = valk_aio_get_sse_registry(sys);
  ASSERT_NOT_NULL(registry);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}
#endif

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_sse_stream_new_null_args", test_sse_stream_new_null_args);
  valk_testsuite_add_test(suite, "test_sse_stream_close_null", test_sse_stream_close_null);
  valk_testsuite_add_test(suite, "test_sse_is_writable_null", test_sse_is_writable_null);
  valk_testsuite_add_test(suite, "test_sse_queue_len_null", test_sse_queue_len_null);
  valk_testsuite_add_test(suite, "test_sse_send_event_null_stream", test_sse_send_event_null_stream);
  valk_testsuite_add_test(suite, "test_sse_send_event_null_data", test_sse_send_event_null_data);
  valk_testsuite_add_test(suite, "test_sse_send_event_closed_stream", test_sse_send_event_closed_stream);
  valk_testsuite_add_test(suite, "test_sse_backpressure_queue_full", test_sse_backpressure_queue_full);
  valk_testsuite_add_test(suite, "test_sse_is_writable_open_stream", test_sse_is_writable_open_stream);
  valk_testsuite_add_test(suite, "test_sse_send_retry_null_stream", test_sse_send_retry_null_stream);
  valk_testsuite_add_test(suite, "test_sse_send_null_stream", test_sse_send_null_stream);
  valk_testsuite_add_test(suite, "test_sse_queue_len_tracking", test_sse_queue_len_tracking);
  valk_testsuite_add_test(suite, "test_sse_stream_state_enum", test_sse_stream_state_enum);
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_sse_registry_init_shutdown", test_sse_registry_init_shutdown);
#endif

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
