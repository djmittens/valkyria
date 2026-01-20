#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"
#include "aio/http2/stream/aio_stream_body.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

typedef struct {
  int on_close_count;
  int on_drain_count;
  u64 total_bytes_received;
  char *received_data;
  size_t received_data_len;
  size_t received_data_cap;
  pthread_mutex_t data_mutex;
} stream_test_state_t;

static void init_test_state(stream_test_state_t *state) {
  state->on_close_count = 0;
  state->on_drain_count = 0;
  state->total_bytes_received = 0;
  state->received_data_cap = 65536;
  state->received_data = malloc(state->received_data_cap);
  state->received_data_len = 0;
  pthread_mutex_init(&state->data_mutex, nullptr);
}

static void free_test_state(stream_test_state_t *state) {
  if (state->received_data) {
    free(state->received_data);
    state->received_data = nullptr;
  }
  pthread_mutex_destroy(&state->data_mutex);
}

static void cb_on_close(valk_stream_body_t *body, void *user_data) {
  UNUSED(body);
  stream_test_state_t *state = user_data;
  pthread_mutex_lock(&state->data_mutex);
  state->on_close_count++;
  pthread_mutex_unlock(&state->data_mutex);
}

static void cb_on_drain(valk_stream_body_t *body, void *user_data) {
  UNUSED(body);
  stream_test_state_t *state = user_data;
  pthread_mutex_lock(&state->data_mutex);
  state->on_drain_count++;
  pthread_mutex_unlock(&state->data_mutex);
}

typedef struct {
  int connectedCount;
  int disconnectedCount;
  int requestCount;
  stream_test_state_t *stream_state;
  valk_stream_body_t *stream_body;
  valk_aio_handle_t *conn;
  nghttp2_session *session;
  i32 stream_id;
} test_handler_state_t;

static void cb_test_onConnect(void *arg, valk_aio_handle_t *conn) {
  test_handler_state_t *state = arg;
  __atomic_fetch_add(&state->connectedCount, 1, __ATOMIC_RELAXED);
  state->conn = conn;
  state->session = conn->http.session;
}

static void cb_test_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  test_handler_state_t *state = arg;
  __atomic_fetch_add(&state->disconnectedCount, 1, __ATOMIC_RELAXED);
}

static void cb_test_onHeader(void *arg, valk_aio_handle_t *conn, u64 stream,
                              char *name, char *value) {
  UNUSED(conn);
  UNUSED(name);
  UNUSED(value);
  test_handler_state_t *state = arg;
  state->stream_id = (i32)stream;
}

static void cb_test_onBody(void *arg, valk_aio_handle_t *conn, u64 stream,
                            u8 flags, valk_buffer_t *buf) {
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  test_handler_state_t *state = arg;
  if (state->stream_state && buf && buf->count > 0) {
    pthread_mutex_lock(&state->stream_state->data_mutex);
    if (state->stream_state->received_data_len + buf->count < state->stream_state->received_data_cap) {
      memcpy(state->stream_state->received_data + state->stream_state->received_data_len,
             buf->items, buf->count);
      state->stream_state->received_data_len += buf->count;
    }
    state->stream_state->total_bytes_received += buf->count;
    pthread_mutex_unlock(&state->stream_state->data_mutex);
  }
}

static void test_stream_body_write_queues_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  REQUIRE_NOT_NULL(sys);

  stream_test_state_t stream_state;
  init_test_state(&stream_state);

  test_handler_state_t state = {
    .stream_state = &stream_state,
    .stream_body = nullptr,
    .conn = nullptr,
    .session = nullptr,
    .stream_id = 0,
  };

  valk_http2_handler_t handler = {
    .arg = &state,
    .onConnect = cb_test_onConnect,
    .onDisconnect = cb_test_onDisconnect,
    .onHeader = cb_test_onHeader,
    .onBody = cb_test_onBody,
  };

  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server_result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);

  valk_aio_http2_client *client = client_result->ref.ptr;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)req_arena;
    req->method = "GET";
    req->scheme = "https";
    req->authority = "localhost";
    req->path = "/stream-test";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);
  ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  free_test_state(&stream_state);

  VALK_PASS();
}

static void test_stream_body_new_with_real_session(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  REQUIRE_NOT_NULL(sys);

  test_handler_state_t state = {0};

  valk_http2_handler_t handler = {
    .arg = &state,
    .onConnect = cb_test_onConnect,
    .onDisconnect = cb_test_onDisconnect,
    .onHeader = cb_test_onHeader,
    .onBody = cb_test_onBody,
  };

  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server_result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);

  usleep(10000);

  ASSERT_NOT_NULL(state.conn);
  ASSERT_NOT_NULL(state.session);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_stream_body_writable_with_session(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  REQUIRE_NOT_NULL(sys);

  test_handler_state_t state = {0};

  valk_http2_handler_t handler = {
    .arg = &state,
    .onConnect = cb_test_onConnect,
    .onDisconnect = cb_test_onDisconnect,
    .onHeader = cb_test_onHeader,
    .onBody = cb_test_onBody,
  };

  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server_result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);

  usleep(10000);

  ASSERT_NOT_NULL(state.conn);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_stream_body_backpressure_queue_max(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;
  conn->http.session = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->queue_max = 3;
  body->queue_len = 3;

  int rv = valk_stream_body_write(body, "x", 1);
  ASSERT_EQ(rv, -2);

  ASSERT_EQ(body->queue_len, 3);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_on_close_callback_unit(VALK_TEST_ARGS()) {
  VALK_TEST();

  stream_test_state_t stream_state;
  init_test_state(&stream_state);

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->on_close = cb_on_close;
  body->user_data = &stream_state;

  pthread_mutex_lock(&stream_state.data_mutex);
  int close_count_before = stream_state.on_close_count;
  pthread_mutex_unlock(&stream_state.data_mutex);
  ASSERT_EQ(close_count_before, 0);

  valk_stream_body_close(body);

  ASSERT_TRUE(body->state == VALK_STREAM_CLOSING || body->state == VALK_STREAM_CLOSED);

  free(body);
  free(conn);
  free_test_state(&stream_state);

  VALK_PASS();
}

static void test_stream_body_on_drain_callback_setup(VALK_TEST_ARGS()) {
  VALK_TEST();

  stream_test_state_t stream_state;
  init_test_state(&stream_state);

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->on_drain = cb_on_drain;
  body->user_data = &stream_state;
  body->queue_max = 100;
  body->queue_len = 0;

  ASSERT_NOT_NULL(body->on_drain);
  ASSERT_EQ(body->user_data, &stream_state);

  free(body);
  free(conn);
  free_test_state(&stream_state);

  VALK_PASS();
}

static void test_stream_body_close_idempotent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;

  valk_stream_body_close(body);
  valk_stream_state_e state1 = body->state;

  valk_stream_body_close(body);
  valk_stream_state_e state2 = body->state;

  ASSERT_EQ(state1, state2);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_write_after_close_fails(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_CLOSED;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 100;
  body->queue_len = 0;

  int rv = valk_stream_body_write(body, "test", 4);
  ASSERT_EQ(rv, -1);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_writable_reflects_state(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 100;
  body->queue_len = 0;
  body->session = nullptr;

  body->state = VALK_STREAM_OPEN;
  bool writable1 = valk_stream_body_writable(body);
  ASSERT_FALSE(writable1);

  body->state = VALK_STREAM_CLOSING;
  bool writable2 = valk_stream_body_writable(body);
  ASSERT_FALSE(writable2);

  body->state = VALK_STREAM_CLOSED;
  bool writable3 = valk_stream_body_writable(body);
  ASSERT_FALSE(writable3);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_queue_len_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->queue_max = 100;

  body->queue_len = 0;
  ASSERT_EQ(valk_stream_body_queue_len(body), 0);

  body->queue_len = 42;
  ASSERT_EQ(valk_stream_body_queue_len(body), 42);

  body->queue_len = 100;
  ASSERT_EQ(valk_stream_body_queue_len(body), 100);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_activity_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->last_activity_ms = 0;

  valk_stream_body_touch_activity(body);
  u64 time1 = body->last_activity_ms;
  ASSERT_GT(time1, 0);

  usleep(1000);
  valk_stream_body_touch_activity(body);
  u64 time2 = body->last_activity_ms;
  ASSERT_GE(time2, time1);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_idle_timeout_behavior(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->idle_timeout_ms = 0;
  body->last_activity_ms = 0;

  ASSERT_FALSE(valk_stream_body_is_idle_expired(body));

  body->idle_timeout_ms = 1;
  body->last_activity_ms = 0;

  usleep(2000);
  ASSERT_TRUE(valk_stream_body_is_idle_expired(body));

  valk_stream_body_touch_activity(body);
  ASSERT_FALSE(valk_stream_body_is_idle_expired(body));

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_register_unregister(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body1 = calloc(1, sizeof(valk_stream_body_t));
  body1->state = VALK_STREAM_OPEN;
  body1->conn = conn;
  body1->stream_id = 1;
  body1->next = nullptr;

  valk_stream_body_t *body2 = calloc(1, sizeof(valk_stream_body_t));
  body2->state = VALK_STREAM_OPEN;
  body2->conn = conn;
  body2->stream_id = 3;
  body2->next = nullptr;

  valk_stream_body_register(body1);
  ASSERT_EQ(conn->http.stream_bodies, body1);

  valk_stream_body_register(body2);
  ASSERT_EQ(conn->http.stream_bodies, body2);
  ASSERT_EQ(body2->next, body1);

  valk_stream_body_unregister(body2);
  ASSERT_EQ(conn->http.stream_bodies, body1);

  valk_stream_body_unregister(body1);
  ASSERT_NULL(conn->http.stream_bodies);

  free(body1);
  free(body2);
  free(conn);

  VALK_PASS();
}

static void test_stream_body_bytes_sent_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->bytes_sent = 0;

  conn->http.stream_bodies = body;

  body->bytes_sent = 1234;
  u64 bytes = valk_stream_body_get_bytes_sent(conn, 1);
  ASSERT_EQ(bytes, 1234);

  u64 not_found = valk_stream_body_get_bytes_sent(conn, 999);
  ASSERT_EQ(not_found, 0);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_write_during_close_returns_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 100;
  body->queue_len = 0;

  int rv1 = valk_stream_body_write(body, "test1", 5);
  ASSERT_EQ(rv1, 0);
  ASSERT_EQ(body->queue_len, 1);

  body->state = VALK_STREAM_CLOSING;

  int rv2 = valk_stream_body_write(body, "test2", 5);
  ASSERT_EQ(rv2, -1);
  ASSERT_EQ(body->queue_len, 1);

  body->state = VALK_STREAM_CLOSED;

  int rv3 = valk_stream_body_write(body, "test3", 5);
  ASSERT_EQ(rv3, -1);
  ASSERT_EQ(body->queue_len, 1);

  valk_stream_chunk_t *chunk = body->queue_head;
  while (chunk) {
    valk_stream_chunk_t *next = chunk->next;
    free(chunk);
    chunk = next;
  }

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_writable_false_during_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 100;
  body->queue_len = 0;
  body->session = nullptr;

  body->state = VALK_STREAM_CLOSING;
  ASSERT_FALSE(valk_stream_body_writable(body));

  body->state = VALK_STREAM_CLOSED;
  ASSERT_FALSE(valk_stream_body_writable(body));

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_close_all_closes_multiple_bodies(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body1 = calloc(1, sizeof(valk_stream_body_t));
  body1->state = VALK_STREAM_OPEN;
  body1->conn = conn;
  body1->stream_id = 1;
  body1->next = nullptr;

  valk_stream_body_t *body2 = calloc(1, sizeof(valk_stream_body_t));
  body2->state = VALK_STREAM_OPEN;
  body2->conn = conn;
  body2->stream_id = 3;
  body2->next = nullptr;

  valk_stream_body_t *body3 = calloc(1, sizeof(valk_stream_body_t));
  body3->state = VALK_STREAM_OPEN;
  body3->conn = conn;
  body3->stream_id = 5;
  body3->next = nullptr;

  valk_stream_body_register(body1);
  valk_stream_body_register(body2);
  valk_stream_body_register(body3);

  ASSERT_EQ(conn->http.stream_bodies, body3);
  ASSERT_EQ(body3->next, body2);
  ASSERT_EQ(body2->next, body1);

  valk_stream_body_close_all(conn);

  ASSERT_NULL(conn->http.stream_bodies);
  ASSERT_TRUE(body1->state == VALK_STREAM_CLOSING || body1->state == VALK_STREAM_CLOSED);
  ASSERT_TRUE(body2->state == VALK_STREAM_CLOSING || body2->state == VALK_STREAM_CLOSED);
  ASSERT_TRUE(body3->state == VALK_STREAM_CLOSING || body3->state == VALK_STREAM_CLOSED);

  free(body1);
  free(body2);
  free(body3);
  free(conn);

  VALK_PASS();
}

static void test_stream_write_after_close_all_fails(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 100;
  body->queue_len = 0;
  body->next = nullptr;

  valk_stream_body_register(body);
  ASSERT_EQ(conn->http.stream_bodies, body);

  int rv1 = valk_stream_body_write(body, "before close", 12);
  ASSERT_EQ(rv1, 0);
  ASSERT_EQ(body->queue_len, 1);

  valk_stream_body_close_all(conn);

  int rv2 = valk_stream_body_write(body, "after close", 11);
  ASSERT_EQ(rv2, -1);
  ASSERT_EQ(body->queue_len, 1);

  valk_stream_chunk_t *chunk = body->queue_head;
  while (chunk) {
    valk_stream_chunk_t *next = chunk->next;
    free(chunk);
    chunk = next;
  }

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_stream_close_by_stream_id_unit(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body1 = calloc(1, sizeof(valk_stream_body_t));
  body1->state = VALK_STREAM_OPEN;
  body1->conn = conn;
  body1->stream_id = 1;
  body1->next = nullptr;

  valk_stream_body_t *body2 = calloc(1, sizeof(valk_stream_body_t));
  body2->state = VALK_STREAM_OPEN;
  body2->conn = conn;
  body2->stream_id = 3;
  body2->next = nullptr;

  valk_stream_body_register(body1);
  valk_stream_body_register(body2);

  valk_stream_body_close_by_stream_id(conn, 1);

  ASSERT_TRUE(body1->state == VALK_STREAM_CLOSING || body1->state == VALK_STREAM_CLOSED);
  ASSERT_EQ(body2->state, VALK_STREAM_OPEN);

  valk_stream_body_close_by_stream_id(conn, 999);
  ASSERT_EQ(body2->state, VALK_STREAM_OPEN);

  valk_stream_body_unregister(body2);

  free(body1);
  free(body2);
  free(conn);

  VALK_PASS();
}

static void test_stream_close_by_stream_id_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_stream_body_close_by_stream_id(nullptr, 1);

  VALK_PASS();
}

static void test_stream_close_all_null_conn(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_stream_body_close_all(nullptr);

  VALK_PASS();
}

static void test_stream_close_idempotent_during_race(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 100;
  body->queue_len = 0;
  body->next = nullptr;

  valk_stream_body_register(body);

  valk_stream_body_close(body);
  valk_stream_state_e state1 = body->state;

  valk_stream_body_close(body);
  valk_stream_state_e state2 = body->state;

  valk_stream_body_close(body);
  valk_stream_state_e state3 = body->state;

  ASSERT_EQ(state1, state2);
  ASSERT_EQ(state2, state3);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_concurrent_writes_order_preserved(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 1000;
  body->queue_len = 0;
  body->queue_head = nullptr;
  body->queue_tail = nullptr;
  body->next = nullptr;

  char write_data[100][32];
  for (int i = 0; i < 100; i++) {
    snprintf(write_data[i], 32, "chunk-%03d", i);
    int rv = valk_stream_body_write(body, write_data[i], strlen(write_data[i]));
    ASSERT_EQ(rv, 0);
  }

  ASSERT_EQ(body->queue_len, 100);

  valk_stream_chunk_t *chunk = body->queue_head;
  int idx = 0;
  while (chunk) {
    char expected[32];
    snprintf(expected, 32, "chunk-%03d", idx);
    ASSERT_EQ(chunk->data_len, strlen(expected));
    ASSERT_EQ(memcmp(chunk->data, expected, chunk->data_len), 0);

    valk_stream_chunk_t *next = chunk->next;
    free(chunk);
    chunk = next;
    idx++;
  }

  ASSERT_EQ(idx, 100);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_concurrent_writes_no_corruption(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 1000;
  body->queue_len = 0;
  body->queue_head = nullptr;
  body->queue_tail = nullptr;
  body->next = nullptr;

  char large_data[4096];
  memset(large_data, 'A', sizeof(large_data));

  for (int i = 0; i < 50; i++) {
    large_data[0] = (char)('A' + (i % 26));
    large_data[4095] = (char)('Z' - (i % 26));

    int rv = valk_stream_body_write(body, large_data, sizeof(large_data));
    ASSERT_EQ(rv, 0);
  }

  ASSERT_EQ(body->queue_len, 50);

  valk_stream_chunk_t *chunk = body->queue_head;
  int idx = 0;
  while (chunk) {
    ASSERT_EQ(chunk->data_len, 4096);
    ASSERT_EQ(chunk->data[0], (char)('A' + (idx % 26)));
    ASSERT_EQ(chunk->data[4095], (char)('Z' - (idx % 26)));

    for (size_t j = 1; j < 4095; j++) {
      ASSERT_EQ(chunk->data[j], 'A');
    }

    valk_stream_chunk_t *next = chunk->next;
    free(chunk);
    chunk = next;
    idx++;
  }

  ASSERT_EQ(idx, 50);

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_concurrent_writes_mixed_sizes(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 1000;
  body->queue_len = 0;
  body->queue_head = nullptr;
  body->queue_tail = nullptr;
  body->next = nullptr;

  size_t sizes[] = {1, 10, 100, 1000, 5, 50, 500, 2, 20, 200};
  size_t num_sizes = sizeof(sizes) / sizeof(sizes[0]);
  char *buffers[10];

  for (size_t i = 0; i < num_sizes; i++) {
    buffers[i] = malloc(sizes[i]);
    memset(buffers[i], (char)('A' + i), sizes[i]);
    int rv = valk_stream_body_write(body, buffers[i], sizes[i]);
    ASSERT_EQ(rv, 0);
  }

  ASSERT_EQ(body->queue_len, num_sizes);

  valk_stream_chunk_t *chunk = body->queue_head;
  size_t idx = 0;
  while (chunk) {
    ASSERT_EQ(chunk->data_len, sizes[idx]);
    for (size_t j = 0; j < chunk->data_len; j++) {
      ASSERT_EQ(chunk->data[j], (char)('A' + idx));
    }

    valk_stream_chunk_t *next = chunk->next;
    free(chunk);
    chunk = next;
    idx++;
  }

  ASSERT_EQ(idx, num_sizes);

  for (size_t i = 0; i < num_sizes; i++) {
    free(buffers[i]);
  }

  free(body);
  free(conn);

  VALK_PASS();
}

static void test_concurrent_writes_rapid_succession(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 1;
  body->queue_max = 10000;
  body->queue_len = 0;
  body->queue_head = nullptr;
  body->queue_tail = nullptr;
  body->next = nullptr;

  char seq_data[8];
  for (int i = 0; i < 1000; i++) {
    memcpy(seq_data, &i, sizeof(int));
    seq_data[4] = (char)(i & 0xFF);
    seq_data[5] = (char)((i >> 8) & 0xFF);
    seq_data[6] = (char)((i >> 16) & 0xFF);
    seq_data[7] = (char)((i >> 24) & 0xFF);

    int rv = valk_stream_body_write(body, seq_data, sizeof(seq_data));
    ASSERT_EQ(rv, 0);
  }

  ASSERT_EQ(body->queue_len, 1000);

  valk_stream_chunk_t *chunk = body->queue_head;
  int idx = 0;
  while (chunk) {
    ASSERT_EQ(chunk->data_len, 8);

    int stored_val;
    memcpy(&stored_val, chunk->data, sizeof(int));
    ASSERT_EQ(stored_val, idx);
    ASSERT_EQ(chunk->data[4], (char)(idx & 0xFF));
    ASSERT_EQ(chunk->data[5], (char)((idx >> 8) & 0xFF));

    valk_stream_chunk_t *next = chunk->next;
    free(chunk);
    chunk = next;
    idx++;
  }

  ASSERT_EQ(idx, 1000);

  free(body);
  free(conn);

  VALK_PASS();
}

typedef struct {
  int callback_count;
  u64 captured_body_id;
  i32 captured_stream_id;
  valk_stream_state_e captured_state;
  bool captured_body_was_valid;
  pthread_mutex_t mutex;
} on_close_capture_t;

static void cb_on_close_capture(valk_stream_body_t *body, void *user_data) {
  on_close_capture_t *capture = user_data;
  pthread_mutex_lock(&capture->mutex);
  capture->callback_count++;
  capture->captured_body_was_valid = (body != nullptr);
  if (body) {
    capture->captured_body_id = body->id;
    capture->captured_stream_id = body->stream_id;
    capture->captured_state = body->state;
  }
  pthread_mutex_unlock(&capture->mutex);
}

static void test_on_close_callback_fires_once_on_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  on_close_capture_t capture = {0};
  pthread_mutex_init(&capture.mutex, nullptr);

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 42;
  body->id = 12345;
  body->queue_max = 100;
  body->queue_len = 0;
  body->on_close = cb_on_close_capture;
  body->user_data = &capture;
  body->next = nullptr;

  valk_stream_body_register(body);

  valk_stream_body_close(body);

  valk_stream_body_close(body);

  valk_stream_body_close(body);

  pthread_mutex_lock(&capture.mutex);
  int callback_count = capture.callback_count;
  pthread_mutex_unlock(&capture.mutex);

  ASSERT_TRUE(body->state == VALK_STREAM_CLOSING || body->state == VALK_STREAM_CLOSED);

  ASSERT_LE(callback_count, 1);

  pthread_mutex_destroy(&capture.mutex);
  free(body);
  free(conn);

  VALK_PASS();
}

static void test_on_close_callback_fires_once_on_close_all(VALK_TEST_ARGS()) {
  VALK_TEST();

  on_close_capture_t capture1 = {0};
  on_close_capture_t capture2 = {0};
  pthread_mutex_init(&capture1.mutex, nullptr);
  pthread_mutex_init(&capture2.mutex, nullptr);

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body1 = calloc(1, sizeof(valk_stream_body_t));
  body1->state = VALK_STREAM_OPEN;
  body1->conn = conn;
  body1->stream_id = 1;
  body1->id = 100;
  body1->queue_max = 100;
  body1->on_close = cb_on_close_capture;
  body1->user_data = &capture1;
  body1->next = nullptr;

  valk_stream_body_t *body2 = calloc(1, sizeof(valk_stream_body_t));
  body2->state = VALK_STREAM_OPEN;
  body2->conn = conn;
  body2->stream_id = 3;
  body2->id = 200;
  body2->queue_max = 100;
  body2->on_close = cb_on_close_capture;
  body2->user_data = &capture2;
  body2->next = nullptr;

  valk_stream_body_register(body1);
  valk_stream_body_register(body2);

  valk_stream_body_close_all(conn);

  valk_stream_body_close_all(conn);

  pthread_mutex_lock(&capture1.mutex);
  int count1 = capture1.callback_count;
  pthread_mutex_unlock(&capture1.mutex);

  pthread_mutex_lock(&capture2.mutex);
  int count2 = capture2.callback_count;
  pthread_mutex_unlock(&capture2.mutex);

  ASSERT_LE(count1, 1);
  ASSERT_LE(count2, 1);

  pthread_mutex_destroy(&capture1.mutex);
  pthread_mutex_destroy(&capture2.mutex);
  free(body1);
  free(body2);
  free(conn);

  VALK_PASS();
}

static void test_on_close_callback_can_access_stream_state(VALK_TEST_ARGS()) {
  VALK_TEST();

  on_close_capture_t capture = {0};
  pthread_mutex_init(&capture.mutex, nullptr);

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 777;
  body->id = 99999;
  body->queue_max = 100;
  body->queue_len = 0;
  body->on_close = cb_on_close_capture;
  body->user_data = &capture;
  body->next = nullptr;

  valk_stream_body_register(body);

  body->state = VALK_STREAM_CLOSED;
  if (body->on_close) {
    body->on_close(body, body->user_data);
  }

  pthread_mutex_lock(&capture.mutex);
  ASSERT_EQ(capture.callback_count, 1);
  ASSERT_TRUE(capture.captured_body_was_valid);
  ASSERT_EQ(capture.captured_body_id, 99999);
  ASSERT_EQ(capture.captured_stream_id, 777);
  ASSERT_EQ(capture.captured_state, VALK_STREAM_CLOSED);
  pthread_mutex_unlock(&capture.mutex);

  valk_stream_body_unregister(body);

  pthread_mutex_destroy(&capture.mutex);
  free(body);
  free(conn);

  VALK_PASS();
}

typedef struct {
  valk_stream_body_t *body;
  pthread_barrier_t *barrier;
} close_race_thread_arg_t;

static void *close_race_thread(void *arg) {
  close_race_thread_arg_t *ctx = arg;
  pthread_barrier_wait(ctx->barrier);
  valk_stream_body_close(ctx->body);
  return nullptr;
}

static void test_stream_body_close_pthread_race(VALK_TEST_ARGS()) {
  VALK_TEST();

  on_close_capture_t capture = {0};
  pthread_mutex_init(&capture.mutex, nullptr);

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 123;
  body->id = 77777;
  body->queue_max = 100;
  body->queue_len = 0;
  body->on_close = cb_on_close_capture;
  body->user_data = &capture;
  body->next = nullptr;

  valk_stream_body_register(body);

  pthread_barrier_t barrier;
  pthread_barrier_init(&barrier, nullptr, 2);

  close_race_thread_arg_t arg1 = {.body = body, .barrier = &barrier};
  close_race_thread_arg_t arg2 = {.body = body, .barrier = &barrier};

  pthread_t t1, t2;
  pthread_create(&t1, nullptr, close_race_thread, &arg1);
  pthread_create(&t2, nullptr, close_race_thread, &arg2);

  pthread_join(t1, nullptr);
  pthread_join(t2, nullptr);

  pthread_barrier_destroy(&barrier);

  ASSERT_TRUE(body->state == VALK_STREAM_CLOSING || body->state == VALK_STREAM_CLOSED);

  pthread_mutex_lock(&capture.mutex);
  int callback_count = capture.callback_count;
  pthread_mutex_unlock(&capture.mutex);

  ASSERT_LE(callback_count, 1);

  pthread_mutex_destroy(&capture.mutex);
  free(body);
  free(conn);

  VALK_PASS();
}

static void test_on_close_callback_timing_vs_unregister(VALK_TEST_ARGS()) {
  VALK_TEST();

  on_close_capture_t capture = {0};
  pthread_mutex_init(&capture.mutex, nullptr);

  valk_aio_handle_t *conn = calloc(1, sizeof(valk_aio_handle_t));
  conn->magic = VALK_AIO_HANDLE_MAGIC;
  conn->http.stream_bodies = nullptr;

  valk_stream_body_t *body = calloc(1, sizeof(valk_stream_body_t));
  body->state = VALK_STREAM_OPEN;
  body->conn = conn;
  body->stream_id = 55;
  body->id = 88888;
  body->queue_max = 100;
  body->queue_len = 0;
  body->on_close = cb_on_close_capture;
  body->user_data = &capture;
  body->next = nullptr;

  valk_stream_body_register(body);
  ASSERT_EQ(conn->http.stream_bodies, body);

  valk_stream_body_close(body);

  pthread_mutex_lock(&capture.mutex);
  int final_count = capture.callback_count;
  pthread_mutex_unlock(&capture.mutex);

  ASSERT_LE(final_count, 1);

  pthread_mutex_destroy(&capture.mutex);
  free(body);
  free(conn);

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_stream_body_write_queues_data", test_stream_body_write_queues_data);
  valk_testsuite_add_test(suite, "test_stream_body_new_with_real_session", test_stream_body_new_with_real_session);
  valk_testsuite_add_test(suite, "test_stream_body_writable_with_session", test_stream_body_writable_with_session);
  valk_testsuite_add_test(suite, "test_stream_body_backpressure_queue_max", test_stream_body_backpressure_queue_max);
  valk_testsuite_add_test(suite, "test_stream_body_on_close_callback_unit", test_stream_body_on_close_callback_unit);
  valk_testsuite_add_test(suite, "test_stream_body_on_drain_callback_setup", test_stream_body_on_drain_callback_setup);
  valk_testsuite_add_test(suite, "test_stream_body_close_idempotent", test_stream_body_close_idempotent);
  valk_testsuite_add_test(suite, "test_stream_body_write_after_close_fails", test_stream_body_write_after_close_fails);
  valk_testsuite_add_test(suite, "test_stream_body_writable_reflects_state", test_stream_body_writable_reflects_state);
  valk_testsuite_add_test(suite, "test_stream_body_queue_len_tracking", test_stream_body_queue_len_tracking);
  valk_testsuite_add_test(suite, "test_stream_body_activity_tracking", test_stream_body_activity_tracking);
  valk_testsuite_add_test(suite, "test_stream_body_idle_timeout_behavior", test_stream_body_idle_timeout_behavior);
  valk_testsuite_add_test(suite, "test_stream_body_register_unregister", test_stream_body_register_unregister);
  valk_testsuite_add_test(suite, "test_stream_body_bytes_sent_tracking", test_stream_body_bytes_sent_tracking);
  valk_testsuite_add_test(suite, "test_stream_write_during_close_returns_error", test_stream_write_during_close_returns_error);
  valk_testsuite_add_test(suite, "test_stream_writable_false_during_close", test_stream_writable_false_during_close);
  valk_testsuite_add_test(suite, "test_stream_close_all_closes_multiple_bodies", test_stream_close_all_closes_multiple_bodies);
  valk_testsuite_add_test(suite, "test_stream_write_after_close_all_fails", test_stream_write_after_close_all_fails);
  valk_testsuite_add_test(suite, "test_stream_close_by_stream_id_unit", test_stream_close_by_stream_id_unit);
  valk_testsuite_add_test(suite, "test_stream_close_by_stream_id_null_conn", test_stream_close_by_stream_id_null_conn);
  valk_testsuite_add_test(suite, "test_stream_close_all_null_conn", test_stream_close_all_null_conn);
  valk_testsuite_add_test(suite, "test_stream_close_idempotent_during_race", test_stream_close_idempotent_during_race);
  valk_testsuite_add_test(suite, "test_concurrent_writes_order_preserved", test_concurrent_writes_order_preserved);
  valk_testsuite_add_test(suite, "test_concurrent_writes_no_corruption", test_concurrent_writes_no_corruption);
  valk_testsuite_add_test(suite, "test_concurrent_writes_mixed_sizes", test_concurrent_writes_mixed_sizes);
  valk_testsuite_add_test(suite, "test_concurrent_writes_rapid_succession", test_concurrent_writes_rapid_succession);
  valk_testsuite_add_test(suite, "test_on_close_callback_fires_once_on_close", test_on_close_callback_fires_once_on_close);
  valk_testsuite_add_test(suite, "test_on_close_callback_fires_once_on_close_all", test_on_close_callback_fires_once_on_close_all);
  valk_testsuite_add_test(suite, "test_on_close_callback_can_access_stream_state", test_on_close_callback_can_access_stream_state);
  valk_testsuite_add_test(suite, "test_on_close_callback_timing_vs_unregister", test_on_close_callback_timing_vs_unregister);
  valk_testsuite_add_test(suite, "test_stream_body_close_pthread_race", test_stream_body_close_pthread_race);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
