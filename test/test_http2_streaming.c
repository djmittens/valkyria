// test/test_http2_streaming.c
// Systematic HTTP2/streaming coverage improvements

#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"
#include "aio/http2/aio_http2_conn_fsm.h"
#include "aio/http2/stream/aio_stream_body.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

// ============================================================================
// Connection FSM State Transition Tests
// ============================================================================

static void test_conn_state_str(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_INIT), "INIT");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_HANDSHAKING), "HANDSHAKING");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_ESTABLISHED), "ESTABLISHED");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_GOAWAY_SENT), "GOAWAY_SENT");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_DRAINING), "DRAINING");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_CLOSING), "CLOSING");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_CLOSED), "CLOSED");
  ASSERT_STR_EQ(valk_conn_state_str(VALK_CONN_ERROR), "ERROR");

  VALK_PASS();
}

static void test_conn_event_str(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_START_HANDSHAKE), "START_HANDSHAKE");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_HANDSHAKE_COMPLETE), "HANDSHAKE_COMPLETE");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_HANDSHAKE_FAILED), "HANDSHAKE_FAILED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_SEND_GOAWAY), "SEND_GOAWAY");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_GOAWAY_ACKED), "GOAWAY_ACKED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_STREAMS_DRAINED), "STREAMS_DRAINED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_CLOSE), "CLOSE");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_CLOSED), "CLOSED");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_ERROR), "ERROR");
  ASSERT_STR_EQ(valk_conn_event_str(VALK_CONN_EVT_TIMEOUT), "TIMEOUT");

  VALK_PASS();
}

static void test_conn_is_closing_or_closed(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_FALSE(valk_conn_is_closing_or_closed(VALK_CONN_INIT));
  ASSERT_FALSE(valk_conn_is_closing_or_closed(VALK_CONN_HANDSHAKING));
  ASSERT_FALSE(valk_conn_is_closing_or_closed(VALK_CONN_ESTABLISHED));

  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_GOAWAY_SENT));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_DRAINING));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_CLOSING));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_CLOSED));
  ASSERT_TRUE(valk_conn_is_closing_or_closed(VALK_CONN_ERROR));

  VALK_PASS();
}

// ============================================================================
// Stream Body Edge Cases
// ============================================================================

static void test_stream_body_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  nghttp2_data_provider2 data_prd;

  valk_stream_body_t *body = valk_stream_body_new(nullptr, nullptr, 1, &data_prd, nullptr);
  ASSERT_NULL(body);

  VALK_PASS();
}

static void test_stream_body_close_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_stream_body_close(nullptr);

  VALK_PASS();
}

static void test_stream_body_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_stream_body_free(nullptr);

  VALK_PASS();
}

static void test_stream_body_write_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  int rv = valk_stream_body_write(nullptr, "test", 4);
  ASSERT_EQ(rv, -1);

  VALK_PASS();
}

static void test_stream_body_writable_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool writable = valk_stream_body_writable(nullptr);
  ASSERT_FALSE(writable);

  VALK_PASS();
}

static void test_stream_body_queue_len_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  u64 len = valk_stream_body_queue_len(nullptr);
  ASSERT_EQ(len, 0);

  VALK_PASS();
}

// ============================================================================
// HTTP2 Server/Client Integration Edge Cases
// ============================================================================

typedef struct {
  int connectedCount;
  int disconnectedCount;
  int requestCount;
  int errorCount;
} test_handler_state_t;

static void cb_test_onConnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  test_handler_state_t *state = arg;
  __atomic_fetch_add(&state->connectedCount, 1, __ATOMIC_RELAXED);
}

static void cb_test_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  test_handler_state_t *state = arg;
  __atomic_fetch_add(&state->disconnectedCount, 1, __ATOMIC_RELAXED);
}

static void cb_test_onHeader(void *arg, valk_aio_handle_t *conn, u64 stream,
                              char *name, char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void cb_test_onBody(void *arg, valk_aio_handle_t *conn, u64 stream,
                            u8 flags, valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

static void test_http2_rapid_connect_disconnect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

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

  for (int i = 0; i < 5; i++) {
    valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_lval_t *client_result = valk_async_handle_await(hclient);
    ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);
  }

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  size_t connected = __atomic_load_n(&state.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, 5);

  VALK_PASS();
}

static void test_http2_server_port_accessor(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

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

  int port = valk_aio_http2_server_get_port_from_ref(server_result);
  ASSERT_GT(port, 0);
  ASSERT_LT(port, 65536);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_http2_server_is_stopped(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

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

  ASSERT_FALSE(valk_aio_http2_server_is_stopped(srv));

  valk_async_handle_t *stop_handle = valk_aio_http2_stop(srv);
  valk_async_handle_await(stop_handle);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_http2_concurrent_requests_same_connection(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

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

  valk_aio_http2_client *client = client_result->ref.ptr;

  #define NUM_CONCURRENT_REQUESTS 10
  valk_async_handle_t *request_handles[NUM_CONCURRENT_REQUESTS];

  for (int i = 0; i < NUM_CONCURRENT_REQUESTS; i++) {
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
      req->path = "/";
      req->body = (u8 *)"";
      req->bodyLen = 0;
      da_init(&req->headers);
    }

    request_handles[i] = valk_aio_http2_request_send(req, client);
  }

  for (int i = 0; i < NUM_CONCURRENT_REQUESTS; i++) {
    valk_lval_t *res = valk_async_handle_await(request_handles[i]);
    ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);
  }
  #undef NUM_CONCURRENT_REQUESTS

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_http2_large_request_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

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

  valk_aio_http2_client *client = client_result->ref.ptr;

  #define LARGE_BODY_SIZE (64 * 1024)
  char *large_body = malloc(LARGE_BODY_SIZE);
  ASSERT_NOT_NULL(large_body);
  memset(large_body, 'X', LARGE_BODY_SIZE);

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)req_arena;
    req->method = "POST";
    req->scheme = "https";
    req->authority = "localhost";
    req->path = "/";
    req->body = (u8 *)large_body;
    req->bodyLen = LARGE_BODY_SIZE;
    da_init(&req->headers);
  }

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);
  ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);

  free(large_body);
  #undef LARGE_BODY_SIZE

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_http2_empty_request_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

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

  valk_aio_http2_client *client = client_result->ref.ptr;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)req_arena;
    req->method = "POST";
    req->scheme = "https";
    req->authority = "localhost";
    req->path = "/empty";
    req->body = nullptr;
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);
  ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_http2_different_methods(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

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

  valk_aio_http2_client *client = client_result->ref.ptr;

  const char *methods[] = {"GET", "POST", "PUT", "DELETE"};

  for (int i = 0; i < 4; i++) {
    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);

    valk_http2_request_t *req;
    VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
      req = valk_mem_alloc(sizeof(valk_http2_request_t));
      req->allocator = (void *)req_arena;
      req->method = (char *)methods[i];
      req->scheme = "https";
      req->authority = "localhost";
      req->path = "/";
      req->body = (u8 *)"";
      req->bodyLen = 0;
      da_init(&req->headers);
    }

    valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
    valk_lval_t *res = valk_async_handle_await(hres);
    ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);
  }

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_http2_invalid_host_connection(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "invalid.host.that.does.not.exist", 443, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);

  ASSERT_TRUE(LVAL_TYPE(client_result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_http2_connection_refused(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", 59998, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);

  ASSERT_TRUE(LVAL_TYPE(client_result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

// ============================================================================
// AIO System Configuration Tests
// ============================================================================

static void test_aio_system_name_set_get(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_set_name(sys, "test-system");
  const char *name = valk_aio_get_name(sys);
  ASSERT_NOT_NULL(name);
  ASSERT_STR_EQ(name, "test-system");

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_aio_system_shutdown_twice(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_stop(sys);
  valk_aio_stop(sys);

  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_conn_state_str", test_conn_state_str);
  valk_testsuite_add_test(suite, "test_conn_event_str", test_conn_event_str);
  valk_testsuite_add_test(suite, "test_conn_is_closing_or_closed", test_conn_is_closing_or_closed);

  valk_testsuite_add_test(suite, "test_stream_body_null_args", test_stream_body_null_args);
  valk_testsuite_add_test(suite, "test_stream_body_close_null", test_stream_body_close_null);
  valk_testsuite_add_test(suite, "test_stream_body_free_null", test_stream_body_free_null);
  valk_testsuite_add_test(suite, "test_stream_body_write_null", test_stream_body_write_null);
  valk_testsuite_add_test(suite, "test_stream_body_writable_null", test_stream_body_writable_null);
  valk_testsuite_add_test(suite, "test_stream_body_queue_len_null", test_stream_body_queue_len_null);

  valk_testsuite_add_test(suite, "test_http2_rapid_connect_disconnect", test_http2_rapid_connect_disconnect);
  valk_testsuite_add_test(suite, "test_http2_server_port_accessor", test_http2_server_port_accessor);
  valk_testsuite_add_test(suite, "test_http2_server_is_stopped", test_http2_server_is_stopped);
  valk_testsuite_add_test(suite, "test_http2_concurrent_requests_same_connection", test_http2_concurrent_requests_same_connection);
  valk_testsuite_add_test(suite, "test_http2_large_request_body", test_http2_large_request_body);
  valk_testsuite_add_test(suite, "test_http2_empty_request_body", test_http2_empty_request_body);
  valk_testsuite_add_test(suite, "test_http2_different_methods", test_http2_different_methods);
  valk_testsuite_add_test(suite, "test_http2_invalid_host_connection", test_http2_invalid_host_connection);
  valk_testsuite_add_test(suite, "test_http2_connection_refused", test_http2_connection_refused);

  valk_testsuite_add_test(suite, "test_aio_system_name_set_get", test_aio_system_name_set_get);
  valk_testsuite_add_test(suite, "test_aio_system_shutdown_twice", test_aio_system_shutdown_twice);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
