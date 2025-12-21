#include "../testing.h"
#include "../../src/common.h"
#include "../../src/memory.h"
#include "../../src/aio.h"
#include "../../src/aio_alloc.h"
#include "../../src/collections.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <pthread.h>
#include <sys/socket.h>
#include <netinet/in.h>

typedef struct {
  int connectedCount;
  int disconnectedCount;
} valk_srv_state_t;

static int get_available_port(void) {
  int sock = socket(AF_INET, SOCK_STREAM, 0);
  if (sock < 0) return -1;

  struct sockaddr_in addr = {
    .sin_family = AF_INET,
    .sin_addr.s_addr = INADDR_ANY,
    .sin_port = 0,
  };

  if (bind(sock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
    close(sock);
    return -1;
  }

  socklen_t len = sizeof(addr);
  if (getsockname(sock, (struct sockaddr *)&addr, &len) < 0) {
    close(sock);
    return -1;
  }

  int port = ntohs(addr.sin_port);
  close(sock);
  return port;
}

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

static void cb_onHeader(void *arg, valk_aio_handle_t *conn, size_t stream, char *name,
                 char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void cb_onBody(void *arg, valk_aio_handle_t *conn, size_t stream, uint8_t flags,
               valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

void test_demo_config_has_reasonable_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  ASSERT_EQ(cfg.max_connections, 8);
  ASSERT_EQ(cfg.backpressure_list_max, 50);
  ASSERT_EQ(cfg.pending_stream_pool_size, 24);

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NULL(err);

  VALK_PASS();
}

void test_backpressure_config_validation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.backpressure_list_max = 0;
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);
  ASSERT_GT(cfg.backpressure_list_max, 0);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
void test_server_start_initializes_slabs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  int port = get_available_port();
  ASSERT_GT(port, 0);

  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", port, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  ASSERT_NOT_NULL(tcp_slab);

  size_t initial_available = valk_slab_available(tcp_slab);
  ASSERT_GT(initial_available, 0);

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_multiple_connections(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  int port = get_available_port();
  ASSERT_GT(port, 0);

  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", port, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

  valk_arc_box *clients[4];
  valk_future *futures[4];
  int connected = 0;

  for (int i = 0; i < 4; i++) {
    futures[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clients[i] = valk_future_await(futures[i]);
    if (clients[i]->type == VALK_SUC) {
      connected++;
    }
  }

  ASSERT_EQ(connected, 4);

  for (int i = 0; i < 4; i++) {
    valk_arc_release(clients[i]);
    valk_arc_release(futures[i]);
  }

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  size_t server_connected = __atomic_load_n(&state.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(server_connected, 4);

  VALK_PASS();
}

void test_watermark_thresholds(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.70f;
  cfg.buffer_critical_watermark = 0.90f;

  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NULL(err);

  ASSERT_EQ(cfg.buffer_high_watermark, 0.70f);
  ASSERT_EQ(cfg.buffer_critical_watermark, 0.90f);

  VALK_PASS();
}

void test_connection_with_request_response(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  int port = get_available_port();
  ASSERT_GT(port, 0);

  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", port, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  uint8_t req_buf[sizeof(valk_mem_arena_t) + 4096];
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
    req->body = (uint8_t *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_http2_response_t *response = res->item;
  ASSERT_NOT_NULL(response);
  ASSERT_GT(response->bodyLen, 0);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_system_metrics_access(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  valk_aio_metrics_t *metrics = valk_aio_get_metrics(sys);
  ASSERT_NOT_NULL(metrics);

  valk_aio_system_stats_t *stats = valk_aio_get_system_stats(sys);
  ASSERT_NOT_NULL(stats);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_sse_close_all_streams_null_safe(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_sse_close_all_streams(NULL);

  VALK_PASS();
}

void test_server_listen_invalid_address(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_future *fserv = valk_aio_http2_listen(
      sys, "not.a.valid.ip.address", 8080, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_ERR);

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_server_listen_port_already_bound(VALK_TEST_ARGS()) {
  VALK_TEST();

  int port = get_available_port();
  ASSERT_GT(port, 0);

  int sock = socket(AF_INET, SOCK_STREAM, 0);
  ASSERT_GT(sock, 0);

  struct sockaddr_in addr = {
    .sin_family = AF_INET,
    .sin_addr.s_addr = INADDR_ANY,
    .sin_port = htons(port),
  };

  int bound = bind(sock, (struct sockaddr *)&addr, sizeof(addr));
  ASSERT_EQ(bound, 0);

  int listening = listen(sock, 1);
  ASSERT_EQ(listening, 0);

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", port, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_ERR);

  valk_arc_release(server);
  valk_arc_release(fserv);

  close(sock);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}
#endif

int main(void) {
  valk_mem_init_malloc();
  valk_aio_alloc_init();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_demo_config_has_reasonable_defaults",
                          test_demo_config_has_reasonable_defaults);
  valk_testsuite_add_test(suite, "test_backpressure_config_validation",
                          test_backpressure_config_validation);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_server_start_initializes_slabs",
                          test_server_start_initializes_slabs);
  valk_testsuite_add_test(suite, "test_multiple_connections",
                          test_multiple_connections);
  valk_testsuite_add_test(suite, "test_watermark_thresholds",
                          test_watermark_thresholds);
  valk_testsuite_add_test(suite, "test_connection_with_request_response",
                          test_connection_with_request_response);
  valk_testsuite_add_test(suite, "test_system_metrics_access",
                          test_system_metrics_access);
  valk_testsuite_add_test(suite, "test_sse_close_all_streams_null_safe",
                          test_sse_close_all_streams_null_safe);
  valk_testsuite_add_test(suite, "test_server_listen_invalid_address",
                          test_server_listen_invalid_address);
  valk_testsuite_add_test(suite, "test_server_listen_port_already_bound",
                          test_server_listen_port_already_bound);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
