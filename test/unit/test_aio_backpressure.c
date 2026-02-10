#include "../testing.h"
#include "../../src/common.h"
#include "../../src/memory.h"
#include "../../src/aio/aio.h"
#include "../../src/aio/aio_alloc.h"
#include "../../src/aio/aio_async.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/aio/aio_metrics.h"
#include "../../src/aio/aio_metrics_v2.h"
#include "../../src/collections.h"
#include "../../src/parser.h"

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

void test_demo_config_has_reasonable_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  ASSERT_EQ(cfg.max_connections, 8);
  ASSERT_EQ(cfg.backpressure_list_max, 50);

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

void test_server_start_initializes_slabs(VALK_TEST_ARGS()) {
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

  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(hserv);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  ASSERT_NOT_NULL(tcp_slab);

  size_t initial_available = valk_slab_available(tcp_slab);
  ASSERT_GT(initial_available, 0);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_multiple_connections(VALK_TEST_ARGS()) {
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

  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(hserv);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_lval_t *client_results[4];
  valk_async_handle_t *hclients[4];
  int connected = 0;

  for (int i = 0; i < 4; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
    if (LVAL_TYPE(client_results[i]) != LVAL_ERR) {
      connected++;
    }
  }

  ASSERT_EQ(connected, 4);

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

  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(hserv);
  ASSERT_EQ(LVAL_TYPE(server_result), LVAL_REF);

  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server_result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);

  valk_aio_http2_client *client = client_result->ref.ptr;

  alignas(max_align_t) u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
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

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);
  ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);

  valk_http2_response_t *response = res->ref.ptr;
  ASSERT_NOT_NULL(response);
  ASSERT_GT(response->bodyLen, 0);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_system_metrics_access(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  valk_aio_metrics_v2_t *metrics = VALK_METRICS_V2(sys);
  ASSERT_NOT_NULL(metrics);

  valk_aio_system_stats_v2_t *stats = VALK_SYSTEM_STATS_V2(sys);
  ASSERT_NOT_NULL(stats);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

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

  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "not.a.valid.ip.address", 8080, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(hserv);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_ERR);

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

  // NOLINTNEXTLINE(clang-analyzer-unix.StdCLibraryFunctions) - sock validated by ASSERT_GT above
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

  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", port, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(hserv);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_ERR);

  close(sock);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_aio_alloc_init();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_demo_config_has_reasonable_defaults",
                          test_demo_config_has_reasonable_defaults);
  valk_testsuite_add_test(suite, "test_backpressure_config_validation",
                          test_backpressure_config_validation);

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
  valk_testsuite_add_test(suite, "test_server_listen_invalid_address",
                          test_server_listen_invalid_address);
  valk_testsuite_add_test(suite, "test_server_listen_port_already_bound",
                          test_server_listen_port_already_bound);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
