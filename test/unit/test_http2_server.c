#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"
#include "../../src/metrics_v2.h"
#include "../../src/aio/http2/aio_http2_server.h"
#include "../../src/aio/aio_internal.h"
#include "../../src/aio/aio_ops.h"

#include <stdlib.h>

static valk_aio_http_server *create_test_server(void) {
  valk_aio_http_server *srv = calloc(1, sizeof(valk_aio_http_server));
  srv->port = 8080;
  srv->state = VALK_SRV_LISTENING;
  strncpy(srv->interface, "127.0.0.1", sizeof(srv->interface));
  return srv;
}

static void free_test_server(valk_aio_http_server *srv) {
  free(srv);
}

static valk_aio_system_t *create_test_system(void) {
  valk_aio_system_t *sys = calloc(1, sizeof(valk_aio_system_t));
  sys->ops = &valk_aio_ops_test;
  sys->config.max_servers = 8;
  sys->port_strs = calloc(sys->config.max_servers, 8);
  sys->port_str_idx = 0;
  sys->metrics_state = calloc(1, sizeof(valk_aio_metrics_state_t));
  sys->metrics_state->metrics_v2 = calloc(1, 256);
  sys->metrics_state->system_stats_v2 = calloc(1, 256);
  return sys;
}

static void free_test_system(valk_aio_system_t *sys) {
  free(sys->port_strs);
  free(sys->metrics_state->metrics_v2);
  free(sys->metrics_state->system_stats_v2);
  free(sys->metrics_state);
  free(sys);
}

void test_server_get_port(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();

  int port = valk_aio_http2_server_get_port(srv);
  ASSERT_EQ(port, 8080);

  srv->port = 443;
  port = valk_aio_http2_server_get_port(srv);
  ASSERT_EQ(port, 443);

  free_test_server(srv);
  VALK_PASS();
}

void test_server_is_stopped_null(VALK_TEST_ARGS()) {
  VALK_TEST();
  bool stopped = valk_aio_http2_server_is_stopped(nullptr);
  ASSERT_TRUE(stopped);
  VALK_PASS();
}

void test_server_is_stopped_listening(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();
  srv->state = VALK_SRV_LISTENING;

  bool stopped = valk_aio_http2_server_is_stopped(srv);
  ASSERT_FALSE(stopped);

  free_test_server(srv);
  VALK_PASS();
}

void test_server_is_stopped_closing(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();
  srv->state = VALK_SRV_CLOSING;

  bool stopped = valk_aio_http2_server_is_stopped(srv);
  ASSERT_TRUE(stopped);

  free_test_server(srv);
  VALK_PASS();
}

void test_server_is_stopped_closed(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();
  srv->state = VALK_SRV_CLOSED;

  bool stopped = valk_aio_http2_server_is_stopped(srv);
  ASSERT_TRUE(stopped);

  free_test_server(srv);
  VALK_PASS();
}

void test_server_from_ref(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();

  valk_lval_t ref;
  memset(&ref, 0, sizeof(ref));
  ref.ref.ptr = srv;

  valk_aio_http_server *result = valk_aio_http2_server_from_ref(&ref);
  ASSERT_EQ(result, srv);

  free_test_server(srv);
  VALK_PASS();
}

void test_server_get_port_from_ref(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();
  srv->port = 3000;

  valk_lval_t ref;
  memset(&ref, 0, sizeof(ref));
  ref.ref.ptr = srv;

  int port = valk_aio_http2_server_get_port_from_ref(&ref);
  ASSERT_EQ(port, 3000);

  free_test_server(srv);
  VALK_PASS();
}

void test_cleanup_all_servers_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http2_cleanup_all_servers(nullptr);
  VALK_PASS();
}

void test_cleanup_all_servers_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();
  sys->serverList = nullptr;

  valk_aio_http2_cleanup_all_servers(sys);
  ASSERT_NULL(sys->serverList);

  free_test_system(sys);
  VALK_PASS();
}

void test_server_metrics_init(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_mem_init_malloc();
  valk_metrics_registry_init();

  valk_aio_system_t *sys = create_test_system();
  valk_server_metrics_t metrics;
  memset(&metrics, 0, sizeof(metrics));

  valk_http2_server_metrics_init(sys, &metrics, "test-server", 8080, "https", "main");

  ASSERT_NOT_NULL(metrics.requests_total);
  ASSERT_NOT_NULL(metrics.requests_success);
  ASSERT_NOT_NULL(metrics.requests_client_error);
  ASSERT_NOT_NULL(metrics.requests_server_error);
  ASSERT_NOT_NULL(metrics.connections_active);
  ASSERT_NOT_NULL(metrics.sse_streams_active);
  ASSERT_NOT_NULL(metrics.request_duration);
  ASSERT_NOT_NULL(metrics.sse_stream_duration);
  ASSERT_NOT_NULL(metrics.bytes_sent);
  ASSERT_NOT_NULL(metrics.bytes_recv);
  ASSERT_NOT_NULL(metrics.overload_responses);

  valk_metrics_registry_destroy();
  free_test_system(sys);
  VALK_PASS();
}

void test_server_metrics_init_port_str_wrap(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_mem_init_malloc();
  valk_metrics_registry_init();

  valk_aio_system_t *sys = create_test_system();
  sys->port_str_idx = 7;

  valk_server_metrics_t metrics;
  memset(&metrics, 0, sizeof(metrics));

  valk_http2_server_metrics_init(sys, &metrics, "srv1", 8080, "http", "loop1");
  ASSERT_EQ(sys->port_str_idx, 8);

  valk_http2_server_metrics_init(sys, &metrics, "srv2", 9090, "https", "loop2");
  ASSERT_EQ(sys->port_str_idx, 9);

  valk_metrics_registry_destroy();
  free_test_system(sys);
  VALK_PASS();
}

void test_http2_stop_null_srv(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_async_handle_t *result = valk_aio_http2_stop(nullptr);
  ASSERT_NULL(result);
  VALK_PASS();
}

void test_http2_stop_null_sys(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();
  srv->sys = nullptr;

  valk_async_handle_t *result = valk_aio_http2_stop(srv);
  ASSERT_NULL(result);

  free_test_server(srv);
  VALK_PASS();
}

void test_server_set_handler_null_handler(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();
  srv->lisp_handler_handle = (valk_handle_t){0, 0};

  valk_aio_http2_server_set_handler(srv, nullptr);

  ASSERT_EQ(srv->lisp_handler_handle.generation, 0);

  free_test_server(srv);
  VALK_PASS();
}

void test_cleanup_all_servers_with_servers(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_t *sys = create_test_system();

  sys->httpServers = valk_slab_new(sizeof(valk_aio_http_server), 4);
  valk_aio_http_server *srv1 = (valk_aio_http_server *)valk_slab_aquire(sys->httpServers)->data;
  valk_aio_http_server *srv2 = (valk_aio_http_server *)valk_slab_aquire(sys->httpServers)->data;
  memset(srv1, 0, sizeof(*srv1));
  memset(srv2, 0, sizeof(*srv2));

  srv1->sys = sys;
  srv1->port = 8080;
  srv1->ssl_ctx = nullptr;
  srv1->lisp_handler_handle = (valk_handle_t){0, 0};

  srv2->sys = sys;
  srv2->port = 8081;
  srv2->ssl_ctx = nullptr;
  srv2->lisp_handler_handle = (valk_handle_t){0, 0};

  srv1->next = srv2;
  srv2->prev = srv1;
  sys->serverList = srv1;

  valk_aio_http2_cleanup_all_servers(sys);

  ASSERT_NULL(sys->serverList);

  valk_slab_free(sys->httpServers);
  free_test_system(sys);
  VALK_PASS();
}

void test_server_is_stopped_init_state(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_http_server *srv = create_test_server();
  srv->state = VALK_SRV_INIT;

  bool stopped = valk_aio_http2_server_is_stopped(srv);
  ASSERT_FALSE(stopped);

  free_test_server(srv);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_server_get_port", test_server_get_port);
  valk_testsuite_add_test(suite, "test_server_is_stopped_null", test_server_is_stopped_null);
  valk_testsuite_add_test(suite, "test_server_is_stopped_listening", test_server_is_stopped_listening);
  valk_testsuite_add_test(suite, "test_server_is_stopped_closing", test_server_is_stopped_closing);
  valk_testsuite_add_test(suite, "test_server_is_stopped_closed", test_server_is_stopped_closed);
  valk_testsuite_add_test(suite, "test_server_from_ref", test_server_from_ref);
  valk_testsuite_add_test(suite, "test_server_get_port_from_ref", test_server_get_port_from_ref);
  valk_testsuite_add_test(suite, "test_cleanup_all_servers_null_sys", test_cleanup_all_servers_null_sys);
  valk_testsuite_add_test(suite, "test_cleanup_all_servers_empty_list", test_cleanup_all_servers_empty_list);
  valk_testsuite_add_test(suite, "test_server_metrics_init", test_server_metrics_init);
  valk_testsuite_add_test(suite, "test_server_metrics_init_port_str_wrap", test_server_metrics_init_port_str_wrap);
  valk_testsuite_add_test(suite, "test_http2_stop_null_srv", test_http2_stop_null_srv);
  valk_testsuite_add_test(suite, "test_http2_stop_null_sys", test_http2_stop_null_sys);
  valk_testsuite_add_test(suite, "test_server_set_handler_null_handler", test_server_set_handler_null_handler);
  valk_testsuite_add_test(suite, "test_cleanup_all_servers_with_servers", test_cleanup_all_servers_with_servers);
  valk_testsuite_add_test(suite, "test_server_is_stopped_init_state", test_server_is_stopped_init_state);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
