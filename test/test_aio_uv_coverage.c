#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <unistd.h>
#include <nghttp2/nghttp2.h>
#include <uv.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "collections.h"
#include "common.h"
#include "concurrency.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

typedef struct {
  int connectedCount;
  int disconnectedCount;
  int headerCount;
  int bodyCount;
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
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->headerCount, 1, __ATOMIC_RELAXED);
}

static void cb_onBody(void *arg, valk_aio_handle_t *conn, u64 stream, u8 flags,
               valk_buffer_t *buf) {
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->bodyCount, 1, __ATOMIC_RELAXED);
}

static valk_http2_request_t* create_request(valk_mem_arena_t *arena,
                                             const char *method,
                                             const char *path) {
  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    memset(req, 0, sizeof(*req));
    req->allocator = (void *)arena;
    req->method = (char*)method;
    req->scheme = "https";
    req->authority = "localhost";
    size_t path_len = strlen(path) + 1;
    req->path = valk_mem_alloc(path_len);
    memcpy(req->path, path, path_len);
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }
  return req;
}

static valk_http2_request_t* create_request_with_headers(valk_mem_arena_t *arena,
                                                          const char *method,
                                                          const char *path,
                                                          const char *header_name,
                                                          const char *header_value) {
  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    memset(req, 0, sizeof(*req));
    req->allocator = (void *)arena;
    req->method = (char*)method;
    req->scheme = "https";
    req->authority = "localhost";
    req->path = (char*)path;
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);

    struct valk_http2_header_t h = {
      .name = (u8*)header_name,
      .value = (u8*)header_value,
      .nameLen = strlen(header_name),
      .valueLen = strlen(header_value),
    };
    da_add(&req->headers, h);
  }
  return req;
}

static void test_config_validation_max_connections(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 0;
  ASSERT_NOT_NULL(valk_aio_system_config_validate(&cfg));

  cfg.max_connections = 100001;
  ASSERT_NOT_NULL(valk_aio_system_config_validate(&cfg));

  VALK_PASS();
}

static void test_config_validation_max_streams(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_concurrent_streams = 0;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "max_concurrent_streams");

  cfg.max_concurrent_streams = 1001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_handles(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_handles = 15;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "max_handles");

  cfg.max_handles = 100001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_servers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_servers = 0;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "max_servers");

  cfg.max_servers = 65;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_clients(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_clients = 0;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "max_clients");

  cfg.max_clients = 65;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_tcp_buffer_pool(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.tcp_buffer_pool_size = 1;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "tcp_buffer_pool_size");

  cfg.tcp_buffer_pool_size = 1000001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_arena_pool(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.arena_pool_size = 0;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "arena_pool_size");

  cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.arena_pool_size = 10001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_arena_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.arena_size = (1 << 19);
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "arena_size");

  cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.arena_size = (257ULL << 20);
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_request_body_size(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.max_request_body_size = (1 << 9);
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "max_request_body_size");

  cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.max_request_body_size = (2ULL << 30);
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_queue_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.queue_capacity = 1;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "queue_capacity");

  cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.queue_capacity = 100001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.backpressure_list_max = 0;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "backpressure_list_max");

  cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.backpressure_list_max = 100001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_backpressure_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.backpressure_timeout_ms = 999;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "backpressure_timeout_ms");

  cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.backpressure_timeout_ms = 600001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_pending_stream_pool(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.pending_stream_pool_size = 0;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "pending_stream_pool_size");

  cfg = valk_aio_config_demo();
  valk_aio_system_config_resolve(&cfg);
  cfg.pending_stream_pool_size = 10001;
  err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);

  VALK_PASS();
}

static void test_config_validation_relationships(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 50;
  cfg.queue_capacity = 200;
  cfg.arena_pool_size = 100;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "tcp_buffer_pool_size must be >= max_connections");

  VALK_PASS();
}

static void test_config_validation_arena_relationship(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 200;
  cfg.queue_capacity = 200;
  cfg.arena_pool_size = 5;
  const char *err = valk_aio_system_config_validate(&cfg);
  ASSERT_NOT_NULL(err);
  ASSERT_STR_CONTAINS(err, "arena_pool_size must be >= max_connections / 10");

  VALK_PASS();
}

static void test_config_resolve_defaults(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  ASSERT_EQ(cfg.max_connections, 100);
  ASSERT_EQ(cfg.max_concurrent_streams, 100);
  ASSERT_EQ(cfg.max_handles, 2056);
  ASSERT_EQ(cfg.max_servers, 8);
  ASSERT_EQ(cfg.max_clients, 8);
  ASSERT_GT(cfg.tcp_buffer_pool_size, 0);
  ASSERT_GT(cfg.arena_pool_size, 0);
  ASSERT_EQ(cfg.arena_size, 64 * 1024 * 1024);
  ASSERT_EQ(cfg.max_request_body_size, 8 * 1024 * 1024);
  ASSERT_GT(cfg.queue_capacity, 0);
  ASSERT_DOUBLE_EQ(cfg.buffer_high_watermark, 0.85f, 0.01f);
  ASSERT_DOUBLE_EQ(cfg.buffer_critical_watermark, 0.95f, 0.01f);

  VALK_PASS();
}

static void test_config_resolve_invalid_watermarks(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.95f;
  cfg.buffer_critical_watermark = 0.85f;
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, -1);

  VALK_PASS();
}

static void test_request_with_custom_headers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 8192];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 8192);

  valk_http2_request_t *req = create_request_with_headers(
      req_arena, "GET", "/test", "x-custom-header", "custom-value");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_http2_response_t *response = res->item;
  ASSERT_NOT_NULL(response);
  ASSERT_NOT_NULL(response->body);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_multiple_paths(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  const char *paths[] = {"/", "/api", "/api/v1", "/health", "/metrics"};

  for (size_t i = 0; i < sizeof(paths) / sizeof(paths[0]); i++) {
    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);

    valk_http2_request_t *req = create_request(req_arena, "GET", paths[i]);

    valk_future *fres = valk_aio_http2_request_send(req, client);
    valk_arc_box *res = valk_future_await(fres);
    ASSERT_EQ(res->type, VALK_SUC);

    valk_arc_release(res);
    valk_arc_release(fres);
  }

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_concurrent_streams_same_connection(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

#define NUM_CONCURRENT 10
  valk_future *futures[NUM_CONCURRENT];

  for (int i = 0; i < NUM_CONCURRENT; i++) {
    u8 *req_buf = malloc(sizeof(valk_mem_arena_t) + 4096);
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);

    valk_http2_request_t *req = create_request(req_arena, "GET", "/concurrent");
    futures[i] = valk_aio_http2_request_send(req, client);
  }

  for (int i = 0; i < NUM_CONCURRENT; i++) {
    valk_arc_box *res = valk_future_await(futures[i]);
    ASSERT_EQ(res->type, VALK_SUC);
    valk_arc_release(res);
    valk_arc_release(futures[i]);
  }

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

#undef NUM_CONCURRENT
  VALK_PASS();
}

static void test_production_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_production();
  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

  const char *err = valk_aio_system_config_validate(&cfg);
  if (err != NULL) {
    VALK_FAIL("production config validation failed: %s", err);
  }

  VALK_PASS();
}

static void test_connect_with_hostname(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect_host(sys, "127.0.0.1", port, "test.localhost");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_null_aio_system_accessors(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_TRUE(valk_aio_is_shutting_down(NULL));

  ASSERT_NULL(valk_aio_get_event_loop(NULL));

  const char *unknown_name = valk_aio_get_name(NULL);
  ASSERT_TRUE(strcmp(unknown_name, "unknown") == 0);

  valk_aio_set_name(NULL, "test");

  valk_aio_stop(NULL);
  valk_aio_wait_for_shutdown(NULL);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
static void test_null_metrics_accessors(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_NULL(valk_aio_get_metrics(NULL));
  ASSERT_NULL(valk_aio_get_system_stats(NULL));
  ASSERT_NULL(valk_aio_get_http_clients_registry(NULL));
  ASSERT_NULL(valk_aio_get_gc_heap(NULL));
  ASSERT_NULL(valk_aio_get_scratch_arena(NULL));
  ASSERT_NULL(valk_aio_get_tcp_buffer_slab(NULL));
  ASSERT_NULL(valk_aio_get_handle_slab(NULL));
  ASSERT_NULL(valk_aio_get_stream_arenas_slab(NULL));
  ASSERT_NULL(valk_aio_get_http_servers_slab(NULL));
  ASSERT_NULL(valk_aio_get_http_clients_slab(NULL));

  VALK_PASS();
}

static void test_owner_registry(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  ASSERT_EQ(valk_owner_get_count(sys), 0);
  ASSERT_NULL(valk_owner_get_name(sys, 0));

  ASSERT_EQ(valk_owner_get_count(NULL), 0);
  ASSERT_NULL(valk_owner_get_name(NULL, 0));

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_handle_diagnostics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);

  valk_handle_diag_t diag;
  bool found_http_conn = false;
  for (size_t i = 0; i < handle_slab->numItems && !found_http_conn; i++) {
    valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, i);
    if (kind == VALK_DIAG_HNDL_HTTP_CONN) {
      bool ok = valk_aio_get_handle_diag(sys, i, &diag);
      if (ok) {
        found_http_conn = true;
      }
    }
  }

  ASSERT_FALSE(valk_aio_get_handle_diag(NULL, 0, &diag));
  ASSERT_FALSE(valk_aio_get_handle_diag(sys, 99999, &diag));
  ASSERT_FALSE(valk_aio_get_handle_diag(sys, 0, NULL));

  ASSERT_EQ(valk_aio_get_handle_kind(NULL, 0), VALK_DIAG_HNDL_EMPTY);
  ASSERT_EQ(valk_aio_get_handle_kind(sys, 99999), VALK_DIAG_HNDL_EMPTY);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_update_queue_stats(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  (void)valk_aio_http2_server_get_port_from_ref(result);

  valk_aio_update_queue_stats(sys);
  valk_aio_update_queue_stats(NULL);


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_update_loop_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_update_loop_metrics(sys);
  valk_aio_update_loop_metrics(NULL);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}
#endif

static void test_rapid_connect_disconnect(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

int port = valk_aio_http2_server_get_port_from_ref(result);

#define RAPID_ITERATIONS 5
  for (int i = 0; i < RAPID_ITERATIONS; i++) {
    valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_arc_box *clientBox = valk_future_await(fclient);
    ASSERT_EQ(clientBox->type, VALK_SUC);

    valk_aio_http2_client *client = clientBox->item;

    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);

    valk_http2_request_t *req = create_request(req_arena, "GET", "/");

    valk_future *fres = valk_aio_http2_request_send(req, client);
    valk_arc_box *res = valk_future_await(fres);
    ASSERT_EQ(res->type, VALK_SUC);

    valk_arc_release(res);
    valk_arc_release(fres);
    valk_arc_release(clientBox);
    valk_arc_release(fclient);
  }


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  size_t disconnected = __atomic_load_n(&arg.disconnectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, RAPID_ITERATIONS);
  ASSERT_EQ(disconnected, RAPID_ITERATIONS);

#undef RAPID_ITERATIONS
  VALK_PASS();
}

static void test_double_stop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  ASSERT_FALSE(valk_aio_is_shutting_down(sys));

  valk_aio_stop(sys);
  ASSERT_TRUE(valk_aio_is_shutting_down(sys));

  valk_aio_stop(sys);
  ASSERT_TRUE(valk_aio_is_shutting_down(sys));

  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_server_with_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_http_server_config_t srv_cfg = valk_http_server_config_demo();

  valk_async_handle_t *handle = valk_aio_http2_listen_with_config(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt",
      &handler, NULL, &srv_cfg);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_many_headers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 16384];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 16384);

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)req_arena;
    req->method = "GET";
    req->scheme = "https";
    req->authority = "localhost";
    req->path = "/headers";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);

    for (int i = 0; i < 20; i++) {
      char name[32], value[64];
      snprintf(name, sizeof(name), "x-header-%d", i);
      snprintf(value, sizeof(value), "value-for-header-%d", i);

      char *name_copy = valk_mem_alloc(strlen(name) + 1);
      char *value_copy = valk_mem_alloc(strlen(value) + 1);
      strcpy(name_copy, name);
      strcpy(value_copy, value);

      struct valk_http2_header_t h = {
        .name = (u8*)name_copy,
        .value = (u8*)value_copy,
        .nameLen = strlen(name),
        .valueLen = strlen(value),
      };
      da_add(&req->headers, h);
    }
  }

  ASSERT_EQ(req->headers.count, 20);

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static valk_http2_request_t* create_request_with_body(valk_mem_arena_t *arena,
                                                       const char *method,
                                                       const char *path,
                                                       const char *body) {
  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    memset(req, 0, sizeof(*req));
    req->allocator = (void *)arena;
    req->method = (char*)method;
    req->scheme = "https";
    req->authority = "localhost";
    req->path = (char*)path;
    if (body && strlen(body) > 0) {
      size_t body_len = strlen(body);
      req->body = (u8 *)valk_mem_alloc(body_len + 1);
      memcpy(req->body, body, body_len + 1);
      req->bodyLen = body_len;
    } else {
      req->body = (u8 *)"";
      req->bodyLen = 0;
    }
    da_init(&req->headers);
  }
  return req;
}

static void test_post_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 8192];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 8192);

  valk_http2_request_t *req = create_request_with_body(
      req_arena, "POST", "/api/data", "{\"key\": \"value\"}");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_put_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 8192];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 8192);

  valk_http2_request_t *req = create_request_with_body(
      req_arena, "PUT", "/api/resource/123", "{\"updated\": true}");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_delete_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "DELETE", "/api/resource/123");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_sequential_requests(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  for (int i = 0; i < 10; i++) {
    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);

    char path[64];
    snprintf(path, sizeof(path), "/item/%d", i);
    valk_http2_request_t *req = create_request(req_arena, "GET", path);

    valk_future *fres = valk_aio_http2_request_send(req, client);
    valk_arc_box *res = valk_future_await(fres);
    ASSERT_EQ(res->type, VALK_SUC);

    valk_arc_release(res);
    valk_arc_release(fres);
  }

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_parallel_requests_same_stream(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

#define PARALLEL_REQUESTS 5
  valk_future *futures[PARALLEL_REQUESTS];

  for (int i = 0; i < PARALLEL_REQUESTS; i++) {
    u8 *req_buf = malloc(sizeof(valk_mem_arena_t) + 4096);
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);

    char *path;
    VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
      path = valk_mem_alloc(64);
    }
    snprintf(path, 64, "/parallel/%d", i);
    valk_http2_request_t *req = create_request(req_arena, "GET", path);
    futures[i] = valk_aio_http2_request_send(req, client);
  }

  for (int i = 0; i < PARALLEL_REQUESTS; i++) {
    valk_arc_box *res = valk_future_await(futures[i]);
    ASSERT_EQ(res->type, VALK_SUC);
    valk_arc_release(res);
    valk_arc_release(futures[i]);
  }

#undef PARALLEL_REQUESTS

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_multiple_clients_sequential(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  for (int c = 0; c < 3; c++) {
    valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_arc_box *clientBox = valk_future_await(fclient);
    ASSERT_EQ(clientBox->type, VALK_SUC);

    valk_aio_http2_client *client = clientBox->item;

    for (int r = 0; r < 3; r++) {
      u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);

      valk_http2_request_t *req = create_request(req_arena, "GET", "/");

      valk_future *fres = valk_aio_http2_request_send(req, client);
      valk_arc_box *res = valk_future_await(fres);
      ASSERT_EQ(res->type, VALK_SUC);

      valk_arc_release(res);
      valk_arc_release(fres);
    }

    valk_arc_release(clientBox);
    valk_arc_release(fclient);
  }


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, 3);

  VALK_PASS();
}

static void test_head_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "HEAD", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_NOT_NULL(res);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_options_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "OPTIONS", "*");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_long_path(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 8192];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 8192);

  char long_path[2048];
  strcpy(long_path, "/api/v1/deeply/nested/resource/with/many/path/segments/");
  for (int i = 0; i < 10; i++) {
    char segment[128];
    snprintf(segment, sizeof(segment), "level%d/sublevel%d/", i, i * 2);
    strcat(long_path, segment);
  }

  valk_http2_request_t *req = create_request(req_arena, "GET", long_path);

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_query_string(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET",
      "/search?q=hello+world&page=1&limit=50&sort=date&filter=active");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
static void timer_close_cb(uv_handle_t *handle) {
  UNUSED(handle);
}

static void test_timer_alloc_free(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);
  valk_aio_timer_set_data(timer, (void*)0x1234);

  valk_aio_timer_close(timer, timer_close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_timer_null_safety(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_timer_init(NULL);
  valk_aio_timer_start(NULL, 0, 0, NULL);
  valk_aio_timer_stop(NULL);
  valk_aio_timer_close(NULL, NULL);
  valk_aio_timer_set_data(NULL, NULL);
  valk_aio_timer_free(NULL);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(NULL);
  ASSERT_NULL(timer);

  VALK_PASS();
}

static int g_timer_callback_count = 0;

static void test_timer_callback(uv_timer_t *handle) {
  UNUSED(handle);
  __atomic_fetch_add(&g_timer_callback_count, 1, __ATOMIC_RELAXED);
}

static void test_timer_full_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);

  valk_aio_timer_start(timer, 10, 0, test_timer_callback);

  usleep(50000);

  valk_aio_timer_stop(timer);

  valk_aio_timer_close(timer, timer_close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_timer_repeating(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);

  valk_aio_timer_start(timer, 5, 10, test_timer_callback);

  usleep(80000);

  valk_aio_timer_stop(timer);

  valk_aio_timer_close(timer, timer_close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_timer_double_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);
  valk_aio_timer_close(timer, timer_close_cb);
  valk_aio_timer_close(timer, timer_close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_handle_kind_for_timer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);

  bool found_timer = false;
  for (size_t i = 0; i < handle_slab->numItems; i++) {
    valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, i);
    if (kind == VALK_DIAG_HNDL_TIMER) {
      found_timer = true;
      valk_handle_diag_t diag;
      bool has_diag = valk_aio_get_handle_diag(sys, i, &diag);
      ASSERT_FALSE(has_diag);
      break;
    }
  }
  ASSERT_TRUE(found_timer);

  valk_aio_timer_init(timer);
  valk_aio_timer_close(timer, timer_close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_handle_diagnostics_all_kinds(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);
  valk_aio_timer_init(timer);

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);

  bool found_http_conn = false;
  bool found_timer = false;

  for (size_t i = 0; i < handle_slab->numItems; i++) {
    valk_diag_handle_kind_e kind = valk_aio_get_handle_kind(sys, i);
    switch (kind) {
      case VALK_DIAG_HNDL_HTTP_CONN:
        found_http_conn = true;
        {
          valk_handle_diag_t diag;
          bool ok = valk_aio_get_handle_diag(sys, i, &diag);
          ASSERT_TRUE(ok);
        }
        break;
      case VALK_DIAG_HNDL_TIMER:
        found_timer = true;
        {
          valk_handle_diag_t diag;
          bool ok = valk_aio_get_handle_diag(sys, i, &diag);
          ASSERT_FALSE(ok);
        }
        break;
      case VALK_DIAG_HNDL_EMPTY:
      case VALK_DIAG_HNDL_TCP:
      case VALK_DIAG_HNDL_TASK:
        break;
    }
  }

  ASSERT_TRUE(found_http_conn);
  ASSERT_TRUE(found_timer);

  valk_aio_timer_close(timer, timer_close_cb);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_handle_diag_edge_cases(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_handle_diag_t diag;
  ASSERT_FALSE(valk_aio_get_handle_diag(sys, 0, NULL));

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);
  size_t out_of_bounds = handle_slab->numItems + 100;
  ASSERT_FALSE(valk_aio_get_handle_diag(sys, out_of_bounds, &diag));

  ASSERT_EQ(valk_aio_get_handle_kind(sys, out_of_bounds), VALK_DIAG_HNDL_EMPTY);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_multiple_timers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  #define NUM_TIMERS 5
  valk_aio_handle_t *timers[NUM_TIMERS];

  for (int i = 0; i < NUM_TIMERS; i++) {
    timers[i] = valk_aio_timer_alloc(sys);
    ASSERT_NOT_NULL(timers[i]);
    valk_aio_timer_init(timers[i]);
    valk_aio_timer_set_data(timers[i], (void*)(uptr)i);
  }

  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  int timer_count = 0;
  for (size_t i = 0; i < handle_slab->numItems; i++) {
    if (valk_aio_get_handle_kind(sys, i) == VALK_DIAG_HNDL_TIMER) {
      timer_count++;
    }
  }
  ASSERT_GE(timer_count, NUM_TIMERS);

  for (int i = 0; i < NUM_TIMERS; i++) {
    valk_aio_timer_close(timers[i], timer_close_cb);
  }
  #undef NUM_TIMERS

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void timer_free_cb(uv_handle_t *handle) {
  valk_aio_handle_t *timer = (valk_aio_handle_t *)handle->data;
  valk_aio_timer_free(timer);
}

static void test_timer_free_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);
  valk_aio_timer_set_data(timer, timer);

  valk_aio_timer_close(timer, timer_free_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_timer_stop_before_fire(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_aio_handle_t *timer = valk_aio_timer_alloc(sys);
  ASSERT_NOT_NULL(timer);

  valk_aio_timer_init(timer);

  g_timer_callback_count = 0;
  valk_aio_timer_start(timer, 10000, 0, test_timer_callback);

  valk_aio_timer_stop(timer);

  usleep(20000);

  int count = __atomic_load_n(&g_timer_callback_count, __ATOMIC_ACQUIRE);
  ASSERT_EQ(count, 0);

  valk_aio_timer_close(timer, timer_close_cb);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}
#endif

static void test_response_with_status(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_http2_response_t *response = res->item;
  ASSERT_NOT_NULL(response);
  ASSERT_NOT_NULL(response->status);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_localhost_hostname(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect_host(sys, "localhost", port, NULL);
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_large_body_post(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  size_t body_size = 64 * 1024;
  char *large_body = malloc(body_size + 1);
  memset(large_body, 'X', body_size);
  large_body[body_size] = '\0';

  size_t arena_size = body_size + 4096;
  u8 *req_buf = malloc(sizeof(valk_mem_arena_t) + arena_size);
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, arena_size);

  valk_http2_request_t *req = create_request_with_body(
      req_arena, "POST", "/upload", large_body);

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  free(large_body);
  free(req_buf);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_many_parallel_clients(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  #define NUM_CLIENTS 10
  valk_future *fclient[NUM_CLIENTS];
  valk_arc_box *clientBox[NUM_CLIENTS];
  valk_aio_http2_client *client[NUM_CLIENTS];

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclient[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    clientBox[i] = valk_future_await(fclient[i]);
    ASSERT_EQ(clientBox[i]->type, VALK_SUC);
    client[i] = clientBox[i]->item;
  }

  valk_future *fres[NUM_CLIENTS];
  u8 req_bufs[NUM_CLIENTS][sizeof(valk_mem_arena_t) + 4096];
  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_mem_arena_t *req_arena = (void *)req_bufs[i];
    valk_mem_arena_init(req_arena, 4096);

    valk_http2_request_t *req = create_request(req_arena, "GET", "/");
    fres[i] = valk_aio_http2_request_send(req, client[i]);
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_box *res = valk_future_await(fres[i]);
    ASSERT_EQ(res->type, VALK_SUC);
    valk_arc_release(res);
    valk_arc_release(fres[i]);
    valk_arc_release(clientBox[i]);
    valk_arc_release(fclient[i]);
  }


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
  #undef NUM_CLIENTS
}

static void __attribute__((unused)) test_many_streams_per_client(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  #define NUM_STREAMS 20
  valk_future *fres[NUM_STREAMS];

  for (int i = 0; i < NUM_STREAMS; i++) {
    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);

    char path[64];
    snprintf(path, sizeof(path), "/path/%d", i);
    valk_http2_request_t *req = create_request(req_arena, "GET", path);
    fres[i] = valk_aio_http2_request_send(req, client);
  }

  for (int i = 0; i < NUM_STREAMS; i++) {
    valk_arc_box *res = valk_future_await(fres[i]);
    ASSERT_EQ(res->type, VALK_SUC);
    valk_arc_release(res);
    valk_arc_release(fres[i]);
  }

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
  #undef NUM_STREAMS
}

static void __attribute__((unused)) test_connect_invalid_port(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", 1, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_ERR);

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void __attribute__((unused)) test_connect_invalid_host(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_future *fclient = valk_aio_http2_connect(sys, "192.0.2.1", 8443, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_ERR);

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void __attribute__((unused)) test_burst_requests(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  for (int burst = 0; burst < 3; burst++) {
    #define BURST_SIZE 10
    valk_future *fres[BURST_SIZE];

    for (int i = 0; i < BURST_SIZE; i++) {
      u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);

      valk_http2_request_t *req = create_request(req_arena, "GET", "/");
      fres[i] = valk_aio_http2_request_send(req, client);
    }

    for (int i = 0; i < BURST_SIZE; i++) {
      valk_arc_box *res = valk_future_await(fres[i]);
      ASSERT_EQ(res->type, VALK_SUC);
      valk_arc_release(res);
      valk_arc_release(fres[i]);
    }
    #undef BURST_SIZE
  }

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_empty_body_post(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request_with_body(req_arena, "POST", "/empty", "");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_special_characters_in_path(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET",
      "/path%20with%20spaces/file%2Fthing?a=1&b=2#fragment");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_binary_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  char binary_body[256];
  for (int i = 0; i < 256; i++) {
    binary_body[i] = (char)i;
  }

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = valk_mem_alloc(sizeof(valk_http2_request_t));
  memset(req, 0, sizeof(*req));
  req->allocator = (valk_mem_allocator_t*)req_arena;
  req->method = valk_mem_alloc(5);
  memcpy(req->method, "POST", 5);
  req->path = valk_mem_alloc(8);
  memcpy(req->path, "/binary", 8);
  req->scheme = valk_mem_alloc(6);
  memcpy(req->scheme, "https", 6);
  req->authority = valk_mem_alloc(15);
  memcpy(req->authority, "127.0.0.1:8443", 15);
  req->body = valk_mem_alloc(256);
  memcpy(req->body, binary_body, 256);
  req->bodyLen = 256;
  req->bodyCapacity = 256;

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_patch_request(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request_with_body(
      req_arena, "PATCH", "/resource/123", "{\"field\": \"updated\"}");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
static void test_connection_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);

  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_stream_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  #define NUM_REQS 5
  valk_future *fres[NUM_REQS];
  u8 *req_bufs[NUM_REQS];
  for (int i = 0; i < NUM_REQS; i++) {
    req_bufs[i] = malloc(sizeof(valk_mem_arena_t) + 4096);
    valk_mem_arena_t *req_arena = (void *)req_bufs[i];
    valk_mem_arena_init(req_arena, 4096);
    valk_http2_request_t *req = create_request(req_arena, "GET", "/");
    fres[i] = valk_aio_http2_request_send(req, client);
  }

  for (int i = 0; i < NUM_REQS; i++) {
    valk_arc_box *res = valk_future_await(fres[i]);
    ASSERT_EQ(res->type, VALK_SUC);
    valk_arc_release(res);
    valk_arc_release(fres[i]);
    free(req_bufs[i]);
  }
  #undef NUM_REQS

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_backpressure_under_load(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 8;
  cfg.tcp_buffer_pool_size = 32;
  cfg.arena_pool_size = 16;
  cfg.pending_stream_pool_size = 32;
  cfg.backpressure_timeout_ms = 2000;

  int res = valk_aio_system_config_resolve(&cfg);
  ASSERT_EQ(res, 0);

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

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  #define NUM_CLIENTS 4
  valk_future *client_futures[NUM_CLIENTS];
  valk_arc_box *client_boxes[NUM_CLIENTS];
  valk_aio_http2_client *clients[NUM_CLIENTS];

  for (int i = 0; i < NUM_CLIENTS; i++) {
    client_futures[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  }

  int connected = 0;
  for (int i = 0; i < NUM_CLIENTS; i++) {
    client_boxes[i] = valk_future_await(client_futures[i]);
    if (client_boxes[i]->type == VALK_SUC) {
      clients[connected++] = client_boxes[i]->item;
    }
  }

  ASSERT_GT(connected, 0);

  for (int c = 0; c < connected; c++) {
    u8 req_buf[sizeof(valk_mem_arena_t) + 8192];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 8192);

    valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
    valk_future *freq = valk_aio_http2_request_send(req, clients[c]);
    valk_arc_box *res = valk_future_await(freq);
    valk_arc_release(res);
    valk_arc_release(freq);
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(client_boxes[i]);
    valk_arc_release(client_futures[i]);
  }
  #undef NUM_CLIENTS


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_backpressure_event_driven_resume(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t srv_cfg = {0};
  srv_cfg.max_connections = 8;
  srv_cfg.tcp_buffer_pool_size = 32;
  srv_cfg.arena_pool_size = 16;
  srv_cfg.pending_stream_pool_size = 16;

  int res = valk_aio_system_config_resolve(&srv_cfg);
  ASSERT_EQ(res, 0);

  valk_aio_system_t *srv_sys = valk_aio_start_with_config(&srv_cfg);
  ASSERT_NOT_NULL(srv_sys);

  valk_aio_system_t *client_sys = valk_aio_start();
  ASSERT_NOT_NULL(client_sys);
  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *handle = valk_aio_http2_listen(
      srv_sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_EQ(LVAL_TYPE(result), LVAL_REF);

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(client_sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);
  valk_aio_http2_client *client = clientBox->item;

  #define NUM_STREAMS 6
  valk_future *stream_futures[NUM_STREAMS];
  u8 req_bufs[NUM_STREAMS][sizeof(valk_mem_arena_t) + 4096];

  for (int i = 0; i < NUM_STREAMS; i++) {
    valk_mem_arena_t *req_arena = (void *)req_bufs[i];
    valk_mem_arena_init(req_arena, 4096);
    valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
    stream_futures[i] = valk_aio_http2_request_send(req, client);
  }

  for (int i = 0; i < NUM_STREAMS; i++) {
    valk_arc_box *res = valk_future_await(stream_futures[i]);
    valk_arc_release(res);
    valk_arc_release(stream_futures[i]);
  }
  #undef NUM_STREAMS

  valk_arc_release(clientBox);
  valk_arc_release(fclient);


  valk_aio_stop(client_sys);
  valk_aio_wait_for_shutdown(client_sys);

  valk_aio_stop(srv_sys);
  valk_aio_wait_for_shutdown(srv_sys);

  VALK_PASS();
}




void test_abrupt_client_disconnect(VALK_TEST_ARGS()) {
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

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req = create_request(req_arena, "GET", "/");
  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);
  valk_arc_release(res);
  valk_arc_release(fres);

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  usleep(50000);


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_rapid_client_disconnect_mid_request(VALK_TEST_ARGS()) {
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

  int port = valk_aio_http2_server_get_port_from_ref(result);

  for (int i = 0; i < 3; i++) {
    valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_arc_box *clientBox = valk_future_await(fclient);
    if (clientBox->type == VALK_SUC) {
      valk_aio_http2_client *client = clientBox->item;

      #define RAPID_REQS 5
      valk_future *freq[RAPID_REQS];
      for (int r = 0; r < RAPID_REQS; r++) {
        u8 *req_buf = malloc(sizeof(valk_mem_arena_t) + 4096);
        valk_mem_arena_t *req_arena = (void *)req_buf;
        valk_mem_arena_init(req_arena, 4096);
        valk_http2_request_t *req = create_request(req_arena, "GET", "/rapid");
        freq[r] = valk_aio_http2_request_send(req, client);
      }

      for (int r = 0; r < RAPID_REQS; r++) {
        valk_arc_box *res = valk_future_await(freq[r]);
        valk_arc_release(res);
        valk_arc_release(freq[r]);
      }
      #undef RAPID_REQS

      valk_arc_release(clientBox);
      valk_arc_release(fclient);
    } else {
      valk_arc_release(clientBox);
      valk_arc_release(fclient);
    }
  }

  usleep(100000);


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_multiple_parallel_streams_then_disconnect(VALK_TEST_ARGS()) {
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

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);
  valk_aio_http2_client *client = clientBox->item;

  #define PARALLEL_STREAMS 10
  valk_future *fres[PARALLEL_STREAMS];
  for (int i = 0; i < PARALLEL_STREAMS; i++) {
    u8 *req_buf = malloc(sizeof(valk_mem_arena_t) + 4096);
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);
    char path[32];
    snprintf(path, sizeof(path), "/stream/%d", i);
    valk_http2_request_t *req = create_request(req_arena, "GET", path);
    fres[i] = valk_aio_http2_request_send(req, client);
  }

  for (int i = 0; i < PARALLEL_STREAMS; i++) {
    valk_arc_box *res = valk_future_await(fres[i]);
    ASSERT_EQ(res->type, VALK_SUC);
    valk_arc_release(res);
    valk_arc_release(fres[i]);
  }
  #undef PARALLEL_STREAMS

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  usleep(50000);


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_large_concurrent_body_then_disconnect(VALK_TEST_ARGS()) {
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

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);
  valk_aio_http2_client *client = clientBox->item;

  size_t body_size = 128 * 1024;
  char *large_body = malloc(body_size + 1);
  memset(large_body, 'Y', body_size);
  large_body[body_size] = '\0';

  size_t arena_size = body_size + 4096;
  u8 *req_buf = malloc(sizeof(valk_mem_arena_t) + arena_size);
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, arena_size);

  valk_http2_request_t *req = create_request_with_body(
      req_arena, "POST", "/large-upload", large_body);

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  valk_arc_release(res);
  valk_arc_release(fres);

  valk_arc_release(clientBox);
  valk_arc_release(fclient);

  free(large_body);
  free(req_buf);

  usleep(50000);


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_ssl_connection_state_transitions(VALK_TEST_ARGS()) {
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

  int port = valk_aio_http2_server_get_port_from_ref(result);

  #define TRANSITIONS 10
  for (int i = 0; i < TRANSITIONS; i++) {
    valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_arc_box *clientBox = valk_future_await(fclient);
    ASSERT_EQ(clientBox->type, VALK_SUC);
    valk_aio_http2_client *client = clientBox->item;

    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);
    valk_http2_request_t *req = create_request(req_arena, "GET", "/");
    valk_future *fres = valk_aio_http2_request_send(req, client);
    valk_arc_box *res = valk_future_await(fres);
    ASSERT_EQ(res->type, VALK_SUC);

    valk_arc_release(res);
    valk_arc_release(fres);
    valk_arc_release(clientBox);
    valk_arc_release(fclient);
  }
  #undef TRANSITIONS


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  size_t connected = __atomic_load_n(&state.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, 10);

  VALK_PASS();
}

void test_connection_closing_state_handling(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_TRUE(valk_aio_http_connection_closing(NULL));

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

  int port = valk_aio_http2_server_get_port_from_ref(result);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);
  valk_aio_http2_client *client = clientBox->item;

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);
  valk_http2_request_t *req = create_request(req_arena, "GET", "/");
  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  ASSERT_EQ(res->type, VALK_SUC);
  valk_arc_release(res);
  valk_arc_release(fres);

  valk_arc_release(clientBox);
  valk_arc_release(fclient);


  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

void test_session_validity_checks(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_FALSE(valk_aio_http_session_valid(nullptr, nullptr));
  ASSERT_FALSE(valk_aio_http_session_valid(nullptr, (void*)0x1234));

  VALK_PASS();
}



void test_http2_flush_pending_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_http2_flush_pending(nullptr);

  VALK_PASS();
}

#endif

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_config_validation_max_connections", test_config_validation_max_connections);
  valk_testsuite_add_test(suite, "test_config_validation_max_streams", test_config_validation_max_streams);
  valk_testsuite_add_test(suite, "test_config_validation_handles", test_config_validation_handles);
  valk_testsuite_add_test(suite, "test_config_validation_servers", test_config_validation_servers);
  valk_testsuite_add_test(suite, "test_config_validation_clients", test_config_validation_clients);
  valk_testsuite_add_test(suite, "test_config_validation_tcp_buffer_pool", test_config_validation_tcp_buffer_pool);
  valk_testsuite_add_test(suite, "test_config_validation_arena_pool", test_config_validation_arena_pool);
  valk_testsuite_add_test(suite, "test_config_validation_arena_size", test_config_validation_arena_size);
  valk_testsuite_add_test(suite, "test_config_validation_request_body_size", test_config_validation_request_body_size);
  valk_testsuite_add_test(suite, "test_config_validation_queue_capacity", test_config_validation_queue_capacity);
  valk_testsuite_add_test(suite, "test_config_validation_backpressure", test_config_validation_backpressure);
  valk_testsuite_add_test(suite, "test_config_validation_backpressure_timeout", test_config_validation_backpressure_timeout);
  valk_testsuite_add_test(suite, "test_config_validation_pending_stream_pool", test_config_validation_pending_stream_pool);
  valk_testsuite_add_test(suite, "test_config_validation_relationships", test_config_validation_relationships);
  valk_testsuite_add_test(suite, "test_config_validation_arena_relationship", test_config_validation_arena_relationship);
  valk_testsuite_add_test(suite, "test_config_resolve_defaults", test_config_resolve_defaults);
  valk_testsuite_add_test(suite, "test_config_resolve_invalid_watermarks", test_config_resolve_invalid_watermarks);
  valk_testsuite_add_test(suite, "test_request_with_custom_headers", test_request_with_custom_headers);
  valk_testsuite_add_test(suite, "test_multiple_paths", test_multiple_paths);
  valk_testsuite_add_test(suite, "test_concurrent_streams_same_connection", test_concurrent_streams_same_connection);
  valk_testsuite_add_test(suite, "test_production_config", test_production_config);
  valk_testsuite_add_test(suite, "test_connect_with_hostname", test_connect_with_hostname);
  valk_testsuite_add_test(suite, "test_null_aio_system_accessors", test_null_aio_system_accessors);
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_null_metrics_accessors", test_null_metrics_accessors);
  valk_testsuite_add_test(suite, "test_owner_registry", test_owner_registry);
  valk_testsuite_add_test(suite, "test_handle_diagnostics", test_handle_diagnostics);
  valk_testsuite_add_test(suite, "test_update_queue_stats", test_update_queue_stats);
  valk_testsuite_add_test(suite, "test_update_loop_metrics", test_update_loop_metrics);
#endif
  valk_testsuite_add_test(suite, "test_rapid_connect_disconnect", test_rapid_connect_disconnect);
  valk_testsuite_add_test(suite, "test_double_stop", test_double_stop);
  valk_testsuite_add_test(suite, "test_server_with_config", test_server_with_config);
  valk_testsuite_add_test(suite, "test_many_headers", test_many_headers);
  valk_testsuite_add_test(suite, "test_post_request", test_post_request);
  valk_testsuite_add_test(suite, "test_put_request", test_put_request);
  valk_testsuite_add_test(suite, "test_delete_request", test_delete_request);
  valk_testsuite_add_test(suite, "test_sequential_requests", test_sequential_requests);
  valk_testsuite_add_test(suite, "test_parallel_requests_same_stream", test_parallel_requests_same_stream);
  valk_testsuite_add_test(suite, "test_multiple_clients_sequential", test_multiple_clients_sequential);
  valk_testsuite_add_test(suite, "test_head_request", test_head_request);
  valk_testsuite_add_test(suite, "test_options_request", test_options_request);
  valk_testsuite_add_test(suite, "test_long_path", test_long_path);
  valk_testsuite_add_test(suite, "test_query_string", test_query_string);
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_timer_alloc_free", test_timer_alloc_free);
  valk_testsuite_add_test(suite, "test_timer_null_safety", test_timer_null_safety);
  valk_testsuite_add_test(suite, "test_timer_full_lifecycle", test_timer_full_lifecycle);
  valk_testsuite_add_test(suite, "test_timer_repeating", test_timer_repeating);
  valk_testsuite_add_test(suite, "test_timer_double_close", test_timer_double_close);
  valk_testsuite_add_test(suite, "test_handle_kind_for_timer", test_handle_kind_for_timer);
  valk_testsuite_add_test(suite, "test_handle_diagnostics_all_kinds", test_handle_diagnostics_all_kinds);
  valk_testsuite_add_test(suite, "test_handle_diag_edge_cases", test_handle_diag_edge_cases);
  valk_testsuite_add_test(suite, "test_multiple_timers", test_multiple_timers);
  valk_testsuite_add_test(suite, "test_timer_free_lifecycle", test_timer_free_lifecycle);
  valk_testsuite_add_test(suite, "test_timer_stop_before_fire", test_timer_stop_before_fire);
#endif
  valk_testsuite_add_test(suite, "test_response_with_status", test_response_with_status);
  valk_testsuite_add_test(suite, "test_localhost_hostname", test_localhost_hostname);
  valk_testsuite_add_test(suite, "test_large_body_post", test_large_body_post);
  valk_testsuite_add_test(suite, "test_many_parallel_clients", test_many_parallel_clients);
  valk_testsuite_add_test(suite, "test_empty_body_post", test_empty_body_post);
  valk_testsuite_add_test(suite, "test_special_characters_in_path", test_special_characters_in_path);
  valk_testsuite_add_test(suite, "test_binary_body", test_binary_body);
  valk_testsuite_add_test(suite, "test_patch_request", test_patch_request);
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_connection_metrics", test_connection_metrics);
  valk_testsuite_add_test(suite, "test_stream_metrics", test_stream_metrics);
  valk_testsuite_add_test(suite, "test_backpressure_under_load", test_backpressure_under_load);
  valk_testsuite_add_test(suite, "test_backpressure_event_driven_resume", test_backpressure_event_driven_resume);
  valk_testsuite_add_test(suite, "test_abrupt_client_disconnect", test_abrupt_client_disconnect);
  valk_testsuite_add_test(suite, "test_rapid_client_disconnect_mid_request", test_rapid_client_disconnect_mid_request);
  valk_testsuite_add_test(suite, "test_multiple_parallel_streams_then_disconnect", test_multiple_parallel_streams_then_disconnect);
  valk_testsuite_add_test(suite, "test_large_concurrent_body_then_disconnect", test_large_concurrent_body_then_disconnect);
  valk_testsuite_add_test(suite, "test_ssl_connection_state_transitions", test_ssl_connection_state_transitions);
  valk_testsuite_add_test(suite, "test_connection_closing_state_handling", test_connection_closing_state_handling);
  valk_testsuite_add_test(suite, "test_session_validity_checks", test_session_validity_checks);

  valk_testsuite_add_test(suite, "test_http2_flush_pending_null", test_http2_flush_pending_null);
#endif

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
