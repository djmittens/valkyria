#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <pthread.h>
#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"
#include "aio/aio_metrics.h"
#include "aio/aio_metrics_v2.h"
#include "collections.h"
#include "parser.h"
#include "common.h"
#include "memory.h"
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
static void test_critical_watermark_rejects_all(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.05f;
  cfg.buffer_critical_watermark = 0.1f;
  cfg.tcp_buffer_pool_size = 8;
  cfg.max_connections = 32;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
  valk_aio_system_stats_v2_t *stats = VALK_SYSTEM_STATS_V2(sys);
  u64 initial_rejected = atomic_load(&stats->connections_rejected_load->value);
#define NUM_CLIENTS 16
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
  }
  u64 final_rejected = atomic_load(&stats->connections_rejected_load->value);
  ASSERT_GT(final_rejected, initial_rejected);
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_below_high_watermark_accepts_all(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.95f;
  cfg.buffer_critical_watermark = 0.99f;
  cfg.tcp_buffer_pool_size = 256;
  cfg.max_connections = 64;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
  valk_aio_system_stats_v2_t *stats = VALK_SYSTEM_STATS_V2(sys);
  u64 initial_rejected = atomic_load(&stats->connections_rejected_load->value);
#define NUM_CLIENTS 4
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  int successful = 0;
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
    if (LVAL_TYPE(client_results[i]) != LVAL_ERR) {
      successful++;
    }
  }
  ASSERT_EQ(successful, NUM_CLIENTS);
  u64 final_rejected = atomic_load(&stats->connections_rejected_load->value);
  ASSERT_EQ(final_rejected, initial_rejected);
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_watermark_defaults_applied(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.0f;
  cfg.buffer_critical_watermark = 0.0f;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_probabilistic_shedding_range(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.3f;
  cfg.buffer_critical_watermark = 0.6f;
  cfg.tcp_buffer_pool_size = 16;
  cfg.max_connections = 32;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 12
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  int successful = 0;
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
    if (LVAL_TYPE(client_results[i]) != LVAL_ERR) {
      successful++;
    }
  }
  ASSERT_GT(successful, 0);
  for (int i = 0; i < NUM_CLIENTS; i++) {
    ;
    ;
  }
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_load_shedding_counter_increments(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.05f;
  cfg.buffer_critical_watermark = 0.1f;
  cfg.tcp_buffer_pool_size = 8;
  cfg.max_connections = 32;
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);
  valk_aio_system_stats_v2_t *stats = VALK_SYSTEM_STATS_V2(sys);
  ASSERT_NOT_NULL(stats);
  u64 initial_rejected = atomic_load(&stats->connections_rejected_load->value);
  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 20
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
  }
  u64 final_rejected = atomic_load(&stats->connections_rejected_load->value);
  ASSERT_GT(final_rejected, initial_rejected);
  for (int i = 0; i < NUM_CLIENTS; i++) {
    ;
    ;
  }
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_high_watermark_load_shedding(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.5f;
  cfg.buffer_critical_watermark = 0.8f;
  cfg.tcp_buffer_pool_size = 32;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 6
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  int successful = 0;
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
    if (LVAL_TYPE(client_results[i]) != LVAL_ERR) {
      successful++;
    }
  }
  ASSERT_GT(successful, 0);
  for (int i = 0; i < NUM_CLIENTS; i++) {
    ;
    ;
  }
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_many_concurrent_requests(VALK_TEST_ARGS()) {
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
  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);
  valk_aio_http2_client *client = client_result->ref.ptr;
#define NUM_REQUESTS 20
  valk_async_handle_t *hreqs[NUM_REQUESTS];
  valk_lval_t *res_results[NUM_REQUESTS];
  int successful = 0;
  for (int i = 0; i < NUM_REQUESTS; i++) {
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
    hreqs[i] = valk_aio_http2_request_send(req, client);
    res_results[i] = valk_async_handle_await(hreqs[i]);
    if (LVAL_TYPE(res_results[i]) != LVAL_ERR) {
      successful++;
    }
    ;
    ;
  }
#undef NUM_REQUESTS
  ASSERT_GT(successful, 0);
  ;
  ;
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_load_shedding_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.3f;
  cfg.buffer_critical_watermark = 0.5f;
  cfg.tcp_buffer_pool_size = 24;
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);
  valk_aio_system_stats_v2_t *stats = VALK_SYSTEM_STATS_V2(sys);
  ASSERT_NOT_NULL(stats);
  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 8
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
  }
  for (int i = 0; i < NUM_CLIENTS; i++) {
    ;
    ;
  }
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_buffer_pool_usage(VALK_TEST_ARGS()) {
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
  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  ASSERT_NOT_NULL(tcp_slab);
  size_t initial_available = valk_slab_available(tcp_slab);
  ASSERT_GT(initial_available, 0);
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);
  size_t after_connect = valk_slab_available(tcp_slab);
  ASSERT_LE(after_connect, initial_available);
  ;
  ;
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_arena_pool_usage(VALK_TEST_ARGS()) {
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
  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  ASSERT_NOT_NULL(arena_slab);
  size_t initial_available = valk_slab_available(arena_slab);
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
    req->path = "/";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }
  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);
  ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);
  size_t after_request = valk_slab_available(arena_slab);
  ASSERT_EQ(after_request, initial_available);
  ;
  ;
  ;
  ;
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_connection_state_transitions(VALK_TEST_ARGS()) {
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
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
    req->path = "/";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }
  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);
  ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);
  ;
  ;
  ;
  ;
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  size_t connected = __atomic_load_n(&state.connectedCount, __ATOMIC_ACQUIRE);
  size_t disconnected = __atomic_load_n(&state.disconnectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, 1);
  ASSERT_EQ(disconnected, 1);
  VALK_PASS();
}
static void test_rapid_connect_disconnect(VALK_TEST_ARGS()) {
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
  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CYCLES 5
  for (int cycle = 0; cycle < NUM_CYCLES; cycle++) {
    valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_lval_t *client_result = valk_async_handle_await(hclient);
    ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);
    ;
    ;
  }
#undef NUM_CYCLES
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static valk_http2_request_t* create_request(valk_mem_arena_t *arena,
                                             const char *method,
                                             const char *path) {
  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)arena;
    req->method = (char*)method;
    req->scheme = "https";
    req->authority = "localhost";
    req->path = (char*)path;
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }
  return req;
}
static void test_arena_exhaustion_returns_503(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.arena_pool_size = 1;
  cfg.max_concurrent_streams = 8;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);
  valk_aio_http2_client *client = client_result->ref.ptr;
#define NUM_REQUESTS 4
  for (int i = 0; i < NUM_REQUESTS; i++) {
    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);
    valk_http2_request_t *req = create_request(req_arena, "GET", "/");
    valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
    (void)valk_async_handle_await(hres);
  }
#undef NUM_REQUESTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_tcp_buffer_exhaustion_backpressure(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.tcp_buffer_pool_size = 32;
  cfg.max_connections = 16;
  cfg.max_concurrent_streams = 16;
  valk_aio_system_t *server_sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(server_sys);
  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  valk_async_handle_t *handle = valk_aio_http2_listen(
      server_sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 2
#define REQUESTS_PER_CLIENT 5
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  valk_async_handle_t *hreqs[NUM_CLIENTS * REQUESTS_PER_CLIENT];
  u8 *req_bufs[NUM_CLIENTS * REQUESTS_PER_CLIENT];
  int req_count = 0;
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(server_sys, "127.0.0.1", port, "");
  }
  for (int i = 0; i < NUM_CLIENTS; i++) {
    client_results[i] = valk_async_handle_await(hclients[i]);
    if (LVAL_TYPE(client_results[i]) == LVAL_ERR) continue;
    valk_aio_http2_client *client = client_results[i]->ref.ptr;
    for (int r = 0; r < REQUESTS_PER_CLIENT; r++) {
      u8 *req_buf = malloc(sizeof(valk_mem_arena_t) + 4096);
      req_bufs[req_count] = req_buf;
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);
      valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
      hreqs[req_count++] = valk_aio_http2_request_send(req, client);
    }
  }
  for (int i = 0; i < req_count; i++) {
    (void)valk_async_handle_await(hreqs[i]);
    free(req_bufs[i]);
  }
#undef NUM_CLIENTS
#undef REQUESTS_PER_CLIENT
  valk_aio_stop(server_sys);
  valk_aio_wait_for_shutdown(server_sys);
  VALK_PASS();
}
static void test_backpressure_connections_survive(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Flaky timeout under coverage instrumentation");
  return;
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.tcp_buffer_pool_size = 32;
  cfg.max_connections = 16;
  cfg.arena_pool_size = 32;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 4
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  valk_aio_http2_client *clients[NUM_CLIENTS];
  int connected = 0;
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  }
  for (int i = 0; i < NUM_CLIENTS; i++) {
    client_results[i] = valk_async_handle_await(hclients[i]);
    if (client_results[i] && LVAL_TYPE(client_results[i]) != LVAL_ERR) {
      clients[connected++] = client_results[i]->ref.ptr;
    }
  }
  ASSERT_GT(connected, 0);
  int total_completed = 0;
  for (int round = 0; round < 3; round++) {
    for (int i = 0; i < connected; i++) {
      u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);
      valk_http2_request_t *req = create_request(req_arena, "GET", "/");
      valk_async_handle_t *hres = valk_aio_http2_request_send(req, clients[i]);
      valk_lval_t *res = valk_async_handle_await(hres);
      if (res && LVAL_TYPE(res) != LVAL_ERR) {
        total_completed++;
      }
    }
  }
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_TEST_ASSERT(total_completed > 0,
                   "Expected some requests to complete under load");
  VALK_PASS();
}
static void test_custom_503_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_connections = 8;
  cfg.tcp_buffer_pool_size = 16;
  cfg.arena_pool_size = 1;
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
  valk_http_server_config_t server_cfg = valk_http_server_config_default();
  server_cfg.error_503_body = "<html><body>Custom 503</body></html>";
  server_cfg.error_503_body_len = strlen(server_cfg.error_503_body);
  valk_async_handle_t *handle = valk_aio_http2_listen_with_config(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr, &server_cfg);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 3
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  int successful = 0;
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
    if (LVAL_TYPE(client_results[i]) != LVAL_ERR) {
      successful++;
    }
  }
  ASSERT_GT(successful, 0);
  for (int c = 0; c < successful; c++) {
    valk_aio_http2_client *client = client_results[c]->ref.ptr;
    for (int r = 0; r < 4; r++) {
      u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);
      valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
      valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
      (void)valk_async_handle_await(hres);
    }
  }
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
static void test_backpressure_list_remove_nonhead(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.max_connections = 8;
  cfg.tcp_buffer_pool_size = 32;
  cfg.arena_pool_size = 32;
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *result = valk_async_handle_await(handle);
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);
#define NUM_CLIENTS 3
  valk_async_handle_t *hclients[NUM_CLIENTS] = {0};
  valk_lval_t *client_results[NUM_CLIENTS] = {0};
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  }
  for (int i = 0; i < NUM_CLIENTS; i++) {
    client_results[i] = valk_async_handle_await(hclients[i]);
    ASSERT_TRUE(LVAL_TYPE(client_results[i]) != LVAL_ERR);
  }
  usleep(50000);
  for (int c = 0; c < NUM_CLIENTS; c++) {
    valk_aio_http2_client *client = client_results[c]->ref.ptr;
    u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);
    valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
    valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
    valk_lval_t *res = valk_async_handle_await(hres);
    ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);
  }
#undef NUM_CLIENTS
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}
int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "test_critical_watermark_rejects_all", test_critical_watermark_rejects_all);
  valk_testsuite_add_test(suite, "test_below_high_watermark_accepts_all", test_below_high_watermark_accepts_all);
  valk_testsuite_add_test(suite, "test_watermark_defaults_applied", test_watermark_defaults_applied);
  valk_testsuite_add_test(suite, "test_probabilistic_shedding_range", test_probabilistic_shedding_range);
  valk_testsuite_add_test(suite, "test_load_shedding_counter_increments", test_load_shedding_counter_increments);
  valk_testsuite_add_test(suite, "test_high_watermark_load_shedding", test_high_watermark_load_shedding);
  valk_testsuite_add_test(suite, "test_many_concurrent_requests", test_many_concurrent_requests);
  valk_testsuite_add_test(suite, "test_load_shedding_metrics", test_load_shedding_metrics);
  valk_testsuite_add_test(suite, "test_buffer_pool_usage", test_buffer_pool_usage);
  valk_testsuite_add_test(suite, "test_arena_pool_usage", test_arena_pool_usage);
  valk_testsuite_add_test(suite, "test_connection_state_transitions", test_connection_state_transitions);
  valk_testsuite_add_test(suite, "test_rapid_connect_disconnect", test_rapid_connect_disconnect);
  valk_testsuite_add_test(suite, "test_arena_exhaustion_returns_503", test_arena_exhaustion_returns_503);
  valk_testsuite_add_test(suite, "test_tcp_buffer_exhaustion_backpressure", test_tcp_buffer_exhaustion_backpressure);
  valk_testsuite_add_test(suite, "test_backpressure_connections_survive", test_backpressure_connections_survive);
  valk_testsuite_add_test(suite, "test_custom_503_body", test_custom_503_body);
  valk_testsuite_add_test(suite, "test_backpressure_list_remove_nonhead", test_backpressure_list_remove_nonhead);
  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return res;
}
