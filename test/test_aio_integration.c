#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "aio/aio_internal.h"
#include "aio/aio_metrics.h"
#include "aio/aio_metrics_v2.h"
#include "collections.h"
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

static void test_basic_http2_connection(VALK_TEST_ARGS()) {
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
    req->path = "/";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }
  
  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);
  ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);
  
  valk_http2_response_t *response = res->ref.ptr;
  REQUIRE_NOT_NULL(response);
  ASSERT_NOT_NULL(response->body);
  ASSERT_STR_CONTAINS((char *)response->body, "Valkyria");
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  size_t disconnected = __atomic_load_n(&arg.disconnectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, 1);
  ASSERT_EQ(disconnected, 1);
  
  VALK_PASS();
}

static void test_minimal_config(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_config_t cfg = valk_aio_config_minimal();
  cfg.tcp_buffer_pool_size = 16;
  cfg.queue_capacity = 16;
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);
  
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
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
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_demo_config(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_config_t cfg = valk_aio_config_demo();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);
  
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_multiple_requests_single_connection(VALK_TEST_ARGS()) {
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
  
  for (int i = 0; i < 5; i++) {
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
    
    valk_http2_response_t *response = res->ref.ptr;
    REQUIRE_NOT_NULL(response);
    ASSERT_NOT_NULL(response->body);
  }
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_multiple_concurrent_clients(VALK_TEST_ARGS()) {
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
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server_result);
  int port = valk_aio_http2_server_get_port(srv);
  
  #define NUM_CLIENTS 3
  valk_async_handle_t *hclients[NUM_CLIENTS];
  valk_lval_t *client_results[NUM_CLIENTS];
  valk_aio_http2_client *clients[NUM_CLIENTS];
  
  for (int i = 0; i < NUM_CLIENTS; i++) {
    hclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    client_results[i] = valk_async_handle_await(hclients[i]);
    ASSERT_TRUE(LVAL_TYPE(client_results[i]) != LVAL_ERR);
    clients[i] = client_results[i]->ref.ptr;
  }
  
  for (int i = 0; i < NUM_CLIENTS; i++) {
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
    
    valk_async_handle_t *hres = valk_aio_http2_request_send(req, clients[i]);
    valk_lval_t *res = valk_async_handle_await(hres);
    ASSERT_TRUE(LVAL_TYPE(res) != LVAL_ERR);
  }
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, NUM_CLIENTS);
  
  #undef NUM_CLIENTS
  VALK_PASS();
}

static void test_server_shutdown_with_active_clients(VALK_TEST_ARGS()) {
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
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server_result);
  int port = valk_aio_http2_server_get_port(srv);
  
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  ASSERT_TRUE(LVAL_TYPE(client_result) != LVAL_ERR);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_connect_to_nonexistent_server(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", 59999, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  
  ASSERT_TRUE(LVAL_TYPE(client_result) == LVAL_ERR);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_server_only_no_clients(VALK_TEST_ARGS()) {
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
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, 0);
  
  VALK_PASS();
}

static void test_slab_accessors(VALK_TEST_ARGS()) {
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
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  
  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  ASSERT_NOT_NULL(tcp_slab);
  
  valk_slab_t *handle_slab = valk_aio_get_handle_slab(sys);
  ASSERT_NOT_NULL(handle_slab);
  
  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  ASSERT_NOT_NULL(arena_slab);
  
  valk_slab_t *server_slab = valk_aio_get_http_servers_slab(sys);
  ASSERT_NOT_NULL(server_slab);
  
  valk_slab_t *client_slab = valk_aio_get_http_clients_slab(sys);
  ASSERT_NOT_NULL(client_slab);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_metrics_available(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  
  valk_aio_metrics_v2_t *metrics = VALK_METRICS_V2(sys);
  ASSERT_NOT_NULL(metrics);
  
  valk_aio_system_stats_v2_t *stats = VALK_SYSTEM_STATS_V2(sys);
  ASSERT_NOT_NULL(stats);
  
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
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
    req->path = "/";
    req->body = (u8 *)"";
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

static void test_custom_watermarks(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_config_t cfg = valk_aio_config_minimal();
  cfg.tcp_buffer_pool_size = 16;
  cfg.queue_capacity = 16;
  cfg.buffer_high_watermark = 0.5f;
  cfg.buffer_critical_watermark = 0.7f;
  
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);
  
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_api_config(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_config_t cfg = valk_aio_config_api();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);
  
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_large_payload_config(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_config_t cfg = valk_aio_config_large_payload();
  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);
  
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  
  valk_async_handle_t *server_handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server_result = valk_async_handle_await(server_handle);
  ASSERT_TRUE(LVAL_TYPE(server_result) != LVAL_ERR);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

extern void valk_register_aio_diagnostics_builtins(valk_lenv_t *env);

static valk_lval_t *call_diag_builtin(valk_lenv_t *env, const char *name, valk_lval_t *args) {
  valk_lval_t *sym = valk_lval_sym(name);
  valk_lval_t *fun = valk_lval_eval(env, sym);
  if (LVAL_TYPE(fun) == LVAL_ERR) {
    return fun;
  }
  return valk_lval_eval_call(env, fun, args);
}

static void test_diagnostics_json_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){ ref }, 1);

  valk_lval_t *result = call_diag_builtin(env, "aio/diagnostics-state-json", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_STR);
  ASSERT_NOT_NULL(result->str);
  ASSERT_TRUE(strstr(result->str, "slabs") != nullptr);
  ASSERT_TRUE(strstr(result->str, "gc") != nullptr);
  ASSERT_TRUE(strstr(result->str, "process") != nullptr);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_json_compact(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){ ref }, 1);

  valk_lval_t *result = call_diag_builtin(env, "aio/diagnostics-state-json-compact", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_STR);
  ASSERT_NOT_NULL(result->str);
  ASSERT_TRUE(strstr(result->str, "gc") != nullptr);
  ASSERT_TRUE(strstr(result->str, "rss") != nullptr);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("handles"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_STR);
  ASSERT_NOT_NULL(result->str);
  ASSERT_TRUE(strstr(result->str, "buckets") != nullptr);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_invalid_slab(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("nonexistent_slab"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("handles")
  }, 2);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("wrong_type", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("handles"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_invalid_buckets(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("handles"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(0)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_invalid_arg_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_num(123),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_lval_slab(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("lval"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_stream_arenas(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("stream_arenas"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_STR);
  ASSERT_NOT_NULL(result->str);
  ASSERT_TRUE(strstr(result->str, "buckets") != nullptr);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_http_servers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("http_servers"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_STR);
  ASSERT_NOT_NULL(result->str);
  ASSERT_TRUE(strstr(result->str, "buckets") != nullptr);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_slab_buckets_http_clients(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("aio_system", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){
    ref,
    valk_lval_str("http_clients"),
    valk_lval_num(0),
    valk_lval_num(100),
    valk_lval_num(10)
  }, 5);

  valk_lval_t *result = call_diag_builtin(env, "aio/slab-buckets", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_STR);
  ASSERT_NOT_NULL(result->str);
  ASSERT_TRUE(strstr(result->str, "buckets") != nullptr);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_json_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *args = valk_lval_list(nullptr, 0);

  valk_lval_t *result = call_diag_builtin(env, "aio/diagnostics-state-json", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_json_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){ valk_lval_num(42) }, 1);

  valk_lval_t *result = call_diag_builtin(env, "aio/diagnostics-state-json", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_json_compact_wrong_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *args = valk_lval_list(nullptr, 0);

  valk_lval_t *result = call_diag_builtin(env, "aio/diagnostics-state-json-compact", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_diagnostics_json_compact_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);

  valk_lenv_t *env = valk_lenv_empty();
  valk_register_aio_diagnostics_builtins(env);

  valk_lval_t *ref = valk_lval_ref("wrong_type", sys, nullptr);
  valk_lval_t *args = valk_lval_list((valk_lval_t*[]){ ref }, 1);

  valk_lval_t *result = call_diag_builtin(env, "aio/diagnostics-state-json-compact", args);
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_system_name(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  
  valk_aio_set_name(sys, "test-system");
  const char *name = valk_aio_get_name(sys);
  ASSERT_NOT_NULL(name);
  ASSERT_TRUE(strcmp(name, "test-system") == 0);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_event_loop_accessible(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  
  struct uv_loop_s *loop = valk_aio_get_event_loop(sys);
  ASSERT_NOT_NULL(loop);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_shutting_down_flag(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  
  ASSERT_FALSE(valk_aio_is_shutting_down(sys));
  
  valk_aio_stop(sys);
  
  ASSERT_TRUE(valk_aio_is_shutting_down(sys));
  
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);
  
  valk_mem_init_malloc();
  
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  
  valk_testsuite_add_test(suite, "test_basic_http2_connection", test_basic_http2_connection);
  valk_testsuite_add_test(suite, "test_minimal_config", test_minimal_config);
  valk_testsuite_add_test(suite, "test_demo_config", test_demo_config);
  valk_testsuite_add_test(suite, "test_multiple_requests_single_connection", test_multiple_requests_single_connection);
  valk_testsuite_add_test(suite, "test_multiple_concurrent_clients", test_multiple_concurrent_clients);
  valk_testsuite_add_test(suite, "test_server_shutdown_with_active_clients", test_server_shutdown_with_active_clients);
  valk_testsuite_add_test(suite, "test_connect_to_nonexistent_server", test_connect_to_nonexistent_server);
  valk_testsuite_add_test(suite, "test_server_only_no_clients", test_server_only_no_clients);
  valk_testsuite_add_test(suite, "test_metrics_available", test_metrics_available);
  valk_testsuite_add_test(suite, "test_slab_accessors", test_slab_accessors);
  valk_testsuite_add_test(suite, "test_custom_watermarks", test_custom_watermarks);
  valk_testsuite_add_test(suite, "test_api_config", test_api_config);
  valk_testsuite_add_test(suite, "test_large_payload_config", test_large_payload_config);
  valk_testsuite_add_test(suite, "test_system_name", test_system_name);
  valk_testsuite_add_test(suite, "test_event_loop_accessible", test_event_loop_accessible);
  valk_testsuite_add_test(suite, "test_shutting_down_flag", test_shutting_down_flag);

  // Diagnostics builtins integration tests
  valk_testsuite_add_test(suite, "test_diagnostics_json_basic", test_diagnostics_json_basic);
  valk_testsuite_add_test(suite, "test_diagnostics_json_compact", test_diagnostics_json_compact);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets", test_diagnostics_slab_buckets);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_invalid_slab", test_diagnostics_slab_buckets_invalid_slab);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_wrong_args", test_diagnostics_slab_buckets_wrong_args);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_wrong_ref_type", test_diagnostics_slab_buckets_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_invalid_buckets", test_diagnostics_slab_buckets_invalid_buckets);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_invalid_arg_types", test_diagnostics_slab_buckets_invalid_arg_types);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_lval_slab", test_diagnostics_slab_buckets_lval_slab);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_stream_arenas", test_diagnostics_slab_buckets_stream_arenas);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_http_servers", test_diagnostics_slab_buckets_http_servers);
  valk_testsuite_add_test(suite, "test_diagnostics_slab_buckets_http_clients", test_diagnostics_slab_buckets_http_clients);
  valk_testsuite_add_test(suite, "test_diagnostics_json_wrong_args", test_diagnostics_json_wrong_args);
  valk_testsuite_add_test(suite, "test_diagnostics_json_wrong_type", test_diagnostics_json_wrong_type);
  valk_testsuite_add_test(suite, "test_diagnostics_json_compact_wrong_args", test_diagnostics_json_compact_wrong_args);
  valk_testsuite_add_test(suite, "test_diagnostics_json_compact_wrong_type", test_diagnostics_json_compact_wrong_type);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  
  return res;
}
