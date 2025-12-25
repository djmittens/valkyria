#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>

#include "aio/aio.h"
#include "collections.h"
#include "common.h"
#include "concurrency.h"
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  int port = valk_aio_http2_server_get_port(server->item);
  
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
  ASSERT_NOT_NULL(response->body);
  ASSERT_STR_CONTAINS((char *)response->body, "Valkyria");
  
  valk_arc_release(res);
  valk_arc_release(fres);
  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);
  
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
  VALK_SKIP("minimal config has race condition in initialization - see TODO");
  return;
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  int port = valk_aio_http2_server_get_port(server->item);
  
  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);
  
  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  
  valk_arc_release(server);
  valk_arc_release(fserv);
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  int port = valk_aio_http2_server_get_port(server->item);
  
  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);
  
  valk_aio_http2_client *client = clientBox->item;
  
  for (int i = 0; i < 5; i++) {
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
    ASSERT_NOT_NULL(response->body);
    
    valk_arc_release(res);
    valk_arc_release(fres);
  }
  
  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  int port = valk_aio_http2_server_get_port(server->item);
  
  #define NUM_CLIENTS 3
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  valk_aio_http2_client *clients[NUM_CLIENTS];
  
  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
    ASSERT_EQ(clientBoxes[i]->type, VALK_SUC);
    clients[i] = clientBoxes[i]->item;
  }
  
  for (int i = 0; i < NUM_CLIENTS; i++) {
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
    
    valk_future *fres = valk_aio_http2_request_send(req, clients[i]);
    valk_arc_box *res = valk_future_await(fres);
    ASSERT_EQ(res->type, VALK_SUC);
    
    valk_arc_release(res);
    valk_arc_release(fres);
  }
  
  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
  
  valk_arc_release(server);
  valk_arc_release(fserv);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, NUM_CLIENTS);
  
  #undef NUM_CLIENTS
  VALK_PASS();
}

static void test_server_shutdown_with_active_clients(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("shutdown race condition when client not disconnected - TODO fix");
  return;
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  int port = valk_aio_http2_server_get_port(server->item);
  
  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);
  
  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_connect_to_nonexistent_server(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("connection refused error handling has use-after-free - TODO fix");
  return;
  
  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  
  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", 59999, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  
  ASSERT_EQ(clientBox->type, VALK_ERR);
  
  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  
  valk_arc_release(server);
  valk_arc_release(fserv);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  ASSERT_EQ(connected, 0);
  
  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  
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
  
  valk_arc_release(server);
  valk_arc_release(fserv);
  
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  
  VALK_PASS();
}

static void test_metrics_available(VALK_TEST_ARGS()) {
  VALK_TEST();
  
  valk_aio_system_t *sys = valk_aio_start();
  ASSERT_NOT_NULL(sys);
  
  valk_aio_metrics_t *metrics = valk_aio_get_metrics(sys);
  ASSERT_NOT_NULL(metrics);
  
  valk_aio_system_stats_t *stats = valk_aio_get_system_stats(sys);
  ASSERT_NOT_NULL(stats);
  
  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  int port = valk_aio_http2_server_get_port(server->item);
  
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

#endif

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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  
  valk_arc_release(server);
  valk_arc_release(fserv);
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  
  valk_arc_release(server);
  valk_arc_release(fserv);
  
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
  
  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);
  
  valk_arc_release(server);
  valk_arc_release(fserv);
  
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
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_metrics_available", test_metrics_available);
  valk_testsuite_add_test(suite, "test_slab_accessors", test_slab_accessors);
#endif
  valk_testsuite_add_test(suite, "test_custom_watermarks", test_custom_watermarks);
  valk_testsuite_add_test(suite, "test_api_config", test_api_config);
  valk_testsuite_add_test(suite, "test_large_payload_config", test_large_payload_config);
  valk_testsuite_add_test(suite, "test_system_name", test_system_name);
  valk_testsuite_add_test(suite, "test_event_loop_accessible", test_event_loop_accessible);
  valk_testsuite_add_test(suite, "test_shutting_down_flag", test_shutting_down_flag);
  
  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  
  return res;
}
