#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <pthread.h>

#include "aio.h"
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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

#ifdef VALK_METRICS_ENABLED
  valk_aio_system_stats_t *stats = valk_aio_get_system_stats(sys);
  uint64_t initial_rejected = atomic_load(&stats->connections_rejected_load);
#endif

#define NUM_CLIENTS 16
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  int rejected_count = 0;

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
    if (clientBoxes[i]->type != VALK_SUC) {
      rejected_count++;
    }
  }

#ifdef VALK_METRICS_ENABLED
  uint64_t final_rejected = atomic_load(&stats->connections_rejected_load);
  ASSERT_GT(final_rejected, initial_rejected);
#else
  ASSERT_GT(rejected_count, 0);
#endif

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

#ifdef VALK_METRICS_ENABLED
  valk_aio_system_stats_t *stats = valk_aio_get_system_stats(sys);
  uint64_t initial_rejected = atomic_load(&stats->connections_rejected_load);
#endif

#define NUM_CLIENTS 4
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  int successful = 0;

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
    if (clientBoxes[i]->type == VALK_SUC) {
      successful++;
    }
  }

  ASSERT_EQ(successful, NUM_CLIENTS);

#ifdef VALK_METRICS_ENABLED
  uint64_t final_rejected = atomic_load(&stats->connections_rejected_load);
  ASSERT_EQ(final_rejected, initial_rejected);
#endif

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

#define NUM_CLIENTS 12
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  int successful = 0;
  int failed = 0;

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
    if (clientBoxes[i]->type == VALK_SUC) {
      successful++;
    } else {
      failed++;
    }
  }

  ASSERT_GT(successful, 0);

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
static void test_load_shedding_counter_increments(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.05f;
  cfg.buffer_critical_watermark = 0.1f;
  cfg.tcp_buffer_pool_size = 8;
  cfg.max_connections = 32;

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  valk_aio_system_stats_t *stats = valk_aio_get_system_stats(sys);
  ASSERT_NOT_NULL(stats);
  uint64_t initial_rejected = atomic_load(&stats->connections_rejected_load);
  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
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

#define NUM_CLIENTS 20
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
  }

  uint64_t final_rejected = atomic_load(&stats->connections_rejected_load);
  ASSERT_GT(final_rejected, initial_rejected);

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}
#endif

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

#define NUM_CLIENTS 6
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  int successful = 0;

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
    if (clientBoxes[i]->type == VALK_SUC) {
      successful++;
    }
  }

  ASSERT_GT(successful, 0);

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

#define NUM_REQUESTS 20
  valk_future *freqs[NUM_REQUESTS];
  valk_arc_box *resBoxes[NUM_REQUESTS];
  int successful = 0;

  for (int i = 0; i < NUM_REQUESTS; i++) {
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

    freqs[i] = valk_aio_http2_request_send(req, client);
    resBoxes[i] = valk_future_await(freqs[i]);
    if (resBoxes[i]->type == VALK_SUC) {
      successful++;
    }

    valk_arc_release(resBoxes[i]);
    valk_arc_release(freqs[i]);
  }
#undef NUM_REQUESTS

  ASSERT_GT(successful, 0);

  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

#ifdef VALK_METRICS_ENABLED
static void test_load_shedding_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.buffer_high_watermark = 0.3f;
  cfg.buffer_critical_watermark = 0.5f;
  cfg.tcp_buffer_pool_size = 24;

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  ASSERT_NOT_NULL(sys);

  valk_aio_system_stats_t *stats = valk_aio_get_system_stats(sys);
  ASSERT_NOT_NULL(stats);
  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
      .arg = &state,
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

#define NUM_CLIENTS 8
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_buffer_pool_usage(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("race condition accessing tcp_slab before fully initialized");
  return;

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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

  valk_slab_t *tcp_slab = valk_aio_get_tcp_buffer_slab(sys);
  ASSERT_NOT_NULL(tcp_slab);

  size_t initial_available = valk_slab_available(tcp_slab);
  ASSERT_GT(initial_available, 0);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  size_t after_connect = valk_slab_available(tcp_slab);
  ASSERT_LE(after_connect, initial_available);

  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

  valk_slab_t *arena_slab = valk_aio_get_stream_arenas_slab(sys);
  ASSERT_NOT_NULL(arena_slab);

  size_t initial_available = valk_slab_available(arena_slab);

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

  size_t after_request = valk_slab_available(arena_slab);
  ASSERT_EQ(after_request, initial_available);

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

#define NUM_CYCLES 5
  for (int cycle = 0; cycle < NUM_CYCLES; cycle++) {
    valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_arc_box *clientBox = valk_future_await(fclient);
    ASSERT_EQ(clientBox->type, VALK_SUC);

    valk_arc_release(clientBox);
    valk_arc_release(fclient);
  }
#undef NUM_CYCLES

  valk_arc_release(server);
  valk_arc_release(fserv);

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
    req->body = (uint8_t *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }
  return req;
}

static void test_pending_stream_pool_exhaustion(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = valk_aio_config_demo();
  cfg.arena_pool_size = 1;
  cfg.pending_stream_pool_size = 1;
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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

#define NUM_REQUESTS 4
  for (int i = 0; i < NUM_REQUESTS; i++) {
    uint8_t req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);
    valk_http2_request_t *req = create_request(req_arena, "GET", "/");
    valk_future *fres = valk_aio_http2_request_send(req, client);
    valk_arc_box *res = valk_future_await(fres);
    valk_arc_release(res);
    valk_arc_release(fres);
  }
#undef NUM_REQUESTS

  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);

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

  valk_future *fserv = valk_aio_http2_listen(
      server_sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

#define NUM_CLIENTS 2
#define REQUESTS_PER_CLIENT 5
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  valk_future *freqs[NUM_CLIENTS * REQUESTS_PER_CLIENT];
  uint8_t *req_bufs[NUM_CLIENTS * REQUESTS_PER_CLIENT];
  int req_count = 0;

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(server_sys, "127.0.0.1", port, "");
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    clientBoxes[i] = valk_future_await(fclients[i]);
    if (clientBoxes[i]->type != VALK_SUC) continue;

    valk_aio_http2_client *client = clientBoxes[i]->item;
    for (int r = 0; r < REQUESTS_PER_CLIENT; r++) {
      uint8_t *req_buf = malloc(sizeof(valk_mem_arena_t) + 4096);
      req_bufs[req_count] = req_buf;
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);
      valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
      freqs[req_count++] = valk_aio_http2_request_send(req, client);
    }
  }

  for (int i = 0; i < req_count; i++) {
    valk_arc_box *res = valk_future_await(freqs[i]);
    valk_arc_release(res);
    valk_arc_release(freqs[i]);
    free(req_bufs[i]);
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS
#undef REQUESTS_PER_CLIENT

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(server_sys);
  valk_aio_wait_for_shutdown(server_sys);

  VALK_PASS();
}

static void test_backpressure_connections_survive(VALK_TEST_ARGS()) {
  VALK_TEST();

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

  int port = valk_aio_http2_server_get_port(server->item);

#define NUM_CLIENTS 4
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  valk_aio_http2_client *clients[NUM_CLIENTS];
  int connected = 0;

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  }
  for (int i = 0; i < NUM_CLIENTS; i++) {
    clientBoxes[i] = valk_future_await(fclients[i]);
    if (clientBoxes[i] && clientBoxes[i]->type == VALK_SUC) {
      clients[connected++] = clientBoxes[i]->item;
    }
  }

  ASSERT_GT(connected, 0);

  int total_completed = 0;
  for (int round = 0; round < 3; round++) {
    for (int i = 0; i < connected; i++) {
      uint8_t req_buf[sizeof(valk_mem_arena_t) + 4096];
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);
      valk_http2_request_t *req = create_request(req_arena, "GET", "/");
      valk_future *fres = valk_aio_http2_request_send(req, clients[i]);

      valk_arc_box *res = valk_future_await(fres);
      if (res && res->type == VALK_SUC) {
        total_completed++;
      }
      if (res) valk_arc_release(res);
      valk_arc_release(fres);
    }
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    if (clientBoxes[i]) valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

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
  cfg.pending_stream_pool_size = 2;

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

  valk_future *fserv = valk_aio_http2_listen_with_config(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL, &server_cfg);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

#define NUM_CLIENTS 3
  valk_future *fclients[NUM_CLIENTS];
  valk_arc_box *clientBoxes[NUM_CLIENTS];
  int successful = 0;

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clientBoxes[i] = valk_future_await(fclients[i]);
    if (clientBoxes[i]->type == VALK_SUC) {
      successful++;
    }
  }

  ASSERT_GT(successful, 0);

  for (int c = 0; c < successful; c++) {
    valk_aio_http2_client *client = clientBoxes[c]->item;
    for (int r = 0; r < 4; r++) {
      uint8_t req_buf[sizeof(valk_mem_arena_t) + 4096];
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);
      valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
      valk_future *fres = valk_aio_http2_request_send(req, client);
      valk_arc_box *res = valk_future_await(fres);
      valk_arc_release(res);
      valk_arc_release(fres);
    }
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

  int port = valk_aio_http2_server_get_port(server->item);

#define NUM_CLIENTS 3
  valk_future *fclients[NUM_CLIENTS] = {0};
  valk_arc_box *clientBoxes[NUM_CLIENTS] = {0};

  for (int i = 0; i < NUM_CLIENTS; i++) {
    fclients[i] = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    clientBoxes[i] = valk_future_await(fclients[i]);
    ASSERT_EQ(clientBoxes[i]->type, VALK_SUC);
  }
  
  usleep(50000);

  for (int c = 0; c < NUM_CLIENTS; c++) {
    valk_aio_http2_client *client = clientBoxes[c]->item;
    uint8_t req_buf[sizeof(valk_mem_arena_t) + 4096];
    valk_mem_arena_t *req_arena = (void *)req_buf;
    valk_mem_arena_init(req_arena, 4096);
    valk_http2_request_t *req = create_request(req_arena, "GET", "/test");
    valk_future *fres = valk_aio_http2_request_send(req, client);
    valk_arc_box *res = valk_future_await(fres);
    ASSERT_EQ(res->type, VALK_SUC);
    valk_arc_release(res);
    valk_arc_release(fres);
  }

  for (int i = 0; i < NUM_CLIENTS; i++) {
    valk_arc_release(clientBoxes[i]);
    valk_arc_release(fclients[i]);
  }
#undef NUM_CLIENTS

  valk_arc_release(server);
  valk_arc_release(fserv);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  VALK_PASS();
}

static void test_pending_stream_queue_ordering(VALK_TEST_ARGS()) {
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server = valk_future_await(fserv);
  ASSERT_EQ(server->type, VALK_SUC);

int port = valk_aio_http2_server_get_port(server->item);

  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);
  ASSERT_EQ(clientBox->type, VALK_SUC);

  valk_aio_http2_client *client = clientBox->item;

#define NUM_REQUESTS 3
  for (int round = 0; round < 2; round++) {
    for (int i = 0; i < NUM_REQUESTS; i++) {
      uint8_t req_buf[sizeof(valk_mem_arena_t) + 4096];
      valk_mem_arena_t *req_arena = (void *)req_buf;
      valk_mem_arena_init(req_arena, 4096);
      valk_http2_request_t *req = create_request(req_arena, "GET", "/");
      valk_future *freq = valk_aio_http2_request_send(req, client);
      valk_arc_box *res = valk_future_await(freq);
      valk_arc_release(res);
      valk_arc_release(freq);
    }
  }
#undef NUM_REQUESTS

  valk_arc_release(clientBox);
  valk_arc_release(fclient);
  valk_arc_release(server);
  valk_arc_release(fserv);

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
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_load_shedding_counter_increments", test_load_shedding_counter_increments);
#endif
  valk_testsuite_add_test(suite, "test_high_watermark_load_shedding", test_high_watermark_load_shedding);
  valk_testsuite_add_test(suite, "test_many_concurrent_requests", test_many_concurrent_requests);
#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_load_shedding_metrics", test_load_shedding_metrics);
  valk_testsuite_add_test(suite, "test_buffer_pool_usage", test_buffer_pool_usage);
  valk_testsuite_add_test(suite, "test_arena_pool_usage", test_arena_pool_usage);
#endif
  valk_testsuite_add_test(suite, "test_connection_state_transitions", test_connection_state_transitions);
  valk_testsuite_add_test(suite, "test_rapid_connect_disconnect", test_rapid_connect_disconnect);
  valk_testsuite_add_test(suite, "test_pending_stream_pool_exhaustion", test_pending_stream_pool_exhaustion);
  valk_testsuite_add_test(suite, "test_tcp_buffer_exhaustion_backpressure", test_tcp_buffer_exhaustion_backpressure);
  valk_testsuite_add_test(suite, "test_backpressure_connections_survive", test_backpressure_connections_survive);
  valk_testsuite_add_test(suite, "test_custom_503_body", test_custom_503_body);
  valk_testsuite_add_test(suite, "test_backpressure_list_remove_nonhead", test_backpressure_list_remove_nonhead);
  valk_testsuite_add_test(suite, "test_pending_stream_queue_ordering", test_pending_stream_queue_ordering);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
