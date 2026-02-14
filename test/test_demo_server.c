// test/test_demo_server.c
// Comprehensive tests for demo server endpoints, concurrency, load shedding, and metrics
//
// Build: Part of make build
// Run: ./build/test_demo_server

#include "test_networking.h"

#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "collections.h"
#include "common.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

#include "aio/aio_metrics.h"
#include "metrics_v2.h"
#include "metrics_delta.h"

// ============================================================================
// Test Configuration
// ============================================================================

#define TEST_RESPONSE_SIZE_1MB (1024 * 1024)

// Helper: Start AIO with mellow demo config (low resource usage)
static valk_aio_system_t *start_demo_server(void) {
  valk_aio_system_config_t config = valk_aio_config_demo();
  return valk_aio_start_with_config(&config);
}

// ============================================================================
// Callback implementations (same as test_networking.c)
// ============================================================================

static void demo_cb_onConnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
}

static void demo_cb_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->disconnectedCount, 1, __ATOMIC_RELAXED);
}

static void demo_cb_onHeader(void *arg, valk_aio_handle_t *conn, u64 stream, char *name,
                 char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

static void demo_cb_onBody(void *arg, valk_aio_handle_t *conn, u64 stream, u8 flags,
               valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}

static valk_http2_handler_t *get_noop_handler(void) {
  static valk_http2_handler_t handler;
  static int initialized = 0;
  if (!initialized) {
    handler.arg = nullptr;
    handler.onConnect = demo_cb_onConnect;
    handler.onDisconnect = demo_cb_onDisconnect;
    handler.onHeader = demo_cb_onHeader;
    handler.onBody = demo_cb_onBody;
    initialized = 1;
  }
  return &handler;
}

// ============================================================================
// Helper: Send HTTP/2 request and get response
// ============================================================================

typedef struct {
  char status[16];    // Copy status to avoid use-after-free
  u8 *body;      // Points to copied body
  size_t body_len;
  bool success;
} test_response_t;

static test_response_t send_request(valk_aio_system_t *sys, int port,
                                     const char *method, const char *path) {
  test_response_t result = {0};

  // Build request
  alignas(max_align_t) u8 req_buf[sizeof(valk_mem_arena_t) + 8192];
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 8192);

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)req_arena;
    req->method = (char *)method;
    req->scheme = "https";
    req->authority = "localhost";
    req->path = (char *)path;
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  // Connect
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);

  if (LVAL_TYPE(client_result) == LVAL_ERR) {
    return result;
  }

  valk_aio_http2_client *client = client_result->ref.ptr;

  // Send request
  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res = valk_async_handle_await(hres);

  if (LVAL_TYPE(res) != LVAL_ERR) {
    valk_http2_response_t *response = res->ref.ptr;
    // Copy status to result (avoid use-after-free)
    if (response->status) {
      strncpy(result.status, response->status, sizeof(result.status) - 1);
      result.status[sizeof(result.status) - 1] = '\0';
    }
    // Copy body if present
    if (response->body && response->bodyLen > 0) {
      result.body = malloc(response->bodyLen + 1);
      if (result.body) {
        memcpy(result.body, response->body, response->bodyLen);
        result.body[response->bodyLen] = '\0';
        result.body_len = response->bodyLen;
      }
    }
    result.success = true;
  }

  return result;
}

static void free_response(test_response_t *resp) {
  if (resp->body) {
    free(resp->body);
    resp->body = nullptr;
  }
}

// ============================================================================
// Test: Basic HTTP/2 server with C handler
// ============================================================================

void test_basic_server_c_handler(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = start_demo_server();

  // Use demo handler
  valk_http2_handler_t *handler = get_noop_handler();

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", handler, nullptr);

  valk_lval_t *result = valk_async_handle_await(handle);
  VALK_TEST_ASSERT(LVAL_TYPE(result) != LVAL_ERR, "Server should start successfully");
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  // Send request
  test_response_t resp = send_request(sys, port, "GET", "/");
  VALK_TEST_ASSERT(resp.success, "Request should succeed");
  VALK_TEST_ASSERT(strcmp(resp.status, "200") == 0, "Should return 200, got [%s]", resp.status);
  VALK_TEST_ASSERT(resp.body_len > 0, "Body should not be empty");

  // Cleanup
  free_response(&resp);
  valk_aio_stop(sys);

  VALK_PASS();
}

// ============================================================================
// Test: Multiple requests to same server
// ============================================================================

void test_multiple_requests(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = start_demo_server();

  valk_http2_handler_t *handler = get_noop_handler();

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", handler, nullptr);

  valk_lval_t *result = valk_async_handle_await(handle);
  VALK_TEST_ASSERT(LVAL_TYPE(result) != LVAL_ERR, "Server should start successfully");
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  // Send 5 requests
  for (int i = 0; i < 5; i++) {
    test_response_t resp = send_request(sys, port, "GET", "/");
    VALK_TEST_ASSERT(resp.success, "Request %d should succeed", i);
    VALK_TEST_ASSERT(strcmp(resp.status, "200") == 0,
                     "Request %d should return 200, got [%s]", i, resp.status);
    free_response(&resp);
  }

  valk_aio_stop(sys);

  VALK_PASS();
}

// ============================================================================
// Test: Server with custom configuration
// ============================================================================

void test_custom_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Custom config with small pools
  valk_aio_system_config_t config = {
    .max_connections = 10,
    .max_concurrent_streams = 5,
    .tcp_buffer_pool_size = 50,
    .arena_pool_size = 5,
    .arena_size = 16 * 1024 * 1024,  // 16MB
    .max_request_body_size = 1 * 1024 * 1024,  // 1MB
  };

  valk_aio_system_t *sys = valk_aio_start_with_config(&config);
  VALK_TEST_ASSERT(sys != nullptr, "AIO system should start with custom config");

  valk_http2_handler_t *handler = get_noop_handler();

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", handler, nullptr);

  valk_lval_t *result = valk_async_handle_await(handle);
  VALK_TEST_ASSERT(LVAL_TYPE(result) != LVAL_ERR, "Server should start with custom config");
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  test_response_t resp = send_request(sys, port, "GET", "/");
  VALK_TEST_ASSERT(resp.success, "Request should succeed with custom config");

  free_response(&resp);
  valk_aio_stop(sys);

  VALK_PASS();
}

// ============================================================================
// Test: Metrics collection
// ============================================================================

void test_aio_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = start_demo_server();

  valk_http2_handler_t *handler = get_noop_handler();

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", handler, nullptr);

  valk_lval_t *result = valk_async_handle_await(handle);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  // Send some requests
  for (int i = 0; i < 3; i++) {
    test_response_t resp = send_request(sys, port, "GET", "/");
    VALK_TEST_ASSERT(resp.success, "Request %d should succeed", i);
    free_response(&resp);
  }

  valk_aio_stop(sys);

  VALK_PASS();
}

void test_metrics_json_rendering(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = start_demo_server();

  valk_http2_handler_t *handler = get_noop_handler();

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", handler, nullptr);

  valk_lval_t *result = valk_async_handle_await(handle);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  // Send a request to generate metrics
  test_response_t resp = send_request(sys, port, "GET", "/");
  VALK_TEST_ASSERT(resp.success, "Request should succeed");
  free_response(&resp);

  // Render metrics as JSON using V2 registry
  char *buf = malloc(131072);
  VALK_TEST_ASSERT(buf != nullptr, "Buffer allocation should succeed");
  u64 len = valk_metrics_v2_to_json(&g_metrics, buf, 131072);

  VALK_TEST_ASSERT(len > 100, "JSON should have substantial content: %zu bytes", len);

  free(buf);
  valk_aio_stop(sys);

  VALK_PASS();
}

void test_modular_metrics_counter(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Initialize registry if not done
  valk_metrics_registry_init();

  // Create a counter
  valk_label_set_v2_t labels = {0};
  valk_counter_v2_t *counter = valk_counter_get_or_create(
      "test_demo_requests", "Test counter for demo", &labels);

  VALK_TEST_ASSERT(counter != nullptr, "Counter should be created");

  u64 initial = atomic_load(&counter->value);

  // Increment
  valk_counter_v2_inc(counter);
  valk_counter_v2_inc(counter);
  valk_counter_v2_add(counter, 5);

  u64 final = atomic_load(&counter->value);
  VALK_TEST_ASSERT(final == initial + 7,
                   "Counter should increment by 7: %lu -> %lu", initial, final);

  VALK_PASS();
}

void test_modular_metrics_labeled_counter(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Create counters with different labels
  valk_label_set_v2_t labels_get = {
    .labels = {{"method", "GET"}, {"status", "200"}},
    .count = 2
  };
  valk_label_set_v2_t labels_post = {
    .labels = {{"method", "POST"}, {"status", "201"}},
    .count = 2
  };

  valk_counter_v2_t *counter_get = valk_counter_get_or_create(
      "test_http_requests", "HTTP requests by method", &labels_get);
  valk_counter_v2_t *counter_post = valk_counter_get_or_create(
      "test_http_requests", "HTTP requests by method", &labels_post);

  VALK_TEST_ASSERT(counter_get != nullptr, "GET counter should be created");
  VALK_TEST_ASSERT(counter_post != nullptr, "POST counter should be created");
  VALK_TEST_ASSERT(counter_get != counter_post, "Different labels should create different counters");

  valk_counter_v2_inc(counter_get);
  valk_counter_v2_inc(counter_get);
  valk_counter_v2_inc(counter_post);

  VALK_TEST_ASSERT(atomic_load(&counter_get->value) >= 2, "GET counter should be >= 2");
  VALK_TEST_ASSERT(atomic_load(&counter_post->value) >= 1, "POST counter should be >= 1");

  VALK_PASS();
}

void test_modular_metrics_gauge(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_label_set_v2_t labels = {0};
  valk_gauge_v2_t *gauge = valk_gauge_get_or_create(
      "test_active_connections", "Active connection count", &labels);

  VALK_TEST_ASSERT(gauge != nullptr, "Gauge should be created");

  valk_gauge_v2_set(gauge, 10);
  VALK_TEST_ASSERT(atomic_load(&gauge->value) == 10, "Gauge should be 10");

  valk_gauge_v2_inc(gauge);
  valk_gauge_v2_inc(gauge);
  VALK_TEST_ASSERT(atomic_load(&gauge->value) == 12, "Gauge should be 12");

  valk_gauge_v2_dec(gauge);
  VALK_TEST_ASSERT(atomic_load(&gauge->value) == 11, "Gauge should be 11");

  VALK_PASS();
}

void test_modular_metrics_histogram(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  // Standard latency buckets (in seconds)
  double buckets[] = {0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0, 5.0};

  valk_label_set_v2_t labels = {0};
  valk_histogram_v2_t *hist = valk_histogram_get_or_create(
      "test_request_duration", "Request duration histogram",
      buckets, 8, &labels);

  VALK_TEST_ASSERT(hist != nullptr, "Histogram should be created");

  // Record some observations (in microseconds)
  valk_histogram_v2_observe_us(hist, 500);    // 0.5ms
  valk_histogram_v2_observe_us(hist, 2000);   // 2ms
  valk_histogram_v2_observe_us(hist, 10000);  // 10ms
  valk_histogram_v2_observe_us(hist, 50000);  // 50ms
  valk_histogram_v2_observe_us(hist, 100000); // 100ms

  VALK_TEST_ASSERT(atomic_load(&hist->count) == 5, "Histogram count should be 5");
  VALK_TEST_ASSERT(atomic_load(&hist->sum_micros) == 162500,
                   "Histogram sum should be 162500us");

  VALK_PASS();
}

void test_connection_states(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_srv_state_t state = {0};
  valk_http2_handler_t handler = {
    .arg = &state,
    .onConnect = demo_cb_onConnect,
    .onDisconnect = demo_cb_onDisconnect,
    .onHeader = demo_cb_onHeader,
    .onBody = demo_cb_onBody,
  };

  valk_aio_system_t *sys = start_demo_server();

  valk_async_handle_t *handle = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", &handler, nullptr);

  valk_lval_t *result = valk_async_handle_await(handle);
  VALK_TEST_ASSERT(LVAL_TYPE(result) != LVAL_ERR, "Server should start");
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(result);
  int port = valk_aio_http2_server_get_port(srv);

  // Initial state
  VALK_TEST_ASSERT(__atomic_load_n(&state.connectedCount, __ATOMIC_ACQUIRE) == 0,
                   "Initial connected count should be 0");

  // Connect and send request
  test_response_t resp = send_request(sys, port, "GET", "/");
  VALK_TEST_ASSERT(resp.success, "Request should succeed");
  free_response(&resp);

  // Check connection was tracked
  size_t connected = __atomic_load_n(&state.connectedCount, __ATOMIC_ACQUIRE);
  VALK_TEST_ASSERT(connected >= 1, "Should have at least 1 connection: %zu", connected);

  valk_aio_stop(sys);

  VALK_PASS();
}

// ============================================================================
// Test: Multiple servers on different ports
// ============================================================================

void test_multiple_servers(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_t *sys = start_demo_server();

  valk_http2_handler_t *handler = get_noop_handler();

  // Start two servers with OS-assigned ports
  valk_async_handle_t *handle1 = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", handler, nullptr);
  valk_async_handle_t *handle2 = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, VALK_BUILD_DIR "/server.key", VALK_BUILD_DIR "/server.crt", handler, nullptr);

  valk_lval_t *result1 = valk_async_handle_await(handle1);
  valk_lval_t *result2 = valk_async_handle_await(handle2);

  VALK_TEST_ASSERT(LVAL_TYPE(result1) != LVAL_ERR, "Server 1 should start");
  VALK_TEST_ASSERT(LVAL_TYPE(result2) != LVAL_ERR, "Server 2 should start");

  valk_aio_http_server *srv1 = valk_aio_http2_server_from_ref(result1);
  valk_aio_http_server *srv2 = valk_aio_http2_server_from_ref(result2);
  int port1 = valk_aio_http2_server_get_port(srv1);
  int port2 = valk_aio_http2_server_get_port(srv2);
  VALK_TEST_ASSERT(port1 != port2, "Ports should be different");

  // Request to both servers
  test_response_t resp1 = send_request(sys, port1, "GET", "/");
  test_response_t resp2 = send_request(sys, port2, "GET", "/");

  VALK_TEST_ASSERT(resp1.success, "Request to server 1 should succeed");
  VALK_TEST_ASSERT(resp2.success, "Request to server 2 should succeed");

  free_response(&resp1);
  free_response(&resp2);
  valk_aio_stop(sys);

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

  // Basic server tests
  valk_testsuite_add_test(suite, "test_basic_server_c_handler", test_basic_server_c_handler);
  valk_testsuite_add_test(suite, "test_multiple_requests", test_multiple_requests);
  valk_testsuite_add_test(suite, "test_custom_config", test_custom_config);
  valk_testsuite_add_test(suite, "test_connection_states", test_connection_states);
  valk_testsuite_add_test(suite, "test_multiple_servers", test_multiple_servers);
  valk_testsuite_add_test(suite, "test_aio_metrics", test_aio_metrics);
  valk_testsuite_add_test(suite, "test_metrics_json_rendering", test_metrics_json_rendering);
  valk_testsuite_add_test(suite, "test_modular_metrics_counter", test_modular_metrics_counter);
  valk_testsuite_add_test(suite, "test_modular_metrics_labeled_counter", test_modular_metrics_labeled_counter);
  valk_testsuite_add_test(suite, "test_modular_metrics_gauge", test_modular_metrics_gauge);
  valk_testsuite_add_test(suite, "test_modular_metrics_histogram", test_modular_metrics_histogram);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
