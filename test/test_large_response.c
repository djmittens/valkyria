// test_large_response.c
// Regression tests for large HTTP response handling
// Tests Issue 1 (16KB data loss on EOF) and Issue 2 (pointer arithmetic crash)
// These tests are parameterized to support testing various response sizes

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

// Response size definitions (must match test_large_response_handler.valk)
#define SIZE_1MB   1048576
#define SIZE_2MB   2097152
#define SIZE_5MB   5242880
#define SIZE_10MB 10485760
#define SIZE_25MB 26214400
#define SIZE_50MB 52428800

// Expected pattern for verification (64 chars repeated)
static const char *EXPECTED_PATTERN =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyz./";

// Test context - shared between setup/teardown
typedef struct {
  valk_lenv_t *env;
  valk_lval_t *handler_fn;
  valk_aio_system_t *sys;
  valk_async_handle_t *hserv;
  valk_lval_t *server_result;
  valk_async_handle_t *hclient;
  valk_lval_t *client_result;
  valk_aio_http2_client *client;
  int port;
} test_context_t;

static void __test_thread_onboard(void) {
  if (valk_sys) valk_system_register_thread(valk_sys, NULL, NULL);
}

static bool init_test_context(test_context_t *ctx, VALK_TEST_ARGS()) {
  (void)_suite;
  
  printf("[test] Initializing runtime...\n");
  fflush(stdout);
  
  // Initialize system with GC heap - this registers main thread with GC
  valk_system_config_t sys_cfg = valk_system_config_default();
  sys_cfg.gc_heap_size = 1024ULL * 1024 * 1024;  // 1GB for large response tests
  valk_system_create(&sys_cfg);
  printf("[test] Runtime initialized, heap=%p\n", valk_thread_ctx.heap);
  fflush(stdout);

  // Load prelude
  printf("[test] Loading prelude...\n");
  fflush(stdout);
  valk_lval_t *prelude_ast = valk_parse_file("src/prelude.valk");
  if (!prelude_ast || LVAL_TYPE(prelude_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse prelude: %s",
              prelude_ast ? prelude_ast->str : "nullptr");
    return false;
  }

  ctx->env = valk_lenv_empty();
  valk_lenv_builtins(ctx->env);
  valk_thread_ctx.root_env = ctx->env;
  valk_gc_set_root(valk_thread_ctx.heap, ctx->env);

  while (valk_lval_list_count(prelude_ast)) {
    valk_lval_t *x = valk_lval_eval(ctx->env, valk_lval_pop(prelude_ast, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      VALK_FAIL("Prelude evaluation failed: %s", x->str);
      return false;
    }
  }

  // Load the large response handler
  printf("[test] Loading handler...\n");
  fflush(stdout);
  valk_lval_t *handler_ast = valk_parse_file("test/test_large_response_handler.valk");
  if (!handler_ast || LVAL_TYPE(handler_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse handler: %s",
              handler_ast ? handler_ast->str : "nullptr");
    return false;
  }

  ctx->handler_fn = nullptr;
  while (valk_lval_list_count(handler_ast)) {
    ctx->handler_fn = valk_lval_eval(ctx->env, valk_lval_pop(handler_ast, 0));
    if (LVAL_TYPE(ctx->handler_fn) == LVAL_ERR) {
      VALK_FAIL("Handler evaluation failed: %s", ctx->handler_fn->str);
      return false;
    }
  }

  if (!ctx->handler_fn || LVAL_TYPE(ctx->handler_fn) != LVAL_FUN) {
    VALK_FAIL("Handler is not a function, got type: %s",
              ctx->handler_fn ? valk_ltype_name(LVAL_TYPE(ctx->handler_fn)) : "nullptr");
    return false;
  }
  printf("[test] Handler loaded (type=%s)\n", valk_ltype_name(LVAL_TYPE(ctx->handler_fn)));
  fflush(stdout);

  // Switch to malloc for AIO client operations
  valk_mem_init_malloc();

  // Start AIO system with thread onboard function for event loop thread
  printf("[test] Starting AIO system...\n");
  fflush(stdout);
  valk_aio_system_config_t aio_cfg = valk_aio_config_large_payload();
  aio_cfg.thread_onboard_fn = __test_thread_onboard;
  ctx->sys = valk_aio_start_with_config(&aio_cfg);

  printf("[test] Starting server...\n");
  fflush(stdout);
  ctx->hserv = valk_aio_http2_listen(
      ctx->sys, "0.0.0.0", 0, "build/server.key", "build/server.crt",
      nullptr, ctx->handler_fn);

  ctx->server_result = valk_async_handle_await(ctx->hserv);
  if (LVAL_TYPE(ctx->server_result) == LVAL_ERR) {
    VALK_FAIL("Failed to start server: %s", ctx->server_result->str);
    return false;
  }

  // Get the actual port assigned by the OS
  valk_aio_http_server *srv = (valk_aio_http_server*)ctx->server_result->ref.ptr;
  ctx->port = valk_aio_http2_server_get_port(srv);
  printf("[test] Server started on port %d\n", ctx->port);
  fflush(stdout);

  // Connect client
  printf("[test] Connecting client...\n");
  fflush(stdout);
  ctx->hclient = valk_aio_http2_connect(ctx->sys, "127.0.0.1", ctx->port, "");
  ctx->client_result = valk_async_handle_await(ctx->hclient);

  if (LVAL_TYPE(ctx->client_result) == LVAL_ERR) {
    VALK_FAIL("Failed to connect client: %s", ctx->client_result->str);
    return false;
  }

  printf("[test] Client connected\n");
  fflush(stdout);
  ctx->client = ctx->client_result->ref.ptr;
  return true;
}

// Cleanup test context
static void cleanup_test_context(test_context_t *ctx) {
  if (ctx->sys) {
    valk_aio_stop(ctx->sys);
    valk_aio_wait_for_shutdown(ctx->sys);
  }
  valk_system_destroy(valk_sys);
}

// Parameterized test for large response handling
// Returns true if test passed, false otherwise
static bool test_large_response_size(test_context_t *ctx, const char *path,
                                     size_t expected_size, VALK_TEST_ARGS()) {
  (void)_suite;
  // Build request
  alignas(max_align_t) u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  memset(req_buf, 0, sizeof(req_buf));  // Zero to avoid stale pointer warnings
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)req_arena;
    req->method = "GET";
    req->scheme = "https";
    req->authority = "localhost";
    req->path = (char *)path;
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  printf("[test] Requesting %s (expecting %zu bytes)...\n", path, expected_size);

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, ctx->client);
  valk_lval_t *res = valk_async_handle_await(hres);

  if (LVAL_TYPE(res) == LVAL_ERR) {
    VALK_FAIL("Request to %s failed: %s", path, res->str);
    return false;
  }

  valk_http2_response_t *response = res->ref.ptr;
  printf("[test] Response received: %llu bytes (expected: %llu)\n",
         (unsigned long long)response->bodyLen, (unsigned long long)expected_size);

  // Verify response size - this is the critical regression test for Issue 1
  if (response->bodyLen != expected_size) {
    ssize_t diff = (ssize_t)response->bodyLen - (ssize_t)expected_size;
    VALK_FAIL("Size mismatch for %s: expected %zu bytes, got %zu bytes (diff: %zd)",
              path, expected_size, response->bodyLen, diff);
    return false;
  }

  // Verify content pattern (spot check first 64 bytes and last 64 bytes)
  if (response->bodyLen >= 64) {
    if (memcmp(response->body, EXPECTED_PATTERN, 64) != 0) {
      VALK_FAIL("Content mismatch at start of response for %s", path);
      return false;
    }
    // Check last 64 bytes to catch truncation issues
    size_t end_offset = response->bodyLen - 64;
    if (memcmp((char *)response->body + end_offset, EXPECTED_PATTERN, 64) != 0) {
      VALK_FAIL("Content mismatch at end of response for %s (offset %zu)", path, end_offset);
      return false;
    }
  }

  printf("[test] SUCCESS: %s response verified (%zu bytes)\n", path, expected_size);

  return true;
}

// Test 2MB response - smallest test to catch 16KB data loss
void test_response_2mb(VALK_TEST_ARGS()) {
  VALK_TEST();

  test_context_t ctx = {0};
  if (!init_test_context(&ctx, _suite, _result)) {
    cleanup_test_context(&ctx);
    return;
  }

  bool passed = test_large_response_size(&ctx, "/2mb", SIZE_2MB, _suite, _result);
  cleanup_test_context(&ctx);

  if (passed) {
    VALK_PASS();
  }
}

// Test 10MB response - medium size test
void test_response_10mb(VALK_TEST_ARGS()) {
  VALK_TEST();

  test_context_t ctx = {0};
  if (!init_test_context(&ctx, _suite, _result)) {
    cleanup_test_context(&ctx);
    return;
  }

  bool passed = test_large_response_size(&ctx, "/10mb", SIZE_10MB, _suite, _result);
  cleanup_test_context(&ctx);

  if (passed) {
    VALK_PASS();
  }
}

// Test 50MB response - large test matching original test case
void test_response_50mb(VALK_TEST_ARGS()) {
  VALK_TEST();

  test_context_t ctx = {0};
  if (!init_test_context(&ctx, _suite, _result)) {
    cleanup_test_context(&ctx);
    return;
  }

  bool passed = test_large_response_size(&ctx, "/50mb", SIZE_50MB, _suite, _result);
  cleanup_test_context(&ctx);

  if (passed) {
    VALK_PASS();
  }
}

// Test multiple sequential requests to catch connection state issues
void test_multiple_large_responses(VALK_TEST_ARGS()) {
  VALK_TEST();

  test_context_t ctx = {0};
  if (!init_test_context(&ctx, _suite, _result)) {
    cleanup_test_context(&ctx);
    return;
  }

  printf("[test] Testing multiple sequential large responses...\n");

  // Test sequence of different sizes
  struct {
    const char *path;
    size_t size;
  } tests[] = {
      {"/2mb", SIZE_2MB},
      {"/5mb", SIZE_5MB},
      {"/2mb", SIZE_2MB},   // Repeat to catch state issues
      {"/10mb", SIZE_10MB},
  };

  bool all_passed = true;
  for (size_t i = 0; i < sizeof(tests) / sizeof(tests[0]); i++) {
    printf("[test] Request %zu/%zu: %s\n", i + 1, sizeof(tests) / sizeof(tests[0]), tests[i].path);
    if (!test_large_response_size(&ctx, tests[i].path, tests[i].size, _suite, _result)) {
      all_passed = false;
      break;
    }
  }

  cleanup_test_context(&ctx);

  if (all_passed) {
    VALK_PASS();
  }
}

// Test small response to ensure fixes don't break normal operation
void test_response_small(VALK_TEST_ARGS()) {
  VALK_TEST();

  test_context_t ctx = {0};
  if (!init_test_context(&ctx, _suite, _result)) {
    cleanup_test_context(&ctx);
    return;
  }

  // Build request for /health endpoint (small response)
  alignas(max_align_t) u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  memset(req_buf, 0, sizeof(req_buf));  // Zero to avoid stale pointer warnings
  valk_mem_arena_t *req_arena = (void *)req_buf;
  valk_mem_arena_init(req_arena, 4096);

  valk_http2_request_t *req;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)req_arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)req_arena;
    req->method = "GET";
    req->scheme = "https";
    req->authority = "localhost";
    req->path = "/health";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  printf("[test] Requesting /health (small response)...\n");
  fflush(stdout);

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, ctx.client);
  printf("[test] Waiting for response...\n");
  fflush(stdout);
  valk_lval_t *res = valk_async_handle_await(hres);
  printf("[test] Got response from await\n");
  fflush(stdout);

  if (LVAL_TYPE(res) == LVAL_ERR) {
    VALK_FAIL("Request to /health failed: %s", res->str);
    cleanup_test_context(&ctx);
    return;
  }

  valk_http2_response_t *response = res->ref.ptr;
  printf("[test] Response received: %llu bytes\n", (unsigned long long)response->bodyLen);
  fflush(stdout);

  // Verify "OK" response
  if (response->bodyLen != 2 || memcmp(response->body, "OK", 2) != 0) {
    printf("[test] ABOUT TO FAIL: bodyLen=%llu\n", (unsigned long long)response->bodyLen);
    fflush(stdout);
    VALK_FAIL("Expected 'OK' response, got: %.*s", (int)response->bodyLen,
              (char *)response->body);
  } else {
    printf("[test] SUCCESS: Small response verified\n");
    fflush(stdout);
  }

  cleanup_test_context(&ctx);

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // Add tests in order of increasing size/complexity
  valk_testsuite_add_test(suite, "test_response_small", test_response_small);
  valk_testsuite_add_test(suite, "test_response_2mb", test_response_2mb);
  valk_testsuite_add_test(suite, "test_response_10mb", test_response_10mb);
  valk_testsuite_add_test(suite, "test_response_50mb", test_response_50mb);
  valk_testsuite_add_test(suite, "test_multiple_large_responses", test_multiple_large_responses);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

// Callback implementations (required by test_networking.h)
void cb_onConnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
}

void cb_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  __atomic_fetch_add(&handler->disconnectedCount, 1, __ATOMIC_RELAXED);
}

void cb_onHeader(void *arg, valk_aio_handle_t *conn, u64 stream, char *name,
                 char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

void cb_onBody(void *arg, valk_aio_handle_t *conn, u64 stream, u8 flags,
               valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}
