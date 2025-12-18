// test_large_response.c
// Regression tests for large HTTP response handling
// Tests Issue 1 (16KB data loss on EOF) and Issue 2 (pointer arithmetic crash)
// These tests are parameterized to support testing various response sizes

#include "test_networking.h"

#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "aio.h"
#include "collections.h"
#include "common.h"
#include "concurrency.h"
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
  valk_gc_malloc_heap_t *gc_heap;
  valk_mem_allocator_t *saved_alloc;
  valk_lenv_t *env;
  valk_lval_t *handler_fn;
  valk_aio_system_t *sys;
  valk_future *fserv;
  valk_arc_box *server;
  valk_future *fclient;
  valk_arc_box *clientBox;
  valk_aio_http2_client *client;
  int port;
} test_context_t;

// Initialize test context with Lisp handler
static bool init_test_context(test_context_t *ctx, VALK_TEST_ARGS(), int port) {
  ctx->port = port;

  // Initialize GC heap for Lisp evaluation
  size_t const GC_THRESHOLD_BYTES = 256 * 1024 * 1024;  // 256 MiB for large responses
  ctx->gc_heap = valk_gc_malloc_heap_init(GC_THRESHOLD_BYTES, 0);
  ctx->saved_alloc = valk_thread_ctx.allocator;
  valk_thread_ctx.allocator = (void *)ctx->gc_heap;
  valk_thread_ctx.heap = ctx->gc_heap;

  // Load prelude
  valk_lval_t *prelude_ast = valk_parse_file("src/prelude.valk");
  if (!prelude_ast || LVAL_TYPE(prelude_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse prelude: %s",
              prelude_ast ? prelude_ast->str : "NULL");
    return false;
  }

  ctx->env = valk_lenv_empty();
  valk_lenv_builtins(ctx->env);

  while (valk_lval_list_count(prelude_ast)) {
    valk_lval_t *x = valk_lval_eval(ctx->env, valk_lval_pop(prelude_ast, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      VALK_FAIL("Prelude evaluation failed: %s", x->str);
      return false;
    }
  }

  // Load the large response handler
  valk_lval_t *handler_ast = valk_parse_file("test/test_large_response_handler.valk");
  if (!handler_ast || LVAL_TYPE(handler_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse handler: %s",
              handler_ast ? handler_ast->str : "NULL");
    return false;
  }

  ctx->handler_fn = NULL;
  while (valk_lval_list_count(handler_ast)) {
    ctx->handler_fn = valk_lval_eval(ctx->env, valk_lval_pop(handler_ast, 0));
    if (LVAL_TYPE(ctx->handler_fn) == LVAL_ERR) {
      VALK_FAIL("Handler evaluation failed: %s", ctx->handler_fn->str);
      return false;
    }
  }

  if (!ctx->handler_fn || LVAL_TYPE(ctx->handler_fn) != LVAL_FUN) {
    VALK_FAIL("Handler is not a function");
    return false;
  }

  // Switch back to malloc allocator before AIO calls
  valk_thread_ctx.allocator = ctx->saved_alloc;

  // Start AIO system and server
  ctx->sys = valk_aio_start();

  char port_str[16];
  snprintf(port_str, sizeof(port_str), "%d", port);

  ctx->fserv = valk_aio_http2_listen(
      ctx->sys, "0.0.0.0", port, "build/server.key", "build/server.crt",
      NULL, ctx->handler_fn);

  ctx->server = valk_future_await(ctx->fserv);
  if (ctx->server->type != VALK_SUC) {
    VALK_FAIL("Failed to start server: %s", (char *)ctx->server->item);
    return false;
  }

  // Connect client
  ctx->fclient = valk_aio_http2_connect(ctx->sys, "127.0.0.1", port, "");
  ctx->clientBox = valk_future_await(ctx->fclient);

  if (ctx->clientBox->type != VALK_SUC) {
    VALK_FAIL("Failed to connect client: %s", (char *)ctx->clientBox->item);
    return false;
  }

  ctx->client = ctx->clientBox->item;
  return true;
}

// Cleanup test context
// Note: valk_future_await does NOT retain the result - the future owns it.
// So we only release the futures, not the boxes they contain.
static void cleanup_test_context(test_context_t *ctx) {
  if (ctx->fclient) valk_arc_release(ctx->fclient);
  if (ctx->fserv) valk_arc_release(ctx->fserv);
  if (ctx->sys) {
    valk_aio_stop(ctx->sys);
    valk_aio_wait_for_shutdown(ctx->sys);
  }
  if (ctx->gc_heap) {
    valk_gc_malloc_set_root(ctx->gc_heap, NULL);
    valk_gc_malloc_collect(ctx->gc_heap, NULL);
    valk_gc_malloc_heap_destroy(ctx->gc_heap);
  }
}

// Parameterized test for large response handling
// Returns true if test passed, false otherwise
static bool test_large_response_size(test_context_t *ctx, const char *path,
                                     size_t expected_size, VALK_TEST_ARGS()) {
  // Build request
  uint8_t req_buf[sizeof(valk_mem_arena_t) + 4096];
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
    req->path = path;
    req->body = (uint8_t *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  printf("[test] Requesting %s (expecting %zu bytes)...\n", path, expected_size);

  valk_future *fres = valk_aio_http2_request_send(req, ctx->client);
  valk_arc_box *res = valk_future_await(fres);

  if (res->type != VALK_SUC) {
    VALK_FAIL("Request to %s failed: %s", path, (char *)res->item);
    // Note: don't release res - future owns it
    valk_arc_release(fres);
    return false;
  }

  valk_http2_response_t *response = res->item;
  printf("[test] Response received: %zu bytes (expected: %zu)\n",
         response->bodyLen, expected_size);

  // Verify response size - this is the critical regression test for Issue 1
  if (response->bodyLen != expected_size) {
    ssize_t diff = (ssize_t)response->bodyLen - (ssize_t)expected_size;
    VALK_FAIL("Size mismatch for %s: expected %zu bytes, got %zu bytes (diff: %zd)",
              path, expected_size, response->bodyLen, diff);
    valk_arc_release(fres);
    return false;
  }

  // Verify content pattern (spot check first 64 bytes and last 64 bytes)
  if (response->bodyLen >= 64) {
    if (memcmp(response->body, EXPECTED_PATTERN, 64) != 0) {
      VALK_FAIL("Content mismatch at start of response for %s", path);
      valk_arc_release(fres);
      return false;
    }
    // Check last 64 bytes to catch truncation issues
    size_t end_offset = response->bodyLen - 64;
    if (memcmp((char *)response->body + end_offset, EXPECTED_PATTERN, 64) != 0) {
      VALK_FAIL("Content mismatch at end of response for %s (offset %zu)", path, end_offset);
      valk_arc_release(fres);
      return false;
    }
  }

  printf("[test] SUCCESS: %s response verified (%zu bytes)\n", path, expected_size);

  // Note: don't release res - future owns it
  valk_arc_release(fres);
  return true;
}

// Test 2MB response - smallest test to catch 16KB data loss
void test_response_2mb(VALK_TEST_ARGS()) {
  VALK_TEST();

  test_context_t ctx = {0};
  if (!init_test_context(&ctx, _suite, _result, 6971)) {
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
  if (!init_test_context(&ctx, _suite, _result, 6972)) {
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
  if (!init_test_context(&ctx, _suite, _result, 6973)) {
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
  if (!init_test_context(&ctx, _suite, _result, 6974)) {
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
  if (!init_test_context(&ctx, _suite, _result, 6975)) {
    cleanup_test_context(&ctx);
    return;
  }

  // Build request for /health endpoint (small response)
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
    req->path = "/health";
    req->body = (uint8_t *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  printf("[test] Requesting /health (small response)...\n");

  valk_future *fres = valk_aio_http2_request_send(req, ctx.client);
  valk_arc_box *res = valk_future_await(fres);

  if (res->type != VALK_SUC) {
    VALK_FAIL("Request to /health failed: %s", (char *)res->item);
    valk_arc_release(fres);
    cleanup_test_context(&ctx);
    return;
  }

  valk_http2_response_t *response = res->item;
  printf("[test] Response received: %zu bytes\n", response->bodyLen);

  // Verify "OK" response
  if (response->bodyLen != 2 || memcmp(response->body, "OK", 2) != 0) {
    VALK_FAIL("Expected 'OK' response, got: %.*s", (int)response->bodyLen,
              (char *)response->body);
  } else {
    printf("[test] SUCCESS: Small response verified\n");
  }

  // Note: don't release res - future owns it
  valk_arc_release(fres);
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

void cb_onHeader(void *arg, valk_aio_handle_t *conn, size_t stream, char *name,
                 char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

void cb_onBody(void *arg, valk_aio_handle_t *conn, size_t stream, uint8_t flags,
               valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}
