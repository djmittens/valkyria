#include "test_networking.h"

#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

#include "aio/aio.h"
#include "aio/aio_async.h"
#include "collections.h"
#include "common.h"
#include "concurrency.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

// Expected response size: 50MB = 52428800 bytes
#define LISP_50MB_RESPONSE_SIZE 52428800

void test_demo_socket_server(VALK_TEST_ARGS()) {
  // valk_lval_t *ast = VALK_FIXTURE("prelude");
  valk_aio_system_t *sys = valk_aio_start();

  VALK_TEST();

  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  u8 buf[sizeof(valk_mem_arena_t) + (24048 + (int)8e6)];
  valk_mem_arena_t *arena = (void *)buf;
  valk_mem_arena_init(arena, (24048 + (int)8e6));
  valk_http2_request_t *req;

  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    req = valk_mem_alloc(sizeof(valk_http2_request_t));
    req->allocator = (void *)arena;
    req->method = "GET";
    req->scheme = "https";
    req->authority = "google.com";
    req->path = "/";
    req->body = (u8 *)"";
    req->bodyLen = 0;

    da_init(&req->headers);
  }

  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);

  valk_lval_t *server = valk_async_handle_await(hserv);
  VALK_ASSERT(LVAL_TYPE(server) != LVAL_ERR, "Failed to start server: %s", server->str);
  int port = valk_aio_http2_server_get_port(server->ref.ptr);

  valk_future *fut = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  printf("Arc count of fut : %lld\n", (long long)fut->refcount);
  valk_arc_box *clientBox = valk_future_await(fut);

  printf("Arc count of fut : %lld\n", (long long)fut->refcount);
  printf("Arc count of box : %lld\n", (long long)clientBox->refcount);

  // valk_arc_release(fut);
  // printf("Arc count of fut : %d\n", fut->refcount);

  valk_arc_release(fut);
  VALK_ASSERT(clientBox->type == VALK_SUC, "Error creating client: %s",
              (char*)clientBox->item);

  valk_aio_http2_client *client = clientBox->item;

  // valk_arc_trace_report_print(fut);

  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);
  valk_http2_response_t *response = res->item;

  if (strcmp((char*)response->body, VALK_HTTP_MOTD) != 0) {
    VALK_FAIL(
        "Did not receive the expected result from the servier Expected: "
        "[%s] Actual: [%s]",
        VALK_HTTP_MOTD, response->body);
  }

  // if (strcmp((char *)response->body, VALK_HTTP_MOTD)) {
  //   VALK_FAIL(
  //       "Did not receive the expected result from the servier Expected: "
  //       "[%s] Actual: [%s]",
  //       VALK_HTTP_MOTD, response);
  // }

  // Cleanup (server is now an LVAL, not arc_box)
  valk_arc_release(fres);

  // Release the response and client boxes
  valk_arc_release(res);
  valk_arc_release(clientBox);

  // TODO(networking): This will close all connections passing the test
  // obviously now need to implement tthe proper shutdown procedures
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  // raise(SIGABRT);

  // these are atomics because, we read it from main thread end write in event
  // loop
  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);

  size_t disconnected =
      __atomic_load_n(&arg.disconnectedCount, __ATOMIC_ACQUIRE);

  // TODO(networking): refactor the codebase to allow this test
  VALK_TEST_ASSERT(connected == 1 && disconnected == 1,
                   "Expected a single client connection %zu, %zu", connected,
                   disconnected);

  VALK_PASS();

  // All of these are void, after i kill the system.. turns out when everything
  // is with done with slabs, we dont need to free individual shit i will need
  // to uncomment, once i implement graceful shutdown valk_arc_release(fserv);
  // valk_arc_release(server);
  // valk_lval_free(ast);
  // free(response);
}

void test_tcp_client_disconnect(VALK_TEST_ARGS()) {
  valk_aio_system_t *sys = valk_aio_start();
  VALK_TEST();

  valk_srv_state_t arg = {0};
  valk_http2_handler_t handler = {
      .arg = &arg,
      .onConnect = cb_onConnect,
      .onDisconnect = cb_onDisconnect,
      .onHeader = cb_onHeader,
      .onBody = cb_onBody,
  };

  valk_async_handle_t *hserv2 = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_lval_t *server2 = valk_async_handle_await(hserv2);
  (void)server2;
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}

// Test: Lisp handler returning a 50MB response
// This tests the full path through the Lisp machinery:
//   Lisp handler -> response building -> HTTP/2 framing -> SSL -> TCP
void test_lisp_50mb_response(VALK_TEST_ARGS()) {
  VALK_TEST();

  printf("[test] Initializing runtime...\n");
  fflush(stdout);
  
  valk_runtime_config_t cfg = valk_runtime_config_default();
  cfg.gc_heap_size = 1024ULL * 1024 * 1024;  // 1GB for 50MB test
  if (valk_runtime_init(&cfg) != 0) {
    VALK_FAIL("Failed to initialize runtime");
    return;
  }
  printf("[test] Runtime initialized, heap=%p\n", valk_thread_ctx.heap);
  fflush(stdout);

  // Load prelude
  printf("[test] Loading prelude...\n");
  fflush(stdout);
  valk_lval_t *prelude_ast = valk_parse_file("src/prelude.valk");
  printf("[test] Parsed prelude: %p\n", (void*)prelude_ast);
  fflush(stdout);
  if (!prelude_ast || LVAL_TYPE(prelude_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse prelude: %s",
              prelude_ast ? prelude_ast->str : "NULL");
    return;
  }

  printf("[test] Creating env...\n");
  fflush(stdout);
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  valk_thread_ctx.root_env = env;
  valk_gc_malloc_set_root(valk_thread_ctx.heap, env);
  printf("[test] Env created, evaluating prelude...\n");
  fflush(stdout);

  // Evaluate prelude
  int expr_count = 0;
  while (valk_lval_list_count(prelude_ast)) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(prelude_ast, 0));
    expr_count++;
    if (expr_count % 50 == 0) {
      printf("[test] Evaluated %d expressions...\n", expr_count);
      fflush(stdout);
    }
    if (LVAL_TYPE(x) == LVAL_ERR) {
      VALK_FAIL("Prelude evaluation failed: %s", x->str);
      return;
    }
  }
  printf("[test] Prelude loaded (%d expressions)\n", expr_count);

  // Load the 50MB handler
  printf("[test] Loading 50MB handler...\n");
  valk_lval_t *handler_ast = valk_parse_file("test/test_lisp_50mb_handler.valk");
  if (!handler_ast || LVAL_TYPE(handler_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse handler: %s",
              handler_ast ? handler_ast->str : "NULL");
    return;
  }

  // Evaluate handler file - the last expression is the handler lambda
  valk_lval_t *handler_fn = NULL;
  while (valk_lval_list_count(handler_ast)) {
    handler_fn = valk_lval_eval(env, valk_lval_pop(handler_ast, 0));
    if (LVAL_TYPE(handler_fn) == LVAL_ERR) {
      VALK_FAIL("Handler evaluation failed: %s", handler_fn->str);
      return;
    }
  }

  if (!handler_fn || LVAL_TYPE(handler_fn) != LVAL_FUN) {
    VALK_FAIL("Handler is not a function, got type: %s",
              handler_fn ? valk_ltype_name(LVAL_TYPE(handler_fn)) : "NULL");
    return;
  }
  printf("[test] Handler loaded (type=%s)\n", valk_ltype_name(LVAL_TYPE(handler_fn)));

  // Switch to malloc for AIO client operations (arc boxes require thread-safe allocator)
  valk_mem_init_malloc();

  // Start AIO system with thread onboard function for event loop
  valk_aio_system_config_t aio_cfg = valk_aio_config_large_payload();
  aio_cfg.thread_onboard_fn = valk_runtime_get_onboard_fn();
  valk_aio_system_t *sys = valk_aio_start_with_config(&aio_cfg);

  // Start server with Lisp handler on port 0 (OS assigns port)
  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt",
      NULL, handler_fn);  // Pass Lisp handler

  valk_lval_t *server = valk_async_handle_await(hserv);
  if (LVAL_TYPE(server) == LVAL_ERR) {
    VALK_FAIL("Failed to start server: %s", server->str);
    valk_aio_stop(sys);
    valk_aio_wait_for_shutdown(sys);
    return;
  }
  int port = valk_aio_http2_server_get_port(server->ref.ptr);
  printf("[test] Server started on port %d\n", port);

  // Connect client
  printf("[test] Connecting client...\n");
  valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *clientBox = valk_future_await(fclient);

  if (clientBox->type != VALK_SUC) {
    VALK_FAIL("Failed to connect client: %s", (char*)clientBox->item);
    valk_arc_release(fclient);
    valk_aio_stop(sys);
    valk_aio_wait_for_shutdown(sys);
    return;
  }

  valk_aio_http2_client *client = clientBox->item;
  printf("[test] Client connected\n");

  // Build request for /big endpoint
  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
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
    req->path = "/big";
    req->body = (u8 *)"";
    req->bodyLen = 0;
    da_init(&req->headers);
  }

  // Send request and wait for response
  printf("[test] Requesting /big (expecting %d bytes)...\n", LISP_50MB_RESPONSE_SIZE);
  valk_future *fres = valk_aio_http2_request_send(req, client);
  valk_arc_box *res = valk_future_await(fres);

  if (res->type != VALK_SUC) {
    VALK_FAIL("Request failed: %s", (char*)res->item);
    valk_arc_release(fres);
    valk_arc_release(fclient);
    valk_aio_stop(sys);
    valk_aio_wait_for_shutdown(sys);
    return;
  }

  valk_http2_response_t *response = res->item;
  printf("[test] Response received: %llu bytes\n", (unsigned long long)response->bodyLen);

  // Verify response size
  if (response->bodyLen != LISP_50MB_RESPONSE_SIZE) {
    VALK_FAIL("Expected %d bytes, got %zu bytes",
              LISP_50MB_RESPONSE_SIZE, response->bodyLen);
  } else {
    printf("[test] SUCCESS: Received full 50MB response!\n");
  }

  // Verify response content (spot check first 64 bytes)
  const char *expected_pattern = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyz./";
  if (response->bodyLen >= 64 && memcmp(response->body, expected_pattern, 64) != 0) {
    VALK_FAIL("Response content mismatch in first 64 bytes");
  }

  // Cleanup
  valk_arc_release(fres);
  valk_arc_release(fclient);

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  // Cleanup runtime
  valk_runtime_shutdown();

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  // Use malloc for now, by default
  // probably should think of how to add this by default everywhere
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_demo_socket_server",
                          test_demo_socket_server);
  valk_testsuite_add_test(suite, "test_lisp_50mb_response",
                          test_lisp_50mb_response);

  // load fixtures
  // valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  // valk_lenv_t *env = valk_lenv_empty();
  // valk_lenv_builtins(env); // load the builtins
  // valk_lval_t *r = valk_lval_eval(env, valk_lval_copy(ast));
  // valk_lval_free(r);
  //
  // valk_testsuite_fixture_add(suite, "prelude", ast,
  //                            (_fixture_copy_f *)valk_lval_copy,
  //                            (_fixture_free_f *)valk_lval_free);
  // valk_testsuite_fixture_add(suite, "env", env,
  //                            (_fixture_copy_f *)valk_lenv_copy,
  //                            (_fixture_free_f *)valk_lenv_free);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

void cb_onConnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;

  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
}

void cb_onDisconnect(void *arg, valk_aio_handle_t *conn) {
  UNUSED(conn);
  valk_srv_state_t *handler = arg;
  printf("HOLLYYEE got called, %d\n", handler->disconnectedCount);
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
