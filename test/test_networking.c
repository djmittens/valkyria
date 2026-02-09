#include "test_networking.h"

#include <stdlib.h>
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

#define LISP_50MB_RESPONSE_SIZE 52428800

static void __test_thread_onboard(void) {
  if (valk_sys) valk_system_register_thread(valk_sys, NULL, NULL);
}

void test_demo_socket_server(VALK_TEST_ARGS()) {
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);

  valk_lval_t *server = valk_async_handle_await(hserv);
  VALK_ASSERT(LVAL_TYPE(server) != LVAL_ERR, "Failed to start server: %s", server->str);
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server);
  int port = valk_aio_http2_server_get_port(srv);

  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);
  
  VALK_ASSERT(LVAL_TYPE(client_result) != LVAL_ERR, "Error creating client: %s",
              client_result->str);

  valk_aio_http2_client *client = client_result->ref.ptr;

  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res_result = valk_async_handle_await(hres);
  
  VALK_ASSERT(LVAL_TYPE(res_result) != LVAL_ERR, "Request failed: %s", res_result->str);
  
  valk_http2_response_t *response = res_result->ref.ptr;

  if (strcmp((char*)response->body, VALK_HTTP_MOTD) != 0) {
    VALK_FAIL(
        "Did not receive the expected result from the servier Expected: "
        "[%s] Actual: [%s]",
        VALK_HTTP_MOTD, response->body);
  }

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);
  size_t disconnected = __atomic_load_n(&arg.disconnectedCount, __ATOMIC_ACQUIRE);

  VALK_TEST_ASSERT(connected == 1 && disconnected == 1,
                   "Expected a single client connection %zu, %zu", connected,
                   disconnected);

  VALK_PASS();
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
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt", &handler, nullptr);
  valk_lval_t *server2 = valk_async_handle_await(hserv2);
  (void)server2;
  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);
  VALK_PASS();
}

void test_lisp_50mb_response(VALK_TEST_ARGS()) {
  VALK_TEST();

  printf("[test] Initializing runtime...\n");
  fflush(stdout);
  
  valk_system_config_t cfg = valk_system_config_default();
  cfg.gc_heap_size = 1024ULL * 1024 * 1024;
  valk_system_create(&cfg);
  printf("[test] Runtime initialized, heap=%p\n", valk_thread_ctx.heap);
  fflush(stdout);

  printf("[test] Loading prelude...\n");
  fflush(stdout);
  valk_lval_t *prelude_ast = valk_parse_file("src/prelude.valk");
  printf("[test] Parsed prelude: %p\n", (void*)prelude_ast);
  fflush(stdout);
  if (!prelude_ast || LVAL_TYPE(prelude_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse prelude: %s",
              prelude_ast ? prelude_ast->str : "nullptr");
    return;
  }

  printf("[test] Creating env...\n");
  fflush(stdout);
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  valk_thread_ctx.root_env = env;
  valk_gc_set_root(valk_thread_ctx.heap, env);
  printf("[test] Env created, evaluating prelude...\n");
  fflush(stdout);

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

  printf("[test] Loading 50MB handler...\n");
  valk_lval_t *handler_ast = valk_parse_file("test/test_lisp_50mb_handler.valk");
  if (!handler_ast || LVAL_TYPE(handler_ast) == LVAL_ERR) {
    VALK_FAIL("Failed to parse handler: %s",
              handler_ast ? handler_ast->str : "nullptr");
    return;
  }

  valk_lval_t *handler_fn = nullptr;
  while (valk_lval_list_count(handler_ast)) {
    handler_fn = valk_lval_eval(env, valk_lval_pop(handler_ast, 0));
    if (LVAL_TYPE(handler_fn) == LVAL_ERR) {
      VALK_FAIL("Handler evaluation failed: %s", handler_fn->str);
      return;
    }
  }

  if (!handler_fn || LVAL_TYPE(handler_fn) != LVAL_FUN) {
    VALK_FAIL("Handler is not a function, got type: %s",
              handler_fn ? valk_ltype_name(LVAL_TYPE(handler_fn)) : "nullptr");
    return;
  }
  printf("[test] Handler loaded (type=%s)\n", valk_ltype_name(LVAL_TYPE(handler_fn)));

  valk_mem_init_malloc();

  valk_aio_system_config_t aio_cfg = valk_aio_config_large_payload();
  aio_cfg.thread_onboard_fn = __test_thread_onboard;
  valk_aio_system_t *sys = valk_aio_start_with_config(&aio_cfg);

  valk_async_handle_t *hserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 0, "build/server.key", "build/server.crt",
      nullptr, handler_fn);

  valk_lval_t *server = valk_async_handle_await(hserv);
  if (LVAL_TYPE(server) == LVAL_ERR) {
    VALK_FAIL("Failed to start server: %s", server->str);
    valk_aio_stop(sys);
    valk_aio_wait_for_shutdown(sys);
    return;
  }
  valk_aio_http_server *srv = valk_aio_http2_server_from_ref(server);
  int port = valk_aio_http2_server_get_port(srv);
  printf("[test] Server started on port %d\n", port);

  printf("[test] Connecting client...\n");
  valk_async_handle_t *hclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_lval_t *client_result = valk_async_handle_await(hclient);

  if (LVAL_TYPE(client_result) == LVAL_ERR) {
    VALK_FAIL("Failed to connect client: %s", client_result->str);
    valk_aio_stop(sys);
    valk_aio_wait_for_shutdown(sys);
    return;
  }

  valk_aio_http2_client *client = client_result->ref.ptr;
  printf("[test] Client connected\n");

  u8 req_buf[sizeof(valk_mem_arena_t) + 4096];
  memset(req_buf, 0, sizeof(req_buf));
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

  printf("[test] Requesting /big (expecting %d bytes)...\n", LISP_50MB_RESPONSE_SIZE);
  valk_async_handle_t *hres = valk_aio_http2_request_send(req, client);
  valk_lval_t *res_result = valk_async_handle_await(hres);

  if (LVAL_TYPE(res_result) == LVAL_ERR) {
    VALK_FAIL("Request failed: %s", res_result->str);
    valk_aio_stop(sys);
    valk_aio_wait_for_shutdown(sys);
    return;
  }

  valk_http2_response_t *response = res_result->ref.ptr;
  printf("[test] Response received: %llu bytes\n", (unsigned long long)response->bodyLen);

  if (response->bodyLen != LISP_50MB_RESPONSE_SIZE) {
    VALK_FAIL("Expected %d bytes, got %zu bytes",
              LISP_50MB_RESPONSE_SIZE, response->bodyLen);
  } else {
    printf("[test] SUCCESS: Received full 50MB response!\n");
  }

  const char *expected_pattern = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyz./";
  if (response->bodyLen >= 64 && memcmp(response->body, expected_pattern, 64) != 0) {
    VALK_FAIL("Response content mismatch in first 64 bytes");
  }

  valk_aio_stop(sys);
  valk_aio_wait_for_shutdown(sys);

  valk_system_destroy(valk_sys);

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_demo_socket_server",
                          test_demo_socket_server);
  valk_testsuite_add_test(suite, "test_lisp_50mb_response",
                          test_lisp_50mb_response);

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
