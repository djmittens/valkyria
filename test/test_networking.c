#include "test_networking.h"

#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

#include "aio.h"
#include "collections.h"
#include "common.h"
#include "concurrency.h"
#include "memory.h"
#include "testing.h"

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

  uint8_t buf[sizeof(valk_mem_arena_t) + (24048 + (int)8e6)];
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
    req->body = (uint8_t *)"";
    req->bodyLen = 0;

    da_init(&req->headers);
  }

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 6969, "build/server.key", "build/server.crt", &handler);

  valk_arc_box *server = valk_future_await(fserv);

  valk_future *fut = valk_aio_http2_connect(sys, "127.0.0.1", 6969, "");
  printf("Arc count of fut : %ld\n", fut->refcount);
  valk_arc_box *clientBox = valk_future_await(fut);

  printf("Arc count of fut : %ld\n", fut->refcount);
  printf("Arc count of box : %ld\n", clientBox->refcount);

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

  size_t count = __atomic_load_n(&server->refcount, __ATOMIC_ACQUIRE);
  printf("Da fuck %ld\n", count);
  valk_arc_release(server);

  // valk_arc_trace_report_print(fserv);
  valk_arc_release(fserv);
  valk_arc_release(fres);

  // TODO(networking): This will close all connections passing the test
  // obviously now need to implement tthe proper shutdown procedures
  valk_aio_stop(sys);

  // raise(SIGABRT);

  // these are atomics because, we read it from main thread end write in event
  // loop
  size_t connected = __atomic_load_n(&arg.connectedCount, __ATOMIC_ACQUIRE);

  size_t disconnected =
      __atomic_load_n(&arg.disconnectedCount, __ATOMIC_ACQUIRE);

  // TODO(networking): refactor the codebase to allow this test
  VALK_TEST_ASSERT(connected == disconnected == 1,
                   "Expected a single client connection %d, %d", connected,
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

  valk_arc_box *res = valk_future_await(valk_aio_http2_listen(
      sys, "0.0.0.0", 6969, "build/server.key", "build/server.crt", &handler));
  valk_arc_release(res);
  VALK_PASS();
  valk_aio_stop(sys);
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

void cb_onConnect(void *arg, valk_aio_http_conn *) {
  valk_srv_state_t *handler = arg;

  __atomic_fetch_add(&handler->connectedCount, 1, __ATOMIC_RELAXED);
}

void cb_onDisconnect(void *arg, valk_aio_http_conn *) {
  valk_srv_state_t *handler = arg;
  printf("HOLLYYEE got called, %d\n", handler->disconnectedCount);
  __atomic_fetch_add(&handler->disconnectedCount, 1, __ATOMIC_RELAXED);
}

void cb_onHeader(void *arg, valk_aio_http_conn *conn, size_t stream, char *name,
                 char *value) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(name);
  UNUSED(value);
}

void cb_onBody(void *arg, valk_aio_http_conn *conn, size_t stream, uint8_t flags,
               valk_buffer_t *buf) {
  UNUSED(arg);
  UNUSED(conn);
  UNUSED(stream);
  UNUSED(flags);
  UNUSED(buf);
}
