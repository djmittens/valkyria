#include "test_networking.h"

#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

#include "aio.h"
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

  valk_future *fserv = valk_aio_http2_listen(
      sys, "0.0.0.0", 6969, "build/server.key", "build/server.crt", &handler);

  valk_arc_box *server = valk_future_await(fserv);

  char *response = valk_client_demo(sys, "127.0.0.1", "8080");

  if (strcmp(response, VALK_HTTP_MOTD)) {
    VALK_FAIL(
        "Did not receive the expected result from the servier Expected: "
        "[%s] Actual: [%s]",
        VALK_HTTP_MOTD, response);
  }

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

  // valk_arc_release(fserv);
  valk_arc_release(server);
  valk_aio_stop(sys);
  // valk_lval_free(ast);
  free(response);
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

void cb_onHeader(void *arg, valk_aio_http_conn *, size_t stream, char *name,
                 char *value) {}
void cb_onBody(void *arg, valk_aio_http_conn *, size_t stream, uint8_t flags,
               valk_buffer_t *buf) {}
