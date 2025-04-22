#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

#include "aio.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

void test_demo_socket_server(VALK_TEST_ARGS()) {
  valk_lval_t *ast = VALK_FIXTURE("prelude");
  valk_aio_system *sys = valk_aio_start();

  VALK_TEST();

  valk_future_await(valk_aio_http2_listen(
      sys, "0.0.0.0", 6969, "build/server.key", "build/server.crt"));
  printf("What the fudge\n");

  char *response = valk_client_demo(sys, "127.0.0.1", "8080");

  if (strcmp(response, VALK_HTTP_MOTD)) {
    VALK_FAIL(
        "Did not receive the expected result from the servier Expected: "
        "[%s]  Actual: [%s]",
        VALK_HTTP_MOTD, response);
  }
  VALK_PASS();
  valk_aio_stop(sys);
  valk_lval_free(ast);
  free(response);
}

void test_implicit_arena_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_mem_allocator_t alloc_old;
  valk_mem_allocator_t alloc_new;

  valk_thread_ctx.allocator = &alloc_old;
  valk_thread_context_t ctx = {.allocator = &alloc_new};
  VALK_WITH_CTX(ctx) {
    // The function gets context we set
    VALK_TEST_ASSERT(valk_thread_ctx.allocator == &alloc_new,
                     "expected some stuff %d", &alloc_new);
  }
  // VALK_WITH_CTX reset the context back to original
  VALK_TEST_ASSERT(valk_thread_ctx.allocator == &alloc_old,
                   "expected some stuff %d", &alloc_old);
  valk_thread_ctx.allocator = nullptr;
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
  valk_testsuite_add_test(suite, "test_implicit_arena_alloc",
                          test_implicit_arena_alloc);

  // load fixtures
  valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);  // load the builtins
  valk_lval_t *r = valk_lval_eval(env, valk_lval_copy(ast));
  valk_lval_free(r);

  valk_testsuite_fixture_add(suite, "prelude", ast,
                             (_fixture_copy_f *)valk_lval_copy,
                             (_fixture_free_f *)valk_lval_free);
  valk_testsuite_fixture_add(suite, "env", env,
                             (_fixture_copy_f *)valk_lenv_copy,
                             (_fixture_free_f *)valk_lenv_free);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
