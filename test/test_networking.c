#include "aio.h"
#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

#include <signal.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>


void handle_sigusr1(int sig)  {

}

void test_demo_socket_server(VALK_TEST_ARGS()) {
  valk_lval_t *ast = VALK_FIXTURE("prelude");
  VALK_TEST();

  struct sigaction sa;
  sa.sa_flags = 0;
  sa.sa_handler = handle_sigusr1;
  sigemptyset(&sa.sa_mask);

  sigaction(SIGUSR1, &sa, NULL);

  pid_t pid;
  pid = fork();
  if (pid < 0) {
    perror("Forky fork failed 😤\n");
  } else if (pid == 0) {
    printf("Starting server\n");
    valk_server_demo();
    exit(0);
  }

  pause();

  char *response = valk_client_demo("127.0.0.1", "8080");
  kill(pid, SIGTERM);
  printf("Waiting for server to die\n");

  int res;
  waitpid(pid, &res, 0);

  if (WIFSIGNALED(res)) {
    printf("Server killed by signal, %d\n", WTERMSIG(res));
  } else if (WIFEXITED(res)) {
    printf("Server exited with code %d\n", WEXITSTATUS(res));
  } else if (WTERMSIG(res)) {
    printf("Server stopped code %d\n", WTERMSIG(res));
  }

  if (strcmp(response, VALK_HTTP_MOTD)) {
    VALK_FAIL("Did not receive the expected result from the servier Expected: "
              "[%s]  Actual: [%s]",
              VALK_HTTP_MOTD, response);
  }
  VALK_PASS();
  valk_lval_free(ast);
  free(response);
}

int get_ctx() { return (size_t)valk_thread_ctx.allocator; }

void test_implicit_arena_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_thread_ctx.allocator = (void *)6969;
  valk_thread_context_t ctx = {.allocator = (void *)-1};
  VALK_WITH_CTX(ctx) {
    // The function gets context we set
    VALK_ASSERT(get_ctx() == -1, "expected some stuff %d", (int)get_ctx());
  }
  // VALK_WITH_CTX reset the context back to original
  VALK_ASSERT(get_ctx() == 6969, "expected some stuff %d", (int)get_ctx());
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
  valk_lenv_builtins(env); // load the builtins
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
