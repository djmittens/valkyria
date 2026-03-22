#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "aio/aio.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

static valk_lenv_t *create_test_env(void) {
  valk_system_create(nullptr);
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  valk_thread_ctx.root_env = env;
  valk_gc_set_root(valk_thread_ctx.heap, env);
  return env;
}

static valk_lval_t *eval_str(valk_lenv_t *env, const char *code) {
  int pos = 0;
  valk_lval_t *parsed = valk_lval_read_expr(&pos, code);
  if (LVAL_TYPE(parsed) == LVAL_ERR) return parsed;
  return valk_lval_eval(env, parsed);
}

static void test_pipe_stdin_open_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  valk_lval_t *r = eval_str(env, "(pipe/stdin-open sys)");
  ASSERT_LVAL_TYPE(r, LVAL_REF);

  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_pipe_stdout_open_write(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(1);
  dup2(pfd[1], 1);
  close(pfd[1]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {out} (pipe/stdout-open sys))");
  eval_str(env, "(pipe/write out \"hello pipe\")");
  eval_str(env, "(aio/await (aio/sleep sys 100))");

  char buf[256] = {0};
  int flags = fcntl(pfd[0], F_GETFL);
  fcntl(pfd[0], F_SETFL, flags | O_NONBLOCK);
  ssize_t n = read(pfd[0], buf, sizeof(buf) - 1);
  VALK_TEST_ASSERT(n > 0, "should have read data from pipe");
  if (n > 0) {
    buf[n] = '\0';
    ASSERT_STR_EQ(buf, "hello pipe");
  }

  eval_str(env, "(pipe/close out)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  dup2(saved, 1);
  close(saved);
  close(pfd[0]);
  VALK_PASS();
}

static void test_pipe_on_data_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {got-data} 0)");
  eval_str(env, "(pipe/on-data in (\\ {chunk} {(def {got-data} 1)}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  write(pfd[1], "test", 4);

  eval_str(env, "(aio/await (aio/sleep sys 200))");

  valk_lval_t *got = eval_str(env, "(+ got-data 0)");
  ASSERT_LVAL_NUM(got, 1);

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_lsp_reader_single_message(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {msg-count} 0)");
  eval_str(env, "(= {last-body} \"\")");
  eval_str(env, "(pipe/lsp-reader in (\\ {body} {(do "
                "(def {msg-count} (+ msg-count 1)) "
                "(def {last-body} body))}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  const char *msg = "Content-Length: 14\r\n\r\n{\"id\":1,\"m\":0}";
  write(pfd[1], msg, strlen(msg));

  eval_str(env, "(aio/await (aio/sleep sys 200))");

  valk_lval_t *count = eval_str(env, "(+ msg-count 0)");
  ASSERT_LVAL_NUM(count, 1);

  valk_lval_t *body = eval_str(env, "(str last-body \"\")");
  ASSERT_LVAL_TYPE(body, LVAL_STR);
  ASSERT_STR_EQ(body->str, "{\"id\":1,\"m\":0}");

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_lsp_reader_multiple_messages(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {msg-count} 0)");
  eval_str(env, "(pipe/lsp-reader in (\\ {body} {(def {msg-count} (+ msg-count 1))}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  const char *msg1 = "Content-Length: 3\r\n\r\nabc";
  const char *msg2 = "Content-Length: 5\r\n\r\nhello";
  write(pfd[1], msg1, strlen(msg1));
  write(pfd[1], msg2, strlen(msg2));

  eval_str(env, "(aio/await (aio/sleep sys 200))");

  valk_lval_t *count = eval_str(env, "(+ msg-count 0)");
  ASSERT_LVAL_NUM(count, 2);

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_lsp_reader_partial_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {msg-count} 0)");
  eval_str(env, "(pipe/lsp-reader in (\\ {body} {(def {msg-count} (+ msg-count 1))}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  write(pfd[1], "Content-Le", 10);
  usleep(20000);
  write(pfd[1], "ngth: 5\r\n\r\n", 11);
  usleep(20000);
  write(pfd[1], "hel", 3);
  usleep(20000);
  write(pfd[1], "lo", 2);

  eval_str(env, "(aio/await (aio/sleep sys 300))");

  valk_lval_t *count = eval_str(env, "(+ msg-count 0)");
  ASSERT_LVAL_NUM(count, 1);

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_lsp_reader_no_content_length(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {msg-count} 0)");
  eval_str(env, "(pipe/lsp-reader in (\\ {body} {(def {msg-count} (+ msg-count 1))}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  const char *bad = "X-Header: foo\r\n\r\n";
  const char *good = "Content-Length: 2\r\n\r\nok";
  write(pfd[1], bad, strlen(bad));
  write(pfd[1], good, strlen(good));

  eval_str(env, "(aio/await (aio/sleep sys 200))");

  valk_lval_t *count = eval_str(env, "(+ msg-count 0)");
  ASSERT_LVAL_NUM(count, 1);

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_lsp_reader_zero_content_length(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {msg-count} 0)");
  eval_str(env, "(pipe/lsp-reader in (\\ {body} {(def {msg-count} (+ msg-count 1))}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  const char *zero_len = "Content-Length: 0\r\n\r\n";
  const char *valid = "Content-Length: 4\r\n\r\ngood";
  write(pfd[1], zero_len, strlen(zero_len));
  write(pfd[1], valid, strlen(valid));

  eval_str(env, "(aio/await (aio/sleep sys 200))");

  valk_lval_t *count = eval_str(env, "(+ msg-count 0)");
  ASSERT_LVAL_NUM(count, 1);

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_aio_dispatch_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start (list :num-threads 2))))");
  eval_str(env, "(= {d-result} 0)");
  eval_str(env, "(aio/dispatch sys (\\ {x} {(+ x 42)}) 100 "
                "(\\ {r} {(def {d-result} r)}))");

  eval_str(env, "(aio/await (aio/sleep sys 300))");

  valk_lval_t *result = eval_str(env, "(+ d-result 0)");
  ASSERT_LVAL_NUM(result, 142);

  eval_str(env, "(aio/stop sys)");
  VALK_PASS();
}

static void test_aio_dispatch_single_loop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start (list :num-threads 1))))");
  eval_str(env, "(= {d-result} 0)");
  eval_str(env, "(aio/dispatch sys (\\ {x} {(* x 2)}) 21 "
                "(\\ {r} {(def {d-result} r)}))");

  eval_str(env, "(aio/await (aio/sleep sys 300))");

  valk_lval_t *result = eval_str(env, "(+ d-result 0)");
  ASSERT_LVAL_NUM(result, 42);

  eval_str(env, "(aio/stop sys)");
  VALK_PASS();
}

static void test_pipe_arg_validation(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");

  valk_lval_t *r;

  r = eval_str(env, "(pipe/stdin-open 42)");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(pipe/stdout-open 42)");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(pipe/write 42 \"data\")");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(pipe/on-data 42 (\\ {x} {x}))");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(pipe/close 42)");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(pipe/lsp-reader 42 (\\ {x} {x}))");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(aio/dispatch 42 (\\ {x} {x}) 1 (\\ {r} {r}))");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(aio/dispatch sys 42 1 (\\ {r} {r}))");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(aio/dispatch sys (\\ {x} {x}) 1 42)");
  ASSERT_LVAL_ERROR(r);

  eval_str(env, "(aio/stop sys)");
  VALK_PASS();
}

static void test_pipe_write_type_validation(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");

  valk_lval_t *r = eval_str(env, "(pipe/write in 42)");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(pipe/on-data in 42)");
  ASSERT_LVAL_ERROR(r);

  r = eval_str(env, "(pipe/lsp-reader in 42)");
  ASSERT_LVAL_ERROR(r);

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_lsp_reader_large_message(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {body-len} 0)");
  eval_str(env, "(pipe/lsp-reader in (\\ {body} {(def {body-len} (len body))}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  sz body_size = 8192;
  char *body = malloc(body_size);
  memset(body, 'x', body_size);

  char header[64];
  int hlen = snprintf(header, sizeof(header), "Content-Length: %zu\r\n\r\n", body_size);
  write(pfd[1], header, hlen);

  sz written = 0;
  while (written < body_size) {
    sz chunk = body_size - written;
    if (chunk > 2048) chunk = 2048;
    write(pfd[1], body + written, chunk);
    written += chunk;
    usleep(10000);
  }
  free(body);

  eval_str(env, "(aio/await (aio/sleep sys 500))");

  valk_lval_t *blen = eval_str(env, "(+ body-len 0)");
  ASSERT_LVAL_NUM(blen, (i64)body_size);

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_pipe_on_data_no_callback(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  write(pfd[1], "data-no-cb", 10);
  eval_str(env, "(aio/await (aio/sleep sys 100))");

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_lsp_reader_handler_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(pipe/lsp-reader in (\\ {body} {(err \"handler error\")}))");

  eval_str(env, "(aio/await (aio/sleep sys 50))");

  const char *msg = "Content-Length: 2\r\n\r\nok";
  write(pfd[1], msg, strlen(msg));

  eval_str(env, "(aio/await (aio/sleep sys 200))");

  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 50))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

static void test_dispatch_callback_error(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start (list :num-threads 2))))");
  eval_str(env, "(aio/dispatch sys (\\ {x} {x}) 1 "
                "(\\ {r} {(err \"cb error\")}))");

  eval_str(env, "(aio/await (aio/sleep sys 300))");

  eval_str(env, "(aio/stop sys)");
  VALK_PASS();
}

static void test_pipe_close_then_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pfd[2];
  pipe(pfd);
  int saved = dup(0);
  dup2(pfd[0], 0);
  close(pfd[0]);

  valk_lenv_t *env = create_test_env();
  eval_str(env, "(= {sys} (aio/await (aio/start)))");
  eval_str(env, "(= {in} (pipe/stdin-open sys))");
  eval_str(env, "(= {cb-count} 0)");
  eval_str(env, "(pipe/on-data in (\\ {chunk} {(def {cb-count} (+ cb-count 1))}))");
  eval_str(env, "(pipe/close in)");
  eval_str(env, "(aio/await (aio/sleep sys 100))");
  eval_str(env, "(aio/stop sys)");

  close(pfd[1]);
  dup2(saved, 0);
  close(saved);
  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_pipe_stdin_open_close", test_pipe_stdin_open_close);
  valk_testsuite_add_test(suite, "test_pipe_stdout_open_write", test_pipe_stdout_open_write);
  valk_testsuite_add_test(suite, "test_pipe_on_data_callback", test_pipe_on_data_callback);
  valk_testsuite_add_test(suite, "test_lsp_reader_single_message", test_lsp_reader_single_message);
  valk_testsuite_add_test(suite, "test_lsp_reader_multiple_messages", test_lsp_reader_multiple_messages);
  valk_testsuite_add_test(suite, "test_lsp_reader_partial_data", test_lsp_reader_partial_data);
  valk_testsuite_add_test(suite, "test_lsp_reader_no_content_length", test_lsp_reader_no_content_length);
  valk_testsuite_add_test(suite, "test_lsp_reader_zero_content_length", test_lsp_reader_zero_content_length);
  valk_testsuite_add_test(suite, "test_aio_dispatch_basic", test_aio_dispatch_basic);
  valk_testsuite_add_test(suite, "test_aio_dispatch_single_loop", test_aio_dispatch_single_loop);
  valk_testsuite_add_test(suite, "test_lsp_reader_large_message", test_lsp_reader_large_message);
  valk_testsuite_add_test(suite, "test_pipe_on_data_no_callback", test_pipe_on_data_no_callback);
  valk_testsuite_add_test(suite, "test_lsp_reader_handler_error", test_lsp_reader_handler_error);
  valk_testsuite_add_test(suite, "test_dispatch_callback_error", test_dispatch_callback_error);
  valk_testsuite_add_test(suite, "test_pipe_close_then_close", test_pipe_close_then_close);
  valk_testsuite_add_test(suite, "test_pipe_arg_validation", test_pipe_arg_validation);
  valk_testsuite_add_test(suite, "test_pipe_write_type_validation", test_pipe_write_type_validation);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
