#define _POSIX_C_SOURCE 200809L
#include "testing.h"
#include "common.h"

#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netdb.h>
#include <unistd.h>
#include <poll.h>

#include "aio.h"
#include "parser.h"

static void __aio_free(void *system) { valk_aio_stop(system); }

static void test_http2_google_script(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Quick network reachability probe to the host/port used by the script.
  // Avoids needing an env var and reports a proper skip.
  {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd >= 0) {
      int flags = fcntl(fd, F_GETFL, 0);
      if (flags != -1) fcntl(fd, F_SETFL, flags | O_NONBLOCK);

      struct addrinfo hints = {0}, *res = NULL;
      hints.ai_family = AF_INET;
      hints.ai_socktype = SOCK_STREAM;
      int gai = getaddrinfo("google.com", "443", &hints, &res);
      if (gai == 0 && res) {
        int rc = connect(fd, res->ai_addr, res->ai_addrlen);
        if (rc < 0 && errno == EINPROGRESS) {
          struct pollfd p = {.fd = fd, .events = POLLOUT};
          int pr = poll(&p, 1, 500 /* ms */);
          if (pr == 1 && (p.revents & POLLOUT)) {
            int soerr = 0; socklen_t slen = sizeof soerr;
            if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &soerr, &slen) == 0 && soerr == 0) {
              // Reachable
            } else {
              freeaddrinfo(res);
              close(fd);
              VALK_SKIP("network unreachable (SO_ERROR=%d) to google.com:443", soerr);
              return;
            }
          } else {
            freeaddrinfo(res);
            close(fd);
            VALK_SKIP("network probe timeout to google.com:443");
            return;
          }
        } else if (rc == 0) {
          // Immediate connect success
        } else {
          freeaddrinfo(res);
          close(fd);
          VALK_SKIP("network connect failed to google.com:443 (errno=%d)", errno);
          return;
        }
      } else {
        VALK_SKIP("DNS resolution failed for google.com");
        close(fd);
        return;
      }
      freeaddrinfo(res);
      close(fd);
    } else {
      VALK_SKIP("socket() failed for network probe");
      return;
    }
  }

  // Setup language env and builtins
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // Set VALK_MODE to "test" to stub out shutdown
  valk_lenv_put(env, valk_lval_sym("VALK_MODE"), valk_lval_str("test"));

  // Start async runtime and bind into env as in REPL
  valk_aio_system_t *aio = valk_aio_start();
  valk_lenv_put(env, valk_lval_sym("aio"),
                valk_lval_ref("aio_system", aio, __aio_free));

  // Load prelude
  valk_lval_t *prelude = valk_parse_file("src/prelude.valk");
  while (prelude->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(prelude, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      VALK_FAIL("Prelude eval failed");
      return;
    }
  }

  // Evaluate the google HTTP/2 script; any error fails the test
  valk_lval_t *script = valk_parse_file("test/google_http2.valk");
  valk_lval_t *last_result = NULL;
  while (script->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(script, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      VALK_FAIL("Script eval failed");
      return;
    } else {
      valk_lval_println(x);
      last_result = x;
    }
  }

  // Verify shutdown was called with exit code 0
  VALK_TEST_ASSERT(last_result != NULL, "Expected script to produce a result");
  VALK_TEST_ASSERT(LVAL_TYPE(last_result) == LVAL_NUM,
                   "Expected shutdown to return a number");
  VALK_TEST_ASSERT(last_result->num == 0,
                   "Expected shutdown to be called with exit code 0");

  VALK_PASS();
}

static void test_http2_error_handling(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Setup language env and builtins
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // Set VALK_MODE to "test" to stub out shutdown
  valk_lenv_put(env, valk_lval_sym("VALK_MODE"), valk_lval_str("test"));

  // Start async runtime and bind into env
  valk_aio_system_t *aio = valk_aio_start();
  valk_lenv_put(env, valk_lval_sym("aio"),
                valk_lval_ref("aio_system", aio, __aio_free));

  // Load prelude
  valk_lval_t *prelude = valk_parse_file("src/prelude.valk");
  while (prelude->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(prelude, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      VALK_FAIL("Prelude eval failed");
      return;
    }
  }

  // Evaluate the error handling script - we EXPECT this to fail
  valk_lval_t *script = valk_parse_file("test/http2_error_handling.valk");
  int got_expected_error = 0;
  while (script->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(script, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      // We expect an error from the connection failure
      valk_lval_println(x);
      // Check that it's a connection-related error
      if (strstr(x->str, "ERR:") != NULL || strstr(x->str, "connection") != NULL ||
          strstr(x->str, "Connection") != NULL) {
        got_expected_error = 1;
        break;
      } else {
        VALK_FAIL("Got error but not a connection error: %s", x->str);
        return;
      }
    } else {
      valk_lval_println(x);
    }
  }

  // Verify we got the expected error
  VALK_TEST_ASSERT(got_expected_error,
                   "Expected connection error but script succeeded");

  VALK_PASS();
}

static void test_http2_rst_stream_handling(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Quick network reachability check
  {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd >= 0) {
      int flags = fcntl(fd, F_GETFL, 0);
      if (flags != -1) fcntl(fd, F_SETFL, flags | O_NONBLOCK);

      struct addrinfo hints = {0}, *res = NULL;
      hints.ai_family = AF_INET;
      hints.ai_socktype = SOCK_STREAM;
      int gai = getaddrinfo("google.com", "443", &hints, &res);
      if (gai == 0 && res) {
        int rc = connect(fd, res->ai_addr, res->ai_addrlen);
        if (rc < 0 && errno == EINPROGRESS) {
          struct pollfd p = {.fd = fd, .events = POLLOUT};
          int pr = poll(&p, 1, 500);
          if (pr != 1 || !(p.revents & POLLOUT)) {
            freeaddrinfo(res);
            close(fd);
            VALK_SKIP("network unreachable to google.com:443");
            return;
          }
        }
      } else {
        VALK_SKIP("DNS resolution failed for google.com");
        close(fd);
        return;
      }
      freeaddrinfo(res);
      close(fd);
    }
  }

  // Setup language env and builtins
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // Set VALK_MODE to "test"
  valk_lenv_put(env, valk_lval_sym("VALK_MODE"), valk_lval_str("test"));

  // Start async runtime
  valk_aio_system_t *aio = valk_aio_start();
  valk_lenv_put(env, valk_lval_sym("aio"),
                valk_lval_ref("aio_system", aio, __aio_free));

  // Load prelude
  valk_lval_t *prelude = valk_parse_file("src/prelude.valk");
  while (prelude->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(prelude, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      VALK_FAIL("Prelude eval failed");
      return;
    }
  }

  // Evaluate the RST_STREAM handling script
  // This may result in either an error (if server sends RST_STREAM)
  // or success (if server accepts the request)
  valk_lval_t *script = valk_parse_file("test/http2_rst_stream.valk");
  while (script->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(script, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      // If we get an error, it should be an HTTP/2 stream error
      valk_lval_println(x);
      if (strstr(x->str, "HTTP/2 stream error") != NULL ||
          strstr(x->str, "ERR:") != NULL) {
        // This is expected - server rejected with RST_STREAM
        VALK_PASS();
        return;
      } else {
        VALK_FAIL("Got unexpected error: %s", x->str);
        return;
      }
    } else {
      valk_lval_println(x);
    }
  }

  // If we got here without error, server accepted the request
  // This is also valid behavior
  VALK_PASS();
}

static void test_http2_server_client(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Setup language env and builtins
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // Set VALK_MODE to "test" to stub out shutdown
  valk_lenv_put(env, valk_lval_sym("VALK_MODE"), valk_lval_str("test"));

  // Start async runtime
  valk_aio_system_t *aio = valk_aio_start();
  valk_lenv_put(env, valk_lval_sym("aio"),
                valk_lval_ref("aio_system", aio, __aio_free));

  // Load prelude
  valk_lval_t *prelude = valk_parse_file("src/prelude.valk");
  while (prelude->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(prelude, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      VALK_FAIL("Prelude eval failed");
      return;
    }
  }

  // Evaluate the server/client test script
  valk_lval_t *script = valk_parse_file("test/http2_server_client.valk");
  valk_lval_t *last_result = NULL;
  while (script->expr.count) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(script, 0));
    if (LVAL_TYPE(x) == LVAL_ERR) {
      valk_lval_println(x);
      VALK_FAIL("Script eval failed: %s", x->str);
      return;
    } else {
      valk_lval_println(x);
      last_result = x;
    }
  }

  // Verify shutdown was called with exit code 0
  VALK_TEST_ASSERT(last_result != NULL, "Expected script to produce a result");
  VALK_TEST_ASSERT(LVAL_TYPE(last_result) == LVAL_NUM,
                   "Expected shutdown to return a number");
  VALK_TEST_ASSERT(last_result->num == 0,
                   "Expected shutdown to be called with exit code 0");

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "test_http2_google_script",
                          test_http2_google_script);
  valk_testsuite_add_test(suite, "test_http2_error_handling",
                          test_http2_error_handling);
  valk_testsuite_add_test(suite, "test_http2_rst_stream_handling",
                          test_http2_rst_stream_handling);
  valk_testsuite_add_test(suite, "test_http2_server_client",
                          test_http2_server_client);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return res;
}
