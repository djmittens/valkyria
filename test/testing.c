#include "testing.h"

#include <inttypes.h>
#include <poll.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#include "collections.h"
#include "common.h"
#include "memory.h"

#define SEC_TO_MS(sec) ((sec) * 1000)
#define SEC_TO_US(sec) ((sec) * 1000000)
#define SEC_TO_NS(sec) ((sec) * 1000000000)

#define NS_TO_SEC(ns) ((ns) / 1000000000)
#define NS_TO_MS(ns) ((ns) / 1000000)
#define NS_TO_US(ns) ((ns) / 1000)

#ifndef VALK_REPORT_WIDTH
#define VALK_REPORT_WIDTH 100
#endif
const char *DOT_FILL =
    ".........................................................................."
    ".........................................................................."
    ".........................................................................."
    ".........................................................................."
    "....";

valk_test_suite_t *valk_testsuite_empty(const char *filename) {
  valk_test_suite_t *res = malloc(sizeof(valk_test_suite_t));
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(res, 0, sizeof(valk_test_suite_t));
  res->filename = strdup(filename);
  da_init(&res->tests);
  da_init(&res->fixtures);
  da_init(&res->results);

  return res;
}

void valk_testsuite_free(valk_test_suite_t *suite) {
  for (size_t i = 0; i < suite->tests.count; i++) {
    free(suite->tests.items[i].name);
    da_free(&suite->tests.items[i].labels);
  }
  free(suite->tests.items);

  for (size_t i = 0; i < suite->fixtures.count; i++) {
    free(suite->fixtures.items[i].name);
    suite->fixtures.items[i].free(suite->fixtures.items[i].value);
  }

  free(suite->fixtures.items);

  for (size_t i = 0; i < suite->results.count; i++) {
    if (suite->results.items[i].type == VALK_TEST_FAIL) {
      free(suite->results.items[i].error);
    }
  }
  free(suite->results.items);

  free(suite->filename);

  free(suite);
}

size_t valk_testsuite_add_test(valk_test_suite_t *suite, const char *name,
                               valk_test_f *func) {
  valk_test_t test = {.name = strdup(name), .func = func};
  da_init(&test.labels);
  da_add(&suite->tests, test);

  return suite->tests.count;
}

valk_test_result_t *valk_testsuite_new_result(valk_test_suite_t *suite,
                                              const char *testName) {
  valk_test_result_t res;

  for (size_t i = 0; i < suite->tests.count; ++i) {
    if (strcmp(suite->tests.items[i].name, testName) == 0) {
      res.testOffset = i;
      res.type = VALK_TEST_UNDEFINED;
      da_add(&suite->results, res);
      return &suite->results.items[suite->results.count - 1];
    }
  }

  return nullptr;
}

int valk_test_fork(valk_test_t *self, valk_test_suite_t *suite,
                   struct pollfd fds[2]) {
  int pout[2], perr[2];
  pipe(pout);
  pipe(perr);
  valk_test_result_t res = {0};
  pid_t pid = fork();
  if (pid == 0) {
    // child
    dup2(pout[1], STDOUT_FILENO);
    dup2(perr[1], STDERR_FILENO);

    // route all the stuff
    close(pout[0]);
    close(perr[0]);
    close(pout[1]);
    close(perr[1]);

    printf("🏃 Running: %s\n", self->name);
    self->func(&suite->results.items[0]);
    exit(0);
  }

  // parent
  // we only read
  close(pout[1]);
  close(perr[1]);

  fds[0].fd = pout[0];
  fds[0].events = POLLIN;
  fds[1].fd = perr[0];
  fds[1].events = POLLIN;
  return pid;
}

int valk_testsuite_run(valk_test_suite_t *suite) {
  valk_ring_t *bout = valk_mem_alloc(sizeof(valk_ring_t) + 64 * 10);
  valk_ring_t *berr = valk_mem_alloc(sizeof(valk_ring_t) + 64 * 10);
  for (size_t i = 0; i < suite->tests.count; i++) {
    struct pollfd fds[2];
    int pid = valk_test_fork(&suite->tests.items[i], suite, fds);

    valk_ring_init(bout, 64 * 10);
    valk_ring_init(berr, 64 * 10);
    while (1) {
      int r = poll(fds, 2, -1);

      if (r <= 0) continue;
      uint8_t buf[256];

      if (fds[0].revents & POLLIN) {
        ssize_t n = read(fds[0].fd, buf, sizeof buf);
        if (n > 0) {
          valk_ring_append(bout, buf, (size_t)n);
        }
      }
      if (fds[1].revents & POLLIN) {
        ssize_t n = read(fds[1].fd, buf, sizeof buf);
        if (n > 0) {
          valk_ring_append(bout, buf, (size_t)n);
        }
      }
      if (fds[0].revents & POLLHUP && fds[1].revents & POLLHUP) {
        break;
      }
    }

    close(fds[1].fd);
    close(fds[1].fd);

    int wstatus;
    waitpid(pid, &wstatus, 0);
    if (WIFEXITED(wstatus)) {
      if (WEXITSTATUS(wstatus)) {
        printf("STDOUT ----- \n");
        valk_ring_print(bout, stdout);
        printf("STDERR ----- \n");
        valk_ring_print(berr, stderr);
      }
      printf("SUCCESS\n");

    } else if (WIFSIGNALED(wstatus)) {
      printf("STDOUT ----- \n");
      valk_ring_print(bout, stdout);
      printf("STDERR ----- \n");
      valk_ring_print(berr, stderr);
      printf("FAILURE %d\n", WTERMSIG(wstatus));
    }
  }

  // for (size_t i = 0; i < suite->results.count; i++) {
  //   valk_test_result_t *result = &suite->results.items[i];
  //   if (result->type != VALK_TEST_PASS) {
  //     return 1;
  //   }
  // }

  valk_mem_free(bout);
  valk_mem_free(berr);
  return 0;
}

void valk_testsuite_print(valk_test_suite_t *suite) {
  printf("[%zu/%zu] %s Suite Results: \n", suite->results.count,
         suite->tests.count, suite->filename);
  for (size_t i = 0; i < suite->results.count; i++) {
    valk_test_result_t *result = &suite->results.items[i];
    valk_test_t *test = &suite->tests.items[result->testOffset];
    char *precision;
    switch (result->timePrecision) {
      case VALK_MILLIS:
        precision = "ms";
        break;
      case VALK_MICROS:
        precision = "µs";
        break;
      case VALK_NANOS:
        precision = "ns";
        break;
    }

    int len = VALK_REPORT_WIDTH - strlen(test->name);

    switch (result->type) {
      case VALK_TEST_UNDEFINED: {
        printf("%s%.*s  UNDEFINED\n", test->name, len, DOT_FILL);
        break;
      }
      case VALK_TEST_PASS:
        printf("✅ %s%.*s  PASS : in %" PRIu64 "(%s)\n", test->name, len,
               DOT_FILL, (result->stopTime - result->startTime), precision);
        break;
      case VALK_TEST_FAIL:
        printf("🐞 %s%.*s  FAIL : in %" PRIu64 "(%s)\n", test->name, len,
               DOT_FILL, (result->stopTime - result->startTime), precision);
        printf("ERROR\n");
        break;
    }
  }
}

void valk_testsuite_fixture_add(valk_test_suite_t *suite, const char *name,
                                void *value, _fixture_copy_f *copyFunc,
                                _fixture_free_f *freeFunc) {
  valk_test_fixture_t res = {
      .value = value, .copy = copyFunc, .free = freeFunc, .name = strdup(name)};
  da_add(&suite->fixtures, res);
}

void *valk_testsuite_fixture_get(valk_test_suite_t *suite, const char *name) {
  for (size_t i = 0; i < suite->fixtures.count; i++) {
    if (strcmp(suite->fixtures.items[i].name, name) == 0) {
      return suite->fixtures.items[i].copy(suite->fixtures.items[i].value);
    }
  }
  return NULL;
}

long valk_get_nanos(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return SEC_TO_NS(ts.tv_sec) + ts.tv_nsec;
}

long valk_get_millis(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return SEC_TO_MS(ts.tv_sec) + NS_TO_MS(ts.tv_nsec);
}

long valk_get_micros(void) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  return SEC_TO_US(ts.tv_sec) + NS_TO_US(ts.tv_nsec);
}

long valk_get_time(valk_time_precision_e p) {
  switch (p) {
    case VALK_MILLIS:
      return valk_get_millis();
    case VALK_MICROS:
      return valk_get_micros();
    case VALK_NANOS:
      return valk_get_nanos();
  }
}
