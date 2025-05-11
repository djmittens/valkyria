#define _POSIX_C_SOURCE 200809L
#include "testing.h"

#include <inttypes.h>
#include <poll.h>
#include <stdckdint.h>
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

#define VALK_TEST_FORK 1

const char *DOT_FILL =
    ".........................................................................."
    ".........................................................................."
    ".........................................................................."
    ".........................................................................."
    "....";

const char *UND_FILL =
    "__________________________________________________________________________"
    "__________________________________________________________________________"
    "__________________________________________________________________________"
    "__________________________________________________________________________"
    "____";
valk_test_suite_t *valk_testsuite_empty(const char *filename) {
  valk_test_suite_t *res = malloc(sizeof(valk_test_suite_t));
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(res, 0, sizeof(valk_test_suite_t));
  res->filename = strdup(filename);

  da_init(&res->tests);
  da_init(&res->fixtures);

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
    // close(pout[1]);
    // close(perr[1]);
    close(pout[0]);
    close(perr[0]);

    printf("🏃 Running: %s\n", self->name);
    self->func(suite, &self->result);

    uint8_t *p = (void *)&self->result;
    size_t size = sizeof(self->result);

    // write  out the result
    while (size) {
      size_t n = fwrite(p, 1, size, stderr);
      p += n;
      size -= n;
    }

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

void valk_test_fork_await(valk_test_t *test, int pid, struct pollfd fds[2]) {
  while (1) {
    int r = poll(fds, 2, -1);

    if (r <= 0)
      continue;
    uint8_t buf[256];

    if (fds[0].revents & POLLIN) {
      ssize_t n = read(fds[0].fd, buf, sizeof buf);
      if (n > 0) {
        valk_ring_write(test->_stdout, buf, (size_t)n);
      }
    }
    if (fds[1].revents & POLLIN) {
      ssize_t n = read(fds[1].fd, buf, sizeof buf);
      if (n > 0) {
        valk_ring_write(test->_stderr, buf, (size_t)n);
      }
    }
    if (fds[0].revents & POLLHUP && fds[1].revents & POLLHUP) {
      break;
    }
  }

  close(fds[0].fd);
  close(fds[1].fd);

  int wstatus;
  waitpid(pid, &wstatus, 0);
  if (WIFEXITED(wstatus)) {
    //  TODO(networking): Probably should record the exit status at some point
    if (WEXITSTATUS(wstatus)) {
    } else {
    }

    valk_ring_rewind(test->_stderr, sizeof(test->result));
    valk_ring_read(test->_stderr, sizeof(test->result), &test->result);
  } else if (WIFSIGNALED(wstatus)) {
    test->result.type = VALK_TEST_CRSH;
    int sig = WTERMSIG(wstatus);
    char *name = strsignal(sig);

    size_t len = snprintf(nullptr, 0, "Child died because of signal %d(%s)\n",
                          sig, name);
    char buf[++len];

    snprintf(buf, len, "Child died because of signal %d(%s)\n", sig, name);

    valk_ring_write(test->_stderr, (void *)buf, len);
  }
}

int valk_testsuite_run(valk_test_suite_t *suite) {
  static size_t ring_size = 0;
  static valk_slab_t *slab = nullptr;
  if (slab == nullptr) {
    ring_size = valk_next_pow2(642);
    slab = valk_slab_new(sizeof(valk_ring_t) + ring_size, 100);
  }

  for (size_t i = 0; i < suite->tests.count; i++) {
    valk_test_t *test = &suite->tests.items[i];

    test->_stdout = (void *)valk_slab_aquire(slab)->data;
    valk_ring_init(test->_stdout, ring_size);
    test->_stderr = (void *)valk_slab_aquire(slab)->data;
    valk_ring_init(test->_stderr, ring_size);

#ifdef VALK_TEST_FORK
    struct pollfd fds[2];
    int pid = valk_test_fork(test, suite, fds);
    valk_test_fork_await(test, pid, fds);
#else
    printf("🏃 Running: %s\n", test->name);
    test->func(suite, &test->result);
#endif
  }

  // for (size_t i = 0; i < suite->results.count; i++) {
  //   valk_test_result_t *result = &suite->results.items[i];
  //   if (result->type != VALK_TEST_PASS) {
  //     return 1;
  //   }
  // }

  return 0;
}

void valk_testsuite_print(valk_test_suite_t *suite) {
  printf("[%zu/%zu] %s Suite Results: \n", suite->tests.count,
         suite->tests.count, suite->filename);
  for (size_t i = 0; i < suite->tests.count; i++) {
    valk_test_t *test = &suite->tests.items[i];
    valk_test_result_t *result = &test->result;
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

      printf("\n[STDOUT]%.*s\n", VALK_REPORT_WIDTH + 3, UND_FILL);
      valk_ring_fread(test->_stdout, test->_stdout->capacity + 1, stdout);
      // valk_ring_print(test->_stdout, stdout);
      printf("\n[STDERR]%.*s\n", VALK_REPORT_WIDTH + 3, UND_FILL);
      valk_ring_fread(test->_stderr, test->_stderr->capacity, stdout);
      printf("\n________%.*s\n", VALK_REPORT_WIDTH + 3, UND_FILL);

      break;
    case VALK_TEST_CRSH:
      printf("🌀 %s%.*s  CRSH : in %" PRIu64 "(%s)\n", test->name, len,
             DOT_FILL, (result->stopTime - result->startTime), precision);

      printf("\n[STDOUT]%.*s\n", VALK_REPORT_WIDTH + 3, UND_FILL);
      valk_ring_fread(test->_stdout, test->_stdout->capacity + 1, stdout);
      // valk_ring_print(test->_stdout, stdout);
      printf("\n[STDERR]%.*s\n", VALK_REPORT_WIDTH + 3, UND_FILL);
      valk_ring_fread(test->_stderr, test->_stderr->capacity, stdout);
      printf("\n________%.*s\n", VALK_REPORT_WIDTH + 3, UND_FILL);

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
