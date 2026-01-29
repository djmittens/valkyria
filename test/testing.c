#define _POSIX_C_SOURCE 200809L
#include "testing.h"

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <poll.h>
#include <signal.h>
#include <stdbool.h>
#include <stdckdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#include "collections.h"
#include "common.h"
#include "gc.h"
#include "memory.h"

#if defined(__GNUC__) && defined(VALK_COVERAGE_BUILD)
extern void __gcov_dump(void);
#endif

#define SEC_TO_MS(sec) ((sec) * 1000)
#define SEC_TO_US(sec) ((sec) * 1000000)
#define SEC_TO_NS(sec) ((sec) * 1000000000)

#define NS_TO_SEC(ns) ((ns) / 1000000000)
#define NS_TO_MS(ns) ((ns) / 1000000)
#define NS_TO_US(ns) ((ns) / 1000)

#ifndef VALK_REPORT_WIDTH
#define VALK_REPORT_WIDTH 100
#endif

// Disable fork-based testing when running under AddressSanitizer
// ASAN doesn't properly support fork() - shadow memory state becomes inconsistent
#if defined(__SANITIZE_ADDRESS__) || (defined(__has_feature) && __has_feature(address_sanitizer))
#define VALK_TEST_FORK_COMPILED 0
#else
#define VALK_TEST_FORK_COMPILED 1
#endif

#if VALK_TEST_FORK_COMPILED
static bool valk_test_fork_disabled(void) {
  return getenv("VALK_TEST_NO_FORK") != nullptr;
}
#endif

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

#define ANSI_YELLOW_BG "\033[43m"
#define ANSI_BLACK_FG "\033[30m"
#define ANSI_RESET "\033[0m"

// Nerd Font: U+E0B8 =  , U+E0BE = 
#define NF_SLANT ""

static void __attribute__((unused)) valk_print_police_tape_line(int tiles) {
  printf(ANSI_YELLOW_BG ANSI_BLACK_FG);
  for (int i = 0; i < tiles; ++i) {
    printf(NF_SLANT);
  }
  printf(ANSI_RESET);
}

static char* valk_str_dup(const char* str) {
  size_t len = strlen(str) + 1;
  char* copy = valk_mem_alloc(len);
  memcpy(copy, str, len);
  return copy;
}

valk_test_suite_t *valk_testsuite_empty(const char *filename) {
  valk_test_suite_t *res = valk_mem_alloc(sizeof(valk_test_suite_t));
  memset(res, 0, sizeof(valk_test_suite_t));
  res->filename = valk_str_dup(filename);

  da_init(&res->tests);
  da_init(&res->fixtures);

  return res;
}

void valk_testsuite_free(valk_test_suite_t *suite) {
  for (size_t i = 0; i < suite->tests.count; i++) {
    valk_mem_free(suite->tests.items[i].name);
    da_free(&suite->tests.items[i].labels);
  }
  valk_mem_free(suite->tests.items);

  for (size_t i = 0; i < suite->fixtures.count; i++) {
    valk_mem_free(suite->fixtures.items[i].name);
    suite->fixtures.items[i].free(suite->fixtures.items[i].value);
  }

  valk_mem_free(suite->fixtures.items);

  valk_mem_free(suite->filename);

  valk_mem_free(suite);
}

size_t valk_testsuite_add_test(valk_test_suite_t *suite, const char *name,
                               valk_test_f *func) {
  valk_test_t test = {.name = valk_str_dup(name), .func = func};
  da_init(&test.labels);
  // Initialize the result to UNDEFINED
  test.result.type = VALK_TEST_UNDEFINED;
  test.result.startTime = 0;
  test.result.stopTime = 0;
  test.result.timePrecision = VALK_MICROS;
  da_add(&suite->tests, test);

  return suite->tests.count;
}

static void valk_set_nonblocking(int fd) {
  int flags = fcntl(fd, F_GETFL, 0);
  if (flags == -1) {
    perror("fcntl");
    VALK_RAISE("could not set the forked shit non-blocking");
  }
  fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}

static void valk_timeout_signal_handler(int sig) {
  (void)sig;
  valk_diag_dump_on_timeout();
}

int valk_test_fork(valk_test_t *self, valk_test_suite_t *suite,
                   struct pollfd fds[2]) {
  int pout[2], perr[2];
  pipe(pout);
  pipe(perr);
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
    
    // Install SIGUSR1 handler for timeout diagnostics
    signal(SIGUSR1, valk_timeout_signal_handler);

    // Reset all global GC state after fork - critical for test isolation
    // This clears stale pointers to parent's heaps, TLABs, and GC coordinator state
    valk_gc_reset_after_fork();
    
    // Reinitialize thread-local allocator after fork
    valk_mem_init_malloc();
    
    // Call suite-specific fork handler if set (e.g., for SSL reinitialization)
    if (suite->fork_child_handler) {
      suite->fork_child_handler();
    }

    printf("🏃 Running: %s\n", self->name);
    fflush(stdout);
    self->func(suite, &self->result);

    fflush(stdout);
    fflush(stderr);

    u8 *p = (void *)&self->result;
    size_t size = sizeof(self->result);

    while (size) {
      ssize_t n = write(STDERR_FILENO, p, size);
      if (n <= 0) break;
      p += n;
      size -= (size_t)n;
    }

#if defined(__GNUC__) && defined(VALK_COVERAGE_BUILD)
    __gcov_dump();
#endif
    _exit(0);
  }

  // parent
  // we only read
  close(pout[1]);
  close(perr[1]);

  fds[0].fd = pout[0];
  valk_set_nonblocking(fds[0].fd);
  fds[0].events = POLLIN;
  fds[1].fd = perr[0];
  valk_set_nonblocking(fds[1].fd);
  fds[1].events = POLLIN;
  return pid;
}

void valk_test_fork_await(valk_test_t *test, int pid, struct pollfd fds[2]) {
  int timeoutSeconds = 180;
  const char *env_timeout = getenv("VALK_TEST_TIMEOUT_SECONDS");
  if (env_timeout) {
    int val = atoi(env_timeout);
    if (val > 0) timeoutSeconds = val;
  }

  const int pollTimeoutMs = 100;  // Poll every 100ms to check timeout
  int elapsedMs = 0;
  bool timedOut = false;

  while (!timedOut) {
    int r = poll(fds, 2, pollTimeoutMs);

    if (r < 0) {
      if (errno == EINTR) continue;
      perror("poll");
      break;
    }

    if (r == 0) {
      // Poll timeout - check if we've exceeded total timeout
      elapsedMs += pollTimeoutMs;
      if (elapsedMs >= SEC_TO_MS(timeoutSeconds)) {
        timedOut = true;
        break;
      }
      continue;
    }

    u8 buf[256];

    if (fds[0].revents & POLLIN) {
      ssize_t n = read(fds[0].fd, buf, sizeof buf);
      if (n > 0) {
        valk_ring_write(test->_stdout, buf, (size_t)n);
      } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        // No data available, continue
      } else if (n == 0) {
        // EOF on stdout
        fds[0].fd = -1;
      } else {
        perror("read stdout");
        break;
      }
    }
    if (fds[1].revents & POLLIN) {
      ssize_t n = read(fds[1].fd, buf, sizeof buf);
      if (n > 0) {
        valk_ring_write(test->_stderr, buf, (size_t)n);
      } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        // No data available, continue
      } else if (n == 0) {
        // EOF on stderr
        fds[1].fd = -1;
      } else {
        perror("read stderr");
        break;
      }
    }
    // On POLLHUP without POLLIN, mark FD as done (no more data coming)
    if ((fds[0].revents & POLLHUP) && !(fds[0].revents & POLLIN)) {
      fds[0].fd = -1;
    }
    if ((fds[1].revents & POLLHUP) && !(fds[1].revents & POLLIN)) {
      fds[1].fd = -1;
    }
    // Exit when both FDs are closed/invalid
    if (fds[0].fd < 0 && fds[1].fd < 0) {
      break;
    }
  }

  if (fds[0].fd >= 0) close(fds[0].fd);
  if (fds[1].fd >= 0) close(fds[1].fd);

  if (timedOut) {
    // Timeout was reached - send SIGUSR1 to trigger diagnostic dump, then kill
    kill(pid, SIGUSR1);
    
    // Give the child time to write diagnostics (up to 500ms)
    struct pollfd wait_fds[2] = {
      {.fd = fds[0].fd >= 0 ? fds[0].fd : -1, .events = POLLIN},
      {.fd = fds[1].fd >= 0 ? fds[1].fd : -1, .events = POLLIN}
    };
    int wait_ms = 500;
    while (wait_ms > 0) {
      int r = poll(wait_fds, 2, 50);
      if (r > 0) {
        u8 buf[1024];
        if (wait_fds[0].revents & POLLIN) {
          ssize_t n = read(wait_fds[0].fd, buf, sizeof buf);
          if (n > 0) valk_ring_write(test->_stdout, buf, (size_t)n);
        }
        if (wait_fds[1].revents & POLLIN) {
          ssize_t n = read(wait_fds[1].fd, buf, sizeof buf);
          if (n > 0) valk_ring_write(test->_stderr, buf, (size_t)n);
        }
      }
      wait_ms -= 50;
    }
    
    // Now kill for real
    kill(pid, SIGKILL);

    test->result.type = VALK_TEST_CRSH;
    size_t len = snprintf(nullptr, 0, "Test timed out after %d seconds\n",
                          timeoutSeconds);
    char buf[++len];

    snprintf(buf, len, "Test timed out after %d seconds\n", timeoutSeconds);
    valk_ring_write(test->_stderr, (void *)buf, len);
    // Still need to reap the child
    waitpid(pid, nullptr, 0);
    return;
  }

  int wstatus;
  waitpid(pid, &wstatus, 0);
  if (WIFEXITED(wstatus)) {
    valk_ring_rewind(test->_stderr, sizeof(test->result));
    valk_ring_read(test->_stderr, sizeof(test->result), &test->result);
  } else if (WIFSIGNALED(wstatus)) {
    test->result.type = VALK_TEST_CRSH;

    int sig = WTERMSIG(wstatus);
    const char *name = strsignal(sig);

    size_t len = snprintf(nullptr, 0, "Child died because of signal %d (%s)\n",
                          sig, name);
    char buf[++len];

    snprintf(buf, len, "Child died because of signal %d (%s)\n", sig, name);

    valk_ring_write(test->_stderr, (void *)buf, len);
  }
}

int valk_testsuite_run(valk_test_suite_t *suite) {
  static size_t ring_size = 0;
  static valk_slab_t *slab = nullptr;
  if (slab == nullptr) {
    ring_size = valk_next_pow2(642);
    slab = valk_slab_new(sizeof(valk_ring_t) + ring_size, 512);
  }

  bool result = 0;

  for (size_t i = 0; i < suite->tests.count; i++) {
    valk_test_t *test = &suite->tests.items[i];

    test->_stdout = (void *)valk_slab_aquire(slab)->data;
    valk_ring_init(test->_stdout, ring_size);
    test->_stderr = (void *)valk_slab_aquire(slab)->data;
    valk_ring_init(test->_stderr, ring_size);

#if VALK_TEST_FORK_COMPILED
    if (!valk_test_fork_disabled()) {
      struct pollfd fds[2];
      int pid = valk_test_fork(test, suite, fds);
      valk_test_fork_await(test, pid, fds);
    } else {
      fprintf(stderr, "Running: %s (no fork)\n", test->name);
      test->func(suite, &test->result);
    }
#else
    fprintf(stderr, "Running: %s\n", test->name);
    test->func(suite, &test->result);
#endif
    result |= !(test->result.type == VALK_TEST_PASS ||
                test->result.type == VALK_TEST_SKIP);
  }

  // for (size_t i = 0; i < suite->results.count; i++) {
  //   valk_test_result_t *result = &suite->results.items[i];
  //   if (result->type != VALK_TEST_PASS) {
  //     return 1;
  //   }
  // }

  return result;
}

static void valk_print_io(valk_test_t *test) {
  putc('\n', stdout);
  valk_print_police_tape_line(1);
  printf("[STDOUT]");
  valk_print_police_tape_line(VALK_REPORT_WIDTH / 2);
  putc('\n', stdout);

  valk_ring_fread(test->_stdout, test->_stdout->capacity + 1, stdout);

  // valk_ring_print(test->_stdout, stdout);
  putc('\n', stdout);
  valk_print_police_tape_line(1);
  printf("[STDERR]");
  valk_print_police_tape_line(VALK_REPORT_WIDTH / 2);
  putc('\n', stdout);
  if (test->result.type == VALK_TEST_CRSH) {
    // if the test crash then there were no results in stderr
    valk_ring_fread(test->_stderr, test->_stderr->capacity, stdout);
  } else {
    valk_ring_fread(test->_stderr,
                    test->_stderr->capacity - sizeof(test->result), stdout);
  }
  putc('\n', stdout);
  // valk_print_police_tape_line(VALK_REPORT_WIDTH / 2 + 5);
  // putc('\n', stdout);
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

    // Base padding calculation (for lines without emoji)
    int len = VALK_REPORT_WIDTH - strlen(test->name);

    switch (result->type) {
      case VALK_TEST_UNDEFINED: {
        printf("%s%.*s  UNDEFINED\n", test->name, len, DOT_FILL);
        break;
      }
      case VALK_TEST_PASS:
        // Emoji ✅ + space = 3 display columns
        printf("✅ %s%.*s  PASS : in %llu(%s)\n", test->name, len - 3,
               DOT_FILL, (unsigned long long)(result->stopTime - result->startTime), precision);
        break;
      case VALK_TEST_SKIP:
        // Emoji ⏭️ + space = 3 display columns
        printf("⏭️  %s%.*s  SKIP : in %llu(%s)\n", test->name, len - 3,
               DOT_FILL, (unsigned long long)(result->stopTime - result->startTime), precision);
        break;
      case VALK_TEST_FAIL:
        // Emoji 🐞 + space = 3 display columns
        printf("🐞 %s%.*s  FAIL : in %llu(%s)\n", test->name, len - 3,
               DOT_FILL, (unsigned long long)(result->stopTime - result->startTime), precision);
        valk_print_io(test);
        break;
      case VALK_TEST_CRSH:
        // Emoji 🌀 + space = 3 display columns
        printf("🌀 %s%.*s  CRSH : in %llu(%s)\n", test->name, len - 3,
               DOT_FILL, (unsigned long long)(result->stopTime - result->startTime), precision);
        valk_print_io(test);
        break;
      default:
        printf("❓ %s%.*s  UNKNOWN(type=%d)\n", test->name, len - 3, DOT_FILL, result->type);
        break;
    }
  }
}

void valk_testsuite_fixture_add(valk_test_suite_t *suite, const char *name,
                                void *value, _fixture_copy_f *copyFunc,
                                _fixture_free_f *freeFunc) {
  valk_test_fixture_t res = {
      .value = value, .copy = copyFunc, .free = freeFunc, .name = valk_str_dup(name)};
  da_add(&suite->fixtures, res);
}

void *valk_testsuite_fixture_get(valk_test_suite_t *suite, const char *name) {
  for (size_t i = 0; i < suite->fixtures.count; i++) {
    if (strcmp(suite->fixtures.items[i].name, name) == 0) {
      return suite->fixtures.items[i].copy(suite->fixtures.items[i].value);
    }
  }
  return nullptr;
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
