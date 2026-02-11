#include "builtins_internal.h"

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <stdio.h>

#ifndef __linux__
static int memfd_create(const char *name, unsigned int flags) {
  (void)name;
  (void)flags;
  char tmpl[] = "/tmp/valk_cap_XXXXXX";
  int fd = mkstemp(tmpl);
  if (fd >= 0) unlink(tmpl);
  return fd;
}
#endif

typedef struct {
  int saved_stdout;
  int saved_stderr;
  int capture_stdout;
  int capture_stderr;
} valk_capture_state_t;

// LCOV_EXCL_START - ref destructor: only runs when GC collects the ref, not guaranteed in short tests
static void valk_capture_state_free(void *ptr) {
  valk_capture_state_t *s = ptr;
  if (s->saved_stdout >= 0) close(s->saved_stdout);
  if (s->saved_stderr >= 0) close(s->saved_stderr);
  if (s->capture_stdout >= 0) close(s->capture_stdout);
  if (s->capture_stderr >= 0) close(s->capture_stderr);
  valk_mem_free(s);
}
// LCOV_EXCL_STOP

static valk_lval_t *valk_builtin_capture_start(valk_lenv_t *e,
                                               valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 0); // LCOV_EXCL_BR_LINE - macro-generated validation

  int fd_out = memfd_create("cap_stdout", 0);
  int fd_err = memfd_create("cap_stderr", 0);
  if (fd_out < 0 || fd_err < 0) { // LCOV_EXCL_START
    if (fd_out >= 0) close(fd_out);
    if (fd_err >= 0) close(fd_err);
    LVAL_RAISE(a, "test/capture-start: memfd_create failed");
  } // LCOV_EXCL_STOP

  fflush(stdout);
  fflush(stderr);

  int saved_out = dup(STDOUT_FILENO);
  int saved_err = dup(STDERR_FILENO);
  if (saved_out < 0 || saved_err < 0) { // LCOV_EXCL_START
    close(fd_out);
    close(fd_err);
    if (saved_out >= 0) close(saved_out);
    if (saved_err >= 0) close(saved_err);
    LVAL_RAISE(a, "test/capture-start: dup() failed");
  } // LCOV_EXCL_STOP

  dup2(fd_out, STDOUT_FILENO);
  dup2(fd_err, STDERR_FILENO);

  valk_capture_state_t *state = valk_mem_alloc(sizeof(valk_capture_state_t));
  state->saved_stdout = saved_out;
  state->saved_stderr = saved_err;
  state->capture_stdout = fd_out;
  state->capture_stderr = fd_err;

  return valk_lval_ref("capture_state", state, valk_capture_state_free);
}

// LCOV_EXCL_BR_START - read() partial failure and lseek edge cases
static char *read_fd_contents(int fd, u64 *out_len) {
  off_t size = lseek(fd, 0, SEEK_END);
  if (size <= 0) {
    *out_len = 0;
    char *buf = valk_mem_alloc(1);
    buf[0] = '\0';
    return buf;
  }
  lseek(fd, 0, SEEK_SET);
  char *buf = valk_mem_alloc((u64)size);
  u64 total = 0;
  while (total < (u64)size) {
    ssize_t n = read(fd, buf + total, (u64)size - total);
    if (n <= 0) break;
    total += (u64)n;
  }
  *out_len = total;
  return buf;
}
// LCOV_EXCL_BR_STOP

// LCOV_EXCL_BR_START - macro-generated validation branches
static valk_lval_t *valk_builtin_capture_stop(valk_lenv_t *e,
                                              valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);

  valk_lval_t *ref = valk_lval_list_nth(a, 0);
  LVAL_ASSERT_TYPE(a, ref, LVAL_REF);
  LVAL_ASSERT(a, strcmp(ref->ref.type, "capture_state") == 0,
              "test/capture-stop: expected capture_state ref");
  // LCOV_EXCL_BR_STOP

  valk_capture_state_t *state = ref->ref.ptr;

  fflush(stdout);
  fflush(stderr);

  dup2(state->saved_stdout, STDOUT_FILENO);
  dup2(state->saved_stderr, STDERR_FILENO);
  close(state->saved_stdout);
  close(state->saved_stderr);
  state->saved_stdout = -1;
  state->saved_stderr = -1;

  u64 out_len, err_len;
  char *out_data = read_fd_contents(state->capture_stdout, &out_len);
  char *err_data = read_fd_contents(state->capture_stderr, &err_len);
  close(state->capture_stdout);
  close(state->capture_stderr);
  state->capture_stdout = -1;
  state->capture_stderr = -1;

  valk_lval_t *out_str = valk_lval_str_n(out_data, out_len);
  valk_lval_t *err_str = valk_lval_str_n(err_data, err_len);
  valk_mem_free(out_data);
  valk_mem_free(err_data);

  valk_lval_t *items[] = {
    valk_lval_sym(":stdout"), out_str,
    valk_lval_sym(":stderr"), err_str,
  };
  return valk_lval_qlist(items, 4);
}

void valk_register_test_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "test/capture-start", valk_builtin_capture_start);
  valk_lenv_put_builtin(env, "test/capture-stop", valk_builtin_capture_stop);
}
