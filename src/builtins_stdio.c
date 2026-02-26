#include "builtins_internal.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static valk_lval_t *valk_builtin_stdin_read_line(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 0);

  size_t cap = 256;
  char *buf = malloc(cap);
  size_t len = 0;

  for (;;) {
    int c = fgetc(stdin);
    if (c == EOF) {
      if (len == 0) { free(buf); return valk_lval_nil(); }
      break;
    }
    if (len + 1 >= cap) { cap *= 2; buf = realloc(buf, cap); }
    buf[len++] = (char)c;
    if (c == '\n') break;
  }
  buf[len] = '\0';

  valk_lval_t *result = valk_lval_str(buf);
  free(buf);
  return result;
}

static valk_lval_t *valk_builtin_stdin_read_bytes(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);

  long n = valk_lval_list_nth(a, 0)->num;
  if (n <= 0) return valk_lval_str("");

  char *buf = malloc(n + 1);
  size_t total = 0;
  while (total < (size_t)n) {
    size_t got = fread(buf + total, 1, n - total, stdin);
    if (got == 0) break;
    total += got;
  }
  buf[total] = '\0';

  if (total < (size_t)n) {
    free(buf);
    return valk_lval_err("stdin/read-bytes: EOF after %zu of %ld bytes", total, n);
  }

  valk_lval_t *result = valk_lval_str(buf);
  free(buf);
  return result;
}

static valk_lval_t *valk_builtin_stdout_write(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *s = valk_lval_list_nth(a, 0)->str;
  fwrite(s, 1, strlen(s), stdout);
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_stdout_flush(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 0);
  fflush(stdout);
  return valk_lval_nil();
}

static valk_lval_t *valk_builtin_stderr_write(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_STR);

  const char *s = valk_lval_list_nth(a, 0)->str;
  fwrite(s, 1, strlen(s), stderr);
  fflush(stderr);
  return valk_lval_nil();
}

void valk_register_stdio_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "stdin/read-line", valk_builtin_stdin_read_line);
  valk_lenv_put_builtin(env, "stdin/read-bytes", valk_builtin_stdin_read_bytes);
  valk_lenv_put_builtin(env, "stdout/write", valk_builtin_stdout_write);
  valk_lenv_put_builtin(env, "stdout/flush", valk_builtin_stdout_flush);
  valk_lenv_put_builtin(env, "stderr/write", valk_builtin_stderr_write);
}
