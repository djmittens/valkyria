#include "testing.h"
#include "../src/memory.h"

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static int write_valk(const char *path, const char *src) {
  FILE *f = fopen(path, "w");
  if (!f) return -1;
  size_t n = strlen(src);
  int ok = fwrite(src, 1, n, f) == n;
  fclose(f);
  return ok ? 0 : -1;
}

static int run_valk_build(const char *script, const char *out) {
  char valk[PATH_MAX];
  snprintf(valk, sizeof(valk), "%s/valk", VALK_BUILD_DIR);
  pid_t pid = fork();
  if (pid == 0) {
    execl(valk, valk, "--build", script, "-o", out, (char *)NULL);
    _exit(127);
  }
  int st;
  if (waitpid(pid, &st, 0) < 0) return -1;
  return WIFEXITED(st) ? WEXITSTATUS(st) : -1;
}

static int run_produced(const char *path, char *const extra_argv[]) {
  pid_t pid = fork();
  if (pid == 0) {
    // Build a fresh argv with path as argv[0].
    size_t extra_count = 0;
    while (extra_argv && extra_argv[extra_count]) extra_count++;
    char **args = calloc(extra_count + 2, sizeof(char *));
    args[0] = (char *)path;
    for (size_t i = 0; i < extra_count; i++) args[i + 1] = extra_argv[i];
    execv(path, args);
    _exit(127);
  }
  int st;
  if (waitpid(pid, &st, 0) < 0) return -1;
  return WIFEXITED(st) ? WEXITSTATUS(st) : -1;
}

// Trivial lambda: binary exits with (+ 2 3) = 5.
void test_build_lambda_exit_code(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *src = "/tmp/valk_build_test_lambda.valk";
  const char *out = "/tmp/valk_build_test_lambda.bin";
  VALK_TEST_ASSERT(write_valk(src, "(\\ {argv} {+ 2 3})") == 0, "write src");

  VALK_TEST_ASSERT(run_valk_build(src, out) == 0, "valk --build succeeds");

  struct stat st;
  VALK_TEST_ASSERT(stat(out, &st) == 0 && (st.st_mode & S_IXUSR),
                   "produced binary is executable");

  int rc = run_produced(out, NULL);
  VALK_TEST_ASSERT(rc == 5, "binary exit code == (+ 2 3)");

  unlink(src);
  unlink(out);
  VALK_PASS();
}

// Lambda sees the full argv list: exit with (len argv) == 3 for "bin a b".
void test_build_lambda_receives_argv(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *src = "/tmp/valk_build_test_argv.valk";
  const char *out = "/tmp/valk_build_test_argv.bin";
  VALK_TEST_ASSERT(write_valk(src, "(\\ {argv} {len argv})") == 0, "write src");

  VALK_TEST_ASSERT(run_valk_build(src, out) == 0, "valk --build succeeds");

  char *extra[] = {"a", "b", NULL};
  int rc = run_produced(out, extra);
  VALK_TEST_ASSERT(rc == 3, "binary sees argv of length 3");

  unlink(src);
  unlink(out);
  VALK_PASS();
}

// Qexpr entry: the binary evaluates the qexpr body, which resolves `argv`
// via late binding in the image env.
void test_build_qexpr_entry(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *src = "/tmp/valk_build_test_qexpr.valk";
  const char *out = "/tmp/valk_build_test_qexpr.bin";
  VALK_TEST_ASSERT(write_valk(src, "{len argv}") == 0, "write src");

  VALK_TEST_ASSERT(run_valk_build(src, out) == 0, "valk --build succeeds");

  char *extra[] = {"x", "y", "z", NULL};
  int rc = run_produced(out, extra);
  VALK_TEST_ASSERT(rc == 4, "qexpr sees argv via late binding");

  unlink(src);
  unlink(out);
  VALK_PASS();
}

// Build-time state is baked in: a value computed before the entry lambda
// is captured via closure and observed at runtime.
void test_build_time_state_captured(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *src = "/tmp/valk_build_test_state.valk";
  const char *out = "/tmp/valk_build_test_state.bin";
  const char *body =
      "(def {precomputed} (* 6 7))\n"
      "(\\ {argv} {precomputed})\n";
  VALK_TEST_ASSERT(write_valk(src, body) == 0, "write src");

  VALK_TEST_ASSERT(run_valk_build(src, out) == 0, "valk --build succeeds");

  int rc = run_produced(out, NULL);
  VALK_TEST_ASSERT(rc == 42, "binary sees precomputed value from build time");

  unlink(src);
  unlink(out);
  VALK_PASS();
}

// Stage 1: a chain of lambdas where each calls the previous. Exercises
// direct-call emission (compiled body calls sibling AOT'd lambda without
// going through valk_lval_eval_call). Result: (+ 10 (+ 20 12)) = 42.
void test_build_aot_direct_call_chain(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *src = "/tmp/valk_build_test_chain.valk";
  const char *out = "/tmp/valk_build_test_chain.bin";
  const char *body =
      "(def {add-two} (\\ {a b} {+ a b}))\n"
      "(def {triple} (\\ {a b c} {add-two (add-two a b) c}))\n"
      "(\\ {argv} {triple 10 20 12})\n";
  VALK_TEST_ASSERT(write_valk(src, body) == 0, "write src");

  VALK_TEST_ASSERT(run_valk_build(src, out) == 0, "valk --build succeeds");

  int rc = run_produced(out, NULL);
  VALK_TEST_ASSERT(rc == 42, "chained direct calls produce 42");

  unlink(src);
  unlink(out);
  VALK_PASS();
}

// Stage 3: self-recursive tail call lowered as phi+branch. A naive
// recursive implementation would blow the native stack at ~10k frames;
// this recurses 100,000 times and must run in constant stack space.
void test_build_aot_tco_self_recursion(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *src = "/tmp/valk_build_test_tco.valk";
  const char *out = "/tmp/valk_build_test_tco.bin";
  const char *body =
      "(def {loop} (\\ {n acc} "
      "  {if (== n 0) acc (loop (- n 1) acc)}))\n"
      "(\\ {argv} {loop 100000 42})\n";
  VALK_TEST_ASSERT(write_valk(src, body) == 0, "write src");

  VALK_TEST_ASSERT(run_valk_build(src, out) == 0, "valk --build succeeds");

  int rc = run_produced(out, NULL);
  VALK_TEST_ASSERT(rc == 42, "100k-deep tail recursion returns 42");

  unlink(src);
  unlink(out);
  VALK_PASS();
}

// Mutual tail recursion: is-even ↔ is-odd with forward reference. Requires
// both the slow-variant adapter (so tree walker dispatches the top-level
// call into the _fast chain) and the _fast sibcall lowering. 1,000,000
// iterations must run in constant stack.
void test_build_aot_tco_mutual_recursion(VALK_TEST_ARGS()) {
  VALK_TEST();
  const char *src = "/tmp/valk_build_test_mutual.valk";
  const char *out = "/tmp/valk_build_test_mutual.bin";
  const char *body =
      "(def {is-even} (\\ {n} "
      "  {if (== n 0) 1 (is-odd (- n 1))}))\n"
      "(def {is-odd} (\\ {n} "
      "  {if (== n 0) 0 (is-even (- n 1))}))\n"
      "(\\ {argv} {is-even 1000000})\n";
  VALK_TEST_ASSERT(write_valk(src, body) == 0, "write src");

  VALK_TEST_ASSERT(run_valk_build(src, out) == 0, "valk --build succeeds");

  int rc = run_produced(out, NULL);
  VALK_TEST_ASSERT(rc == 1, "mutual 1M tail recursion returns 1 (truthy)");

  unlink(src);
  unlink(out);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "build_lambda_exit_code",
                          test_build_lambda_exit_code);
  valk_testsuite_add_test(suite, "build_lambda_receives_argv",
                          test_build_lambda_receives_argv);
  valk_testsuite_add_test(suite, "build_qexpr_entry",
                          test_build_qexpr_entry);
  valk_testsuite_add_test(suite, "build_time_state_captured",
                          test_build_time_state_captured);
  valk_testsuite_add_test(suite, "build_aot_direct_call_chain",
                          test_build_aot_direct_call_chain);
  valk_testsuite_add_test(suite, "build_aot_tco_self_recursion",
                          test_build_aot_tco_self_recursion);
  valk_testsuite_add_test(suite, "build_aot_tco_mutual_recursion",
                          test_build_aot_tco_mutual_recursion);
  int rc = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return rc;
}
