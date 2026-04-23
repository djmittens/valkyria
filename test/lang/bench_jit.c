// Standalone micro-benchmark comparing tree-walker eval, one-shot JIT
// (no cache), and cached JIT on a tight arithmetic expression.
//
// Not linked into make test — run manually: build/bench_jit

#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/llvm/llvm_jit.h"

#include <stdio.h>
#include <time.h>

static double now_sec(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
}

static valk_lenv_t *make_full_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  return env;
}

// Drive N iterations of a source string through the given path, report total
// time + ns-per-call.
static void bench(const char *label, const char *src, long n,
                  double (*runner)(const char *src, long n)) {
  double elapsed = runner(src, n);
  double ns_per = (elapsed * 1e9) / (double)n;
  printf("  %-28s %8.3f ms total   %8.1f ns/call   (n=%ld)\n",
         label, elapsed * 1e3, ns_per, n);
}

// ---- runners ----

static double run_tree_walker(const char *src, long n) {
  valk_lenv_t *env = make_full_env();
  valk_lval_t *ast = valk_parse_text(src);   // parser returns list of top-level
  valk_lval_t *expr = ast->cons.head;         // single top-level form
  double t0 = now_sec();
  volatile long sum = 0;
  for (long i = 0; i < n; i++) {
    valk_lval_t *r = valk_lval_eval(env, expr);
    if (r && LVAL_TYPE(r) == LVAL_NUM) sum += r->num;
  }
  double t1 = now_sec();
  (void)sum;
  return t1 - t0;
}

static double run_jit_one_shot(const char *src, long n) {
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();
  double t0 = now_sec();
  volatile long sum = 0;
  for (long i = 0; i < n; i++) {
    // valk_jit_eval (not _string) doesn't use the cache: compiles a fresh
    // module, runs it, drops the module. This is the pre-change cost.
    valk_lval_t *ast = valk_parse_text(src);
    valk_lval_t *expr = ast->cons.head;
    valk_lval_t *r = valk_jit_eval(jit, env, expr);
    if (r && LVAL_TYPE(r) == LVAL_NUM) sum += r->num;
  }
  double t1 = now_sec();
  (void)sum;
  valk_jit_free(jit);
  return t1 - t0;
}

static double run_jit_cached(const char *src, long n) {
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();
  // Warm the cache with one call so the first iter isn't a compile.
  valk_jit_eval_string(jit, env, src);
  double t0 = now_sec();
  volatile long sum = 0;
  for (long i = 0; i < n; i++) {
    valk_lval_t *r = valk_jit_eval_string(jit, env, src);
    if (r && LVAL_TYPE(r) == LVAL_NUM) sum += r->num;
  }
  double t1 = now_sec();
  (void)sum;
  printf("      (cache hits=%llu, misses=%llu)\n",
         (unsigned long long)valk_jit_cache_hits(jit),
         (unsigned long long)valk_jit_cache_misses(jit));
  valk_jit_free(jit);
  return t1 - t0;
}

static void run_case(const char *src, long n_tw, long n_jit) {
  printf("\nExpression: %s\n", src);
  bench("tree walker",      src, n_tw,  run_tree_walker);
  bench("JIT one-shot",     src, n_jit, run_jit_one_shot);
  bench("JIT cached",       src, n_tw,  run_jit_cached);
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();

  // Pure arithmetic, will hit numeric fast path.
  run_case("(+ 3 4)",            1000000, 200);
  run_case("(+ (* 3 4) (- 9 2))", 500000, 200);
  run_case("(< 5 10)",            1000000, 200);

  // Funcall (no specialization). Cache still helps; fast path doesn't apply.
  run_case("(do (def {x} 7) x)",  500000, 200);

  return 0;
}
