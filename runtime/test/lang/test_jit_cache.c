#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/llvm/llvm_jit.h"

static valk_lenv_t *make_full_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  return env;
}

// Repeated eval of the same source text should hit the cache instead of
// triggering another compile.
void test_jit_cache_hits_on_repeat(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *r1 = valk_jit_eval_string(jit, env, "(+ 1 2)");
  ASSERT_LVAL_TYPE(r1, LVAL_NUM);
  ASSERT_LVAL_NUM(r1, 3);
  VALK_TEST_ASSERT(valk_jit_cache_misses(jit) == 1, "first eval is a miss");
  VALK_TEST_ASSERT(valk_jit_cache_hits(jit) == 0, "first eval no hit");

  valk_lval_t *r2 = valk_jit_eval_string(jit, env, "(+ 1 2)");
  ASSERT_LVAL_TYPE(r2, LVAL_NUM);
  ASSERT_LVAL_NUM(r2, 3);
  VALK_TEST_ASSERT(valk_jit_cache_hits(jit) == 1, "second eval is a hit");
  VALK_TEST_ASSERT(valk_jit_cache_misses(jit) == 1, "still one miss");

  valk_lval_t *r3 = valk_jit_eval_string(jit, env, "(+ 1 2)");
  ASSERT_LVAL_NUM(r3, 3);
  VALK_TEST_ASSERT(valk_jit_cache_hits(jit) == 2, "third eval also hits");

  valk_jit_free(jit);
  VALK_PASS();
}

// Distinct source strings produce distinct cache entries.
void test_jit_cache_distinct_sources(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env, "(+ 1 2)");
  valk_jit_eval_string(jit, env, "(+ 3 4)");
  valk_jit_eval_string(jit, env, "(+ 5 6)");
  VALK_TEST_ASSERT(valk_jit_cache_misses(jit) == 3, "three misses");
  VALK_TEST_ASSERT(valk_jit_cache_hits(jit) == 0, "no hits");

  // Now re-eval each; all should hit.
  valk_jit_eval_string(jit, env, "(+ 1 2)");
  valk_jit_eval_string(jit, env, "(+ 3 4)");
  valk_jit_eval_string(jit, env, "(+ 5 6)");
  VALK_TEST_ASSERT(valk_jit_cache_hits(jit) == 3, "three hits on round two");
  VALK_TEST_ASSERT(valk_jit_cache_misses(jit) == 3, "still three misses");

  valk_jit_free(jit);
  VALK_PASS();
}

// A cached function should still observe env mutations that happen between
// calls (the env is passed as a parameter, not baked into the compiled code).
void test_jit_cache_env_sensitivity(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env, "(def {v} 10)");
  valk_lval_t *r1 = valk_jit_eval_string(jit, env, "(+ v 1)");
  ASSERT_LVAL_NUM(r1, 11);

  // Rebind v, repeat.
  valk_jit_eval_string(jit, env, "(def {v} 100)");
  valk_lval_t *r2 = valk_jit_eval_string(jit, env, "(+ v 1)");
  ASSERT_LVAL_NUM(r2, 101);
  VALK_TEST_ASSERT(valk_jit_cache_hits(jit) >= 1,
                   "(+ v 1) hit cache on second call");

  valk_jit_free(jit);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();
  setenv("VALK_TEST_NO_FORK", "1", 1);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "jit_cache_hits_on_repeat", test_jit_cache_hits_on_repeat);
  valk_testsuite_add_test(suite, "jit_cache_distinct_sources", test_jit_cache_distinct_sources);
  valk_testsuite_add_test(suite, "jit_cache_env_sensitivity", test_jit_cache_env_sensitivity);
  int rc = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return rc;
}
