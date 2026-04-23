#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/llvm/llvm_jit.h"

#include <stdlib.h>
#include <unistd.h>

static valk_lenv_t *make_full_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  return env;
}

// Fast-path arithmetic matches builtin semantics.
void test_jit_numeric_fast_arith(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  struct { const char *src; long want; } cases[] = {
    {"(+ 3 4)",    7},
    {"(- 10 3)",   7},
    {"(* 6 7)",   42},
    {"(/ 20 4)",   5},
    {"(/ 7 2)",    3},   // integer division, floor toward zero
    {"(- 5 10)",  -5},
    {"(* -3 4)", -12},
  };
  for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
    valk_lval_t *r = valk_jit_eval_string(jit, env, cases[i].src);
    ASSERT_LVAL_TYPE(r, LVAL_NUM);
    VALK_TEST_ASSERT(r->num == cases[i].want, cases[i].src);
  }

  valk_jit_free(jit);
  VALK_PASS();
}

// Fast-path comparisons return 1/0 (matching valk_lval_num bool convention).
void test_jit_numeric_fast_cmp(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  struct { const char *src; long want; } cases[] = {
    {"(< 1 2)",  1}, {"(< 2 1)", 0}, {"(< 2 2)", 0},
    {"(> 1 2)",  0}, {"(> 2 1)", 1}, {"(> 2 2)", 0},
    {"(<= 2 2)", 1}, {"(<= 3 2)", 0},
    {"(>= 2 2)", 1}, {"(>= 1 2)", 0},
    {"(== 5 5)", 1}, {"(== 5 6)", 0},
  };
  for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
    valk_lval_t *r = valk_jit_eval_string(jit, env, cases[i].src);
    ASSERT_LVAL_TYPE(r, LVAL_NUM);
    VALK_TEST_ASSERT(r->num == cases[i].want, cases[i].src);
  }

  valk_jit_free(jit);
  VALK_PASS();
}

// Division by zero must fall back to the builtin and produce an error lval,
// not trigger LLVM UB.
void test_jit_numeric_div_by_zero(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *r = valk_jit_eval_string(jit, env, "(/ 5 0)");
  ASSERT_LVAL_TYPE(r, LVAL_ERR);

  valk_jit_free(jit);
  VALK_PASS();
}

// When at least one operand is non-numeric, the slow path must handle it —
// so a user-shadowed operator still dispatches correctly.
void test_jit_numeric_shadow_via_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  // Rebind + to a lambda that always returns 999 regardless of args.
  valk_jit_eval_string(jit, env, "(def {+} (\\ {x y} {999}))");

  // Call with non-number to force slow path: lhs is a qexpr (LVAL_CONS).
  // Fast-path guard fails -> goes through slow path -> user-shadowed fn.
  valk_lval_t *r = valk_jit_eval_string(jit, env, "(+ {a} {b})");
  ASSERT_LVAL_TYPE(r, LVAL_NUM);
  ASSERT_LVAL_NUM(r, 999);

  valk_jit_free(jit);
  VALK_PASS();
}

// Nested specialized ops compose correctly.
void test_jit_numeric_nested(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *r = valk_jit_eval_string(jit, env, "(+ (* 3 4) (- 10 2))");
  ASSERT_LVAL_TYPE(r, LVAL_NUM);
  ASSERT_LVAL_NUM(r, 20);

  valk_lval_t *r2 = valk_jit_eval_string(jit, env, "(if (< 1 2) (* 7 6) 0)");
  ASSERT_LVAL_TYPE(r2, LVAL_NUM);
  ASSERT_LVAL_NUM(r2, 42);

  valk_jit_free(jit);
  VALK_PASS();
}

// The specialization should not break existing behavior for arity != 2.
// (+ 1 2 3) is arity-3 and must fall to the builtin path.
void test_jit_numeric_arity_not_specialized(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *r = valk_jit_eval_string(jit, env, "(+ 1 2 3 4)");
  ASSERT_LVAL_TYPE(r, LVAL_NUM);
  ASSERT_LVAL_NUM(r, 10);

  valk_jit_free(jit);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();
  setenv("VALK_TEST_NO_FORK", "1", 1);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);
  valk_testsuite_add_test(suite, "jit_numeric_fast_arith", test_jit_numeric_fast_arith);
  valk_testsuite_add_test(suite, "jit_numeric_fast_cmp", test_jit_numeric_fast_cmp);
  valk_testsuite_add_test(suite, "jit_numeric_div_by_zero", test_jit_numeric_div_by_zero);
  valk_testsuite_add_test(suite, "jit_numeric_shadow_via_type", test_jit_numeric_shadow_via_type);
  valk_testsuite_add_test(suite, "jit_numeric_nested", test_jit_numeric_nested);
  valk_testsuite_add_test(suite, "jit_numeric_arity_not_specialized", test_jit_numeric_arity_not_specialized);
  int rc = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return rc;
}
