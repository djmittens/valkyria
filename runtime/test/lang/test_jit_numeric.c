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

// Negative divisor must reach the builtin (which errors), not produce
// LLVM signed-division UB. The numeric fast path emits an SLE-against-0
// guard precisely for this case.
void test_jit_numeric_negative_divisor(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *r = valk_jit_eval_string(jit, env, "(/ 100 -5)");
  // A negative divisor is ordinary division. Both this and the tree walker
  // used to treat every y <= 0 as "Division By Zero" — the JIT grew a
  // y <= 0 guard specifically to mirror the builtin's bug, and this test
  // pinned it. Only y == 0 is an error now.
  ASSERT_LVAL_TYPE(r, LVAL_NUM);
  ASSERT_LVAL_NUM(r, -20);

  valk_jit_free(jit);
  VALK_PASS();
}

// Boundary: large i64 multiplications wrap rather than UB. Tree walker
// uses `i64 *= ...` which wraps; JIT uses LLVMBuildMul (no nsw flag set
// in numeric_codegen) so it also wraps. Verify they produce the same
// result for an overflowing product.
void test_jit_numeric_large_wrap(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  // 9*10^18 * 2 = 1.8*10^19 → overflows i64. Wrapped two's complement
  // value: 18000000000000000000 - 2^64 = -446744073709551616. Both JIT
  // and builtin must produce this exact value.
  valk_lval_t *r = valk_jit_eval_string(jit, env,
      "(* 9000000000000000000 2)");
  ASSERT_LVAL_TYPE(r, LVAL_NUM);
  VALK_TEST_ASSERT(r->num == -446744073709551616LL,
                   "i64 mul wrap matches builtin two's complement");

  valk_jit_free(jit);
  VALK_PASS();
}

// Comparison with a non-number is a slow path because the type check
// fails — and the builtin reports an error rather than coercing. Verify
// JIT preserves the same "this op only supports Numbers" semantics.
void test_jit_numeric_cmp_non_num(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  // (< {} 5) — empty qexpr vs num, builtin path errors.
  valk_lval_t *r = valk_jit_eval_string(jit, env, "(< {} 5)");
  ASSERT_LVAL_TYPE(r, LVAL_ERR);

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
  valk_testsuite_add_test(suite, "jit_numeric_negative_divisor", test_jit_numeric_negative_divisor);
  valk_testsuite_add_test(suite, "jit_numeric_large_wrap", test_jit_numeric_large_wrap);
  valk_testsuite_add_test(suite, "jit_numeric_cmp_non_num", test_jit_numeric_cmp_non_num);
  valk_testsuite_add_test(suite, "jit_numeric_shadow_via_type", test_jit_numeric_shadow_via_type);
  valk_testsuite_add_test(suite, "jit_numeric_nested", test_jit_numeric_nested);
  valk_testsuite_add_test(suite, "jit_numeric_arity_not_specialized", test_jit_numeric_arity_not_specialized);
  int rc = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return rc;
}
