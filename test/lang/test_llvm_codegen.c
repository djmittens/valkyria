#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/llvm/llvm_codegen.h"
#include "../src/llvm/llvm_jit.h"
#include "../src/llvm/llvm_aot.h"

#include <stdio.h>
#include <string.h>

static valk_lenv_t *make_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  return env;
}

void test_codegen_num_literal(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_num");
  valk_lval_t *expr = valk_lval_num(42);
  LLVMValueRef fn = valk_llvm_compile_toplevel(ctx, expr);
  VALK_TEST_ASSERT(fn != NULL, "Should compile number literal");

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_codegen_str_literal(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_str");
  valk_lval_t *expr = valk_lval_str("hello");
  LLVMValueRef fn = valk_llvm_compile_toplevel(ctx, expr);
  VALK_TEST_ASSERT(fn != NULL, "Should compile string literal");

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_codegen_nil_literal(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_nil");
  valk_lval_t *expr = valk_lval_nil();
  LLVMValueRef fn = valk_llvm_compile_toplevel(ctx, expr);
  VALK_TEST_ASSERT(fn != NULL, "Should compile nil");

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_codegen_sym_lookup(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_sym");
  valk_lval_t *expr = valk_lval_sym("x");
  LLVMValueRef fn = valk_llvm_compile_toplevel(ctx, expr);
  VALK_TEST_ASSERT(fn != NULL, "Should compile symbol");

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_codegen_arithmetic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_arith");

  // (+ 1 2)
  valk_lval_t *expr = valk_parse_text("(+ 1 2)");
  VALK_TEST_ASSERT(expr != NULL, "Should parse (+ 1 2)");

  valk_lval_t *first = expr->cons.head;
  LLVMValueRef fn = valk_llvm_compile_toplevel(ctx, first);
  VALK_TEST_ASSERT(fn != NULL, "Should compile (+ 1 2)");

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_codegen_if_expr(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_if");

  valk_lval_t *expr = valk_parse_text("(if 1 42 0)");
  VALK_TEST_ASSERT(expr != NULL, "Should parse if expression");

  valk_lval_t *first = expr->cons.head;
  LLVMValueRef fn = valk_llvm_compile_toplevel(ctx, first);
  VALK_TEST_ASSERT(fn != NULL, "Should compile if expression");

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_codegen_do_expr(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_do");

  valk_lval_t *expr = valk_parse_text("(do 1 2 3)");
  VALK_TEST_ASSERT(expr != NULL, "Should parse do expression");

  LLVMValueRef fn = valk_llvm_compile_toplevel(ctx, expr->cons.head);
  VALK_TEST_ASSERT(fn != NULL, "Should compile do expression");

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_codegen_dump_ir(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_dump");

  valk_lval_t *expr = valk_parse_text("(+ 1 2)");
  valk_llvm_compile_toplevel(ctx, expr->cons.head);

  char *ir = valk_llvm_dump_ir(ctx);
  VALK_TEST_ASSERT(ir != NULL, "Should dump IR");
  VALK_TEST_ASSERT(strstr(ir, "valk_lval_num") != NULL,
    "IR should contain valk_lval_num call");
  VALK_TEST_ASSERT(strstr(ir, "__valk_expr_") != NULL,
    "IR should contain function name");

  LLVMDisposeMessage(ir);
  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_jit_num(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();
  VALK_TEST_ASSERT(jit != NULL, "Should create JIT");

  valk_lval_t *expr = valk_lval_num(42);
  valk_lval_t *result = valk_jit_eval(jit, env, expr);

  VALK_TEST_ASSERT(result != NULL, "JIT should return result");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_string(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();
  VALK_TEST_ASSERT(jit != NULL, "Should create JIT");

  valk_lval_t *expr = valk_lval_str("hello");
  valk_lval_t *result = valk_jit_eval(jit, env, expr);

  VALK_TEST_ASSERT(result != NULL, "JIT should return result");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "hello");

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_arithmetic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();
  VALK_TEST_ASSERT(jit != NULL, "Should create JIT");

  valk_lval_t *result = valk_jit_eval_string(jit, env, "(+ 1 2)");
  VALK_TEST_ASSERT(result != NULL, "JIT should return result");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 3);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_nested_arithmetic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *result = valk_jit_eval_string(jit, env, "(+ (* 3 4) (- 10 5))");
  VALK_TEST_ASSERT(result != NULL, "Should evaluate nested arithmetic");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 17);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_if_true(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *result = valk_jit_eval_string(jit, env, "(if 1 42 0)");
  VALK_TEST_ASSERT(result != NULL, "Should evaluate if-true");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_if_false(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *result = valk_jit_eval_string(jit, env, "(if 0 42 99)");
  VALK_TEST_ASSERT(result != NULL, "Should evaluate if-false");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 99);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_def_and_lookup(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env, "(def {x} 42)");
  valk_lval_t *result = valk_jit_eval_string(jit, env, "x");
  VALK_TEST_ASSERT(result != NULL, "Should look up defined variable");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_do_sequence(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *result = valk_jit_eval_string(jit, env, "(do 1 2 3)");
  VALK_TEST_ASSERT(result != NULL, "Should evaluate do sequence");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 3);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_lambda(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env, "(def {double} (\\ {x} {* x 2}))");
  valk_lval_t *result = valk_jit_eval_string(jit, env, "(double 21)");
  VALK_TEST_ASSERT(result != NULL, "Should call JIT-compiled lambda");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_fun_def(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env, "(def {square} (\\ {x} {* x x}))");
  valk_lval_t *result = valk_jit_eval_string(jit, env, "(square 7)");
  VALK_TEST_ASSERT(result != NULL, "Should call def+lambda function");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 49);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_multiple_exprs(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env, "(def {a} 10)");
  valk_jit_eval_string(jit, env, "(def {b} 20)");
  valk_lval_t *result = valk_jit_eval_string(jit, env, "(+ a b)");

  VALK_TEST_ASSERT(result != NULL, "Should evaluate multiple JIT invocations");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 30);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_jit_recursive_function(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env,
    "(def {fact} (\\ {n} {if (== n 0) {1} {* n (fact (- n 1))}}))");
  valk_lval_t *result = valk_jit_eval_string(jit, env, "(fact 10)");
  VALK_TEST_ASSERT(result != NULL, "Should compute factorial");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 3628800);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_aot_emit_ir(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_aot");
  valk_lval_t *expr = valk_parse_text("(+ 1 2)");
  valk_llvm_compile_toplevel(ctx, expr->cons.head);

  int rc = valk_aot_emit_ir(ctx, "/tmp/valk_test_aot.ll");
  VALK_TEST_ASSERT(rc == 0, "Should emit LLVM IR file");

  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

void test_aot_emit_object(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_aot_obj");
  valk_lval_t *exprs = valk_parse_text("(+ 1 2)");
  valk_llvm_compile_program(ctx, exprs);

  char *err = NULL;
  VALK_TEST_ASSERT(valk_llvm_verify(ctx, &err),
    "Module should verify: %s", err ? err : "");

  int rc = valk_aot_emit_object(ctx, "/tmp/valk_test_aot.o");
  VALK_TEST_ASSERT(rc == 0, "Should emit object file");

  valk_llvm_ctx_free(ctx);
  VALK_PASS();
}

// A body list whose first element is an atom is ONE expression spread
// over the list — `{\ {q} {+ p q}}` is (\ {q} {+ p q}), not three
// statements. Classifying that as fast-safe made the fast variant build
// the returned closure over the AOT root env instead of the call env, so
// the enclosing function's formals came back unbound at runtime.
static valk_lval_t *body_of(const char *src) {
  valk_lval_t *exprs = valk_parse_text(src);
  return exprs->cons.head;
}

void test_fast_safe_rejects_capturing_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(!valk_llvm_body_is_fast_safe(body_of("{\\ {q} {+ p q}}")),
    "body that IS a lambda captures the call env");
  VALK_TEST_ASSERT(!valk_llvm_body_is_fast_safe(body_of("{fn {q} {+ p q}}")),
    "body that IS an fn captures the call env");
  VALK_TEST_ASSERT(!valk_llvm_body_is_fast_safe(body_of("{= {loc} 1}")),
    "body that IS a `=` mutates the call env");
  VALK_TEST_ASSERT(!valk_llvm_body_is_fast_safe(body_of("{def {g} 1}")),
    "body that IS a `def` mutates the env");
  VALK_TEST_ASSERT(
    !valk_llvm_body_is_fast_safe(body_of("{do (= {loc} 1) (\\ {q} {loc})}")),
    "sequence body containing a lambda still rejected");

  VALK_TEST_ASSERT(valk_llvm_body_is_fast_safe(body_of("{+ x 1}")),
    "plain arithmetic body stays fast-safe");
  VALK_TEST_ASSERT(
    valk_llvm_body_is_fast_safe(body_of("{if (== n 0) acc (loop (- n 1) acc)}")),
    "if/tail-call body stays fast-safe");
  VALK_TEST_ASSERT(valk_llvm_body_is_fast_safe(body_of("{do (foo x) (bar x)}")),
    "capture-free sequence body stays fast-safe");

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();

  setenv("VALK_TEST_NO_FORK", "1", 1);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "codegen_num_literal", test_codegen_num_literal);
  valk_testsuite_add_test(suite, "codegen_str_literal", test_codegen_str_literal);
  valk_testsuite_add_test(suite, "codegen_nil_literal", test_codegen_nil_literal);
  valk_testsuite_add_test(suite, "codegen_sym_lookup", test_codegen_sym_lookup);
  valk_testsuite_add_test(suite, "codegen_arithmetic", test_codegen_arithmetic);
  valk_testsuite_add_test(suite, "codegen_if_expr", test_codegen_if_expr);
  valk_testsuite_add_test(suite, "codegen_do_expr", test_codegen_do_expr);
  valk_testsuite_add_test(suite, "codegen_dump_ir", test_codegen_dump_ir);
  valk_testsuite_add_test(suite, "jit_num", test_jit_num);
  valk_testsuite_add_test(suite, "jit_string", test_jit_string);
  valk_testsuite_add_test(suite, "jit_arithmetic", test_jit_arithmetic);
  valk_testsuite_add_test(suite, "jit_nested_arithmetic", test_jit_nested_arithmetic);
  valk_testsuite_add_test(suite, "jit_if_true", test_jit_if_true);
  valk_testsuite_add_test(suite, "jit_if_false", test_jit_if_false);
  valk_testsuite_add_test(suite, "jit_def_and_lookup", test_jit_def_and_lookup);
  valk_testsuite_add_test(suite, "jit_do_sequence", test_jit_do_sequence);
  valk_testsuite_add_test(suite, "jit_lambda", test_jit_lambda);
  valk_testsuite_add_test(suite, "jit_fun_def", test_jit_fun_def);
  valk_testsuite_add_test(suite, "jit_multiple_exprs", test_jit_multiple_exprs);
  valk_testsuite_add_test(suite, "jit_recursive_function", test_jit_recursive_function);
  valk_testsuite_add_test(suite, "aot_emit_ir", test_aot_emit_ir);
  valk_testsuite_add_test(suite, "aot_emit_object", test_aot_emit_object);
  valk_testsuite_add_test(suite, "fast_safe_rejects_capturing_body",
                          test_fast_safe_rejects_capturing_body);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return result;
}
