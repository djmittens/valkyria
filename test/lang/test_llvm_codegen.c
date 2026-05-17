#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/llvm/llvm_codegen.h"
#include "../src/llvm/llvm_aot.h"

#include <stdio.h>
#include <string.h>

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
  valk_testsuite_add_test(suite, "aot_emit_ir", test_aot_emit_ir);
  valk_testsuite_add_test(suite, "aot_emit_object", test_aot_emit_object);

  int result = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return result;
}
