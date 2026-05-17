#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/gc.h"
#include "../src/vir/vir.h"
#include "../src/llvm/llvm_codegen.h"
#include "../src/llvm/vir_to_llvm.h"

#include <stdio.h>
#include <string.h>

extern vir_func_t *vir_lower_toplevel(vir_builder_t *b, valk_lval_t *expr,
                                      const char *name);
extern void vir_gc_insert_safepoints(vir_module_t *mod);

void test_vir_build_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *mod = vir_module_new("test");
  vir_builder_t *b = vir_builder_new(mod);

  vir_func_t *fn = vir_builder_add_func(b, "test_fn", 1);
  vir_block_t *entry = vir_builder_add_block(b, "entry");
  vir_builder_set_block(b, entry);

  vir_value_t *num = vir_build_const_num(b, 42);
  vir_build_ret(b, num);

  ASSERT_NOT_NULL(fn);
  ASSERT_NOT_NULL(fn->entry);
  ASSERT_EQ(fn->num_params, 1);
  ASSERT_STR_EQ(fn->name, "test_fn");

  vir_builder_free(b);
  vir_module_free(mod);
  VALK_PASS();
}

void test_vir_print(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *mod = vir_module_new("test_print");
  vir_builder_t *b = vir_builder_new(mod);
  vir_func_t *fn = vir_builder_add_func(b, "add_test", 1);
  vir_block_t *entry = vir_builder_add_block(b, "entry");
  vir_builder_set_block(b, entry);

  vir_value_t *env = fn->params[0];
  vir_value_t *plus = vir_build_env_get(b, env, "+");
  vir_value_t *n1 = vir_build_const_num(b, 1);
  vir_value_t *n2 = vir_build_const_num(b, 2);
  vir_value_t *nil = vir_build_const_nil(b);
  vir_value_t *l1 = vir_build_qcons(b, n2, nil);
  vir_value_t *args = vir_build_qcons(b, n1, l1);
  vir_value_t *result = vir_build_call(b, plus, &args, 1);
  vir_build_ret(b, result);

  char buf[4096];
  FILE *f = fmemopen(buf, sizeof(buf), "w");
  vir_print_module(mod, f);
  fclose(f);

  VALK_TEST_ASSERT(strstr(buf, "func @add_test") != NULL,
    "Should print function name");
  VALK_TEST_ASSERT(strstr(buf, "const.num 1") != NULL,
    "Should print const.num");
  VALK_TEST_ASSERT(strstr(buf, "env.get") != NULL,
    "Should print env.get");

  vir_builder_free(b);
  vir_module_free(mod);
  VALK_PASS();
}

void test_vir_if_cfg(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *mod = vir_module_new("test_if");
  vir_builder_t *b = vir_builder_new(mod);
  vir_func_t *fn = vir_builder_add_func(b, "if_test", 1);
  vir_block_t *entry = vir_builder_add_block(b, "entry");
  vir_block_t *then_bb = vir_builder_add_block(b, "then");
  vir_block_t *else_bb = vir_builder_add_block(b, "else");
  vir_block_t *merge_bb = vir_builder_add_block(b, "merge");

  vir_builder_set_block(b, entry);
  vir_value_t *num = vir_build_const_num(b, 1);
  vir_value_t *cond = vir_build_truthy(b, num);
  vir_build_br_if(b, cond, then_bb, else_bb);

  vir_builder_set_block(b, then_bb);
  vir_value_t *t_val = vir_build_const_num(b, 42);
  vir_build_br(b, merge_bb);

  vir_builder_set_block(b, else_bb);
  vir_value_t *e_val = vir_build_const_num(b, 0);
  vir_build_br(b, merge_bb);

  vir_builder_set_block(b, merge_bb);
  vir_value_t *phi = vir_build_phi(b, VIR_TYPE_PTR);
  vir_phi_add_incoming(phi, t_val, then_bb);
  vir_phi_add_incoming(phi, e_val, else_bb);
  vir_build_ret(b, phi);

  ASSERT_EQ(fn->num_blocks, 4);
  ASSERT_EQ(merge_bb->num_preds, 2);

  vir_builder_free(b);
  vir_module_free(mod);
  VALK_PASS();
}

void test_vir_lower_num(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *mod = vir_module_new("test");
  vir_builder_t *b = vir_builder_new(mod);

  valk_lval_t *expr = valk_lval_num(42);
  vir_func_t *fn = vir_lower_toplevel(b, expr, "test_fn");

  ASSERT_NOT_NULL(fn);
  ASSERT_NOT_NULL(fn->entry);
  ASSERT_NOT_NULL(fn->entry->first);
  ASSERT_EQ(fn->entry->first->opcode, VIR_CONST_NUM);

  vir_builder_free(b);
  vir_module_free(mod);
  VALK_PASS();
}

void test_vir_lower_if(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *mod = vir_module_new("test");
  vir_builder_t *b = vir_builder_new(mod);

  valk_lval_t *ast = valk_parse_text("(if 1 42 0)");
  vir_func_t *fn = vir_lower_toplevel(b, ast->cons.head, "test_if");

  ASSERT_NOT_NULL(fn);
  ASSERT_GT(fn->num_blocks, 1);

  vir_builder_free(b);
  vir_module_free(mod);
  VALK_PASS();
}

// VIR_GC_ROOT/UNROOT opcodes and vir_gc_insert_roots IR pass were
// retired alongside the runtime root_stack. The compiler no longer
// emits root tracking; conservative native-stack scanning at safepoints
// (gc_mark.c::scan_thread_native_stack) covers compiled-code lvals
// automatically. The remaining VIR_GC_SAFEPOINT op is exercised by
// test_vir_gc_safepoint_present below.

void test_vir_to_llvm_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *vmod = vir_module_new("test");
  vir_builder_t *b = vir_builder_new(vmod);

  valk_lval_t *ast = valk_parse_text("(+ 1 2)");
  vir_lower_toplevel(b, ast->cons.head, "test_fn");
  vir_gc_insert_safepoints(vmod);

  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("test_llvm");
  vir_to_llvm_module(ctx, vmod);

  char *err = NULL;
  bool ok = valk_llvm_verify(ctx, &err);
  VALK_TEST_ASSERT(ok, "Module should verify: %s", err ? err : "");

  char *ir = valk_llvm_dump_ir(ctx);
  VALK_TEST_ASSERT(strstr(ir, "valk_gc_safepoint_fn") != NULL,
    "IR should contain safepoint call");
  LLVMDisposeMessage(ir);

  valk_llvm_ctx_free(ctx);
  vir_builder_free(b);
  vir_module_free(vmod);
  VALK_PASS();
}

void test_vir_gc_safepoint_present(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *vmod = vir_module_new("gc_test");
  vir_builder_t *b = vir_builder_new(vmod);

  valk_lval_t *ast = valk_parse_text("(do (def {x} 1) (def {y} 2) (+ x y))");
  vir_lower_toplevel(b, ast->cons.head, "gc_fn");
  vir_gc_insert_safepoints(vmod);

  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("gc_llvm");
  vir_to_llvm_module(ctx, vmod);

  char *ir = valk_llvm_dump_ir(ctx);
  // The compiler emits safepoint polls; conservative stack scanning
  // (gc_mark.c::scan_thread_native_stack) handles roots — no IR-level
  // root tracking is emitted any more.
  VALK_TEST_ASSERT(strstr(ir, "valk_gc_safepoint_fn") != NULL,
    "Should have safepoint calls");
  LLVMDisposeMessage(ir);

  valk_llvm_ctx_free(ctx);
  vir_builder_free(b);
  vir_module_free(vmod);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();

  setenv("VALK_TEST_NO_FORK", "1", 1);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "vir_build_basic", test_vir_build_basic);
  valk_testsuite_add_test(suite, "vir_print", test_vir_print);
  valk_testsuite_add_test(suite, "vir_if_cfg", test_vir_if_cfg);
  valk_testsuite_add_test(suite, "vir_lower_num", test_vir_lower_num);
  valk_testsuite_add_test(suite, "vir_lower_if", test_vir_lower_if);
  valk_testsuite_add_test(suite, "vir_to_llvm_basic", test_vir_to_llvm_basic);
  valk_testsuite_add_test(suite, "vir_gc_safepoint_present", test_vir_gc_safepoint_present);

  int result = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return result;
}
