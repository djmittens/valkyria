#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/gc.h"
#include "../src/vir/vir.h"
#include "../src/llvm/llvm_codegen.h"
#include "../src/llvm/llvm_jit.h"
#include "../src/llvm/vir_to_llvm.h"

#include <stdio.h>
#include <string.h>

extern vir_func_t *vir_lower_toplevel(vir_builder_t *b, valk_lval_t *expr,
                                      const char *name);
extern void vir_gc_insert_roots(vir_module_t *mod);
extern void vir_gc_insert_safepoints(vir_module_t *mod);

static valk_lenv_t *make_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  return env;
}

static void free_vir_leftovers(vir_module_t *mod) {
  for (vir_func_t *fn = mod->func_list; fn; fn = fn->next) {
    for (u32 i = 0; i < fn->num_params; i++) {
      free(fn->params[i]);
      fn->params[i] = NULL;
    }
    for (vir_block_t *bb = fn->block_list; bb; bb = bb->next) {
      for (vir_value_t *v = bb->first; v; v = v->next) {
        if (v->opcode == VIR_ENV_GET || v->opcode == VIR_ENV_PUT ||
            v->opcode == VIR_ENV_DEF) {
          free(v->str_val);
          v->str_val = NULL;
        }
      }
    }
  }
}

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
  free_vir_leftovers(mod);
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
  free_vir_leftovers(mod);
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
  free_vir_leftovers(mod);
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
  free_vir_leftovers(mod);
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
  free_vir_leftovers(mod);
  vir_module_free(mod);
  VALK_PASS();
}

void test_vir_gc_root_insertion(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *mod = vir_module_new("test");
  vir_builder_t *b = vir_builder_new(mod);

  valk_lval_t *ast = valk_parse_text("(+ 1 2)");
  vir_lower_toplevel(b, ast->cons.head, "test_fn");

  vir_gc_insert_roots(mod);
  vir_gc_insert_safepoints(mod);

  bool has_gc_root = false;
  bool has_gc_safepoint = false;
  vir_func_t *fn = mod->func_list;
  while (fn) {
    vir_block_t *bb = fn->block_list;
    while (bb) {
      vir_value_t *v = bb->first;
      while (v) {
        if (v->opcode == VIR_GC_ROOT) has_gc_root = true;
        if (v->opcode == VIR_GC_SAFEPOINT) has_gc_safepoint = true;
        v = v->next;
      }
      bb = bb->next;
    }
    fn = fn->next;
  }

  ASSERT_TRUE(has_gc_safepoint);
  ASSERT_TRUE(has_gc_root);

  vir_builder_free(b);
  free_vir_leftovers(mod);
  vir_module_free(mod);
  VALK_PASS();
}

void test_vir_to_llvm_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *vmod = vir_module_new("test");
  vir_builder_t *b = vir_builder_new(vmod);

  valk_lval_t *ast = valk_parse_text("(+ 1 2)");
  vir_lower_toplevel(b, ast->cons.head, "test_fn");
  vir_gc_insert_roots(vmod);
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
  free_vir_leftovers(vmod);
  vir_module_free(vmod);
  VALK_PASS();
}

void test_vir_jit_arithmetic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();

  vir_module_t *vmod = vir_module_new("jit_test");
  vir_builder_t *vb = vir_builder_new(vmod);

  valk_lval_t *ast = valk_parse_text("(+ 1 2)");
  vir_lower_toplevel(vb, ast->cons.head, "__jit_fn");
  vir_gc_insert_roots(vmod);
  vir_gc_insert_safepoints(vmod);

  valk_jit_t *jit = valk_jit_new();
  ASSERT_NOT_NULL(jit);

  valk_lval_t *result = valk_jit_eval_string(jit, env, "(+ 1 2)");
  ASSERT_LVAL_NUM(result, 3);

  valk_jit_free(jit);
  vir_builder_free(vb);
  free_vir_leftovers(vmod);
  vir_module_free(vmod);
  VALK_PASS();
}

void test_vir_jit_if(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_lval_t *result = valk_jit_eval_string(jit, env, "(if 1 42 0)");
  ASSERT_LVAL_NUM(result, 42);

  result = valk_jit_eval_string(jit, env, "(if 0 42 99)");
  ASSERT_LVAL_NUM(result, 99);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_vir_jit_recursive(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = make_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, env,
    "(def {fact} (\\ {n} {if (== n 0) {1} {* n (fact (- n 1))}}))");
  valk_lval_t *result = valk_jit_eval_string(jit, env, "(fact 10)");
  ASSERT_LVAL_NUM(result, 3628800);

  valk_jit_free(jit);
  VALK_PASS();
}

void test_vir_gc_safepoint_present(VALK_TEST_ARGS()) {
  VALK_TEST();
  vir_module_t *vmod = vir_module_new("gc_test");
  vir_builder_t *b = vir_builder_new(vmod);

  valk_lval_t *ast = valk_parse_text("(do (def {x} 1) (def {y} 2) (+ x y))");
  vir_lower_toplevel(b, ast->cons.head, "gc_fn");
  vir_gc_insert_roots(vmod);
  vir_gc_insert_safepoints(vmod);

  valk_llvm_ctx_t *ctx = valk_llvm_ctx_new("gc_llvm");
  vir_to_llvm_module(ctx, vmod);

  char *ir = valk_llvm_dump_ir(ctx);
  VALK_TEST_ASSERT(strstr(ir, "valk_gc_safepoint_fn") != NULL,
    "Should have safepoint calls");
  VALK_TEST_ASSERT(strstr(ir, "valk_gc_root_save") != NULL ||
                   strstr(ir, "valk_gc_root_push_fn") != NULL,
    "Should have GC root tracking");
  LLVMDisposeMessage(ir);

  valk_llvm_ctx_free(ctx);
  vir_builder_free(b);
  free_vir_leftovers(vmod);
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
  valk_testsuite_add_test(suite, "vir_gc_root_insertion", test_vir_gc_root_insertion);
  valk_testsuite_add_test(suite, "vir_to_llvm_basic", test_vir_to_llvm_basic);
  valk_testsuite_add_test(suite, "vir_jit_arithmetic", test_vir_jit_arithmetic);
  valk_testsuite_add_test(suite, "vir_jit_if", test_vir_jit_if);
  valk_testsuite_add_test(suite, "vir_jit_recursive", test_vir_jit_recursive);
  valk_testsuite_add_test(suite, "vir_gc_safepoint_present", test_vir_gc_safepoint_present);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return result;
}
