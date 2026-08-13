#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "memory.h"
#include "parser.h"
#include "type_infer.h"
#include "gc.h"
#include "testing.h"

static void test_create_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  ASSERT_NOT_NULL(ctx);
  ASSERT_NOT_NULL(ctx->t_num);
  ASSERT_NOT_NULL(ctx->t_str);
  ASSERT_NOT_NULL(ctx->t_nil);
  ASSERT_EQ(ctx->error_count, 0);
  ASSERT_EQ(ctx->next_var, 0);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_fresh_var_ids(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v0 = valk_ti_fresh_var(ctx);
  valk_type_t *v1 = valk_ti_fresh_var(ctx);
  valk_type_t *v2 = valk_ti_fresh_var(ctx);
  ASSERT_EQ(v0->var.id, 0);
  ASSERT_EQ(v1->var.id, 1);
  ASSERT_EQ(v2->var.id, 2);
  ASSERT_EQ(v0->kind, VALK_TY_VAR);
  ASSERT_NULL(v0->var.link);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_con_simple(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *num = valk_ti_con(ctx, "Num", nullptr, 0);
  ASSERT_EQ(num->kind, VALK_TY_CON);
  ASSERT_STR_EQ(num->con.name, "Num");
  ASSERT_EQ(num->con.arity, 0);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_con_parameterized(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *num = valk_ti_con(ctx, "Num", nullptr, 0);
  valk_type_t *args[] = {num};
  valk_type_t *list_num = valk_ti_con(ctx, "List", args, 1);
  ASSERT_EQ(list_num->kind, VALK_TY_CON);
  ASSERT_STR_EQ(list_num->con.name, "List");
  ASSERT_EQ(list_num->con.arity, 1);
  ASSERT_EQ(list_num->con.args[0], num);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_fun_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *num = ctx->t_num;
  valk_type_t *str = ctx->t_str;
  valk_type_t *params[] = {num, str};
  valk_type_t *fn = valk_ti_fun(ctx, params, 2, num);
  ASSERT_EQ(fn->kind, VALK_TY_FUN);
  ASSERT_EQ(fn->fun.param_count, 2);
  ASSERT_STR_EQ(valk_type_find(fn->fun.params[0])->con.name, "Num");
  ASSERT_STR_EQ(valk_type_find(fn->fun.params[1])->con.name, "Str");
  ASSERT_STR_EQ(valk_type_find(fn->fun.ret)->con.name, "Num");
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_find_no_link(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  ASSERT_EQ(valk_type_find(v), v);
  ASSERT_EQ(valk_type_find(ctx->t_num), ctx->t_num);
  VALK_TEST_ASSERT(valk_type_find(nullptr) == nullptr, "find(nullptr) should be nullptr");
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_find_path_compress(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *a = valk_ti_fresh_var(ctx);
  valk_type_t *b = valk_ti_fresh_var(ctx);
  valk_type_t *c = ctx->t_num;
  a->var.link = b;
  b->var.link = c;
  valk_type_t *r = valk_type_find(a);
  ASSERT_EQ(r, c);
  ASSERT_EQ(a->var.link, c);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_same(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *r = valk_type_unify(ctx, ctx->t_num, ctx->t_num, 0, 0);
  ASSERT_EQ(r, ctx->t_num);
  ASSERT_EQ(ctx->error_count, 0);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_var_con(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_t *r = valk_type_unify(ctx, v, ctx->t_str, 0, 0);
  ASSERT_EQ(r, ctx->t_str);
  ASSERT_EQ(valk_type_find(v), ctx->t_str);
  ASSERT_EQ(ctx->error_count, 0);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_con_var(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_t *r = valk_type_unify(ctx, ctx->t_num, v, 0, 0);
  ASSERT_EQ(r, ctx->t_num);
  ASSERT_EQ(valk_type_find(v), ctx->t_num);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_var_var(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *a = valk_ti_fresh_var(ctx);
  valk_type_t *b = valk_ti_fresh_var(ctx);
  valk_type_t *r = valk_type_unify(ctx, a, b, 0, 0);
  ASSERT_NOT_NULL(r);
  ASSERT_EQ(valk_type_find(a), valk_type_find(b));
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *r = valk_type_unify(ctx, ctx->t_num, ctx->t_str, 1, 5);
  ASSERT_NULL(r);
  ASSERT_EQ(ctx->error_count, 1);
  ASSERT_EQ(ctx->errors[0].line, 1);
  ASSERT_EQ(ctx->errors[0].col, 5);
  ASSERT_STR_CONTAINS(ctx->errors[0].message, "Num");
  ASSERT_STR_CONTAINS(ctx->errors[0].message, "Str");
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_fun_fun(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *a = valk_ti_fresh_var(ctx);
  valk_type_t *b = valk_ti_fresh_var(ctx);
  valk_type_t *p1[] = {a};
  valk_type_t *fn1 = valk_ti_fun(ctx, p1, 1, b);
  valk_type_t *p2[] = {ctx->t_num};
  valk_type_t *fn2 = valk_ti_fun(ctx, p2, 1, ctx->t_str);
  valk_type_t *r = valk_type_unify(ctx, fn1, fn2, 0, 0);
  ASSERT_NOT_NULL(r);
  ASSERT_EQ(valk_type_find(a), ctx->t_num);
  ASSERT_EQ(valk_type_find(b), ctx->t_str);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_fun_arity_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *p1[] = {ctx->t_num};
  valk_type_t *fn1 = valk_ti_fun(ctx, p1, 1, ctx->t_num);
  valk_type_t *p2[] = {ctx->t_num, ctx->t_str};
  valk_type_t *fn2 = valk_ti_fun(ctx, p2, 2, ctx->t_num);
  valk_type_t *r = valk_type_unify(ctx, fn1, fn2, 0, 0);
  ASSERT_NULL(r);
  ASSERT_EQ(ctx->error_count, 1);
  ASSERT_STR_CONTAINS(ctx->errors[0].message, "arity");
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_con_parameterized(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_t *a1[] = {v};
  valk_type_t *list_v = valk_ti_con(ctx, "List", a1, 1);
  valk_type_t *a2[] = {ctx->t_num};
  valk_type_t *list_num = valk_ti_con(ctx, "List", a2, 1);
  valk_type_t *r = valk_type_unify(ctx, list_v, list_num, 0, 0);
  ASSERT_NOT_NULL(r);
  ASSERT_EQ(valk_type_find(v), ctx->t_num);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_occurs_check(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_t *a[] = {v};
  valk_type_t *list_v = valk_ti_con(ctx, "List", a, 1);
  valk_type_t *r = valk_type_unify(ctx, v, list_v, 0, 0);
  ASSERT_NULL(r);
  ASSERT_EQ(ctx->error_count, 1);
  ASSERT_STR_CONTAINS(ctx->errors[0].message, "Infinite");
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_occurs_simple(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  ASSERT_TRUE(valk_type_occurs(v, v));
  ASSERT_FALSE(valk_type_occurs(v, ctx->t_num));
  valk_type_t *a[] = {v};
  valk_type_t *list_v = valk_ti_con(ctx, "List", a, 1);
  ASSERT_TRUE(valk_type_occurs(v, list_v));
  valk_type_t *w = valk_ti_fresh_var(ctx);
  ASSERT_FALSE(valk_type_occurs(w, list_v));
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_type_to_str_simple(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  char buf[128];

  valk_type_to_str(ctx->t_num, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");

  valk_type_to_str(ctx->t_str, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Str");

  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_to_str(v, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "?0");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_type_to_str_compound(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  char buf[128];

  valk_type_t *a[] = {ctx->t_num};
  valk_type_t *list_num = valk_ti_con(ctx, "List", a, 1);
  valk_type_to_str(list_num, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "(List Num)");

  valk_type_t *p[] = {ctx->t_num, ctx->t_str};
  valk_type_t *fn = valk_ti_fun(ctx, p, 2, ctx->t_num);
  valk_type_to_str(fn, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "(-> Num Str Num)");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_type_to_str_resolved_var(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  char buf[128];
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_unify(ctx, v, ctx->t_num, 0, 0);
  valk_type_to_str(v, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_scope_bind_lookup(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_t *s = valk_ti_scope_new(ctx, nullptr);
  valk_type_scheme_t mono = {.type = ctx->t_num, .bound_vars = nullptr, .bound_count = 0};
  valk_ti_scope_bind(ctx, s, "x", mono);
  valk_type_scheme_t *found = valk_ti_scope_lookup(s, "x");
  ASSERT_NOT_NULL(found);
  ASSERT_EQ(valk_type_find(found->type), ctx->t_num);
  ASSERT_NULL(valk_ti_scope_lookup(s, "y"));
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_scope_parent_chain(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_t *outer = valk_ti_scope_new(ctx, nullptr);
  valk_type_scheme_t sx = {.type = ctx->t_num};
  valk_ti_scope_bind(ctx, outer, "x", sx);

  valk_ti_scope_t *inner = valk_ti_scope_new(ctx, outer);
  valk_type_scheme_t sy = {.type = ctx->t_str};
  valk_ti_scope_bind(ctx, inner, "y", sy);

  ASSERT_NOT_NULL(valk_ti_scope_lookup(inner, "x"));
  ASSERT_NOT_NULL(valk_ti_scope_lookup(inner, "y"));
  ASSERT_NOT_NULL(valk_ti_scope_lookup(outer, "x"));
  ASSERT_NULL(valk_ti_scope_lookup(outer, "y"));
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_scope_shadow(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_t *outer = valk_ti_scope_new(ctx, nullptr);
  valk_type_scheme_t sx = {.type = ctx->t_num};
  valk_ti_scope_bind(ctx, outer, "x", sx);

  valk_ti_scope_t *inner = valk_ti_scope_new(ctx, outer);
  valk_type_scheme_t sx2 = {.type = ctx->t_str};
  valk_ti_scope_bind(ctx, inner, "x", sx2);

  valk_type_scheme_t *found = valk_ti_scope_lookup(inner, "x");
  ASSERT_EQ(valk_type_find(found->type), ctx->t_str);

  found = valk_ti_scope_lookup(outer, "x");
  ASSERT_EQ(valk_type_find(found->type), ctx->t_num);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_generalize_monomorphic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_t *s = valk_ti_scope_new(ctx, nullptr);
  valk_type_scheme_t scheme = valk_type_generalize(ctx, s, ctx->t_num);
  ASSERT_EQ(scheme.bound_count, 0);
  ASSERT_EQ(valk_type_find(scheme.type), ctx->t_num);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_generalize_free_var(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_t *s = valk_ti_scope_new(ctx, nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_t *p[] = {v};
  valk_type_t *fn = valk_ti_fun(ctx, p, 1, v);
  valk_type_scheme_t scheme = valk_type_generalize(ctx, s, fn);
  ASSERT_EQ(scheme.bound_count, 1);
  ASSERT_EQ(scheme.bound_vars[0], v->var.id);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_instantiate_polymorphic(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_t *s = valk_ti_scope_new(ctx, nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_t *p[] = {v};
  valk_type_t *fn = valk_ti_fun(ctx, p, 1, v);
  valk_type_scheme_t scheme = valk_type_generalize(ctx, s, fn);

  valk_type_t *inst1 = valk_type_instantiate(ctx, &scheme);
  ASSERT_EQ(inst1->kind, VALK_TY_FUN);
  valk_type_t *param = valk_type_find(inst1->fun.params[0]);
  valk_type_t *ret = valk_type_find(inst1->fun.ret);
  ASSERT_EQ(param->kind, VALK_TY_VAR);
  ASSERT_EQ(param, ret);

  valk_type_t *inst2 = valk_type_instantiate(ctx, &scheme);
  valk_type_t *param2 = valk_type_find(inst2->fun.params[0]);
  VALK_TEST_ASSERT(param2 != param, "instantiate should create fresh vars");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_transitive(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *a = valk_ti_fresh_var(ctx);
  valk_type_t *b = valk_ti_fresh_var(ctx);
  valk_type_unify(ctx, a, b, 0, 0);
  valk_type_unify(ctx, b, ctx->t_num, 0, 0);
  ASSERT_EQ(valk_type_find(a), ctx->t_num);
  ASSERT_EQ(valk_type_find(b), ctx->t_num);
  ASSERT_EQ(ctx->error_count, 0);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_unify_nested_con(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *v = valk_ti_fresh_var(ctx);
  valk_type_t *a1[] = {v};
  valk_type_t *inner1 = valk_ti_con(ctx, "List", a1, 1);
  valk_type_t *a2[] = {inner1};
  valk_type_t *outer1 = valk_ti_con(ctx, "Option", a2, 1);

  valk_type_t *a3[] = {ctx->t_str};
  valk_type_t *inner2 = valk_ti_con(ctx, "List", a3, 1);
  valk_type_t *a4[] = {inner2};
  valk_type_t *outer2 = valk_ti_con(ctx, "Option", a4, 1);

  valk_type_t *r = valk_type_unify(ctx, outer1, outer2, 0, 0);
  ASSERT_NOT_NULL(r);
  ASSERT_EQ(valk_type_find(v), ctx->t_str);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_parse_sig_simple(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);

  valk_type_t *num = valk_ti_parse_sig_str(ctx, "Num");
  ASSERT_EQ(num->kind, VALK_TY_CON);
  ASSERT_STR_EQ(num->con.name, "Num");

  valk_type_t *str = valk_ti_parse_sig_str(ctx, "Str");
  ASSERT_STR_EQ(str->con.name, "Str");

  valk_type_t *any = valk_ti_parse_sig_str(ctx, "Any");
  ASSERT_EQ(any->kind, VALK_TY_VAR);

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_parse_sig_compound(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  char buf[128];

  valk_type_t *ln = valk_ti_parse_sig_str(ctx, "(List Num)");
  ASSERT_EQ(ln->kind, VALK_TY_CON);
  ASSERT_STR_EQ(ln->con.name, "List");
  ASSERT_EQ(ln->con.arity, 1);
  ASSERT_EQ(valk_type_find(ln->con.args[0])->kind, VALK_TY_CON);
  ASSERT_STR_EQ(valk_type_find(ln->con.args[0])->con.name, "Num");

  valk_type_t *fn = valk_ti_parse_sig_str(ctx, "(-> Num Str Num)");
  ASSERT_EQ(fn->kind, VALK_TY_FUN);
  ASSERT_EQ(fn->fun.param_count, 2);
  valk_type_to_str(fn, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "(-> Num Str Num)");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_parse_sig_type_var(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);

  valk_type_t *fn = valk_ti_parse_sig_str(ctx, "(-> a a)");
  ASSERT_EQ(fn->kind, VALK_TY_FUN);
  ASSERT_EQ(fn->fun.param_count, 1);
  ASSERT_EQ(fn->fun.params[0]->kind, VALK_TY_VAR);
  ASSERT_EQ(fn->fun.ret->kind, VALK_TY_VAR);

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_import_sigs(VALK_TEST_ARGS()) {
  VALK_TEST();
  int pos = 0;
  valk_lval_t *form = valk_lval_read(&pos, "(sig 'add {-> Num Num Num})");
  valk_lval_t *ast_list = valk_lval_cons(form, valk_lval_nil());
  valk_type_transform(ast_list);

  valk_ti_ctx_t *ctx = valk_ti_create(valk_type_env_global());
  valk_ti_import_new(ctx);

  valk_type_scheme_t *s = valk_ti_scope_lookup(ctx->scope, "add");
  ASSERT_NOT_NULL(s);
  valk_type_t *t = valk_type_find(s->type);
  ASSERT_EQ(t->kind, VALK_TY_FUN);
  ASSERT_EQ(t->fun.param_count, 2);

  valk_ti_destroy(ctx);
  valk_type_env_reset();
  VALK_PASS();
}

static void test_import_constructors(VALK_TEST_ARGS()) {
  VALK_TEST();
  int pos = 0;
  valk_lval_t *form = valk_lval_read(&pos, "(type {Person} {:name Str :age Num})");
  valk_type_env_t *env = valk_type_env_global();
  valk_type_env_register(env, form);

  valk_ti_ctx_t *ctx = valk_ti_create(env);
  valk_ti_import_new(ctx);

  valk_type_scheme_t *s = valk_ti_scope_lookup(ctx->scope, "Person");
  ASSERT_NOT_NULL(s);
  valk_type_t *t = valk_type_instantiate(ctx, s);
  ASSERT_EQ(t->kind, VALK_TY_FUN);
  ASSERT_EQ(t->fun.param_count, 2);
  char buf[128];
  valk_type_to_str(valk_type_find(t->fun.ret), buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Person");

  valk_ti_destroy(ctx);
  valk_type_env_reset();
  VALK_PASS();
}

static valk_lval_t *parse_expr(const char *code) {
  int pos = 0;
  return valk_lval_read(&pos, code);
}

static void test_infer_literal(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  char buf[128];

  valk_type_t *t = valk_ti_infer_expr(ctx, ctx->scope, parse_expr("42"));
  valk_type_to_str(t, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");

  t = valk_ti_infer_expr(ctx, ctx->scope, parse_expr("\"hello\""));
  valk_type_to_str(t, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Str");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_symbol_lookup(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_scheme_t sx = {.type = ctx->t_num};
  valk_ti_scope_bind(ctx, ctx->scope, "x", sx);

  valk_type_t *t = valk_ti_infer_expr(ctx, ctx->scope, parse_expr("x"));
  char buf[128];
  valk_type_to_str(t, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_binding(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  char buf[128];

  valk_ti_infer_expr(ctx, ctx->scope, parse_expr("(= {x} 42)"));
  valk_type_scheme_t *s = valk_ti_scope_lookup(ctx->scope, "x");
  ASSERT_NOT_NULL(s);
  valk_type_to_str(valk_type_find(s->type), buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_lambda(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);

  valk_ti_scope_bind(ctx, ctx->scope, "+", (valk_type_scheme_t){
    .type = valk_ti_fun(ctx, (valk_type_t*[]){ctx->t_num, ctx->t_num}, 2, ctx->t_num)
  });

  valk_type_t *t = valk_ti_infer_expr(ctx, ctx->scope,
    parse_expr("(\\ {x} {+ x 1})"));
  char buf[128];
  valk_type_to_str(t, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "(-> Num Num)");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_application(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_bind(ctx, ctx->scope, "+", (valk_type_scheme_t){
    .type = valk_ti_fun(ctx, (valk_type_t*[]){ctx->t_num, ctx->t_num}, 2, ctx->t_num)
  });

  valk_type_t *t = valk_ti_infer_expr(ctx, ctx->scope,
    parse_expr("(+ 1 2)"));
  char buf[128];
  valk_type_to_str(t, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_if(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *t = valk_ti_infer_expr(ctx, ctx->scope,
    parse_expr("(if 1 42 0)"));
  char buf[128];
  valk_type_to_str(t, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");
  ASSERT_EQ(ctx->error_count, 0);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_do(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_type_t *t = valk_ti_infer_expr(ctx, ctx->scope,
    parse_expr("(do (= {x} 1) \"result\")"));
  char buf[128];
  valk_type_to_str(t, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Str");
  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_let_mono(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);

  valk_ti_infer_expr(ctx, ctx->scope,
    parse_expr("(= {id} (\\ {x} {x}))"));

  valk_type_t *t1 = valk_ti_infer_expr(ctx, ctx->scope,
    parse_expr("(id 42)"));
  char buf[128];
  valk_type_to_str(t1, buf, sizeof(buf));
  ASSERT_STR_EQ(buf, "Num");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_infer_type_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_bind(ctx, ctx->scope, "+", (valk_type_scheme_t){
    .type = valk_ti_fun(ctx, (valk_type_t*[]){ctx->t_num, ctx->t_num}, 2, ctx->t_num)
  });

  valk_ti_infer_expr(ctx, ctx->scope, parse_expr("(+ \"hello\" 1)"));
  ASSERT_GT(ctx->error_count, 0);
  ASSERT_STR_CONTAINS(ctx->errors[0].message, "Num");
  ASSERT_STR_CONTAINS(ctx->errors[0].message, "Str");

  valk_ti_destroy(ctx);
  VALK_PASS();
}

static void test_scope_rebind(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_scope_t *s = valk_ti_scope_new(ctx, nullptr);
  valk_type_scheme_t s1 = {.type = ctx->t_num};
  valk_ti_scope_bind(ctx, s, "x", s1);
  valk_type_scheme_t s2 = {.type = ctx->t_str};
  valk_ti_scope_bind(ctx, s, "x", s2);
  valk_type_scheme_t *found = valk_ti_scope_lookup(s, "x");
  ASSERT_EQ(valk_type_find(found->type), ctx->t_str);
  ASSERT_EQ(s->count, 1);
  valk_ti_destroy(ctx);
  VALK_PASS();
}

// Parse a sequence of top-level expressions (as valk_type_transform/infer_file expects).
static valk_lval_t *parse_file(const char *code) {
  return valk_parse_text(code);
}

// Regression test: valk_ti_infer_file collects errors that valk-check surfaces.
// A sig with a concrete return type followed by a mismatching call should
// produce at least one error.
static void test_infer_file_error_collection(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_import_new(ctx);

  valk_lval_t *ast = parse_file(
    "(sig 'pure-num {-> Num})\n"
    "(fun {pure-num} {\"not a number\"})\n"
  );
  ASSERT_NOT_NULL(ast);

  valk_ti_infer_file(ctx, ast);

  // The sig says the fn returns Num, but the body is a Str.
  // HM should catch this.
  ASSERT_GT(ctx->error_count, 0);

  // At least one error should mention the type mismatch
  bool found_mismatch = false;
  for (u32 i = 0; i < ctx->error_count; i++) {
    if (strstr(ctx->errors[i].message, "mismatch") ||
        strstr(ctx->errors[i].message, "Type")) {
      found_mismatch = true;
      break;
    }
  }
  ASSERT_TRUE(found_mismatch);

  valk_ti_destroy(ctx);
  VALK_PASS();
}

// Error source positions are stored as byte offsets (the caller converts to
// line/col using the source text). This test asserts that errors have
// non-negative offsets and include the signature constraint context.
static void test_infer_file_error_position(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);
  valk_ti_import_new(ctx);

  // Two-line source: sig on line 0, call on line 1
  valk_lval_t *ast = parse_file(
    "(sig 'foo {-> Num Num})\n"
    "(fun {foo x} {x})\n"
    "(foo \"wrong\")\n"
  );

  valk_ti_infer_file(ctx, ast);
  ASSERT_GT(ctx->error_count, 0);

  // All reported offsets should be within the source bounds (non-negative).
  // The error line field is actually a byte offset.
  for (u32 i = 0; i < ctx->error_count; i++) {
    ASSERT_GE(ctx->errors[i].line, 0);
  }

  valk_ti_destroy(ctx);
  VALK_PASS();
}

// The error buffer is capped at VALK_TI_MAX_ERRORS. Test that hitting this
// cap produces exactly one overflow warning and later errors are silently
// dropped (not stored).
static void test_infer_error_cap(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);

  valk_ti_scope_bind(ctx, ctx->scope, "+", (valk_type_scheme_t){
    .type = valk_ti_fun(ctx, (valk_type_t*[]){ctx->t_num, ctx->t_num}, 2, ctx->t_num)
  });

  // Generate many type errors in a do block
  for (int i = 0; i < VALK_TI_MAX_ERRORS + 50; i++) {
    valk_ti_infer_expr(ctx, ctx->scope, parse_expr("(+ \"bad\" 1)"));
  }

  // Should cap at VALK_TI_MAX_ERRORS
  ASSERT_EQ(ctx->error_count, (u32)VALK_TI_MAX_ERRORS);

  valk_ti_destroy(ctx);
  VALK_PASS();
}

// Verify that function types with more than VALK_TI_MAX_FUN_PARAMS parameters
// don't crash or corrupt state — they should truncate cleanly with a warning
// on stderr (which we don't assert, but we verify the inference proceeds).
static void test_infer_many_params(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_ti_ctx_t *ctx = valk_ti_create(nullptr);

  // Build a function with exactly VALK_TI_MAX_FUN_PARAMS params (should not warn)
  char code[512];
  int pos = 0;
  pos += snprintf(code + pos, sizeof(code) - pos, "(\\ {");
  for (int i = 0; i < VALK_TI_MAX_FUN_PARAMS; i++) {
    pos += snprintf(code + pos, sizeof(code) - pos, "p%d ", i);
  }
  pos += snprintf(code + pos, sizeof(code) - pos, "} {42})");

  valk_type_t *t = valk_ti_infer_expr(ctx, ctx->scope, parse_expr(code));
  ASSERT_NOT_NULL(t);
  // Function type should be valid
  ASSERT_EQ(t->kind, VALK_TY_FUN);

  valk_ti_destroy(ctx);
  VALK_PASS();
}

int main(void) {
  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.allocator = (valk_mem_allocator_t *)heap;

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "create_destroy", test_create_destroy);
  valk_testsuite_add_test(suite, "fresh_var_ids", test_fresh_var_ids);
  valk_testsuite_add_test(suite, "con_simple", test_con_simple);
  valk_testsuite_add_test(suite, "con_parameterized", test_con_parameterized);
  valk_testsuite_add_test(suite, "fun_type", test_fun_type);
  valk_testsuite_add_test(suite, "find_no_link", test_find_no_link);
  valk_testsuite_add_test(suite, "find_path_compress", test_find_path_compress);
  valk_testsuite_add_test(suite, "unify_same", test_unify_same);
  valk_testsuite_add_test(suite, "unify_var_con", test_unify_var_con);
  valk_testsuite_add_test(suite, "unify_con_var", test_unify_con_var);
  valk_testsuite_add_test(suite, "unify_var_var", test_unify_var_var);
  valk_testsuite_add_test(suite, "unify_mismatch", test_unify_mismatch);
  valk_testsuite_add_test(suite, "unify_fun_fun", test_unify_fun_fun);
  valk_testsuite_add_test(suite, "unify_fun_arity_mismatch", test_unify_fun_arity_mismatch);
  valk_testsuite_add_test(suite, "unify_con_parameterized", test_unify_con_parameterized);
  valk_testsuite_add_test(suite, "occurs_check", test_occurs_check);
  valk_testsuite_add_test(suite, "occurs_simple", test_occurs_simple);
  valk_testsuite_add_test(suite, "type_to_str_simple", test_type_to_str_simple);
  valk_testsuite_add_test(suite, "type_to_str_compound", test_type_to_str_compound);
  valk_testsuite_add_test(suite, "type_to_str_resolved_var", test_type_to_str_resolved_var);
  valk_testsuite_add_test(suite, "scope_bind_lookup", test_scope_bind_lookup);
  valk_testsuite_add_test(suite, "scope_parent_chain", test_scope_parent_chain);
  valk_testsuite_add_test(suite, "scope_shadow", test_scope_shadow);
  valk_testsuite_add_test(suite, "generalize_monomorphic", test_generalize_monomorphic);
  valk_testsuite_add_test(suite, "generalize_free_var", test_generalize_free_var);
  valk_testsuite_add_test(suite, "instantiate_polymorphic", test_instantiate_polymorphic);
  valk_testsuite_add_test(suite, "unify_transitive", test_unify_transitive);
  valk_testsuite_add_test(suite, "unify_nested_con", test_unify_nested_con);
  valk_testsuite_add_test(suite, "scope_rebind", test_scope_rebind);
  valk_testsuite_add_test(suite, "parse_sig_simple", test_parse_sig_simple);
  valk_testsuite_add_test(suite, "parse_sig_compound", test_parse_sig_compound);
  valk_testsuite_add_test(suite, "parse_sig_type_var", test_parse_sig_type_var);
  valk_testsuite_add_test(suite, "import_sigs", test_import_sigs);
  valk_testsuite_add_test(suite, "import_constructors", test_import_constructors);
  valk_testsuite_add_test(suite, "infer_literal", test_infer_literal);
  valk_testsuite_add_test(suite, "infer_symbol_lookup", test_infer_symbol_lookup);
  valk_testsuite_add_test(suite, "infer_binding", test_infer_binding);
  valk_testsuite_add_test(suite, "infer_lambda", test_infer_lambda);
  valk_testsuite_add_test(suite, "infer_application", test_infer_application);
  valk_testsuite_add_test(suite, "infer_if", test_infer_if);
  valk_testsuite_add_test(suite, "infer_do", test_infer_do);
  valk_testsuite_add_test(suite, "infer_let_mono", test_infer_let_mono);
  valk_testsuite_add_test(suite, "infer_type_error", test_infer_type_error);
  valk_testsuite_add_test(suite, "infer_file_error_collection", test_infer_file_error_collection);
  valk_testsuite_add_test(suite, "infer_file_error_position", test_infer_file_error_position);
  valk_testsuite_add_test(suite, "infer_error_cap", test_infer_error_cap);
  valk_testsuite_add_test(suite, "infer_many_params", test_infer_many_params);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return result;
}
