#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "memory.h"
#include "parser.h"
#include "type_env.h"
#include "gc.h"
#include "testing.h"

static valk_lval_t *make_type_form(const char *code) {
  int pos = 0;
  return valk_lval_read(&pos, code);
}

static void test_env_new_free(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  VALK_TEST_ASSERT(env != NULL, "env should not be null");
  VALK_TEST_ASSERT(env->type_count == 0, "type_count should be 0");
  VALK_TEST_ASSERT(env->constructor_count == 0, "constructor_count should be 0");
  valk_type_env_free(env);

  VALK_PASS();
}

static void test_env_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_free(NULL);

  VALK_PASS();
}

static void test_register_sum_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *form = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_lval_t *err = valk_type_env_register(env, form);
  VALK_TEST_ASSERT(err == NULL, "registering Color should succeed");
  VALK_TEST_ASSERT(env->type_count == 1, "should have 1 type");
  VALK_TEST_ASSERT(env->constructor_count == 3, "should have 3 constructors");

  valk_type_decl_t *t = valk_type_env_find_type(env, "Color");
  VALK_TEST_ASSERT(t != NULL, "should find Color type");
  VALK_TEST_ASSERT(t->is_product == false, "Color is not a product type");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_register_product_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *form = make_type_form("(type {Person} {:name Str :age Num})");
  valk_lval_t *err = valk_type_env_register(env, form);
  VALK_TEST_ASSERT(err == NULL, "registering Person should succeed");
  VALK_TEST_ASSERT(env->type_count == 1, "should have 1 type");

  valk_type_decl_t *t = valk_type_env_find_type(env, "Person");
  VALK_TEST_ASSERT(t != NULL, "should find Person type");
  VALK_TEST_ASSERT(t->is_product == true, "Person is a product type");

  valk_constructor_t *ctor = valk_type_env_find_constructor(env, "Person");
  VALK_TEST_ASSERT(ctor != NULL, "should find Person constructor");
  VALK_TEST_ASSERT(ctor->field_count == 2, "Person should have 2 fields, got %llu", ctor->field_count);

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_register_parameterized_type(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *form = make_type_form("(type {Option a} {None} {Some :value a})");
  valk_lval_t *err = valk_type_env_register(env, form);
  VALK_TEST_ASSERT(err == NULL, "registering Option should succeed");

  valk_type_decl_t *t = valk_type_env_find_type(env, "Option");
  VALK_TEST_ASSERT(t != NULL, "should find Option type");
  VALK_TEST_ASSERT(t->param_count == 1, "Option should have 1 type param, got %llu", t->param_count);
  VALK_TEST_ASSERT(strcmp(t->params[0], "a") == 0, "param should be 'a'");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_find_type_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_type_decl_t *t = valk_type_env_find_type(env, "Nonexistent");
  VALK_TEST_ASSERT(t == NULL, "should not find Nonexistent type");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_find_constructor_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_constructor_t *c = valk_type_env_find_constructor(env, "Nonexistent");
  VALK_TEST_ASSERT(c == NULL, "should not find Nonexistent constructor");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_type_for_constructor(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *form = make_type_form("(type {Shape} {Circle :radius Num} {Rect :w Num :h Num})");
  valk_type_env_register(env, form);

  valk_type_decl_t *t = valk_type_env_type_for_constructor(env, "Shape::Circle");
  VALK_TEST_ASSERT(t != NULL, "should find type for Shape::Circle");
  VALK_TEST_ASSERT(strcmp(t->name, "Shape") == 0, "type should be Shape");

  valk_type_decl_t *t2 = valk_type_env_type_for_constructor(env, "Nonexistent");
  VALK_TEST_ASSERT(t2 == NULL, "should not find type for Nonexistent");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_duplicate_type_ignored(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *form1 = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_lval_t *form2 = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_type_env_register(env, form1);
  valk_lval_t *err = valk_type_env_register(env, form2);
  VALK_TEST_ASSERT(err == NULL, "duplicate type should be silently ignored");
  VALK_TEST_ASSERT(env->type_count == 1, "should still have 1 type");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_register_too_few_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *form = make_type_form("(type {Color})");
  valk_lval_t *err = valk_type_env_register(env, form);
  VALK_TEST_ASSERT(err != NULL, "too few args should produce error");
  VALK_TEST_ASSERT(LVAL_TYPE(err) == LVAL_ERR, "should be LVAL_ERR");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_global_env(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_type_env_t *env1 = valk_type_env_global();
  VALK_TEST_ASSERT(env1 != NULL, "global env should not be null");
  valk_type_env_t *env2 = valk_type_env_global();
  VALK_TEST_ASSERT(env1 == env2, "global env should be singleton");

  valk_lval_t *f = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_type_env_register(env1, f);
  VALK_TEST_ASSERT(env1->type_count == 1, "should have 1 type before reset");

  valk_type_env_reset();
  valk_type_env_t *env3 = valk_type_env_global();
  VALK_TEST_ASSERT(env3 != NULL, "new env should not be null after reset");
  VALK_TEST_ASSERT(env3->type_count == 0, "new env should have 0 types after reset");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_expr_type_form(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *form = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_lval_t *result = valk_type_transform_expr(form);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "type form should transform to nil");

  valk_type_env_t *env = valk_type_env_global();
  VALK_TEST_ASSERT(env->type_count == 1, "should have registered Color");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_expr_sig_form(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *form = make_type_form("(sig add {-> Num Num Num})");
  valk_lval_t *result = valk_type_transform_expr(form);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NIL, "sig form should transform to nil");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_expr_passthrough(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *form = make_type_form("(+ 1 2)");
  valk_lval_t *result = valk_type_transform_expr(form);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "non-type expr should pass through");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_batch(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *exprs = valk_parse_text(
    "(type {Color} {Red} {Green} {Blue})\n"
    "(sig add {-> Num Num Num})\n"
    "(+ 1 2)"
  );
  valk_lval_t *result = valk_type_transform(exprs);
  VALK_TEST_ASSERT(result != NULL, "batch transform should not be null");

  valk_type_env_t *env = valk_type_env_global();
  VALK_TEST_ASSERT(env->type_count == 1, "should have registered Color in batch");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_batch_no_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *exprs = valk_parse_text("(+ 1 2)\n(+ 3 4)");
  valk_lval_t *result = valk_type_transform(exprs);
  VALK_TEST_ASSERT(result == exprs, "no types -> return original exprs");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_constructor_call(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_type_transform_expr(type_form);

  valk_lval_t *call = make_type_form("(Red)");
  valk_lval_t *result = valk_type_transform_expr(call);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "Red call should transform to cons");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_accessor(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Person} {:name Str :age Num})");
  valk_type_transform_expr(type_form);

  valk_lval_t *accessor = make_type_form("(Person:name p)");
  valk_lval_t *result = valk_type_transform_expr(accessor);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "accessor should transform to cons");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_match(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Option a} {None} {Some :value a})");
  valk_type_transform_expr(type_form);

  valk_lval_t *match = make_type_form("(match x {(Some :value v) v} {(None) 0})");
  valk_lval_t *result = valk_type_transform_expr(match);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "match should transform to cons");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_match_wildcard(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Option a} {None} {Some :value a})");
  valk_type_transform_expr(type_form);

  valk_lval_t *match = make_type_form("(match x {(Some :value v) v} {_ 0})");
  valk_lval_t *result = valk_type_transform_expr(match);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "match with wildcard should transform");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_match_literal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_type_transform_expr(type_form);

  valk_lval_t *match = make_type_form("(match 1 {1 \"one\"} {2 \"two\"} {_ \"other\"})");
  valk_lval_t *result = valk_type_transform_expr(match);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "match with literals should transform");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_match_string_literal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Color} {Red})");
  valk_type_transform_expr(type_form);

  valk_lval_t *match = make_type_form("(match x {\"hello\" 1} {_ 0})");
  valk_lval_t *result = valk_type_transform_expr(match);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "match with string literal should transform");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_match_positional(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Shape} {Circle :radius Num} {Rect :w Num :h Num})");
  valk_type_transform_expr(type_form);

  valk_lval_t *match = make_type_form("(match s {(Circle r) r} {(Rect w h) (+ w h)})");
  valk_lval_t *result = valk_type_transform_expr(match);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "match with positional patterns should transform");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_match_multi_body(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Option a} {None} {Some :value a})");
  valk_type_transform_expr(type_form);

  valk_lval_t *match = make_type_form("(match x {(Some :value v) (+ v 1) v} {_ 0})");
  valk_lval_t *result = valk_type_transform_expr(match);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "match multi-body clause should transform");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_match_wildcard_skip(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Shape} {Circle :radius Num} {Rect :w Num :h Num})");
  valk_type_transform_expr(type_form);

  valk_lval_t *match = make_type_form("(match s {(Rect _ h) h} {_ 0})");
  valk_lval_t *result = valk_type_transform_expr(match);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "match with _ in positional should skip binding");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_env_free_with_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *f1 = make_type_form("(type {Option a} {None} {Some :value a})");
  valk_type_env_register(env, f1);
  valk_lval_t *f2 = make_type_form("(type {Shape} {Circle :radius Num} {Rect :w Num :h Num})");
  valk_type_env_register(env, f2);

  VALK_TEST_ASSERT(env->type_count == 2, "should have 2 types");
  valk_type_env_free(env);

  VALK_PASS();
}

static void test_type_transform_batch_with_match(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *exprs = valk_parse_text(
    "(type {Option a} {None} {Some :value a})\n"
    "(match x {(Some :value v) v} {(None) 0})"
  );
  valk_lval_t *result = valk_type_transform(exprs);
  VALK_TEST_ASSERT(result != NULL, "batch with match should transform");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "result should be cons");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_quoted_match(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Option a} {None} {Some :value a})");
  valk_type_transform_expr(type_form);

  valk_lval_t *qmatch = make_type_form("{match x {(Some :value v) v} {(None) 0}}");
  valk_lval_t *result = valk_type_transform_expr(qmatch);
  VALK_TEST_ASSERT(result != NULL, "quoted match should transform");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_transform_nested_expr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *type_form = make_type_form("(type {Color} {Red} {Green} {Blue})");
  valk_type_transform_expr(type_form);

  valk_lval_t *nested = make_type_form("(list (Red) (Green))");
  valk_lval_t *result = valk_type_transform_expr(nested);
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS, "nested constructors should transform");

  valk_type_env_reset();
  VALK_PASS();
}

static void test_type_env_reset_no_env(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_type_env_reset();

  VALK_PASS();
}

// Accessing a nonexistent field via Type:field should produce a clear error,
// not silently fall through to a runtime lookup.
static void test_accessor_unknown_field(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_type_transform_expr(make_type_form("(type {Person} {:name Str :age Num})"));

  valk_lval_t *bad = make_type_form("(Person:email p)");
  valk_lval_t *result = valk_type_transform_expr(bad);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR,
    "accessor with unknown field should produce an error");
  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_TEST_ASSERT(strstr(result->str, "email") != NULL,
      "error message should mention the missing field");
  }

  valk_type_env_reset();
  VALK_PASS();
}

// Accessing an unknown constructor via Type:field should produce an error.
static void test_accessor_unknown_constructor(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_lval_t *bad = make_type_form("(Unknown:field p)");
  valk_lval_t *result = valk_type_transform_expr(bad);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_CONS || LVAL_TYPE(result) == LVAL_SYM,
    "unknown constructor should pass through when no types are registered");

  valk_type_env_reset();
  VALK_PASS();
}

// Constructor call with mismatched arity should produce an error.
static void test_constructor_arity_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_type_transform_expr(make_type_form("(type {Point} {:x Num :y Num})"));

  valk_lval_t *bad = make_type_form("(Point 1)");
  valk_lval_t *result = valk_type_transform_expr(bad);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR,
    "constructor call with wrong arity should error");
  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_TEST_ASSERT(strstr(result->str, "Point") != NULL,
      "error should mention the constructor name");
  }

  valk_type_env_reset();
  VALK_PASS();
}

// Accessing an unknown field via var:field (lowercase variable) should error
// when the variable's type is known from a prior binding. This exercises
// resolve_field_access in type_transform_forms.c for PRODUCT types.
static void test_var_field_access_unknown_field(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_type_transform_expr(make_type_form("(type {Person} {:name Str :age Num})"));

  // Bind p to a Person value so the scope knows p's type
  valk_lval_t *bind = make_type_form("(= {p} (Person :name \"Alice\" :age 30))");
  valk_type_transform_expr(bind);

  // Now access an unknown field
  valk_lval_t *bad = make_type_form("p:email");
  valk_lval_t *result = valk_type_transform_expr(bad);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR,
    "var:field with unknown field on known type should error");
  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_TEST_ASSERT(strstr(result->str, "email") != NULL,
      "error message should mention the missing field");
    VALK_TEST_ASSERT(strstr(result->str, "Person") != NULL,
      "error message should mention the type name");
  }

  valk_type_env_reset();
  VALK_PASS();
}

// For SUM types, a variable's type is the type name (e.g. "Shape"), but
// the constructors are qualified (Shape::Circle, Shape::Square). Accessing
// a field that doesn't exist in any constructor should error rather than
// silently fall through to (plist/get). This exercises the sum-type branch
// of resolve_field_access.
static void test_var_field_access_sum_type_unknown_field(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_type_transform_expr(make_type_form(
    "(type {Shape} {Circle :radius Num} {Square :side Num})"));

  // Bind s to a Shape-typed value
  valk_lval_t *bind = make_type_form("(= {s} (Circle :radius 5))");
  valk_type_transform_expr(bind);

  // Access a field that doesn't exist in Circle OR Square
  valk_lval_t *bad = make_type_form("s:volume");
  valk_lval_t *result = valk_type_transform_expr(bad);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR,
    "sum type var:field with unknown field should error");
  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_TEST_ASSERT(strstr(result->str, "volume") != NULL,
      "error message should mention the missing field");
  }

  valk_type_env_reset();
  VALK_PASS();
}

// Keyword-mode constructor call missing a field should produce an error.
static void test_constructor_missing_field(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_reset();
  valk_type_transform_expr(make_type_form("(type {Point} {:x Num :y Num})"));

  valk_lval_t *bad = make_type_form("(Point :x 1)");
  valk_lval_t *result = valk_type_transform_expr(bad);

  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR,
    "constructor with missing field should error");
  if (LVAL_TYPE(result) == LVAL_ERR) {
    VALK_TEST_ASSERT(strstr(result->str, ":y") != NULL,
      "error should name the missing field");
  }

  valk_type_env_reset();
  VALK_PASS();
}

static void test_find_by_module_stripped_name(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();
  valk_lval_t *err = valk_type_env_register(env, make_type_form("(type {m/Color} {Red})"));
  VALK_TEST_ASSERT(err == NULL, "registering m/Color should succeed");

  VALK_TEST_ASSERT(valk_type_env_find_type(env, "Color") != NULL,
                   "short name should find module-prefixed type");
  VALK_TEST_ASSERT(valk_type_env_find_constructor(env, "Color::Red") != NULL,
                   "short name should find module-prefixed constructor");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_register_malformed_type_forms(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();

  valk_lval_t *err = valk_type_env_register(env, make_type_form("(type Red {Blue} {Green})"));
  VALK_TEST_ASSERT(err != NULL, "non-qexpr name should error");

  err = valk_type_env_register(env, make_type_form("(type {T3} Blah {X})"));
  VALK_TEST_ASSERT(err != NULL, "non-qexpr first variant should error");

  err = valk_type_env_register(env, make_type_form("(type {T4} {(X)} {Y})"));
  VALK_TEST_ASSERT(err == NULL, "cons variant head is skipped, not an error");
  VALK_TEST_ASSERT(valk_type_env_find_constructor(env, "T4::Y") != NULL,
                   "later symbol variants still register");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_register_wide_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();

  char form[2048];
  int pos = snprintf(form, sizeof(form), "(type {Wide}");
  for (int i = 0; i < 20; i++)
    pos += snprintf(form + pos, sizeof(form) - pos, " {V%d}", i);
  snprintf(form + pos, sizeof(form) - pos, ")");
  valk_lval_t *err = valk_type_env_register(env, make_type_form(form));
  VALK_TEST_ASSERT(err == NULL, "20-variant type should register");
  VALK_TEST_ASSERT(valk_type_env_find_type(env, "Wide")->constructor_count == 20,
                   "all 20 variants should register");

  pos = snprintf(form, sizeof(form), "(type {BigRec} {");
  for (int i = 0; i < 20; i++)
    pos += snprintf(form + pos, sizeof(form) - pos, "%s:f%d Num", i ? " " : "", i);
  snprintf(form + pos, sizeof(form) - pos, "})");
  err = valk_type_env_register(env, make_type_form(form));
  VALK_TEST_ASSERT(err == NULL, "20-field product type should register");
  VALK_TEST_ASSERT(valk_type_env_find_constructor(env, "BigRec")->field_count == 20,
                   "all 20 fields should register");

  pos = snprintf(form, sizeof(form), "(type {Poly");
  for (int i = 0; i < 20; i++)
    pos += snprintf(form + pos, sizeof(form) - pos, " p%d", i);
  snprintf(form + pos, sizeof(form) - pos, "} {Mk})");
  err = valk_type_env_register(env, make_type_form(form));
  VALK_TEST_ASSERT(err == NULL, "20-param type should register");
  VALK_TEST_ASSERT(valk_type_env_find_type(env, "Poly")->param_count == 20,
                   "all 20 params should register");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_register_sig_basic_and_guards(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();

  valk_type_env_register_sig(env, make_type_form("(sig {f} {-> Num Str})"));
  valk_type_sig_t *sig = valk_type_env_find_sig(env, "f");
  VALK_TEST_ASSERT(sig != NULL, "sig f should register");
  VALK_TEST_ASSERT(sig->param_count == 1, "f takes one param");
  VALK_TEST_ASSERT(strcmp(sig->return_type, "Str") == 0, "f returns Str");

  valk_type_env_register_sig(env, make_type_form("(sig {g})"));
  VALK_TEST_ASSERT(valk_type_env_find_sig(env, "g") == NULL, "too-short sig is ignored");

  valk_type_env_register_sig(env, make_type_form("(sig h {-> Num})"));
  VALK_TEST_ASSERT(valk_type_env_find_sig(env, "h") == NULL, "non-qexpr name is ignored");

  valk_type_env_register_sig(env, make_type_form("(sig {123} {-> Num})"));
  VALK_TEST_ASSERT(env->sig_count == 1, "non-symbol name is ignored");

  valk_type_env_register_sig(env, make_type_form("(sig {i} 42)"));
  VALK_TEST_ASSERT(valk_type_env_find_sig(env, "i") == NULL, "non-qexpr type list is ignored");

  valk_type_env_register_sig(env, make_type_form("(sig {j} {Num Str})"));
  VALK_TEST_ASSERT(valk_type_env_find_sig(env, "j") == NULL, "missing arrow is ignored");

  valk_type_env_register_sig(env, make_type_form("(sig {k} {(x) Num})"));
  VALK_TEST_ASSERT(valk_type_env_find_sig(env, "k") == NULL, "non-symbol arrow is ignored");

  valk_type_env_register_sig(env, make_type_form("(sig {l} {->})"));
  VALK_TEST_ASSERT(valk_type_env_find_sig(env, "l") == NULL, "empty type list is ignored");

  valk_type_env_free(env);
  VALK_PASS();
}

static void test_register_sig_type_exprs(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_type_env_t *env = valk_type_env_new();

  valk_type_env_register_sig(env, make_type_form("(sig {nested} {-> (List Num) Num})"));
  valk_type_sig_t *sig = valk_type_env_find_sig(env, "nested");
  VALK_TEST_ASSERT(sig != NULL, "nested type sig should register");
  VALK_TEST_ASSERT(strcmp(sig->param_types[0], "(List Num)") == 0,
                   "nested type expr should serialize");

  valk_type_env_register_sig(env, make_type_form("(sig {deep} {-> (Result (List Num)) Num})"));
  sig = valk_type_env_find_sig(env, "deep");
  VALK_TEST_ASSERT(sig != NULL, "doubly nested sig should register");
  VALK_TEST_ASSERT(strcmp(sig->param_types[0], "(Result (List Num))") == 0,
                   "doubly nested type expr should serialize");

  valk_type_env_register_sig(env, make_type_form("(sig {odd} {-> 1 Num})"));
  sig = valk_type_env_find_sig(env, "odd");
  VALK_TEST_ASSERT(sig != NULL, "sig with unserializable param still registers");

  valk_type_env_register_sig(env, make_type_form("(sig {amp} {-> & Num Str})"));
  sig = valk_type_env_find_sig(env, "amp");
  VALK_TEST_ASSERT(sig != NULL, "sig with & prefix should register");
  VALK_TEST_ASSERT(sig->param_count == 1, "& is not counted as a param");

  valk_type_env_register_sig(env, make_type_form("(sig {mod/fn} {-> Num Num})"));
  VALK_TEST_ASSERT(valk_type_env_find_sig(env, "fn") != NULL,
                   "short name should find module-prefixed sig");

  char form[4096];
  int pos = snprintf(form, sizeof(form), "(sig {huge} {->");
  for (int i = 0; i < 40; i++)
    pos += snprintf(form + pos, sizeof(form) - pos, " Num");
  snprintf(form + pos, sizeof(form) - pos, "})");
  valk_type_env_register_sig(env, make_type_form(form));
  sig = valk_type_env_find_sig(env, "huge");
  VALK_TEST_ASSERT(sig != NULL, "over-long sig should register truncated");
  VALK_TEST_ASSERT(sig->param_count <= 32, "params should be truncated to the max");

  valk_type_env_free(env);
  VALK_PASS();
}

int main(void) {
  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.allocator = (valk_mem_allocator_t *)heap;

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "env_new_free", test_env_new_free);
  valk_testsuite_add_test(suite, "env_free_null", test_env_free_null);
  valk_testsuite_add_test(suite, "register_sum_type", test_register_sum_type);
  valk_testsuite_add_test(suite, "register_product_type", test_register_product_type);
  valk_testsuite_add_test(suite, "register_parameterized_type", test_register_parameterized_type);
  valk_testsuite_add_test(suite, "find_type_not_found", test_find_type_not_found);
  valk_testsuite_add_test(suite, "find_constructor_not_found", test_find_constructor_not_found);
  valk_testsuite_add_test(suite, "type_for_constructor", test_type_for_constructor);
  valk_testsuite_add_test(suite, "duplicate_type_ignored", test_duplicate_type_ignored);
  valk_testsuite_add_test(suite, "register_too_few_args", test_register_too_few_args);
  valk_testsuite_add_test(suite, "global_env", test_global_env);
  valk_testsuite_add_test(suite, "transform_expr_type_form", test_type_transform_expr_type_form);
  valk_testsuite_add_test(suite, "transform_expr_sig_form", test_type_transform_expr_sig_form);
  valk_testsuite_add_test(suite, "transform_expr_passthrough", test_type_transform_expr_passthrough);
  valk_testsuite_add_test(suite, "transform_batch", test_type_transform_batch);
  valk_testsuite_add_test(suite, "transform_batch_no_types", test_type_transform_batch_no_types);
  valk_testsuite_add_test(suite, "transform_constructor_call", test_type_transform_constructor_call);
  valk_testsuite_add_test(suite, "transform_accessor", test_type_transform_accessor);
  valk_testsuite_add_test(suite, "transform_match", test_type_transform_match);
  valk_testsuite_add_test(suite, "transform_match_wildcard", test_type_transform_match_wildcard);
  valk_testsuite_add_test(suite, "transform_match_literal", test_type_transform_match_literal);
  valk_testsuite_add_test(suite, "transform_match_string_literal", test_type_transform_match_string_literal);
  valk_testsuite_add_test(suite, "transform_match_positional", test_type_transform_match_positional);
  valk_testsuite_add_test(suite, "transform_match_multi_body", test_type_transform_match_multi_body);
  valk_testsuite_add_test(suite, "transform_match_wildcard_skip", test_type_transform_match_wildcard_skip);
  valk_testsuite_add_test(suite, "env_free_with_types", test_env_free_with_types);
  valk_testsuite_add_test(suite, "transform_batch_with_match", test_type_transform_batch_with_match);
  valk_testsuite_add_test(suite, "transform_quoted_match", test_type_transform_quoted_match);
  valk_testsuite_add_test(suite, "transform_nested_expr", test_type_transform_nested_expr);
  valk_testsuite_add_test(suite, "env_reset_no_env", test_type_env_reset_no_env);
  valk_testsuite_add_test(suite, "accessor_unknown_field", test_accessor_unknown_field);
  valk_testsuite_add_test(suite, "accessor_unknown_constructor", test_accessor_unknown_constructor);
  valk_testsuite_add_test(suite, "constructor_arity_mismatch", test_constructor_arity_mismatch);
  valk_testsuite_add_test(suite, "constructor_missing_field", test_constructor_missing_field);
  valk_testsuite_add_test(suite, "var_field_access_unknown_field", test_var_field_access_unknown_field);
  valk_testsuite_add_test(suite, "var_field_access_sum_type_unknown_field", test_var_field_access_sum_type_unknown_field);
  valk_testsuite_add_test(suite, "find_by_module_stripped_name", test_find_by_module_stripped_name);
  valk_testsuite_add_test(suite, "register_malformed_type_forms", test_register_malformed_type_forms);
  valk_testsuite_add_test(suite, "register_wide_types", test_register_wide_types);
  valk_testsuite_add_test(suite, "register_sig_basic_and_guards", test_register_sig_basic_and_guards);
  valk_testsuite_add_test(suite, "register_sig_type_exprs", test_register_sig_type_exprs);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
