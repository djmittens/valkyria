#include <stdlib.h>
#include <string.h>

#include "common.h"
#include "diag.h"
#include "memory.h"
#include "parser.h"
#include "gc.h"
#include "testing.h"

static valk_lenv_t *g_env = nullptr;

static void setup_env(void) {
  if (!g_env) {
    g_env = valk_lenv_empty();
    valk_lenv_builtins(g_env);
  }
}

static bool env_has_name(const char *name, void *ctx) {
  valk_lenv_t *env = ctx;
  while (env) {
    for (u64 i = 0; i < env->symbols.count; i++)
      if (strcmp(env->symbols.items[i], name) == 0) return true;
    env = env->parent;
  }
  return false;
}

static bool resolver_always_false(const char *name, void *ctx) {
  (void)name; (void)ctx;
  return false;
}

static valk_diag_list_t validate_text(const char *text) {
  valk_lval_t *ast = valk_parse_text(text);
  valk_name_resolver_t resolver = {.is_known = env_has_name, .ctx = g_env};
  return valk_validate_ast(ast, text, resolver);
}

static int diag_count(const char *text) {
  valk_diag_list_t diags = validate_text(text);
  int n = (int)diags.count;
  valk_diag_free(&diags);
  return n;
}

static void test_aio_let_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/let {(x (+ 1 2))} x)");
  VALK_TEST_ASSERT(n == 0, "aio/let with binding: got %d diags", n);
  VALK_PASS();
}

static void test_aio_let_multiple_bindings(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/let {(x 1) (y 2)} (+ x y))");
  VALK_TEST_ASSERT(n == 0, "aio/let multiple bindings: got %d diags", n);
  VALK_PASS();
}

static void test_aio_let_keyword_skip(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/let {:parallel (x 1) (y 2)} (+ x y))");
  VALK_TEST_ASSERT(n == 0, "aio/let with keyword: got %d diags", n);
  VALK_PASS();
}

static void test_aio_let_undefined_in_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/let {(x 1)} bogus_sym)");
  VALK_TEST_ASSERT(n > 0, "aio/let body with undef sym: got %d diags", n);
  VALK_PASS();
}

static void test_aio_let_non_cons(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/let 42)");
  VALK_TEST_ASSERT(n == 0, "aio/let with non-cons: got %d diags", n);
  VALK_PASS();
}

static void test_aio_do_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/do {(+ 1 2)})");
  VALK_TEST_ASSERT(n == 0, "aio/do basic: got %d diags", n);
  VALK_PASS();
}

static void test_aio_do_arrow_binding(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/do {(x <- (+ 1 2)) x})");
  VALK_TEST_ASSERT(n == 0, "aio/do with <- binding: got %d diags", n);
  VALK_PASS();
}

static void test_aio_do_underscore_discard(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/do {(_ <- (+ 1 2)) 42})");
  VALK_TEST_ASSERT(n == 0, "aio/do with _ discard: got %d diags", n);
  VALK_PASS();
}

static void test_aio_do_undefined(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/do {(x <- 1) bogus_var})");
  VALK_TEST_ASSERT(n > 0, "aio/do body with undef: got %d diags", n);
  VALK_PASS();
}

static void test_aio_do_multi_stmts(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/do {(x <- (+ 1 2)) (y <- (+ x 3)) y})");
  VALK_TEST_ASSERT(n == 0, "aio/do multi stmts: got %d diags", n);
  VALK_PASS();
}

static void test_aio_do_plain_exprs(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/do {(+ 1 2) (+ 3 4)})");
  VALK_TEST_ASSERT(n == 0, "aio/do plain exprs: got %d diags", n);
  VALK_PASS();
}

static void test_aio_do_non_cons(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(aio/do 42)");
  VALK_TEST_ASSERT(n == 0, "aio/do non-cons: got %d diags", n);
  VALK_PASS();
}

static void test_match_wildcard(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(match 1 {_ 0})");
  VALK_TEST_ASSERT(n == 0, "match wildcard: got %d diags", n);
  VALK_PASS();
}

static void test_match_ctor_pattern(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count(
    "(type {Maybe} {Just :val} {Nothing})"
    "(match (Just 1) {(Just v) v} {(Nothing) 0})");
  VALK_TEST_ASSERT(n == 0, "match ctor pattern: got %d diags", n);
  VALK_PASS();
}

static void test_match_sym_pattern(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(match 1 {_ 0})");
  VALK_TEST_ASSERT(n == 0, "match sym pattern: got %d diags", n);
  VALK_PASS();
}

static void test_match_multi_body(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count(
    "(type {Maybe} {Just :val} {Nothing})"
    "(match (Just 1) {(Just v) (+ v 1)} {(Nothing) 0})");
  VALK_TEST_ASSERT(n == 0, "match multi body: got %d diags", n);
  VALK_PASS();
}

static void test_match_non_cons(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(match 42)");
  VALK_TEST_ASSERT(n == 0, "match non-cons: got %d diags", n);
  VALK_PASS();
}

static void test_match_keyword_in_pattern(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count(
    "(type {Result} {Ok :val} {Err :msg})"
    "(match (Ok 1) {(Ok x) x} {(Err :timeout) 0})");
  VALK_TEST_ASSERT(n == 0, "match keyword pattern: got %d diags", n);
  VALK_PASS();
}

static void test_accessor_sym(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("Foo:bar");
  VALK_TEST_ASSERT(n == 0, "Foo:bar accessor sym: got %d diags", n);
  VALK_PASS();
}

static void test_accessor_call(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(Foo:bar 42)");
  VALK_TEST_ASSERT(n == 0, "Foo:bar accessor call: got %d diags", n);
  VALK_PASS();
}

static void test_double_colon_sym_flagged(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("Foo::bar");
  VALK_TEST_ASSERT(n > 0, "Foo::bar should be flagged: got %d diags", n);
  VALK_PASS();
}

static void test_keyword_not_flagged(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count(":bar");
  VALK_TEST_ASSERT(n == 0, ":bar keyword: got %d diags", n);
  VALK_PASS();
}

static void test_def_bare_sym(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(do (def x 10) x)");
  VALK_TEST_ASSERT(n == 0, "def bare sym: got %d diags", n);
  VALK_PASS();
}

static void test_let_bare_sym(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(= x 42)");
  VALK_TEST_ASSERT(n == 0, "= bare sym: got %d diags", n);
  VALK_PASS();
}

static void test_annotated_arrow(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(fun {f x -> Num} {x})");
  VALK_TEST_ASSERT(n == 0, "fun with -> annotation: got %d diags", n);
  VALK_PASS();
}

static void test_annotated_double_colon(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(fun {f x :: Num} {x})");
  VALK_TEST_ASSERT(n == 0, "fun with :: annotation: got %d diags", n);
  VALK_PASS();
}

static void test_undefined_sym(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("bogus_symbol");
  VALK_TEST_ASSERT(n > 0, "undefined sym: got %d diags", n);
  VALK_PASS();
}

static void test_undefined_fn(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  valk_diag_list_t diags = validate_text("(xyznoexist 1 2)");
  bool found = false;
  for (size_t i = 0; i < diags.count; i++) {
    if (strstr(diags.items[i].message, "xyznoexist"))
      found = true;
  }
  valk_diag_free(&diags);
  VALK_TEST_ASSERT(found, "undefined function xyznoexist should be flagged");
  VALK_PASS();
}

static void test_fun_params(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(fun {f x y} {+ x y})");
  VALK_TEST_ASSERT(n == 0, "fun params in scope: got %d diags", n);
  VALK_PASS();
}

static void test_lambda_params(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(\\ {x y} {+ x y})");
  VALK_TEST_ASSERT(n == 0, "lambda params in scope: got %d diags", n);
  VALK_PASS();
}

static void test_type_ctors(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(do (type {Color} {Red} {Green} {Blue}) (Red))");
  VALK_TEST_ASSERT(n == 0, "type ctors in scope: got %d diags", n);
  VALK_PASS();
}

static void test_type_product(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(do (type {Point} {:x :y}) (Point 1 2))");
  VALK_TEST_ASSERT(n == 0, "product type: got %d diags", n);
  VALK_PASS();
}

static void test_type_qualified_ctor(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(do (type {Color} {Red} {Green}) (Color::Red))");
  VALK_TEST_ASSERT(n == 0, "qualified ctor: got %d diags", n);
  VALK_PASS();
}

static void test_type_fields(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count(
    "(do (type {Shape} {Circle :radius} {Rect :w :h})"
    "  (Circle 5) (Rect 10 20))");
  VALK_TEST_ASSERT(n == 0, "sum type fields: got %d diags", n);
  VALK_PASS();
}

static void test_sig_adds_name(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(sig 'myfn {-> Num Num})\n(myfn 1)");
  VALK_TEST_ASSERT(n == 0, "sig adds name: got %d diags", n);
  VALK_PASS();
}

static void test_sig_bare(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(sig myfn {-> Num Num})");
  VALK_TEST_ASSERT(n == 0, "sig bare name: got %d diags", n);
  VALK_PASS();
}

static void test_quoted_data(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("'{unknown stuff here}");
  VALK_TEST_ASSERT(n == 0, "quoted unknown head: got %d diags", n);
  VALK_PASS();
}

static void test_quoted_special_form(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("'{if true {1} {2}}");
  VALK_TEST_ASSERT(n == 0, "quoted special form: got %d diags", n);
  VALK_PASS();
}

static void test_non_sym_head(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("((\\ {x} {x}) 42)");
  VALK_TEST_ASSERT(n == 0, "non-sym head: got %d diags", n);
  VALK_PASS();
}

static void test_number_literal(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("42");
  VALK_TEST_ASSERT(n == 0, "number literal: got %d diags", n);
  VALK_PASS();
}

static void test_string_literal(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("\"hello world\"");
  VALK_TEST_ASSERT(n == 0, "string literal: got %d diags", n);
  VALK_PASS();
}

static void test_empty_input(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("");
  VALK_TEST_ASSERT(n == 0, "empty input: got %d diags", n);
  VALK_PASS();
}

static void test_multiple_undefined(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(+ aaa bbb)");
  VALK_TEST_ASSERT(n == 2, "two undefined syms: got %d diags", n);
  VALK_PASS();
}

static void test_do_local_binding(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(do (= {x} 1) (= {y} (+ x 1)) y)");
  VALK_TEST_ASSERT(n == 0, "do local binding: got %d diags", n);
  VALK_PASS();
}

static void test_nested_fun(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(fun {outer a} {fun {inner b} {+ a b}})");
  VALK_TEST_ASSERT(n == 0, "nested fun: got %d diags", n);
  VALK_PASS();
}

static void test_no_resolver(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  const char *text = "(+ 1 2)";
  valk_lval_t *ast = valk_parse_text(text);
  valk_name_resolver_t resolver = {.is_known = resolver_always_false, .ctx = NULL};
  valk_diag_list_t diags = valk_validate_ast(ast, text, resolver);
  int n = (int)diags.count;
  valk_diag_free(&diags);
  VALK_TEST_ASSERT(n > 0, "always-false resolver should flag +: got %d diags", n);
  VALK_PASS();
}

static void test_comment_skipping(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("; comment\n42");
  VALK_TEST_ASSERT(n == 0, "comment skipping: got %d diags", n);
  VALK_PASS();
}

static void test_varargs(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n = diag_count("(fun {f x & rest} {rest})");
  VALK_TEST_ASSERT(n == 0, "varargs: got %d diags", n);
  VALK_PASS();
}

static void test_diag_error_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  valk_diag_list_t diags = validate_text("bogus1 bogus2");
  int errors = valk_diag_error_count(&diags);
  VALK_TEST_ASSERT(errors == 2, "should have 2 errors, got %d", errors);
  valk_diag_free(&diags);
  VALK_PASS();
}

static void test_diag_fprint(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  valk_diag_list_t diags = validate_text("bogus_sym");
  VALK_TEST_ASSERT(diags.count > 0, "should have at least 1 diag");
  valk_diag_fprint(&diags, "test.valk", "bogus_sym", stderr);
  valk_diag_free(&diags);
  VALK_PASS();
}

static void test_diag_fprint_multiline(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  const char *text = "(+ 1 2)\nbogus_fn";
  valk_diag_list_t diags = validate_text(text);
  VALK_TEST_ASSERT(diags.count > 0, "should have diags");
  valk_diag_fprint(&diags, "test.valk", text, stderr);
  valk_diag_free(&diags);
  VALK_PASS();
}

static void test_diag_fprint_warning(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_diag_list_t diags;
  valk_diag_init(&diags);
  valk_diag_add(&diags, "test warning", 0, 4, VALK_DIAG_WARNING);
  valk_diag_add(&diags, "test info", 0, 4, VALK_DIAG_INFO);
  valk_diag_fprint(&diags, "test.valk", "test", stderr);
  int errors = valk_diag_error_count(&diags);
  VALK_TEST_ASSERT(errors == 0, "warning/info not errors: got %d", errors);
  valk_diag_free(&diags);
  VALK_PASS();
}

static void test_ctx_with_forms(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n1 = diag_count("(ctx/with 1 2 3)");
  VALK_TEST_ASSERT(n1 == 0, "ctx/with: got %d diags", n1);
  int n2 = diag_count("(ctx/with-deadline 1 2)");
  VALK_TEST_ASSERT(n2 == 0, "ctx/with-deadline: got %d diags", n2);
  VALK_PASS();
}

static void test_eval_read_quote_forms(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();
  int n1 = diag_count("(eval 42)");
  VALK_TEST_ASSERT(n1 == 0, "eval: got %d diags", n1);
  int n2 = diag_count("(read \"hello\")");
  VALK_TEST_ASSERT(n2 == 0, "read: got %d diags", n2);
  int n3 = diag_count("(quote 42)");
  VALK_TEST_ASSERT(n3 == 0, "quote: got %d diags", n3);
  VALK_PASS();
}

int main(void) {
  valk_gc_heap_t *heap = valk_gc_heap_create(0);
  valk_thread_ctx.allocator = (valk_mem_allocator_t *)heap;

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "aio_let_basic", test_aio_let_basic);
  valk_testsuite_add_test(suite, "aio_let_multiple_bindings", test_aio_let_multiple_bindings);
  valk_testsuite_add_test(suite, "aio_let_keyword_skip", test_aio_let_keyword_skip);
  valk_testsuite_add_test(suite, "aio_let_undefined_in_body", test_aio_let_undefined_in_body);
  valk_testsuite_add_test(suite, "aio_let_non_cons", test_aio_let_non_cons);
  valk_testsuite_add_test(suite, "aio_do_basic", test_aio_do_basic);
  valk_testsuite_add_test(suite, "aio_do_arrow_binding", test_aio_do_arrow_binding);
  valk_testsuite_add_test(suite, "aio_do_underscore_discard", test_aio_do_underscore_discard);
  valk_testsuite_add_test(suite, "aio_do_undefined", test_aio_do_undefined);
  valk_testsuite_add_test(suite, "aio_do_multi_stmts", test_aio_do_multi_stmts);
  valk_testsuite_add_test(suite, "aio_do_plain_exprs", test_aio_do_plain_exprs);
  valk_testsuite_add_test(suite, "aio_do_non_cons", test_aio_do_non_cons);
  valk_testsuite_add_test(suite, "match_wildcard", test_match_wildcard);
  valk_testsuite_add_test(suite, "match_ctor_pattern", test_match_ctor_pattern);
  valk_testsuite_add_test(suite, "match_sym_pattern", test_match_sym_pattern);
  valk_testsuite_add_test(suite, "match_multi_body", test_match_multi_body);
  valk_testsuite_add_test(suite, "match_non_cons", test_match_non_cons);
  valk_testsuite_add_test(suite, "match_keyword_in_pattern", test_match_keyword_in_pattern);
  valk_testsuite_add_test(suite, "accessor_sym", test_accessor_sym);
  valk_testsuite_add_test(suite, "accessor_call", test_accessor_call);
  valk_testsuite_add_test(suite, "double_colon_sym_flagged", test_double_colon_sym_flagged);
  valk_testsuite_add_test(suite, "keyword_not_flagged", test_keyword_not_flagged);
  valk_testsuite_add_test(suite, "def_bare_sym", test_def_bare_sym);
  valk_testsuite_add_test(suite, "let_bare_sym", test_let_bare_sym);
  valk_testsuite_add_test(suite, "annotated_arrow", test_annotated_arrow);
  valk_testsuite_add_test(suite, "annotated_double_colon", test_annotated_double_colon);
  valk_testsuite_add_test(suite, "undefined_sym", test_undefined_sym);
  valk_testsuite_add_test(suite, "undefined_fn", test_undefined_fn);
  valk_testsuite_add_test(suite, "fun_params", test_fun_params);
  valk_testsuite_add_test(suite, "lambda_params", test_lambda_params);
  valk_testsuite_add_test(suite, "type_ctors", test_type_ctors);
  valk_testsuite_add_test(suite, "type_product", test_type_product);
  valk_testsuite_add_test(suite, "type_qualified_ctor", test_type_qualified_ctor);
  valk_testsuite_add_test(suite, "type_fields", test_type_fields);
  valk_testsuite_add_test(suite, "sig_adds_name", test_sig_adds_name);
  valk_testsuite_add_test(suite, "sig_bare", test_sig_bare);
  valk_testsuite_add_test(suite, "quoted_data", test_quoted_data);
  valk_testsuite_add_test(suite, "quoted_special_form", test_quoted_special_form);
  valk_testsuite_add_test(suite, "non_sym_head", test_non_sym_head);
  valk_testsuite_add_test(suite, "number_literal", test_number_literal);
  valk_testsuite_add_test(suite, "string_literal", test_string_literal);
  valk_testsuite_add_test(suite, "empty_input", test_empty_input);
  valk_testsuite_add_test(suite, "multiple_undefined", test_multiple_undefined);
  valk_testsuite_add_test(suite, "do_local_binding", test_do_local_binding);
  valk_testsuite_add_test(suite, "nested_fun", test_nested_fun);
  valk_testsuite_add_test(suite, "no_resolver", test_no_resolver);
  valk_testsuite_add_test(suite, "comment_skipping", test_comment_skipping);
  valk_testsuite_add_test(suite, "varargs", test_varargs);
  valk_testsuite_add_test(suite, "diag_error_count", test_diag_error_count);
  valk_testsuite_add_test(suite, "diag_fprint", test_diag_fprint);
  valk_testsuite_add_test(suite, "diag_fprint_multiline", test_diag_fprint_multiline);
  valk_testsuite_add_test(suite, "diag_fprint_warning", test_diag_fprint_warning);
  valk_testsuite_add_test(suite, "ctx_with_forms", test_ctx_with_forms);
  valk_testsuite_add_test(suite, "eval_read_quote_forms", test_eval_read_quote_forms);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
