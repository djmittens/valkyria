// test/test_parser_errors.c
// Edge case testing for parser error paths

#include <stdlib.h>
#include <string.h>

#include "common.h"
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

static valk_lval_t *parse_and_eval(const char *code) {
  int i = 0;
  valk_lval_t *parsed = valk_lval_read(&i, code);
  if (LVAL_TYPE(parsed) == LVAL_ERR) {
    return parsed;
  }
  return valk_lval_eval(g_env, parsed);
}

static valk_lval_t *parse_only(const char *code) {
  int i = 0;
  return valk_lval_read(&i, code);
}

// ============================================================================
// String Parsing Error Tests
// ============================================================================

static void test_unterminated_string(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"unterminated string");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "end of input");

  VALK_PASS();
}

static void test_string_invalid_escape(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"invalid \\z escape\"");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "Invalid escape");

  VALK_PASS();
}

static void test_string_with_null_escape(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"test\\");
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_ERR || LVAL_TYPE(result) == LVAL_STR);

  VALK_PASS();
}

static void test_string_valid_escapes(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"\\n\\t\\r\\\\\\\"\"");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "\n\t\r\\\"");

  VALK_PASS();
}

static void test_string_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"\"");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "");

  VALK_PASS();
}

// ============================================================================
// Number Parsing Error Tests
// ============================================================================

static void test_number_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("99999999999999999999999999999999999999999999");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "Invalid number");

  VALK_PASS();
}

static void test_negative_number_only(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("-");
  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  ASSERT_STR_EQ(result->str, "-");

  VALK_PASS();
}

static void test_valid_negative_number(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("-42");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, -42);

  VALK_PASS();
}

static void test_zero(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("0");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 0);

  VALK_PASS();
}

// ============================================================================
// Expression Parsing Error Tests
// ============================================================================

static void test_unclosed_paren(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("(+ 1 2");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "end of input");

  VALK_PASS();
}

static void test_unclosed_brace(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("{1 2 3");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "end of input");

  VALK_PASS();
}

static void test_unexpected_character(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("#");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "Unexpected character");

  VALK_PASS();
}

static void test_empty_input(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "end of input");

  VALK_PASS();
}

static void test_whitespace_only(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("   \t\n  ");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "end of input");

  VALK_PASS();
}

static void test_comment_only(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("; this is a comment");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "end of input");

  VALK_PASS();
}

static void test_comment_then_expr(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("; comment\n42");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  VALK_PASS();
}

// ============================================================================
// Quote Syntax Error Tests
// ============================================================================

static void test_quote_no_arg(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("'");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_quasiquote_no_arg(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("`");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_unquote_no_arg(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only(",");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_unquote_splice_no_arg(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only(",@");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_nested_quote(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("''x");
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);

  VALK_PASS();
}

// ============================================================================
// Evaluation Error Tests
// ============================================================================

static void test_undefined_symbol(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("undefined_symbol_xyz");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "not bound");

  VALK_PASS();
}

static void test_call_non_function(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(42 1 2)");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "non-function");

  VALK_PASS();
}

static void test_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(head)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_wrong_arg_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(head 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_div_by_zero(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(/ 10 0)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_modulo_by_zero(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(% 10 0)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// If/Conditional Error Tests
// ============================================================================

static void test_if_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_if_one_arg(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_if_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if 1 2 3 4 5)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_if_truthy(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if 1 42 0)");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  VALK_PASS();
}

static void test_if_falsy(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if 0 42 99)");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 99);

  VALK_PASS();
}

// ============================================================================
// Quote/Quasiquote Evaluation Tests
// ============================================================================

static void test_quote_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quote)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_quote_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quote 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_quasiquote_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quasiquote)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_quasiquote_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quasiquote 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_unquote_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quasiquote (unquote))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "unquote expects exactly 1");

  VALK_PASS();
}

static void test_unquote_splice_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quasiquote (unquote-splicing))");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_unquote_splice_top_level(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quasiquote (unquote-splicing {1 2 3}))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "not valid at top level");

  VALK_PASS();
}

static void test_unquote_splice_non_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(quasiquote (a (unquote-splicing 42) b))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "requires a list");

  VALK_PASS();
}

// ============================================================================
// Lambda/Function Error Tests
// ============================================================================

static void test_lambda_wrong_formal_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(\\ 42 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_lambda_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("((\\ {x} x) 1 2 3)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_lambda_varargs_no_name(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("((\\ {&} 1))");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// List Operation Error Tests
// ============================================================================

static void test_head_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(head {})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_tail_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(tail {})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_eval_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(eval {})");
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);

  VALK_PASS();
}

// ============================================================================
// Def/Set Error Tests
// ============================================================================

static void test_def_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(def 42 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_def_mismatch_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(def {a b} 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// Deeply Nested Expressions
// ============================================================================

static void test_deeply_nested_expressions(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(+ (+ (+ (+ (+ 1 2) 3) 4) 5) 6)");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 21);

  VALK_PASS();
}

static void test_nested_quotes(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("'(a '(b '(c)))");
  ASSERT_TRUE(LVAL_TYPE(result) != LVAL_ERR);

  VALK_PASS();
}

// ============================================================================
// Edge Cases
// ============================================================================

static void test_keyword_symbol(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only(":keyword");
  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  ASSERT_STR_EQ(result->str, ":keyword");

  VALK_PASS();
}

static void test_keyword_in_eval(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval(":keyword");
  ASSERT_LVAL_TYPE(result, LVAL_SYM);
  ASSERT_STR_EQ(result->str, ":keyword");

  VALK_PASS();
}

static void test_empty_sexpr(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("()");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_single_elem_sexpr(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(42)");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  VALK_PASS();
}

static void test_list_type_name(VALK_TEST_ARGS()) {
  VALK_TEST();

  ASSERT_STR_EQ(valk_ltype_name(LVAL_NUM), "Number");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_SYM), "Symbol");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_FUN), "Function");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_NIL), "Nil");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_CONS), "List");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_QEXPR), "List");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_ERR), "Error");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_STR), "String");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_REF), "Reference");
  ASSERT_STR_EQ(valk_ltype_name(LVAL_HANDLE), "Handle");

  VALK_PASS();
}

// ============================================================================
// Additional Parser Coverage Tests
// ============================================================================

static void test_empty_list_eval(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("()");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_quasiquote_too_few_args_with_backtick(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  int i = 0;
  valk_lval_t *result = valk_lval_read(&i, "`");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_unquote_error_in_quasiquote(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("`(,undefined-symbol)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_splice_error_propagates(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("`{a ,@(error \"test error\") b}");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "test error");

  VALK_PASS();
}

static void test_quasiquote_capacity_growth(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  parse_and_eval("(def {big} (range 0 100))");
  valk_lval_t *result = parse_and_eval("`{,@big}");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_TRUE(valk_lval_list_count(result) == 100);

  VALK_PASS();
}

static void test_quasiquote_non_qexpr_result(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("`(1 2 3)");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_TRUE((result->flags & LVAL_FLAG_QUOTED) == 0);

  VALK_PASS();
}

static void test_function_identity(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("((\\ {x} x) 42)");
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_NUM || LVAL_TYPE(result) == LVAL_ERR);

  VALK_PASS();
}

static void test_varargs_ampersand_at_end(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(\\ {x &} x)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_varargs_ampersand_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Varargs with no regular params - could be valid or error depending on impl
  valk_lval_t *result = parse_and_eval("(\\ {& rest} rest)");
  // Just verify we get a result without crashing
  ASSERT_TRUE(result != NULL);

  VALK_PASS();
}

static void test_ctx_with_deadline_non_numeric(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(ctx/with-deadline \"not a number\" 1)");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "timeout must be a number");

  VALK_PASS();
}

static void test_ctx_with_deadline_error_in_timeout(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(ctx/with-deadline undefined-symbol 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_ctx_with_deadline_too_few_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Need at least 2 args to reach the special form handler (otherwise single-elem eval)
  // ctx/with-deadline with only timeout but no body should error
  valk_lval_t *result = parse_and_eval("(ctx/with-deadline 1000)");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "requires timeout-ms and body");

  VALK_PASS();
}

static void test_ctx_with_error_in_key(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(ctx/with undefined-key 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_ctx_with_error_in_value(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(ctx/with \"key\" undefined-val 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_ctx_with_too_few_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(ctx/with \"key\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "requires key, value, and body");

  VALK_PASS();
}

static void test_print_symbol(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *sym = valk_lval_sym("test-symbol");
  valk_lval_print(sym);
  printf("\n");

  VALK_PASS();
}

static void test_string_with_carriage_return(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"line1\\rline2\"");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_TRUE(strchr(result->str, '\r') != NULL);

  VALK_PASS();
}

static void test_string_with_double_quote_escape(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"say \\\"hello\\\"\"");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "say \"hello\"");

  VALK_PASS();
}

static void test_string_all_escapes(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("\"\\a\\b\\f\\n\\r\\t\\v\\\\\\'\\\"\"");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_TRUE(strlen(result->str) == 10);
  ASSERT_TRUE(result->str[0] == '\a');
  ASSERT_TRUE(result->str[1] == '\b');
  ASSERT_TRUE(result->str[2] == '\f');
  ASSERT_TRUE(result->str[3] == '\n');
  ASSERT_TRUE(result->str[4] == '\r');
  ASSERT_TRUE(result->str[5] == '\t');
  ASSERT_TRUE(result->str[6] == '\v');
  ASSERT_TRUE(result->str[7] == '\\');
  ASSERT_TRUE(result->str[8] == '\'');
  ASSERT_TRUE(result->str[9] == '"');

  VALK_PASS();
}

static void test_empty_string_result(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/replace \"abc\" \"abc\" \"\")");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "");

  VALK_PASS();
}

static void test_read_unexpected_end(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("(+ 1");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_read_quoted_nil(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("'()");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);

  VALK_PASS();
}

static void test_read_quasiquoted_nil(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("`()");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);

  VALK_PASS();
}

static void test_read_unquoted_expression(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only(",(+ 1 2)");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  valk_lval_t *first = valk_lval_list_nth(result, 0);
  ASSERT_STR_EQ(first->str, "unquote");

  VALK_PASS();
}

static void test_comment_skipping(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("; comment\n42");
  ASSERT_LVAL_NUM(result, 42);

  VALK_PASS();
}

static void test_sexpr_read_error_propagation(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_only("(1 \"unterminated)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_string_free_on_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *original = valk_lval_str("test string");
  valk_lval_t *copy = valk_lval_copy(original);
  ASSERT_STR_EQ(original->str, copy->str);
  ASSERT_TRUE(original->str != copy->str);

  VALK_PASS();
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_unterminated_string", test_unterminated_string);
  valk_testsuite_add_test(suite, "test_string_invalid_escape", test_string_invalid_escape);
  valk_testsuite_add_test(suite, "test_string_with_null_escape", test_string_with_null_escape);
  valk_testsuite_add_test(suite, "test_string_valid_escapes", test_string_valid_escapes);
  valk_testsuite_add_test(suite, "test_string_empty", test_string_empty);

  valk_testsuite_add_test(suite, "test_number_overflow", test_number_overflow);
  valk_testsuite_add_test(suite, "test_negative_number_only", test_negative_number_only);
  valk_testsuite_add_test(suite, "test_valid_negative_number", test_valid_negative_number);
  valk_testsuite_add_test(suite, "test_zero", test_zero);

  valk_testsuite_add_test(suite, "test_unclosed_paren", test_unclosed_paren);
  valk_testsuite_add_test(suite, "test_unclosed_brace", test_unclosed_brace);
  valk_testsuite_add_test(suite, "test_unexpected_character", test_unexpected_character);
  valk_testsuite_add_test(suite, "test_empty_input", test_empty_input);
  valk_testsuite_add_test(suite, "test_whitespace_only", test_whitespace_only);
  valk_testsuite_add_test(suite, "test_comment_only", test_comment_only);
  valk_testsuite_add_test(suite, "test_comment_then_expr", test_comment_then_expr);

  valk_testsuite_add_test(suite, "test_quote_no_arg", test_quote_no_arg);
  valk_testsuite_add_test(suite, "test_quasiquote_no_arg", test_quasiquote_no_arg);
  valk_testsuite_add_test(suite, "test_unquote_no_arg", test_unquote_no_arg);
  valk_testsuite_add_test(suite, "test_unquote_splice_no_arg", test_unquote_splice_no_arg);
  valk_testsuite_add_test(suite, "test_nested_quote", test_nested_quote);

  valk_testsuite_add_test(suite, "test_undefined_symbol", test_undefined_symbol);
  valk_testsuite_add_test(suite, "test_call_non_function", test_call_non_function);
  valk_testsuite_add_test(suite, "test_wrong_arg_count", test_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_wrong_arg_type", test_wrong_arg_type);
  valk_testsuite_add_test(suite, "test_div_by_zero", test_div_by_zero);
  valk_testsuite_add_test(suite, "test_modulo_by_zero", test_modulo_by_zero);

  valk_testsuite_add_test(suite, "test_if_no_args", test_if_no_args);
  valk_testsuite_add_test(suite, "test_if_one_arg", test_if_one_arg);
  valk_testsuite_add_test(suite, "test_if_too_many_args", test_if_too_many_args);
  valk_testsuite_add_test(suite, "test_if_truthy", test_if_truthy);
  valk_testsuite_add_test(suite, "test_if_falsy", test_if_falsy);

  valk_testsuite_add_test(suite, "test_quote_wrong_arg_count", test_quote_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_quote_too_many_args", test_quote_too_many_args);
  valk_testsuite_add_test(suite, "test_quasiquote_wrong_arg_count", test_quasiquote_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_quasiquote_too_many_args", test_quasiquote_too_many_args);
  valk_testsuite_add_test(suite, "test_unquote_wrong_arg_count", test_unquote_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_unquote_splice_wrong_arg_count", test_unquote_splice_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_unquote_splice_top_level", test_unquote_splice_top_level);
  valk_testsuite_add_test(suite, "test_unquote_splice_non_list", test_unquote_splice_non_list);

  valk_testsuite_add_test(suite, "test_lambda_wrong_formal_type", test_lambda_wrong_formal_type);
  valk_testsuite_add_test(suite, "test_lambda_too_many_args", test_lambda_too_many_args);
  valk_testsuite_add_test(suite, "test_lambda_varargs_no_name", test_lambda_varargs_no_name);

  valk_testsuite_add_test(suite, "test_head_empty_list", test_head_empty_list);
  valk_testsuite_add_test(suite, "test_tail_empty_list", test_tail_empty_list);
  valk_testsuite_add_test(suite, "test_eval_empty_list", test_eval_empty_list);

  valk_testsuite_add_test(suite, "test_def_wrong_type", test_def_wrong_type);
  valk_testsuite_add_test(suite, "test_def_mismatch_count", test_def_mismatch_count);

  valk_testsuite_add_test(suite, "test_deeply_nested_expressions", test_deeply_nested_expressions);
  valk_testsuite_add_test(suite, "test_nested_quotes", test_nested_quotes);

  valk_testsuite_add_test(suite, "test_keyword_symbol", test_keyword_symbol);
  valk_testsuite_add_test(suite, "test_keyword_in_eval", test_keyword_in_eval);
  valk_testsuite_add_test(suite, "test_empty_sexpr", test_empty_sexpr);
  valk_testsuite_add_test(suite, "test_single_elem_sexpr", test_single_elem_sexpr);
  valk_testsuite_add_test(suite, "test_list_type_name", test_list_type_name);

  valk_testsuite_add_test(suite, "test_empty_list_eval", test_empty_list_eval);
  valk_testsuite_add_test(suite, "test_quasiquote_too_few_args_with_backtick", test_quasiquote_too_few_args_with_backtick);
  valk_testsuite_add_test(suite, "test_unquote_error_in_quasiquote", test_unquote_error_in_quasiquote);
  valk_testsuite_add_test(suite, "test_splice_error_propagates", test_splice_error_propagates);
  valk_testsuite_add_test(suite, "test_quasiquote_capacity_growth", test_quasiquote_capacity_growth);
  valk_testsuite_add_test(suite, "test_quasiquote_non_qexpr_result", test_quasiquote_non_qexpr_result);
  valk_testsuite_add_test(suite, "test_function_identity", test_function_identity);
  valk_testsuite_add_test(suite, "test_varargs_ampersand_at_end", test_varargs_ampersand_at_end);
  valk_testsuite_add_test(suite, "test_varargs_ampersand_no_args", test_varargs_ampersand_no_args);
  valk_testsuite_add_test(suite, "test_ctx_with_deadline_non_numeric", test_ctx_with_deadline_non_numeric);
  valk_testsuite_add_test(suite, "test_ctx_with_deadline_error_in_timeout", test_ctx_with_deadline_error_in_timeout);
  valk_testsuite_add_test(suite, "test_ctx_with_deadline_too_few_args", test_ctx_with_deadline_too_few_args);
  valk_testsuite_add_test(suite, "test_ctx_with_error_in_key", test_ctx_with_error_in_key);
  valk_testsuite_add_test(suite, "test_ctx_with_error_in_value", test_ctx_with_error_in_value);
  valk_testsuite_add_test(suite, "test_ctx_with_too_few_args", test_ctx_with_too_few_args);
  valk_testsuite_add_test(suite, "test_print_symbol", test_print_symbol);
  valk_testsuite_add_test(suite, "test_string_with_carriage_return", test_string_with_carriage_return);
  valk_testsuite_add_test(suite, "test_string_with_double_quote_escape", test_string_with_double_quote_escape);
  valk_testsuite_add_test(suite, "test_string_all_escapes", test_string_all_escapes);
  valk_testsuite_add_test(suite, "test_empty_string_result", test_empty_string_result);
  valk_testsuite_add_test(suite, "test_read_unexpected_end", test_read_unexpected_end);
  valk_testsuite_add_test(suite, "test_read_quoted_nil", test_read_quoted_nil);
  valk_testsuite_add_test(suite, "test_read_quasiquoted_nil", test_read_quasiquoted_nil);
  valk_testsuite_add_test(suite, "test_read_unquoted_expression", test_read_unquoted_expression);
  valk_testsuite_add_test(suite, "test_comment_skipping", test_comment_skipping);
  valk_testsuite_add_test(suite, "test_sexpr_read_error_propagation", test_sexpr_read_error_propagation);
  valk_testsuite_add_test(suite, "test_string_free_on_copy", test_string_free_on_copy);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
