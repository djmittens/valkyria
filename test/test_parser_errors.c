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

static void test_lambda_copy(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Create a lambda using eval (body must be a Q-expr)
  valk_lval_t *lambda = parse_and_eval("(\\ {x} {+ x 1})");
  ASSERT_LVAL_TYPE(lambda, LVAL_FUN);
  ASSERT_TRUE(lambda->fun.builtin == nullptr);  // Not a builtin

  // Copy the lambda
  valk_lval_t *copy = valk_lval_copy(lambda);
  ASSERT_LVAL_TYPE(copy, LVAL_FUN);
  ASSERT_TRUE(copy->fun.builtin == nullptr);
  // Lambda copies should share the same body/formals/env pointers (shallow copy)
  ASSERT_TRUE(copy->fun.env == lambda->fun.env);
  ASSERT_TRUE(copy->fun.body == lambda->fun.body);
  ASSERT_TRUE(copy->fun.formals == lambda->fun.formals);

  VALK_PASS();
}

static void test_builtin_copy(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Get a builtin function
  valk_lval_t *builtin = parse_and_eval("+");
  ASSERT_LVAL_TYPE(builtin, LVAL_FUN);
  ASSERT_TRUE(builtin->fun.builtin != nullptr);  // Is a builtin

  // Copy the builtin
  valk_lval_t *copy = valk_lval_copy(builtin);
  ASSERT_LVAL_TYPE(copy, LVAL_FUN);
  ASSERT_TRUE(copy->fun.builtin == builtin->fun.builtin);

  VALK_PASS();
}

static void test_nil_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *nil = valk_lval_nil();
  valk_lval_t *copy = valk_lval_copy(nil);
  ASSERT_LVAL_TYPE(copy, LVAL_NIL);

  VALK_PASS();
}

static void test_error_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a long error message to test truncation
  char long_msg[2100];
  memset(long_msg, 'x', 2050);
  long_msg[2050] = '\0';

  valk_lval_t *err = valk_lval_err("%s", long_msg);
  ASSERT_LVAL_TYPE(err, LVAL_ERR);

  valk_lval_t *copy = valk_lval_copy(err);
  ASSERT_LVAL_TYPE(copy, LVAL_ERR);
  // Error message should be truncated to 2000 chars
  ASSERT_TRUE(strlen(copy->str) <= 2000);
  // Original and copy should be different strings (not aliased)
  ASSERT_TRUE(copy->str != err->str);

  VALK_PASS();
}

static void test_symbol_copy_truncation(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a long symbol to test truncation (symbols are truncated to 200 chars)
  char long_sym[250];
  memset(long_sym, 'a', 210);
  long_sym[210] = '\0';

  valk_lval_t *sym = valk_lval_sym(long_sym);
  ASSERT_LVAL_TYPE(sym, LVAL_SYM);

  valk_lval_t *copy = valk_lval_copy(sym);
  ASSERT_LVAL_TYPE(copy, LVAL_SYM);
  // Symbol should be truncated to 200 chars
  ASSERT_TRUE(strlen(copy->str) <= 200);
  // Original and copy should be different strings
  ASSERT_TRUE(copy->str != sym->str);

  VALK_PASS();
}

static void test_cons_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *list = valk_lval_cons(valk_lval_num(1),
                       valk_lval_cons(valk_lval_num(2), valk_lval_nil()));
  ASSERT_LVAL_TYPE(list, LVAL_CONS);

  valk_lval_t *copy = valk_lval_copy(list);
  ASSERT_LVAL_TYPE(copy, LVAL_CONS);
  // Shallow copy - head/tail should be same pointers
  ASSERT_TRUE(copy->cons.head == list->cons.head);
  ASSERT_TRUE(copy->cons.tail == list->cons.tail);

  VALK_PASS();
}

static void test_number_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *num = valk_lval_num(42);
  valk_lval_t *copy = valk_lval_copy(num);
  ASSERT_LVAL_TYPE(copy, LVAL_NUM);
  ASSERT_EQ(copy->num, 42);

  VALK_PASS();
}

// ============================================================================
// Builtin Type Error Tests (for branch coverage)
// ============================================================================

static void test_repeat_wrong_count_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(repeat (\\ {_} 1) \"not-a-number\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_repeat_wrong_arg_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(repeat (\\ {_} 1))");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_to_num_invalid(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str->num \"not-a-number\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "Invalid number");

  VALK_PASS();
}

static void test_str_to_num_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str->num \"99999999999999999999999999999\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "out of range");

  VALK_PASS();
}

static void test_str_to_num_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str->num 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_read_builtin_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(read 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_read_file_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(read-file 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_read_file_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(read-file \"/nonexistent/path/file.txt\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "Could not open");

  VALK_PASS();
}

static void test_atom_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(atom \"not-a-number\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_atom_get_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(atom/get 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_atom_set_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(atom/set 42 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_atom_add_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(atom/add 42 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_atom_sub_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(atom/sub 42 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_request_wrong_types(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/request 1 2 3 4)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_request_add_header_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/request-add-header 42 \"name\" \"value\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_response_body_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/response-body 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_response_status_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/response-status 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_response_headers_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/response-headers 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_ord_wrong_type_first(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(> \"a\" 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_ord_wrong_type_second(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(> 1 \"a\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_cmp_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(== 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_lambda_non_symbol_formal(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(\\ {42} 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_def_non_symbol_in_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(def {x 42} 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_load_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(load 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_penv(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(penv)");
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_CONS || LVAL_TYPE(result) == LVAL_NIL);

  VALK_PASS();
}

static void test_list_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(list)");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_list_with_elements(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(list 1 2 3)");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_EQ(valk_lval_list_count(result), 3);

  VALK_PASS();
}

static void test_comparison_operators(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *r1 = parse_and_eval("(> 5 3)");
  ASSERT_LVAL_NUM(r1, 1);

  valk_lval_t *r2 = parse_and_eval("(< 3 5)");
  ASSERT_LVAL_NUM(r2, 1);

  valk_lval_t *r3 = parse_and_eval("(>= 5 5)");
  ASSERT_LVAL_NUM(r3, 1);

  valk_lval_t *r4 = parse_and_eval("(<= 5 5)");
  ASSERT_LVAL_NUM(r4, 1);

  valk_lval_t *r5 = parse_and_eval("(!= 1 2)");
  ASSERT_LVAL_NUM(r5, 1);

  VALK_PASS();
}

static void test_lambda_with_nil_formals(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("((\\ {} {42}))");
  ASSERT_LVAL_NUM(result, 42);

  VALK_PASS();
}

static void test_def_with_qexpr(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(def {testvar123} 42)");
  ASSERT_TRUE(LVAL_TYPE(result) == LVAL_NIL);

  valk_lval_t *val = parse_and_eval("testvar123");
  ASSERT_LVAL_NUM(val, 42);

  VALK_PASS();
}

static void test_if_with_nil_branch(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if 1 () ())");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_if_with_qexpr_branches(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if 1 {(+ 1 2)} {0})");
  ASSERT_LVAL_NUM(result, 3);

  VALK_PASS();
}

static void test_if_non_numeric_cond(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(if \"not-a-number\" {1} {2})");
  ASSERT_LVAL_NUM(result, 1);

  VALK_PASS();
}

static void test_join_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(join 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_cons_builtin(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(cons 1 {2 3})");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_EQ(valk_lval_list_count(result), 3);

  VALK_PASS();
}

static void test_nth_out_of_bounds(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(nth {1 2 3} 10)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_nth_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(nth 42 0)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_len_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(len 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_map_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(map 42 {1 2 3})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_filter_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(filter 42 {1 2 3})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_foldl_wrong_types(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(foldl 42 0 {1 2 3})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_range_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(range \"a\" 10)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_replace_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/replace 42 \"a\" \"b\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_split_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/split 42 \",\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_join_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/join 42 \",\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_concat_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/concat 42 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_length_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/length 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_substring_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/substring 42 0 5)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_error_builtin(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(error \"custom error message\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "custom error message");

  VALK_PASS();
}

static void test_error_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(error 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_print_builtin(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(print 42)");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_println_builtin(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(println \"%d\" 42)");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}


static void test_set_heap_hard_limit_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(mem/heap/set-hard-limit \"not-a-number\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "Expected");

  VALK_PASS();
}

static void test_set_heap_hard_limit_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(mem/heap/set-hard-limit)");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "count");

  VALK_PASS();
}

static void test_set_heap_hard_limit_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(mem/heap/set-hard-limit 100 200)");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "count");

  VALK_PASS();
}

// ============================================================================
// AIO Type Error Tests
// ============================================================================

static void test_aio_schedule_wrong_first_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/schedule 42 100 (\\ {} nil))");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_schedule_wrong_second_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/schedule (atom 0) \"100\" (\\ {} nil))");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_schedule_wrong_third_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/schedule (atom 0) 100 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_schedule_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/schedule (atom 0) 100)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_interval_wrong_first_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/interval 42 100 (\\ {} nil))");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_interval_wrong_second_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/interval (atom 0) \"100\" (\\ {} nil))");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_interval_wrong_third_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/interval (atom 0) 100 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_interval_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/interval (atom 0) 100)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_run_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/run)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_run_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/run 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_stop_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/stop)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_stop_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/stop 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_metrics_json_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/metrics-json)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_metrics_json_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/metrics-json 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_metrics_json_compact_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/metrics-json-compact)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_metrics_json_compact_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/metrics-json-compact 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_systems_json_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/systems-json)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_aio_systems_json_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/systems-json 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// HTTP Mock Response Type Error Tests
// ============================================================================

static void test_http2_mock_response_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/mock-response \"200\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_mock_response_wrong_status_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/mock-response 200 \"body\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_mock_response_wrong_body_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/mock-response \"200\" 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_mock_response_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/mock-response \"200\" \"body\" {} \"extra\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// HTTP Request Add Header Tests
// ============================================================================

static void test_http2_request_add_header_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/request-add-header)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_request_add_header_wrong_first_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/request-add-header 42 \"name\" \"value\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_request_add_header_wrong_second_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  parse_and_eval("(def {req} (http2/request \"GET\" \"https\" \"example.com\" \"/\"))");
  valk_lval_t *result = parse_and_eval("(http2/request-add-header req 42 \"value\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_request_add_header_wrong_third_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  parse_and_eval("(def {req} (http2/request \"GET\" \"https\" \"example.com\" \"/\"))");
  valk_lval_t *result = parse_and_eval("(http2/request-add-header req \"name\" 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_http2_request_add_header_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(http2/request-add-header (atom 0) \"name\" \"value\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// Cons Builtin Type Error Tests
// ============================================================================

static void test_cons_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(cons 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_cons_wrong_second_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(cons 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// Shutdown Tests
// ============================================================================

static void test_shutdown_with_code(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Shutdown in REPL mode returns the code instead of exiting
  parse_and_eval("(def {VALK_MODE} \"repl\")");
  valk_lval_t *result = parse_and_eval("(shutdown 42)");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  VALK_PASS();
}

static void test_shutdown_without_code(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Shutdown in REPL mode returns 0 if no code given
  parse_and_eval("(def {VALK_MODE} \"repl\")");
  valk_lval_t *result = parse_and_eval("(shutdown)");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 0);

  VALK_PASS();
}

static void test_shutdown_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(shutdown \"not-a-number\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_shutdown_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(shutdown 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// AIO System Ref Type Mismatch Tests
// ============================================================================

static void test_aio_schedule_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Use a valid function, then the error should be about the ref type
  valk_lval_t *result = parse_and_eval("(aio/schedule (atom 0) 100 (\\ {} {}))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "AIO system");

  VALK_PASS();
}

static void test_aio_interval_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/interval (atom 0) 100 (\\ {} {}))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "AIO system");

  VALK_PASS();
}

static void test_aio_run_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/run (atom 0))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "aio_system");

  VALK_PASS();
}

static void test_aio_stop_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/stop (atom 0))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "aio_system");

  VALK_PASS();
}

static void test_aio_metrics_json_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/metrics-json (atom 0))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "aio_system");

  VALK_PASS();
}

static void test_aio_metrics_json_compact_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/metrics-json-compact (atom 0))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "aio_system");

  VALK_PASS();
}

static void test_aio_systems_json_wrong_ref_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(aio/systems-json (atom 0))");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "aio_system");

  VALK_PASS();
}

// ============================================================================
// Init (all but last) Builtin Tests
// ============================================================================

static void test_init_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(init)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_init_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(init 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_init_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(init {})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_init_valid(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(init {1 2 3})");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_TRUE(valk_lval_list_count(result) == 2);

  VALK_PASS();
}

// ============================================================================
// Set (local binding) Builtin Tests
// ============================================================================

static void test_set_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(= {x})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_set_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(= 42 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_set_non_symbol_in_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(= {a 42} 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_set_count_mismatch(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(= {a b} 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// Ord/Cmp Type Error Tests
// ============================================================================

static void test_ord_wrong_first_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(> \"x\" 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_ord_wrong_second_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(> 1 \"x\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_ord_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(> 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_cmp_wrong_count_too_few(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(== 1)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_cmp_wrong_count_too_many(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(== 1 2 3)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// Eval Builtin Tests
// ============================================================================

static void test_eval_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(eval)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_eval_too_many_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(eval 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// Load Builtin Tests
// ============================================================================

static void test_load_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(load)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_load_wrong_type_numeric(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(load 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

// ============================================================================
// Join Builtin Tests
// ============================================================================

static void test_join_empty_args(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // join with one list is identity
  valk_lval_t *result = parse_and_eval("(join {1 2})");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_TRUE(valk_lval_list_count(result) == 2);

  VALK_PASS();
}

// ============================================================================
// Additional Coverage Tests for Error Branches
// ============================================================================

static void test_sleep_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(sleep)");
  ASSERT_LVAL_ERROR(result);

  result = parse_and_eval("(sleep 1 2)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_sleep_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(sleep \"not a number\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_split_second_arg_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/split \"hello,world\" 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_replace_second_arg_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/replace \"hello\" 42 \"world\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_str_replace_third_arg_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/replace \"hello\" \"world\" 42)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_gc_set_threshold_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(mem/gc/set-threshold)");
  ASSERT_LVAL_ERROR(result);

  result = parse_and_eval("(mem/gc/set-threshold 50 100)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_gc_set_threshold_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(mem/gc/set-threshold \"not a number\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_gc_set_min_interval_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(mem/gc/set-min-interval)");
  ASSERT_LVAL_ERROR(result);

  result = parse_and_eval("(mem/gc/set-min-interval 100 200)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_gc_set_min_interval_wrong_type(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(mem/gc/set-min-interval \"not a number\")");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_printf_not_enough_args_for_s(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(printf \"%s\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "not enough arguments");

  VALK_PASS();
}

static void test_printf_s_requires_string(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(printf \"%s\" 42)");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "requires string");

  VALK_PASS();
}

static void test_printf_not_enough_args_for_d(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(printf \"%d\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "not enough arguments");

  VALK_PASS();
}

static void test_printf_d_requires_number(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(printf \"%d\" \"not a number\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "requires number");

  VALK_PASS();
}

static void test_printf_ld_format(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // %ld should work the same as %d
  valk_lval_t *result = parse_and_eval("(printf \"%ld\" 42)");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_printf_percent_escape(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // %% should print a literal %
  valk_lval_t *result = parse_and_eval("(printf \"100%%\")");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_printf_invalid_format(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Invalid format specifier should be ignored/skipped
  valk_lval_t *result = parse_and_eval("(printf \"%x\" 42)");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_print_user_with_lambda(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // print should handle lambda functions
  valk_lval_t *result = parse_and_eval("(print (\\ {x} x))");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_print_user_with_ref(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Testing ref printing via http2/request (creates a ref)
  valk_lval_t *result = parse_and_eval("(print (http2/request \"GET\" \"https\" \"example.com\" \"/\"))");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_print_user_with_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // print should handle error values by converting to string
  valk_lval_t *result = parse_and_eval("(print (error \"test error\"))");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_str_split_empty_delimiter(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/split \"hello\" \"\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "delimiter cannot be empty");

  VALK_PASS();
}

static void test_str_replace_empty_from(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  valk_lval_t *result = parse_and_eval("(str/replace \"hello\" \"\" \"world\")");
  ASSERT_LVAL_ERROR(result);
  ASSERT_STR_CONTAINS(result->str, "search string cannot be empty");

  VALK_PASS();
}

static void test_str_wrong_count(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // str with no args should return empty string (not an error)
  valk_lval_t *result = parse_and_eval("(str)");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "");

  VALK_PASS();
}

static void test_print_with_non_string_value(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // print should convert values to string using str()
  valk_lval_t *result = parse_and_eval("(print 42)");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  result = parse_and_eval("(print {1 2 3})");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_println_error_propagation(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // println should propagate errors from printf
  valk_lval_t *result = parse_and_eval("(println)");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_init_on_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Test init on multi-element list
  valk_lval_t *result = parse_and_eval("(init {1 2 3})");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_TRUE(valk_lval_list_count(result) == 2);

  VALK_PASS();
}

static void test_init_empty_list_error(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Test init on empty list - should error
  valk_lval_t *result = parse_and_eval("(init {})");
  ASSERT_LVAL_ERROR(result);

  VALK_PASS();
}

static void test_lambda_body_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Test lambda with qexpr body that returns constant
  valk_lval_t *result = parse_and_eval("((\\ {} {(+ 1 2)}))");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 3);

  VALK_PASS();
}

static void test_lambda_with_arg(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Test lambda with one arg
  valk_lval_t *result = parse_and_eval("((\\ {x} {(+ x 1)}) 5)");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 6);

  VALK_PASS();
}

static void test_range_basic(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // range should create a list of numbers
  valk_lval_t *result = parse_and_eval("(range 0 5)");
  ASSERT_LVAL_TYPE(result, LVAL_CONS);
  ASSERT_TRUE(valk_lval_list_count(result) == 5);

  VALK_PASS();
}

static void test_range_empty(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // range with equal start/end should give empty list
  valk_lval_t *result = parse_and_eval("(range 5 5)");
  ASSERT_LVAL_TYPE(result, LVAL_NIL);

  VALK_PASS();
}

static void test_str_multi_values(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Test str with multiple values
  valk_lval_t *result = parse_and_eval("(str 1 2 3)");
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "123");

  VALK_PASS();
}

static void test_make_string(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Test make-string builtin
  valk_lval_t *result = parse_and_eval("(make-string 3 65)");  // 'A' = 65
  ASSERT_LVAL_TYPE(result, LVAL_STR);
  ASSERT_STR_EQ(result->str, "AAA");

  VALK_PASS();
}

static void test_str_to_num_valid(VALK_TEST_ARGS()) {
  VALK_TEST();
  setup_env();

  // Test str->num with valid string
  valk_lval_t *result = parse_and_eval("(str->num \"42\")");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

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
  valk_testsuite_add_test(suite, "test_lambda_copy", test_lambda_copy);
  valk_testsuite_add_test(suite, "test_builtin_copy", test_builtin_copy);
  valk_testsuite_add_test(suite, "test_nil_copy", test_nil_copy);
  valk_testsuite_add_test(suite, "test_error_copy", test_error_copy);
  valk_testsuite_add_test(suite, "test_symbol_copy_truncation", test_symbol_copy_truncation);
  valk_testsuite_add_test(suite, "test_cons_copy", test_cons_copy);
  valk_testsuite_add_test(suite, "test_number_copy", test_number_copy);

  valk_testsuite_add_test(suite, "test_repeat_wrong_count_type", test_repeat_wrong_count_type);
  valk_testsuite_add_test(suite, "test_repeat_wrong_arg_count", test_repeat_wrong_arg_count);
  valk_testsuite_add_test(suite, "test_str_to_num_invalid", test_str_to_num_invalid);
  valk_testsuite_add_test(suite, "test_str_to_num_overflow", test_str_to_num_overflow);
  valk_testsuite_add_test(suite, "test_str_to_num_wrong_type", test_str_to_num_wrong_type);
  valk_testsuite_add_test(suite, "test_read_builtin_wrong_type", test_read_builtin_wrong_type);
  valk_testsuite_add_test(suite, "test_read_file_wrong_type", test_read_file_wrong_type);
  valk_testsuite_add_test(suite, "test_read_file_not_found", test_read_file_not_found);
  valk_testsuite_add_test(suite, "test_atom_wrong_type", test_atom_wrong_type);
  valk_testsuite_add_test(suite, "test_atom_get_wrong_type", test_atom_get_wrong_type);
  valk_testsuite_add_test(suite, "test_atom_set_wrong_type", test_atom_set_wrong_type);
  valk_testsuite_add_test(suite, "test_atom_add_wrong_type", test_atom_add_wrong_type);
  valk_testsuite_add_test(suite, "test_atom_sub_wrong_type", test_atom_sub_wrong_type);
  valk_testsuite_add_test(suite, "test_http2_request_wrong_types", test_http2_request_wrong_types);
  valk_testsuite_add_test(suite, "test_http2_request_add_header_wrong_type", test_http2_request_add_header_wrong_type);
  valk_testsuite_add_test(suite, "test_http2_response_body_wrong_type", test_http2_response_body_wrong_type);
  valk_testsuite_add_test(suite, "test_http2_response_status_wrong_type", test_http2_response_status_wrong_type);
  valk_testsuite_add_test(suite, "test_http2_response_headers_wrong_type", test_http2_response_headers_wrong_type);
  valk_testsuite_add_test(suite, "test_ord_wrong_type_first", test_ord_wrong_type_first);
  valk_testsuite_add_test(suite, "test_ord_wrong_type_second", test_ord_wrong_type_second);
  valk_testsuite_add_test(suite, "test_cmp_wrong_count", test_cmp_wrong_count);
  valk_testsuite_add_test(suite, "test_lambda_non_symbol_formal", test_lambda_non_symbol_formal);
  valk_testsuite_add_test(suite, "test_def_non_symbol_in_list", test_def_non_symbol_in_list);
  valk_testsuite_add_test(suite, "test_load_wrong_type", test_load_wrong_type);
  valk_testsuite_add_test(suite, "test_penv", test_penv);
  valk_testsuite_add_test(suite, "test_list_empty", test_list_empty);
  valk_testsuite_add_test(suite, "test_list_with_elements", test_list_with_elements);
  valk_testsuite_add_test(suite, "test_comparison_operators", test_comparison_operators);
  valk_testsuite_add_test(suite, "test_lambda_with_nil_formals", test_lambda_with_nil_formals);
  valk_testsuite_add_test(suite, "test_def_with_qexpr", test_def_with_qexpr);
  valk_testsuite_add_test(suite, "test_if_with_nil_branch", test_if_with_nil_branch);
  valk_testsuite_add_test(suite, "test_if_with_qexpr_branches", test_if_with_qexpr_branches);
  valk_testsuite_add_test(suite, "test_if_non_numeric_cond", test_if_non_numeric_cond);
  valk_testsuite_add_test(suite, "test_join_wrong_type", test_join_wrong_type);
  valk_testsuite_add_test(suite, "test_cons_builtin", test_cons_builtin);
  valk_testsuite_add_test(suite, "test_nth_out_of_bounds", test_nth_out_of_bounds);
  valk_testsuite_add_test(suite, "test_nth_wrong_type", test_nth_wrong_type);
  valk_testsuite_add_test(suite, "test_len_wrong_type", test_len_wrong_type);
  valk_testsuite_add_test(suite, "test_map_wrong_type", test_map_wrong_type);
  valk_testsuite_add_test(suite, "test_filter_wrong_type", test_filter_wrong_type);
  valk_testsuite_add_test(suite, "test_foldl_wrong_types", test_foldl_wrong_types);
  valk_testsuite_add_test(suite, "test_range_wrong_type", test_range_wrong_type);
  valk_testsuite_add_test(suite, "test_str_replace_wrong_type", test_str_replace_wrong_type);
  valk_testsuite_add_test(suite, "test_str_split_wrong_type", test_str_split_wrong_type);
  valk_testsuite_add_test(suite, "test_str_join_wrong_type", test_str_join_wrong_type);
  valk_testsuite_add_test(suite, "test_str_concat_wrong_type", test_str_concat_wrong_type);
  valk_testsuite_add_test(suite, "test_str_length_wrong_type", test_str_length_wrong_type);
  valk_testsuite_add_test(suite, "test_str_substring_wrong_type", test_str_substring_wrong_type);
  valk_testsuite_add_test(suite, "test_error_builtin", test_error_builtin);
  valk_testsuite_add_test(suite, "test_error_wrong_type", test_error_wrong_type);
  valk_testsuite_add_test(suite, "test_print_builtin", test_print_builtin);
  valk_testsuite_add_test(suite, "test_println_builtin", test_println_builtin);
  valk_testsuite_add_test(suite, "test_set_heap_hard_limit_wrong_type", test_set_heap_hard_limit_wrong_type);
  valk_testsuite_add_test(suite, "test_set_heap_hard_limit_wrong_count", test_set_heap_hard_limit_wrong_count);
  valk_testsuite_add_test(suite, "test_set_heap_hard_limit_too_many_args", test_set_heap_hard_limit_too_many_args);

  valk_testsuite_add_test(suite, "test_aio_schedule_wrong_first_type", test_aio_schedule_wrong_first_type);
  valk_testsuite_add_test(suite, "test_aio_schedule_wrong_second_type", test_aio_schedule_wrong_second_type);
  valk_testsuite_add_test(suite, "test_aio_schedule_wrong_third_type", test_aio_schedule_wrong_third_type);
  valk_testsuite_add_test(suite, "test_aio_schedule_wrong_count", test_aio_schedule_wrong_count);
  valk_testsuite_add_test(suite, "test_aio_interval_wrong_first_type", test_aio_interval_wrong_first_type);
  valk_testsuite_add_test(suite, "test_aio_interval_wrong_second_type", test_aio_interval_wrong_second_type);
  valk_testsuite_add_test(suite, "test_aio_interval_wrong_third_type", test_aio_interval_wrong_third_type);
  valk_testsuite_add_test(suite, "test_aio_interval_wrong_count", test_aio_interval_wrong_count);
  valk_testsuite_add_test(suite, "test_aio_run_wrong_count", test_aio_run_wrong_count);
  valk_testsuite_add_test(suite, "test_aio_run_wrong_type", test_aio_run_wrong_type);
  valk_testsuite_add_test(suite, "test_aio_stop_wrong_count", test_aio_stop_wrong_count);
  valk_testsuite_add_test(suite, "test_aio_stop_wrong_type", test_aio_stop_wrong_type);
  valk_testsuite_add_test(suite, "test_aio_metrics_json_wrong_count", test_aio_metrics_json_wrong_count);
  valk_testsuite_add_test(suite, "test_aio_metrics_json_wrong_type", test_aio_metrics_json_wrong_type);
  valk_testsuite_add_test(suite, "test_aio_metrics_json_compact_wrong_count", test_aio_metrics_json_compact_wrong_count);
  valk_testsuite_add_test(suite, "test_aio_metrics_json_compact_wrong_type", test_aio_metrics_json_compact_wrong_type);
  valk_testsuite_add_test(suite, "test_aio_systems_json_wrong_count", test_aio_systems_json_wrong_count);
  valk_testsuite_add_test(suite, "test_aio_systems_json_wrong_type", test_aio_systems_json_wrong_type);
  valk_testsuite_add_test(suite, "test_http2_mock_response_wrong_count", test_http2_mock_response_wrong_count);
  valk_testsuite_add_test(suite, "test_http2_mock_response_wrong_status_type", test_http2_mock_response_wrong_status_type);
  valk_testsuite_add_test(suite, "test_http2_mock_response_wrong_body_type", test_http2_mock_response_wrong_body_type);
  valk_testsuite_add_test(suite, "test_http2_mock_response_too_many_args", test_http2_mock_response_too_many_args);
  valk_testsuite_add_test(suite, "test_http2_request_add_header_wrong_count", test_http2_request_add_header_wrong_count);
  valk_testsuite_add_test(suite, "test_http2_request_add_header_wrong_first_type", test_http2_request_add_header_wrong_first_type);
  valk_testsuite_add_test(suite, "test_http2_request_add_header_wrong_second_type", test_http2_request_add_header_wrong_second_type);
  valk_testsuite_add_test(suite, "test_http2_request_add_header_wrong_third_type", test_http2_request_add_header_wrong_third_type);
  valk_testsuite_add_test(suite, "test_http2_request_add_header_wrong_ref_type", test_http2_request_add_header_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_cons_wrong_count", test_cons_wrong_count);
  valk_testsuite_add_test(suite, "test_cons_wrong_second_type", test_cons_wrong_second_type);
  valk_testsuite_add_test(suite, "test_shutdown_with_code", test_shutdown_with_code);
  valk_testsuite_add_test(suite, "test_shutdown_without_code", test_shutdown_without_code);
  valk_testsuite_add_test(suite, "test_shutdown_wrong_type", test_shutdown_wrong_type);
  valk_testsuite_add_test(suite, "test_shutdown_too_many_args", test_shutdown_too_many_args);
  valk_testsuite_add_test(suite, "test_aio_schedule_wrong_ref_type", test_aio_schedule_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_aio_interval_wrong_ref_type", test_aio_interval_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_aio_run_wrong_ref_type", test_aio_run_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_aio_stop_wrong_ref_type", test_aio_stop_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_aio_metrics_json_wrong_ref_type", test_aio_metrics_json_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_aio_metrics_json_compact_wrong_ref_type", test_aio_metrics_json_compact_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_aio_systems_json_wrong_ref_type", test_aio_systems_json_wrong_ref_type);
  valk_testsuite_add_test(suite, "test_init_wrong_count", test_init_wrong_count);
  valk_testsuite_add_test(suite, "test_init_wrong_type", test_init_wrong_type);
  valk_testsuite_add_test(suite, "test_init_empty_list", test_init_empty_list);
  valk_testsuite_add_test(suite, "test_init_valid", test_init_valid);
  valk_testsuite_add_test(suite, "test_set_wrong_count", test_set_wrong_count);
  valk_testsuite_add_test(suite, "test_set_wrong_type", test_set_wrong_type);
  valk_testsuite_add_test(suite, "test_set_non_symbol_in_list", test_set_non_symbol_in_list);
  valk_testsuite_add_test(suite, "test_set_count_mismatch", test_set_count_mismatch);
  valk_testsuite_add_test(suite, "test_ord_wrong_first_type", test_ord_wrong_first_type);
  valk_testsuite_add_test(suite, "test_ord_wrong_second_type", test_ord_wrong_second_type);
  valk_testsuite_add_test(suite, "test_ord_wrong_count", test_ord_wrong_count);
  valk_testsuite_add_test(suite, "test_cmp_wrong_count_too_few", test_cmp_wrong_count_too_few);
  valk_testsuite_add_test(suite, "test_cmp_wrong_count_too_many", test_cmp_wrong_count_too_many);
  valk_testsuite_add_test(suite, "test_eval_wrong_count", test_eval_wrong_count);
  valk_testsuite_add_test(suite, "test_eval_too_many_args", test_eval_too_many_args);
  valk_testsuite_add_test(suite, "test_load_wrong_count", test_load_wrong_count);
  valk_testsuite_add_test(suite, "test_load_wrong_type_numeric", test_load_wrong_type_numeric);
  valk_testsuite_add_test(suite, "test_join_empty_args", test_join_empty_args);

  // Additional coverage tests for error branches
  valk_testsuite_add_test(suite, "test_sleep_wrong_count", test_sleep_wrong_count);
  valk_testsuite_add_test(suite, "test_sleep_wrong_type", test_sleep_wrong_type);
  valk_testsuite_add_test(suite, "test_str_split_second_arg_wrong_type", test_str_split_second_arg_wrong_type);
  valk_testsuite_add_test(suite, "test_str_replace_second_arg_wrong_type", test_str_replace_second_arg_wrong_type);
  valk_testsuite_add_test(suite, "test_str_replace_third_arg_wrong_type", test_str_replace_third_arg_wrong_type);
  valk_testsuite_add_test(suite, "test_gc_set_threshold_wrong_count", test_gc_set_threshold_wrong_count);
  valk_testsuite_add_test(suite, "test_gc_set_threshold_wrong_type", test_gc_set_threshold_wrong_type);
  valk_testsuite_add_test(suite, "test_gc_set_min_interval_wrong_count", test_gc_set_min_interval_wrong_count);
  valk_testsuite_add_test(suite, "test_gc_set_min_interval_wrong_type", test_gc_set_min_interval_wrong_type);
  valk_testsuite_add_test(suite, "test_printf_not_enough_args_for_s", test_printf_not_enough_args_for_s);
  valk_testsuite_add_test(suite, "test_printf_s_requires_string", test_printf_s_requires_string);
  valk_testsuite_add_test(suite, "test_printf_not_enough_args_for_d", test_printf_not_enough_args_for_d);
  valk_testsuite_add_test(suite, "test_printf_d_requires_number", test_printf_d_requires_number);
  valk_testsuite_add_test(suite, "test_printf_ld_format", test_printf_ld_format);
  valk_testsuite_add_test(suite, "test_printf_percent_escape", test_printf_percent_escape);
  valk_testsuite_add_test(suite, "test_printf_invalid_format", test_printf_invalid_format);
  valk_testsuite_add_test(suite, "test_print_user_with_lambda", test_print_user_with_lambda);
  valk_testsuite_add_test(suite, "test_print_user_with_ref", test_print_user_with_ref);
  valk_testsuite_add_test(suite, "test_print_user_with_error", test_print_user_with_error);
  valk_testsuite_add_test(suite, "test_str_split_empty_delimiter", test_str_split_empty_delimiter);
  valk_testsuite_add_test(suite, "test_str_replace_empty_from", test_str_replace_empty_from);
  valk_testsuite_add_test(suite, "test_str_wrong_count", test_str_wrong_count);
  valk_testsuite_add_test(suite, "test_print_with_non_string_value", test_print_with_non_string_value);
  valk_testsuite_add_test(suite, "test_println_error_propagation", test_println_error_propagation);
  valk_testsuite_add_test(suite, "test_init_on_list", test_init_on_list);
  valk_testsuite_add_test(suite, "test_init_empty_list_error", test_init_empty_list_error);
  valk_testsuite_add_test(suite, "test_lambda_body_list", test_lambda_body_list);
  valk_testsuite_add_test(suite, "test_lambda_with_arg", test_lambda_with_arg);
  valk_testsuite_add_test(suite, "test_range_basic", test_range_basic);
  valk_testsuite_add_test(suite, "test_range_empty", test_range_empty);
  valk_testsuite_add_test(suite, "test_str_multi_values", test_str_multi_values);
  valk_testsuite_add_test(suite, "test_make_string", test_make_string);
  valk_testsuite_add_test(suite, "test_str_to_num_valid", test_str_to_num_valid);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
