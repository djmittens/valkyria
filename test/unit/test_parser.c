#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/parser.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void test_lval_num(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_num(42);
  VALK_TEST_ASSERT(val != NULL, "valk_lval_num should return non-NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_NUM, "Type should be LVAL_NUM");
  VALK_TEST_ASSERT(val->num == 42, "Value should be 42");

  VALK_PASS();
}

void test_lval_num_negative(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_num(-1000);
  VALK_TEST_ASSERT(val != NULL, "Should create negative number");
  VALK_TEST_ASSERT(val->num == -1000, "Value should be -1000");

  VALK_PASS();
}

void test_lval_num_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_num(0);
  VALK_TEST_ASSERT(val != NULL, "Should create zero");
  VALK_TEST_ASSERT(val->num == 0, "Value should be 0");

  VALK_PASS();
}

void test_lval_sym(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_sym("test-symbol");
  VALK_TEST_ASSERT(val != NULL, "valk_lval_sym should return non-NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_SYM, "Type should be LVAL_SYM");

  VALK_PASS();
}

void test_lval_sym_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_sym("");
  VALK_TEST_ASSERT(val != NULL, "Should create empty symbol");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_SYM, "Type should be LVAL_SYM");

  VALK_PASS();
}

void test_lval_str(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_str("hello world");
  VALK_TEST_ASSERT(val != NULL, "valk_lval_str should return non-NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be LVAL_STR");
  VALK_TEST_ASSERT(strcmp(val->str, "hello world") == 0, "String should match");

  VALK_PASS();
}

void test_lval_str_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_str("");
  VALK_TEST_ASSERT(val != NULL, "Should create empty string");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be LVAL_STR");
  VALK_TEST_ASSERT(strlen(val->str) == 0, "String should be empty");

  VALK_PASS();
}

void test_lval_str_n(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *data = "hello\0world";
  valk_lval_t *val = valk_lval_str_n(data, 11);
  VALK_TEST_ASSERT(val != NULL, "Should create string with embedded null");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be LVAL_STR");

  VALK_PASS();
}

void test_lval_err(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_err("Test error %d", 42);
  VALK_TEST_ASSERT(val != NULL, "valk_lval_err should return non-NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_ERR, "Type should be LVAL_ERR");
  VALK_TEST_ASSERT(strstr(val->str, "Test error 42") != NULL, "Error should contain message");

  VALK_PASS();
}

void test_lval_err_no_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_err("Simple error");
  VALK_TEST_ASSERT(val != NULL, "Should create simple error");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_ERR, "Type should be LVAL_ERR");

  VALK_PASS();
}

void test_lval_nil(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_nil();
  VALK_TEST_ASSERT(val != NULL, "valk_lval_nil should return non-NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_NIL, "Type should be LVAL_NIL");

  VALK_PASS();
}

void test_lval_cons(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *head = valk_lval_num(1);
  valk_lval_t *tail = valk_lval_nil();
  valk_lval_t *cons = valk_lval_cons(head, tail);

  VALK_TEST_ASSERT(cons != NULL, "Should create cons cell");
  VALK_TEST_ASSERT(LVAL_TYPE(cons) == LVAL_CONS, "Type should be LVAL_CONS");

  valk_lval_t *h = valk_lval_head(cons);
  VALK_TEST_ASSERT(h == head, "head should return the head");

  valk_lval_t *t = valk_lval_tail(cons);
  VALK_TEST_ASSERT(t == tail, "tail should return the tail");

  VALK_PASS();
}

void test_lval_qcons(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *head = valk_lval_num(1);
  valk_lval_t *tail = valk_lval_nil();
  valk_lval_t *qcons = valk_lval_qcons(head, tail);

  VALK_TEST_ASSERT(qcons != NULL, "Should create qexpr cons cell");
  VALK_TEST_ASSERT(LVAL_TYPE(qcons) == LVAL_QEXPR, "Type should be LVAL_QEXPR");

  VALK_PASS();
}

void test_lval_list_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *list = valk_lval_list(NULL, 0);
  VALK_TEST_ASSERT(list != NULL, "Should create empty list");
  VALK_TEST_ASSERT(LVAL_TYPE(list) == LVAL_NIL, "Empty list should be NIL");

  VALK_PASS();
}

void test_lval_list_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *elem = valk_lval_num(42);
  valk_lval_t *arr[] = {elem};
  valk_lval_t *list = valk_lval_list(arr, 1);

  VALK_TEST_ASSERT(list != NULL, "Should create single element list");
  VALK_TEST_ASSERT(LVAL_TYPE(list) == LVAL_CONS, "Type should be LVAL_CONS");

  VALK_PASS();
}

void test_lval_list_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *e1 = valk_lval_num(1);
  valk_lval_t *e2 = valk_lval_num(2);
  valk_lval_t *e3 = valk_lval_num(3);
  valk_lval_t *arr[] = {e1, e2, e3};
  valk_lval_t *list = valk_lval_list(arr, 3);

  VALK_TEST_ASSERT(list != NULL, "Should create multi element list");

  VALK_PASS();
}

void test_lval_qlist_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *qlist = valk_lval_qlist(NULL, 0);
  VALK_TEST_ASSERT(qlist != NULL, "Should create empty qlist");

  VALK_PASS();
}

void test_lval_head_nil(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *nil = valk_lval_nil();
  valk_lval_t *head = valk_lval_head(nil);
  VALK_TEST_ASSERT(head == NULL, "head of nil should be NULL");

  VALK_PASS();
}

void test_lval_tail_nil(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *nil = valk_lval_nil();
  valk_lval_t *tail = valk_lval_tail(nil);
  VALK_TEST_ASSERT(tail == NULL, "tail of nil should be NULL");

  VALK_PASS();
}

void test_lval_copy_num(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *orig = valk_lval_num(99);
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(copy != orig, "copy should be different pointer");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_NUM, "copy type should be NUM");
  VALK_TEST_ASSERT(copy->num == 99, "copy value should be 99");

  VALK_PASS();
}

void test_lval_copy_str(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *orig = valk_lval_str("copy test");
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(strcmp(copy->str, "copy test") == 0, "copy string should match");

  VALK_PASS();
}

void test_lval_copy_nil(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *orig = valk_lval_nil();
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_NIL, "copy type should be NIL");

  VALK_PASS();
}

void test_lenv_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = valk_lenv_empty();
  VALK_TEST_ASSERT(env != NULL, "valk_lenv_empty should return non-NULL");
  VALK_TEST_ASSERT(env->parent == NULL, "new env should have no parent");
  VALK_TEST_ASSERT(env->symbols.count == 0, "new env should have no symbols");

  valk_lenv_free(env);

  VALK_PASS();
}

void test_lenv_put_get(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *val = valk_lval_num(123);
  valk_lval_t *key = valk_lval_sym("test-key");

  valk_lenv_put(env, key, val);
  valk_lval_t *result = valk_lenv_get(env, key);

  VALK_TEST_ASSERT(result != NULL, "Should find the value");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Type should be NUM");
  VALK_TEST_ASSERT(result->num == 123, "Value should be 123");

  valk_lenv_free(env);

  VALK_PASS();
}

void test_lenv_get_not_found(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *key = valk_lval_sym("nonexistent");

  valk_lval_t *result = valk_lenv_get(env, key);
  VALK_TEST_ASSERT(result != NULL, "Should return an error lval");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_ERR, "Type should be ERR");

  valk_lenv_free(env);

  VALK_PASS();
}

void test_lenv_def(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *parent = valk_lenv_empty();
  valk_lenv_t *child = valk_lenv_empty();
  child->parent = parent;

  valk_lval_t *key = valk_lval_sym("global-val");
  valk_lval_t *val = valk_lval_num(999);

  valk_lenv_def(child, key, val);

  valk_lval_t *result = valk_lenv_get(parent, key);
  VALK_TEST_ASSERT(result != NULL, "Should find in parent");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Type should be NUM");
  VALK_TEST_ASSERT(result->num == 999, "Value should be 999");

  valk_lenv_free(child);
  valk_lenv_free(parent);

  VALK_PASS();
}

void test_lenv_copy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *orig = valk_lenv_empty();
  valk_lval_t *key = valk_lval_sym("copy-key");
  valk_lval_t *val = valk_lval_num(555);
  valk_lenv_put(orig, key, val);

  valk_lenv_t *copy = valk_lenv_copy(orig);
  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(copy != orig, "copy should be different pointer");

  valk_lval_t *result = valk_lenv_get(copy, key);
  VALK_TEST_ASSERT(result != NULL, "Should find value in copy");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Result should be NUM");
  VALK_TEST_ASSERT(result->num == 555, "Value should be 555");

  VALK_PASS();
}

void test_lval_type_name(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_NUM), "Number") == 0, "NUM type name");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_SYM), "Symbol") == 0, "SYM type name");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_STR), "String") == 0, "STR type name");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_NIL), "Nil") == 0, "NIL type name");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_ERR), "Error") == 0, "ERR type name");

  VALK_PASS();
}

void test_lval_large_num(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *large = valk_lval_num(9999999999L);
  VALK_TEST_ASSERT(large != NULL, "Should create large number");
  VALK_TEST_ASSERT(large->num == 9999999999L, "Value should be correct");

  VALK_PASS();
}

void test_lval_long_str(VALK_TEST_ARGS()) {
  VALK_TEST();

  char long_str[1024];
  memset(long_str, 'x', sizeof(long_str) - 1);
  long_str[sizeof(long_str) - 1] = '\0';

  valk_lval_t *val = valk_lval_str(long_str);
  VALK_TEST_ASSERT(val != NULL, "Should create long string");
  VALK_TEST_ASSERT(strlen(val->str) == sizeof(long_str) - 1, "String length should match");

  VALK_PASS();
}

void test_lval_eq_num(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *a = valk_lval_num(42);
  valk_lval_t *b = valk_lval_num(42);
  valk_lval_t *c = valk_lval_num(99);

  VALK_TEST_ASSERT(valk_lval_eq(a, b) == 1, "same numbers should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(a, c) == 0, "different numbers should not be equal");

  VALK_PASS();
}

void test_lval_eq_str(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *a = valk_lval_str("hello");
  valk_lval_t *b = valk_lval_str("hello");
  valk_lval_t *c = valk_lval_str("world");

  VALK_TEST_ASSERT(valk_lval_eq(a, b) == 1, "same strings should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(a, c) == 0, "different strings should not be equal");

  VALK_PASS();
}

void test_lval_eq_types_differ(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *num = valk_lval_num(42);
  valk_lval_t *str = valk_lval_str("42");

  VALK_TEST_ASSERT(valk_lval_eq(num, str) == 0, "different types should not be equal");

  VALK_PASS();
}

void test_lenv_free_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_free(NULL);

  VALK_PASS();
}

void test_lval_print(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *num = valk_lval_num(42);
  valk_lval_print(num);

  valk_lval_t *str = valk_lval_str("test");
  valk_lval_print(str);

  valk_lval_t *nil = valk_lval_nil();
  valk_lval_print(nil);

  VALK_PASS();
}

void test_lval_println(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_num(100);
  valk_lval_println(val);

  VALK_PASS();
}

void test_lval_copy_list(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *e1 = valk_lval_num(1);
  valk_lval_t *e2 = valk_lval_num(2);
  valk_lval_t *arr[] = {e1, e2};
  valk_lval_t *orig = valk_lval_list(arr, 2);
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(copy != orig, "copy should be different pointer");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_CONS, "copy should be CONS");

  VALK_PASS();
}

void test_lval_copy_err(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *orig = valk_lval_err("test error");
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_ERR, "copy type should be ERR");

  VALK_PASS();
}

void test_lval_read_number(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "123");
  VALK_TEST_ASSERT(val != NULL, "Should parse number");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_NUM, "Type should be NUM");
  VALK_TEST_ASSERT(val->num == 123, "Value should be 123");

  VALK_PASS();
}

void test_lval_read_negative_number(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "-456");
  VALK_TEST_ASSERT(val != NULL, "Should parse negative number");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_NUM, "Type should be NUM");
  VALK_TEST_ASSERT(val->num == -456, "Value should be -456");

  VALK_PASS();
}

void test_lval_read_symbol(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "my-sym");
  VALK_TEST_ASSERT(val != NULL, "Should parse symbol");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_SYM, "Type should be SYM");
  VALK_TEST_ASSERT(strcmp(val->str, "my-sym") == 0, "Symbol should match");

  VALK_PASS();
}

void test_lval_read_string_simple(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "\"hello\"");
  VALK_TEST_ASSERT(val != NULL, "Should parse string");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be STR");
  VALK_TEST_ASSERT(strcmp(val->str, "hello") == 0, "String should match");

  VALK_PASS();
}

void test_lval_read_string_with_escapes(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "\"hello\\nworld\"");
  VALK_TEST_ASSERT(val != NULL, "Should parse string with escapes");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be STR");
  VALK_TEST_ASSERT(strcmp(val->str, "hello\nworld") == 0, "String should have newline");

  VALK_PASS();
}

void test_lval_read_string_escape_tab(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "\"a\\tb\"");
  VALK_TEST_ASSERT(val != NULL, "Should parse tab escape");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be STR");
  VALK_TEST_ASSERT(strcmp(val->str, "a\tb") == 0, "Should have tab");

  VALK_PASS();
}

void test_lval_read_string_escape_quote(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "\"say \\\"hi\\\"\"");
  VALK_TEST_ASSERT(val != NULL, "Should parse quote escapes");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be STR");
  VALK_TEST_ASSERT(strcmp(val->str, "say \"hi\"") == 0, "Should have quotes");

  VALK_PASS();
}

void test_lval_read_string_unterminated(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "\"unclosed");
  VALK_TEST_ASSERT(val != NULL, "Should return error");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_ERR, "Type should be ERR");

  VALK_PASS();
}

void test_lval_read_string_invalid_escape(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "\"bad\\x\"");
  VALK_TEST_ASSERT(val != NULL, "Should return error");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_ERR, "Type should be ERR for invalid escape");

  VALK_PASS();
}

void test_lval_read_sexpr(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "(+ 1 2)");
  VALK_TEST_ASSERT(val != NULL, "Should parse s-expr");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_CONS, "Type should be CONS");
  VALK_TEST_ASSERT(valk_lval_list_count(val) == 3, "Should have 3 elements");

  VALK_PASS();
}

void test_lval_read_qexpr(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "{a b c}");
  VALK_TEST_ASSERT(val != NULL, "Should parse q-expr");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_QEXPR, "Type should be QEXPR");
  VALK_TEST_ASSERT(valk_lval_list_count(val) == 3, "Should have 3 elements");

  VALK_PASS();
}

void test_lval_read_quote(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "'x");
  VALK_TEST_ASSERT(val != NULL, "Should parse quote");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_QEXPR, "Type should be QEXPR");

  VALK_PASS();
}

void test_lval_read_quasiquote(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "`x");
  VALK_TEST_ASSERT(val != NULL, "Should parse quasiquote");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_CONS, "Type should be CONS");
  valk_lval_t *first = valk_lval_list_nth(val, 0);
  VALK_TEST_ASSERT(LVAL_TYPE(first) == LVAL_SYM, "First should be symbol");
  VALK_TEST_ASSERT(strcmp(first->str, "quasiquote") == 0, "Should be quasiquote");

  VALK_PASS();
}

void test_lval_read_unquote(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, ",x");
  VALK_TEST_ASSERT(val != NULL, "Should parse unquote");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_CONS, "Type should be CONS");
  valk_lval_t *first = valk_lval_list_nth(val, 0);
  VALK_TEST_ASSERT(LVAL_TYPE(first) == LVAL_SYM, "First should be symbol");
  VALK_TEST_ASSERT(strcmp(first->str, "unquote") == 0, "Should be unquote");

  VALK_PASS();
}

void test_lval_read_unquote_splicing(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, ",@xs");
  VALK_TEST_ASSERT(val != NULL, "Should parse unquote-splicing");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_CONS, "Type should be CONS");
  valk_lval_t *first = valk_lval_list_nth(val, 0);
  VALK_TEST_ASSERT(LVAL_TYPE(first) == LVAL_SYM, "First should be symbol");
  VALK_TEST_ASSERT(strcmp(first->str, "unquote-splicing") == 0, "Should be unquote-splicing");

  VALK_PASS();
}

void test_lval_read_comment(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "; comment\n42");
  VALK_TEST_ASSERT(val != NULL, "Should parse past comment");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_NUM, "Type should be NUM");
  VALK_TEST_ASSERT(val->num == 42, "Value should be 42");

  VALK_PASS();
}

void test_lval_read_unexpected_char(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "#bad");
  VALK_TEST_ASSERT(val != NULL, "Should return error");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_ERR, "Type should be ERR");

  VALK_PASS();
}

void test_lval_read_unclosed_paren(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "(+ 1 2");
  VALK_TEST_ASSERT(val != NULL, "Should return error");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_ERR, "Type should be ERR for unclosed paren");

  VALK_PASS();
}

void test_lval_pop_first(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *e1 = valk_lval_num(1);
  valk_lval_t *e2 = valk_lval_num(2);
  valk_lval_t *e3 = valk_lval_num(3);
  valk_lval_t *arr[] = {e1, e2, e3};
  valk_lval_t *list = valk_lval_list(arr, 3);

  valk_lval_t *popped = valk_lval_pop(list, 0);
  VALK_TEST_ASSERT(popped != NULL, "popped should not be NULL");
  VALK_TEST_ASSERT(popped->num == 1, "popped value should be 1");
  VALK_TEST_ASSERT(valk_lval_list_count(list) == 2, "list should have 2 elements");

  VALK_PASS();
}

void test_lval_pop_middle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *e1 = valk_lval_num(1);
  valk_lval_t *e2 = valk_lval_num(2);
  valk_lval_t *e3 = valk_lval_num(3);
  valk_lval_t *arr[] = {e1, e2, e3};
  valk_lval_t *list = valk_lval_list(arr, 3);

  valk_lval_t *popped = valk_lval_pop(list, 1);
  VALK_TEST_ASSERT(popped != NULL, "popped should not be NULL");
  VALK_TEST_ASSERT(popped->num == 2, "popped value should be 2");
  VALK_TEST_ASSERT(valk_lval_list_count(list) == 2, "list should have 2 elements");

  VALK_PASS();
}

void test_lval_join_two_lists(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *a1 = valk_lval_num(1);
  valk_lval_t *a2 = valk_lval_num(2);
  valk_lval_t *arr1[] = {a1, a2};
  valk_lval_t *list1 = valk_lval_list(arr1, 2);

  valk_lval_t *b1 = valk_lval_num(3);
  valk_lval_t *b2 = valk_lval_num(4);
  valk_lval_t *arr2[] = {b1, b2};
  valk_lval_t *list2 = valk_lval_list(arr2, 2);

  valk_lval_t *joined = valk_lval_join(list1, list2);
  VALK_TEST_ASSERT(joined != NULL, "joined should not be NULL");
  VALK_TEST_ASSERT(valk_lval_list_count(joined) == 4, "joined should have 4 elements");

  VALK_PASS();
}

void test_lval_join_single_element(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *a1 = valk_lval_num(1);
  valk_lval_t *arr1[] = {a1};
  valk_lval_t *list1 = valk_lval_list(arr1, 1);

  valk_lval_t *single = valk_lval_num(99);
  valk_lval_t *joined = valk_lval_join(list1, single);
  VALK_TEST_ASSERT(joined != NULL, "joined should not be NULL");
  VALK_TEST_ASSERT(valk_lval_list_count(joined) == 2, "joined should have 2 elements");

  VALK_PASS();
}

void test_lval_ref_type_truncation(VALK_TEST_ARGS()) {
  VALK_TEST();

  char long_type[200];
  memset(long_type, 'x', sizeof(long_type) - 1);
  long_type[sizeof(long_type) - 1] = '\0';

  valk_lval_t *ref = valk_lval_ref(long_type, NULL, NULL);
  VALK_TEST_ASSERT(ref != NULL, "ref should not be NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(ref) == LVAL_REF, "Type should be REF");
  VALK_TEST_ASSERT(strlen(ref->ref.type) <= 100, "Type should be truncated");

  VALK_PASS();
}

void test_lval_sym_truncation(VALK_TEST_ARGS()) {
  VALK_TEST();

  char long_sym[300];
  memset(long_sym, 'a', sizeof(long_sym) - 1);
  long_sym[sizeof(long_sym) - 1] = '\0';

  valk_lval_t *sym = valk_lval_sym(long_sym);
  VALK_TEST_ASSERT(sym != NULL, "sym should not be NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(sym) == LVAL_SYM, "Type should be SYM");
  VALK_TEST_ASSERT(strlen(sym->str) <= 200, "Symbol should be truncated");

  VALK_PASS();
}

void test_lenv_parent_lookup(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *parent = valk_lenv_empty();
  valk_lenv_t *child = valk_lenv_empty();
  child->parent = parent;

  valk_lval_t *key = valk_lval_sym("parent-val");
  valk_lval_t *val = valk_lval_num(777);
  valk_lenv_put(parent, key, val);

  valk_lval_t *result = valk_lenv_get(child, key);
  VALK_TEST_ASSERT(result != NULL, "Should find in parent");
  VALK_TEST_ASSERT(LVAL_TYPE(result) == LVAL_NUM, "Type should be NUM");
  VALK_TEST_ASSERT(result->num == 777, "Value should be 777");

  valk_lenv_free(child);
  valk_lenv_free(parent);

  VALK_PASS();
}

// Fallback lookup test removed - we now use pure lexical scoping
// The fallback chain was for dynamic scoping which we no longer support

void test_lenv_put_overwrite(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *key = valk_lval_sym("x");
  valk_lval_t *val1 = valk_lval_num(100);
  valk_lval_t *val2 = valk_lval_num(200);

  valk_lenv_put(env, key, val1);
  valk_lenv_put(env, key, val2);

  valk_lval_t *result = valk_lenv_get(env, key);
  VALK_TEST_ASSERT(result != NULL, "Should find value");
  VALK_TEST_ASSERT(result->num == 200, "Should be overwritten value");

  valk_lenv_free(env);

  VALK_PASS();
}

void test_lval_list_is_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *nil = valk_lval_nil();
  VALK_TEST_ASSERT(valk_lval_list_is_empty(nil) == 1, "nil should be empty");
  VALK_TEST_ASSERT(valk_lval_list_is_empty(NULL) == 1, "NULL should be empty");

  valk_lval_t *elem = valk_lval_num(1);
  valk_lval_t *arr[] = {elem};
  valk_lval_t *list = valk_lval_list(arr, 1);
  VALK_TEST_ASSERT(valk_lval_list_is_empty(list) == 0, "non-empty list should not be empty");

  VALK_PASS();
}

void test_lval_list_nth_out_of_bounds(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *elem = valk_lval_num(1);
  valk_lval_t *arr[] = {elem};
  valk_lval_t *list = valk_lval_list(arr, 1);

  valk_lval_t *result = valk_lval_list_nth(list, 10);
  VALK_TEST_ASSERT(result == NULL, "out of bounds should return NULL");

  VALK_PASS();
}

void test_lval_eq_nil(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *nil1 = valk_lval_nil();
  valk_lval_t *nil2 = valk_lval_nil();

  VALK_TEST_ASSERT(valk_lval_eq(nil1, nil2) == 1, "nils should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(nil1, NULL) == 0, "nil should not equal NULL");
  VALK_TEST_ASSERT(valk_lval_eq(NULL, NULL) == 1, "NULLs should be equal");

  VALK_PASS();
}

void test_lval_eq_cons(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *a1[] = {valk_lval_num(1), valk_lval_num(2)};
  valk_lval_t *a2[] = {valk_lval_num(1), valk_lval_num(2)};
  valk_lval_t *a3[] = {valk_lval_num(1), valk_lval_num(3)};

  valk_lval_t *list1 = valk_lval_list(a1, 2);
  valk_lval_t *list2 = valk_lval_list(a2, 2);
  valk_lval_t *list3 = valk_lval_list(a3, 2);

  VALK_TEST_ASSERT(valk_lval_eq(list1, list2) == 1, "identical lists should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(list1, list3) == 0, "different lists should not be equal");

  VALK_PASS();
}

void test_lval_copy_sym(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *orig = valk_lval_sym("my-symbol");
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_SYM, "copy type should be SYM");
  VALK_TEST_ASSERT(strcmp(copy->str, "my-symbol") == 0, "copy value should match");
  VALK_TEST_ASSERT(copy->str != orig->str, "copy should have its own string");

  VALK_PASS();
}

void test_lval_copy_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  int data = 42;
  valk_lval_t *orig = valk_lval_ref("test-ref", &data, NULL);
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_REF, "copy type should be REF");
  VALK_TEST_ASSERT(strcmp(copy->ref.type, "test-ref") == 0, "copy type should match");
  VALK_TEST_ASSERT(copy->ref.ptr == &data, "copy ptr should match");

  VALK_PASS();
}

void test_lval_copy_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *copy = valk_lval_copy(NULL);
  VALK_TEST_ASSERT(copy == NULL, "copy of NULL should be NULL");

  VALK_PASS();
}

void test_ltype_name_unknown(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *name = valk_ltype_name((valk_ltype_e)99);
  VALK_TEST_ASSERT(name != NULL, "Should return a name");
  VALK_TEST_ASSERT(strcmp(name, "Unknown") == 0, "Should be Unknown");

  VALK_PASS();
}

void test_ltype_name_all_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_FUN), "Function") == 0, "FUN type");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_CONS), "S-Expr") == 0, "CONS type");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_QEXPR), "Q-Expr") == 0, "QEXPR type");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_REF), "Reference") == 0, "REF type");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_HANDLE), "Handle") == 0, "HANDLE type");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_FORWARD), "Forward") == 0, "FORWARD type");
  VALK_TEST_ASSERT(strcmp(valk_ltype_name(LVAL_UNDEFINED), "UNDEFINED") == 0, "UNDEFINED type");

  VALK_PASS();
}

void test_str_join(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *strs[] = {"hello", "world", "test"};
  char *result = valk_str_join(3, strs, ", ");

  VALK_TEST_ASSERT(result != NULL, "result should not be NULL");
  VALK_TEST_ASSERT(strcmp(result, "hello, world, test") == 0, "join should work");

  valk_mem_free(result);

  VALK_PASS();
}

void test_str_join_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *strs[] = {"only"};
  char *result = valk_str_join(1, strs, ", ");

  VALK_TEST_ASSERT(result != NULL, "result should not be NULL");
  VALK_TEST_ASSERT(strcmp(result, "only") == 0, "single join should work");

  valk_mem_free(result);

  VALK_PASS();
}

void test_lenv_copy_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *copy = valk_lenv_copy(NULL);
  VALK_TEST_ASSERT(copy == NULL, "copy of NULL env should be NULL");

  VALK_PASS();
}

void test_lenv_copy_with_parent_chain(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *grandparent = valk_lenv_empty();
  valk_lenv_t *parent = valk_lenv_empty();
  valk_lenv_t *child = valk_lenv_empty();
  parent->parent = grandparent;
  child->parent = parent;

  valk_lval_t *gp_key = valk_lval_sym("gp-val");
  valk_lval_t *gp_val = valk_lval_num(111);
  valk_lenv_put(grandparent, gp_key, gp_val);

  valk_lval_t *p_key = valk_lval_sym("p-val");
  valk_lval_t *p_val = valk_lval_num(222);
  valk_lenv_put(parent, p_key, p_val);

  valk_lval_t *c_key = valk_lval_sym("c-val");
  valk_lval_t *c_val = valk_lval_num(333);
  valk_lenv_put(child, c_key, c_val);

  valk_lenv_t *copy = valk_lenv_copy(child);
  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(copy->parent == NULL, "copy should have flattened parent");

  valk_lval_t *res_gp = valk_lenv_get(copy, gp_key);
  VALK_TEST_ASSERT(LVAL_TYPE(res_gp) == LVAL_NUM, "Should find grandparent value");
  VALK_TEST_ASSERT(res_gp->num == 111, "grandparent value should be correct");

  valk_lval_t *res_p = valk_lenv_get(copy, p_key);
  VALK_TEST_ASSERT(LVAL_TYPE(res_p) == LVAL_NUM, "Should find parent value");
  VALK_TEST_ASSERT(res_p->num == 222, "parent value should be correct");

  valk_lval_t *res_c = valk_lenv_get(copy, c_key);
  VALK_TEST_ASSERT(LVAL_TYPE(res_c) == LVAL_NUM, "Should find child value");
  VALK_TEST_ASSERT(res_c->num == 333, "child value should be correct");

  VALK_PASS();
}

void test_lval_str_n_zero_length(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *val = valk_lval_str_n("hello", 0);
  VALK_TEST_ASSERT(val != NULL, "Should create empty string");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_STR, "Type should be STR");
  VALK_TEST_ASSERT(strlen(val->str) == 0, "String should be empty");

  VALK_PASS();
}

void test_lval_print_forward(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t val;
  val.flags = LVAL_FORWARD;
  val.forward = (struct valk_lval_t *)0xDEADBEEF;
  valk_lval_print(&val);

  VALK_PASS();
}

void test_lval_print_undefined(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t val;
  val.flags = LVAL_UNDEFINED;
  valk_lval_print(&val);

  VALK_PASS();
}

void test_lval_print_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  int data = 42;
  valk_lval_t *ref = valk_lval_ref("test-type", &data, NULL);
  valk_lval_print(ref);

  VALK_PASS();
}

void test_lval_print_lambda(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *formals = valk_lval_nil();
  valk_lval_t *body = valk_lval_nil();
  valk_lval_t *lambda = valk_lval_lambda(env, formals, body);
  valk_lval_print(lambda);

  VALK_PASS();
}

void test_lval_read_minus_only(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "-");
  VALK_TEST_ASSERT(val != NULL, "Should parse minus");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_SYM, "Minus alone should be symbol");
  VALK_TEST_ASSERT(strcmp(val->str, "-") == 0, "Should be minus symbol");

  VALK_PASS();
}

void test_lval_eq_lambda(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env1 = valk_lenv_empty();
  valk_lenv_t *env2 = valk_lenv_empty();

  valk_lval_t *formals1 = valk_lval_qlist((valk_lval_t*[]){valk_lval_sym("x")}, 1);
  valk_lval_t *body1 = valk_lval_sym("x");
  valk_lval_t *lambda1 = valk_lval_lambda(env1, formals1, body1);

  valk_lval_t *formals2 = valk_lval_qlist((valk_lval_t*[]){valk_lval_sym("x")}, 1);
  valk_lval_t *body2 = valk_lval_sym("x");
  valk_lval_t *lambda2 = valk_lval_lambda(env2, formals2, body2);

  valk_lval_t *formals3 = valk_lval_qlist((valk_lval_t*[]){valk_lval_sym("y")}, 1);
  valk_lval_t *body3 = valk_lval_sym("y");
  valk_lval_t *lambda3 = valk_lval_lambda(env1, formals3, body3);

  VALK_TEST_ASSERT(valk_lval_eq(lambda1, lambda2) == 1, "identical lambdas should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(lambda1, lambda3) == 0, "different lambdas should not be equal");

  VALK_PASS();
}

void test_lval_eq_ref(VALK_TEST_ARGS()) {
  VALK_TEST();

  int data1 = 42;
  int data2 = 99;

  valk_lval_t *ref1 = valk_lval_ref("test", &data1, NULL);
  valk_lval_t *ref2 = valk_lval_ref("test", &data1, NULL);
  valk_lval_t *ref3 = valk_lval_ref("test", &data2, NULL);

  VALK_TEST_ASSERT(valk_lval_eq(ref1, ref2) == 1, "refs to same data should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(ref1, ref3) == 0, "refs to different data should not be equal");

  VALK_PASS();
}

void test_lval_copy_lambda(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *formals = valk_lval_qlist((valk_lval_t*[]){valk_lval_sym("x")}, 1);
  valk_lval_t *body = valk_lval_sym("x");
  valk_lval_t *lambda = valk_lval_lambda(env, formals, body);

  valk_lval_t *copy = valk_lval_copy(lambda);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(copy != lambda, "copy should be different pointer");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_FUN, "copy type should be FUN");
  VALK_TEST_ASSERT(copy->fun.builtin == NULL, "copy should be lambda");

  VALK_PASS();
}

void test_lval_copy_qexpr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *e1 = valk_lval_num(1);
  valk_lval_t *e2 = valk_lval_num(2);
  valk_lval_t *arr[] = {e1, e2};
  valk_lval_t *orig = valk_lval_qlist(arr, 2);
  valk_lval_t *copy = valk_lval_copy(orig);

  VALK_TEST_ASSERT(copy != NULL, "copy should not be NULL");
  VALK_TEST_ASSERT(copy != orig, "copy should be different pointer");
  VALK_TEST_ASSERT(LVAL_TYPE(copy) == LVAL_QEXPR, "copy should be QEXPR");

  VALK_PASS();
}

void test_lval_eq_qexpr(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *a1[] = {valk_lval_num(1), valk_lval_num(2)};
  valk_lval_t *a2[] = {valk_lval_num(1), valk_lval_num(2)};
  valk_lval_t *a3[] = {valk_lval_num(1), valk_lval_num(3)};

  valk_lval_t *qlist1 = valk_lval_qlist(a1, 2);
  valk_lval_t *qlist2 = valk_lval_qlist(a2, 2);
  valk_lval_t *qlist3 = valk_lval_qlist(a3, 2);

  VALK_TEST_ASSERT(valk_lval_eq(qlist1, qlist2) == 1, "identical qlists should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(qlist1, qlist3) == 0, "different qlists should not be equal");

  VALK_PASS();
}

void test_lval_eq_err(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *err1 = valk_lval_err("test error");
  valk_lval_t *err2 = valk_lval_err("test error");
  valk_lval_t *err3 = valk_lval_err("different error");

  VALK_TEST_ASSERT(valk_lval_eq(err1, err2) == 1, "same errors should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(err1, err3) == 0, "different errors should not be equal");

  VALK_PASS();
}

void test_lval_eq_sym(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lval_t *sym1 = valk_lval_sym("test");
  valk_lval_t *sym2 = valk_lval_sym("test");
  valk_lval_t *sym3 = valk_lval_sym("other");

  VALK_TEST_ASSERT(valk_lval_eq(sym1, sym2) == 1, "same symbols should be equal");
  VALK_TEST_ASSERT(valk_lval_eq(sym1, sym3) == 0, "different symbols should not be equal");

  VALK_PASS();
}

void test_lval_read_nested_expr(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "(+ (* 2 3) (- 5 1))");
  VALK_TEST_ASSERT(val != NULL, "Should parse nested expr");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_CONS, "Type should be CONS");
  VALK_TEST_ASSERT(valk_lval_list_count(val) == 3, "Should have 3 elements");

  VALK_PASS();
}

void test_lval_read_empty_list(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "()");
  VALK_TEST_ASSERT(val != NULL, "Should parse empty list");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_NIL, "Empty list should be NIL");

  VALK_PASS();
}

void test_lval_read_empty_qexpr(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "{}");
  VALK_TEST_ASSERT(val != NULL, "Should parse empty qexpr");

  VALK_PASS();
}

void test_lval_read_deeply_nested(VALK_TEST_ARGS()) {
  VALK_TEST();

  int pos = 0;
  valk_lval_t *val = valk_lval_read(&pos, "(((((x)))))");
  VALK_TEST_ASSERT(val != NULL, "Should parse deeply nested");
  VALK_TEST_ASSERT(LVAL_TYPE(val) == LVAL_CONS, "Type should be CONS");

  VALK_PASS();
}



int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_lval_num", test_lval_num);
  valk_testsuite_add_test(suite, "test_lval_num_negative", test_lval_num_negative);
  valk_testsuite_add_test(suite, "test_lval_num_zero", test_lval_num_zero);
  valk_testsuite_add_test(suite, "test_lval_sym", test_lval_sym);
  valk_testsuite_add_test(suite, "test_lval_sym_empty", test_lval_sym_empty);
  valk_testsuite_add_test(suite, "test_lval_str", test_lval_str);
  valk_testsuite_add_test(suite, "test_lval_str_empty", test_lval_str_empty);
  valk_testsuite_add_test(suite, "test_lval_str_n", test_lval_str_n);
  valk_testsuite_add_test(suite, "test_lval_err", test_lval_err);
  valk_testsuite_add_test(suite, "test_lval_err_no_args", test_lval_err_no_args);
  valk_testsuite_add_test(suite, "test_lval_nil", test_lval_nil);
  valk_testsuite_add_test(suite, "test_lval_cons", test_lval_cons);
  valk_testsuite_add_test(suite, "test_lval_qcons", test_lval_qcons);
  valk_testsuite_add_test(suite, "test_lval_list_empty", test_lval_list_empty);
  valk_testsuite_add_test(suite, "test_lval_list_single", test_lval_list_single);
  valk_testsuite_add_test(suite, "test_lval_list_multiple", test_lval_list_multiple);
  valk_testsuite_add_test(suite, "test_lval_qlist_empty", test_lval_qlist_empty);
  valk_testsuite_add_test(suite, "test_lval_head_nil", test_lval_head_nil);
  valk_testsuite_add_test(suite, "test_lval_tail_nil", test_lval_tail_nil);
  valk_testsuite_add_test(suite, "test_lval_copy_num", test_lval_copy_num);
  valk_testsuite_add_test(suite, "test_lval_copy_str", test_lval_copy_str);
  valk_testsuite_add_test(suite, "test_lval_copy_nil", test_lval_copy_nil);
  valk_testsuite_add_test(suite, "test_lenv_empty", test_lenv_empty);
  valk_testsuite_add_test(suite, "test_lenv_put_get", test_lenv_put_get);
  valk_testsuite_add_test(suite, "test_lenv_get_not_found", test_lenv_get_not_found);
  valk_testsuite_add_test(suite, "test_lenv_def", test_lenv_def);
  valk_testsuite_add_test(suite, "test_lenv_copy", test_lenv_copy);
  valk_testsuite_add_test(suite, "test_lval_type_name", test_lval_type_name);
  valk_testsuite_add_test(suite, "test_lval_large_num", test_lval_large_num);
  valk_testsuite_add_test(suite, "test_lval_long_str", test_lval_long_str);
  valk_testsuite_add_test(suite, "test_lval_eq_num", test_lval_eq_num);
  valk_testsuite_add_test(suite, "test_lval_eq_str", test_lval_eq_str);
  valk_testsuite_add_test(suite, "test_lval_eq_types_differ", test_lval_eq_types_differ);
  valk_testsuite_add_test(suite, "test_lenv_free_null", test_lenv_free_null);
  valk_testsuite_add_test(suite, "test_lval_print", test_lval_print);
  valk_testsuite_add_test(suite, "test_lval_println", test_lval_println);
  valk_testsuite_add_test(suite, "test_lval_copy_list", test_lval_copy_list);
  valk_testsuite_add_test(suite, "test_lval_copy_err", test_lval_copy_err);
  valk_testsuite_add_test(suite, "test_lval_read_number", test_lval_read_number);
  valk_testsuite_add_test(suite, "test_lval_read_negative_number", test_lval_read_negative_number);
  valk_testsuite_add_test(suite, "test_lval_read_symbol", test_lval_read_symbol);
  valk_testsuite_add_test(suite, "test_lval_read_string_simple", test_lval_read_string_simple);
  valk_testsuite_add_test(suite, "test_lval_read_string_with_escapes", test_lval_read_string_with_escapes);
  valk_testsuite_add_test(suite, "test_lval_read_string_escape_tab", test_lval_read_string_escape_tab);
  valk_testsuite_add_test(suite, "test_lval_read_string_escape_quote", test_lval_read_string_escape_quote);
  valk_testsuite_add_test(suite, "test_lval_read_string_unterminated", test_lval_read_string_unterminated);
  valk_testsuite_add_test(suite, "test_lval_read_string_invalid_escape", test_lval_read_string_invalid_escape);
  valk_testsuite_add_test(suite, "test_lval_read_sexpr", test_lval_read_sexpr);
  valk_testsuite_add_test(suite, "test_lval_read_qexpr", test_lval_read_qexpr);
  valk_testsuite_add_test(suite, "test_lval_read_quote", test_lval_read_quote);
  valk_testsuite_add_test(suite, "test_lval_read_quasiquote", test_lval_read_quasiquote);
  valk_testsuite_add_test(suite, "test_lval_read_unquote", test_lval_read_unquote);
  valk_testsuite_add_test(suite, "test_lval_read_unquote_splicing", test_lval_read_unquote_splicing);
  valk_testsuite_add_test(suite, "test_lval_read_comment", test_lval_read_comment);
  valk_testsuite_add_test(suite, "test_lval_read_unexpected_char", test_lval_read_unexpected_char);
  valk_testsuite_add_test(suite, "test_lval_read_unclosed_paren", test_lval_read_unclosed_paren);
  valk_testsuite_add_test(suite, "test_lval_pop_first", test_lval_pop_first);
  valk_testsuite_add_test(suite, "test_lval_pop_middle", test_lval_pop_middle);
  valk_testsuite_add_test(suite, "test_lval_join_two_lists", test_lval_join_two_lists);
  valk_testsuite_add_test(suite, "test_lval_join_single_element", test_lval_join_single_element);
  valk_testsuite_add_test(suite, "test_lval_ref_type_truncation", test_lval_ref_type_truncation);
  valk_testsuite_add_test(suite, "test_lval_sym_truncation", test_lval_sym_truncation);
  valk_testsuite_add_test(suite, "test_lenv_parent_lookup", test_lenv_parent_lookup);
  valk_testsuite_add_test(suite, "test_lenv_put_overwrite", test_lenv_put_overwrite);
  valk_testsuite_add_test(suite, "test_lval_list_is_empty", test_lval_list_is_empty);
  valk_testsuite_add_test(suite, "test_lval_list_nth_out_of_bounds", test_lval_list_nth_out_of_bounds);
  valk_testsuite_add_test(suite, "test_lval_eq_nil", test_lval_eq_nil);
  valk_testsuite_add_test(suite, "test_lval_eq_cons", test_lval_eq_cons);
  valk_testsuite_add_test(suite, "test_lval_copy_sym", test_lval_copy_sym);
  valk_testsuite_add_test(suite, "test_lval_copy_ref", test_lval_copy_ref);
  valk_testsuite_add_test(suite, "test_lval_copy_null", test_lval_copy_null);
  valk_testsuite_add_test(suite, "test_ltype_name_unknown", test_ltype_name_unknown);
  valk_testsuite_add_test(suite, "test_ltype_name_all_types", test_ltype_name_all_types);
  valk_testsuite_add_test(suite, "test_str_join", test_str_join);
  valk_testsuite_add_test(suite, "test_str_join_single", test_str_join_single);
  valk_testsuite_add_test(suite, "test_lenv_copy_null", test_lenv_copy_null);
  valk_testsuite_add_test(suite, "test_lenv_copy_with_parent_chain", test_lenv_copy_with_parent_chain);
  valk_testsuite_add_test(suite, "test_lval_str_n_zero_length", test_lval_str_n_zero_length);
  valk_testsuite_add_test(suite, "test_lval_print_forward", test_lval_print_forward);
  valk_testsuite_add_test(suite, "test_lval_print_undefined", test_lval_print_undefined);
  valk_testsuite_add_test(suite, "test_lval_print_ref", test_lval_print_ref);
  valk_testsuite_add_test(suite, "test_lval_print_lambda", test_lval_print_lambda);
  valk_testsuite_add_test(suite, "test_lval_read_minus_only", test_lval_read_minus_only);
  valk_testsuite_add_test(suite, "test_lval_eq_lambda", test_lval_eq_lambda);
  valk_testsuite_add_test(suite, "test_lval_eq_ref", test_lval_eq_ref);
  valk_testsuite_add_test(suite, "test_lval_copy_lambda", test_lval_copy_lambda);
  valk_testsuite_add_test(suite, "test_lval_copy_qexpr", test_lval_copy_qexpr);
  valk_testsuite_add_test(suite, "test_lval_eq_qexpr", test_lval_eq_qexpr);
  valk_testsuite_add_test(suite, "test_lval_eq_err", test_lval_eq_err);
  valk_testsuite_add_test(suite, "test_lval_eq_sym", test_lval_eq_sym);
  valk_testsuite_add_test(suite, "test_lval_read_nested_expr", test_lval_read_nested_expr);
  valk_testsuite_add_test(suite, "test_lval_read_empty_list", test_lval_read_empty_list);
  valk_testsuite_add_test(suite, "test_lval_read_empty_qexpr", test_lval_read_empty_qexpr);
  valk_testsuite_add_test(suite, "test_lval_read_deeply_nested", test_lval_read_deeply_nested);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
