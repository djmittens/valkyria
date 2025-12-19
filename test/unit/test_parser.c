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
  VALK_TEST_ASSERT(env->fallback == NULL, "new env should have no fallback");
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

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
