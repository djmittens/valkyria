#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/image.h"

#include <string.h>
#include <stdlib.h>
#include <unistd.h>

static const char *tmp_path = "/tmp/valk_image_test.img";

void test_image_num_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *v = valk_lval_num(42);
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_NUM);
  ASSERT_LVAL_NUM(r, 42);

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_str_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *v = valk_lval_str("hello world");
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_STR);
  ASSERT_STR_EQ(r->str, "hello world");

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_sym_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *v = valk_lval_sym("foo");
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_SYM);
  ASSERT_STR_EQ(r->str, "foo");

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_nil_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *v = valk_lval_nil();
  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_NIL);

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_cons_list(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Build {1 2 3}.
  valk_lval_t *items[] = {
    valk_lval_num(1), valk_lval_num(2), valk_lval_num(3),
  };
  valk_lval_t *v = valk_lval_list(items, 3);

  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_CONS);

  ASSERT_LVAL_TYPE(r->cons.head, LVAL_NUM);
  ASSERT_LVAL_NUM(r->cons.head, 1);

  valk_lval_t *n2 = r->cons.tail;
  ASSERT_LVAL_TYPE(n2, LVAL_CONS);
  ASSERT_LVAL_TYPE(n2->cons.head, LVAL_NUM);
  ASSERT_LVAL_NUM(n2->cons.head, 2);

  valk_lval_t *n3 = n2->cons.tail;
  ASSERT_LVAL_TYPE(n3, LVAL_CONS);
  ASSERT_LVAL_TYPE(n3->cons.head, LVAL_NUM);
  ASSERT_LVAL_NUM(n3->cons.head, 3);

  ASSERT_LVAL_TYPE(n3->cons.tail, LVAL_NIL);

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_nested_strings(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Mixed list with strings and symbols: {"a" foo "b"}.
  valk_lval_t *items[] = {
    valk_lval_str("a"), valk_lval_sym("foo"), valk_lval_str("b"),
  };
  valk_lval_t *v = valk_lval_list(items, 3);

  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");

  valk_lval_t *a = r->cons.head;
  ASSERT_LVAL_TYPE(a, LVAL_STR);
  ASSERT_STR_EQ(a->str, "a");

  valk_lval_t *s = r->cons.tail->cons.head;
  ASSERT_LVAL_TYPE(s, LVAL_SYM);
  ASSERT_STR_EQ(s->str, "foo");

  valk_lval_t *b = r->cons.tail->cons.tail->cons.head;
  ASSERT_LVAL_TYPE(b, LVAL_STR);
  ASSERT_STR_EQ(b->str, "b");

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();

  setenv("VALK_TEST_NO_FORK", "1", 1);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "num_roundtrip", test_image_num_roundtrip);
  valk_testsuite_add_test(suite, "str_roundtrip", test_image_str_roundtrip);
  valk_testsuite_add_test(suite, "sym_roundtrip", test_image_sym_roundtrip);
  valk_testsuite_add_test(suite, "nil_roundtrip", test_image_nil_roundtrip);
  valk_testsuite_add_test(suite, "cons_list", test_image_cons_list);
  valk_testsuite_add_test(suite, "nested_strings", test_image_nested_strings);

  int result = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return result;
}
