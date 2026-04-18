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

void test_image_env_scalars(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *k1 = valk_lval_sym("a");
  valk_lenv_put(env, k1, valk_lval_num(1));
  valk_lval_t *k2 = valk_lval_sym("b");
  valk_lenv_put(env, k2, valk_lval_str("hello"));

  VALK_TEST_ASSERT(valk_image_dump_env(env, tmp_path) == 0, "dump ok");

  valk_lenv_t *loaded = valk_image_load_env(tmp_path, NULL);
  VALK_TEST_ASSERT(loaded != NULL, "load ok");
  VALK_TEST_ASSERT(loaded->symbols.count == 2, "2 symbols");

  valk_lval_t *ka = valk_lval_sym("a");
  valk_lval_t *va = valk_lenv_get(loaded, ka);
  ASSERT_LVAL_TYPE(va, LVAL_NUM);
  ASSERT_LVAL_NUM(va, 1);

  valk_lval_t *kb = valk_lval_sym("b");
  valk_lval_t *vb = valk_lenv_get(loaded, kb);
  ASSERT_LVAL_TYPE(vb, LVAL_STR);
  ASSERT_STR_EQ(vb->str, "hello");

  valk_image_load_free_env(loaded);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_env_parent_chain(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *parent = valk_lenv_empty();
  valk_lenv_put(parent, valk_lval_sym("p"), valk_lval_num(100));

  valk_lenv_t *child = valk_lenv_empty();
  child->parent = parent;
  valk_lenv_put(child, valk_lval_sym("c"), valk_lval_num(200));

  VALK_TEST_ASSERT(valk_image_dump_env(child, tmp_path) == 0, "dump ok");

  valk_lenv_t *loaded = valk_image_load_env(tmp_path, NULL);
  VALK_TEST_ASSERT(loaded != NULL, "load ok");
  VALK_TEST_ASSERT(loaded->parent != NULL, "has parent");

  valk_lval_t *kc = valk_lval_sym("c");
  valk_lval_t *vc = valk_lenv_get(loaded, kc);
  ASSERT_LVAL_TYPE(vc, LVAL_NUM);
  ASSERT_LVAL_NUM(vc, 200);

  valk_lval_t *kp = valk_lval_sym("p");
  valk_lval_t *vp = valk_lenv_get(loaded, kp);
  ASSERT_LVAL_TYPE(vp, LVAL_NUM);
  ASSERT_LVAL_NUM(vp, 100);

  valk_image_load_free_env(loaded);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_lambda_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = valk_lenv_empty();
  valk_lval_t *formal_items[] = { valk_lval_sym("x") };
  valk_lval_t *formals = valk_lval_qlist(formal_items, 1);
  valk_lval_t *body = valk_lval_sym("x");
  valk_lval_t *lambda = valk_lval_lambda(env, formals, body);

  VALK_TEST_ASSERT(valk_image_dump(lambda, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_FUN);
  VALK_TEST_ASSERT(r->fun.builtin == NULL, "no builtin");
  VALK_TEST_ASSERT(r->fun.formals != NULL, "has formals");
  ASSERT_LVAL_TYPE(r->fun.formals, LVAL_CONS);
  ASSERT_LVAL_TYPE(r->fun.formals->cons.head, LVAL_SYM);
  ASSERT_STR_EQ(r->fun.formals->cons.head->str, "x");
  ASSERT_LVAL_TYPE(r->fun.body, LVAL_SYM);
  ASSERT_STR_EQ(r->fun.body->str, "x");
  VALK_TEST_ASSERT(r->fun.env != NULL, "has closure env");

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_lambda_with_closure(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_put(env, valk_lval_sym("captured"), valk_lval_num(42));

  valk_lval_t *formal_items[] = { valk_lval_sym("x") };
  valk_lval_t *formals = valk_lval_qlist(formal_items, 1);
  valk_lval_t *body = valk_lval_sym("captured");
  valk_lval_t *lambda = valk_lval_lambda(env, formals, body);

  VALK_TEST_ASSERT(valk_image_dump(lambda, tmp_path) == 0, "dump ok");

  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_FUN);
  VALK_TEST_ASSERT(r->fun.env != NULL, "has closure env");

  valk_lval_t *k = valk_lval_sym("captured");
  valk_lval_t *v = valk_lenv_get(r->fun.env, k);
  ASSERT_LVAL_TYPE(v, LVAL_NUM);
  ASSERT_LVAL_NUM(v, 42);

  valk_image_load_free(r);
  unlink(tmp_path);
  VALK_PASS();
}

static valk_lval_t *image_test_builtin(valk_lenv_t *env, valk_lval_t *args) {
  (void)env; (void)args;
  return valk_lval_num(999);
}

void test_image_builtin_stub_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put_builtin(src, "my-bi", image_test_builtin);

  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump ok");

  valk_lenv_t *reg = valk_lenv_empty();
  valk_lenv_put_builtin(reg, "my-bi", image_test_builtin);

  valk_lenv_t *loaded = valk_image_load_env(tmp_path, reg);
  VALK_TEST_ASSERT(loaded != NULL, "load ok");

  valk_lval_t *k = valk_lval_sym("my-bi");
  valk_lval_t *found = valk_lenv_get(loaded, k);
  ASSERT_LVAL_TYPE(found, LVAL_FUN);
  VALK_TEST_ASSERT(found->fun.builtin == image_test_builtin,
                   "builtin pointer re-resolved from registry");

  valk_lval_t *reg_found = valk_lenv_get(reg, k);
  VALK_TEST_ASSERT(found == reg_found, "loaded value is the registry's lval");

  valk_image_load_free_env(loaded);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_builtin_missing_registry_fails(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put_builtin(src, "my-bi", image_test_builtin);

  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump ok");

  valk_lenv_t *loaded = valk_image_load_env(tmp_path, NULL);
  VALK_TEST_ASSERT(loaded == NULL, "load fails without registry");

  valk_lenv_t *empty_reg = valk_lenv_empty();
  valk_lenv_t *loaded2 = valk_image_load_env(tmp_path, empty_reg);
  VALK_TEST_ASSERT(loaded2 == NULL, "load fails when registry missing name");

  unlink(tmp_path);
  VALK_PASS();
}

void test_image_overlay_shadowing(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put(src, valk_lval_sym("x"), valk_lval_num(1));
  valk_lenv_put(src, valk_lval_sym("y"), valk_lval_num(2));

  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump ok");

  valk_lenv_t *overlay = valk_image_load_overlay(tmp_path, NULL);
  VALK_TEST_ASSERT(overlay != NULL, "overlay load ok");
  VALK_TEST_ASSERT(overlay->parent != NULL, "overlay has parent");

  // Lookup through parent.
  valk_lval_t *v_x = valk_lenv_get(overlay, valk_lval_sym("x"));
  ASSERT_LVAL_TYPE(v_x, LVAL_NUM);
  ASSERT_LVAL_NUM(v_x, 1);

  // Shadow in overlay.
  valk_lenv_put(overlay, valk_lval_sym("x"), valk_lval_num(100));
  v_x = valk_lenv_get(overlay, valk_lval_sym("x"));
  ASSERT_LVAL_NUM(v_x, 100);

  // y still visible via parent.
  valk_lval_t *v_y = valk_lenv_get(overlay, valk_lval_sym("y"));
  ASSERT_LVAL_NUM(v_y, 2);

  // Overlay contains exactly one entry (just the shadow).
  VALK_TEST_ASSERT(overlay->symbols.count == 1, "overlay has 1 def");

  valk_image_load_free_overlay(overlay);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_overlay_def_stops_at_frozen(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *src = valk_lenv_empty();
  valk_lenv_put(src, valk_lval_sym("x"), valk_lval_num(1));

  VALK_TEST_ASSERT(valk_image_dump_env(src, tmp_path) == 0, "dump ok");

  valk_lenv_t *overlay = valk_image_load_overlay(tmp_path, NULL);
  VALK_TEST_ASSERT(overlay != NULL, "overlay load ok");

  valk_lenv_t *frozen = overlay->parent;
  u64 before_count = frozen->symbols.count;
  char **before_items = frozen->symbols.items;

  // def via overlay must land in overlay, not the frozen parent.
  valk_lenv_def(overlay, valk_lval_sym("newvar"), valk_lval_num(77));

  VALK_TEST_ASSERT(frozen->symbols.count == before_count,
                   "frozen env symbols.count unchanged");
  VALK_TEST_ASSERT(frozen->symbols.items == before_items,
                   "frozen env symbols.items pointer unchanged");

  valk_lval_t *v = valk_lenv_get(overlay, valk_lval_sym("newvar"));
  ASSERT_LVAL_TYPE(v, LVAL_NUM);
  ASSERT_LVAL_NUM(v, 77);

  // overlay now has exactly the one new def.
  VALK_TEST_ASSERT(overlay->symbols.count == 1, "overlay has 1 def");

  valk_image_load_free_overlay(overlay);
  unlink(tmp_path);
  VALK_PASS();
}

void test_image_sym_reintern(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *v = valk_lval_sym("the-sym");
  VALK_TEST_ASSERT(v->flags & LVAL_FLAG_INTERNED, "original is interned");

  VALK_TEST_ASSERT(valk_image_dump(v, tmp_path) == 0, "dump ok");
  valk_lval_t *r = valk_image_load(tmp_path);
  VALK_TEST_ASSERT(r != NULL, "load ok");
  ASSERT_LVAL_TYPE(r, LVAL_SYM);
  VALK_TEST_ASSERT(r->flags & LVAL_FLAG_INTERNED, "reloaded is interned");

  valk_lval_t *fresh = valk_lval_sym("the-sym");
  VALK_TEST_ASSERT(r->str == fresh->str,
                   "reloaded str pointer matches fresh interned str");

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
  valk_testsuite_add_test(suite, "env_scalars", test_image_env_scalars);
  valk_testsuite_add_test(suite, "env_parent_chain", test_image_env_parent_chain);
  valk_testsuite_add_test(suite, "lambda_roundtrip", test_image_lambda_roundtrip);
  valk_testsuite_add_test(suite, "lambda_with_closure", test_image_lambda_with_closure);
  valk_testsuite_add_test(suite, "builtin_stub_roundtrip", test_image_builtin_stub_roundtrip);
  valk_testsuite_add_test(suite, "builtin_missing_registry_fails", test_image_builtin_missing_registry_fails);
  valk_testsuite_add_test(suite, "sym_reintern", test_image_sym_reintern);
  valk_testsuite_add_test(suite, "overlay_shadowing", test_image_overlay_shadowing);
  valk_testsuite_add_test(suite, "overlay_def_stops_at_frozen", test_image_overlay_def_stops_at_frozen);

  int result = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return result;
}
