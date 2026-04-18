#include "testing.h"
#include "../src/parser.h"
#include "../src/memory.h"
#include "../src/image.h"
#include "../src/llvm/llvm_jit.h"

#include <string.h>
#include <stdlib.h>
#include <unistd.h>

static const char *tmp_path = "/tmp/valk_image_jit_test.img";

static valk_lenv_t *make_full_env(void) {
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  return env;
}

// End-to-end: JIT-define a lambda, dump env, reload as overlay with a
// fresh builtin registry, JIT-call the reloaded lambda.
void test_image_jit_roundtrip(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *src_env = make_full_env();
  valk_jit_t *jit = valk_jit_new();
  VALK_TEST_ASSERT(jit != NULL, "jit init");

  valk_lval_t *def_res = valk_jit_eval_string(jit, src_env,
    "(def {double} (\\ {x} {* x 2}))");
  VALK_TEST_ASSERT(def_res != NULL && LVAL_TYPE(def_res) != LVAL_ERR,
                   "def via JIT ok");

  VALK_TEST_ASSERT(valk_image_dump_env(src_env, tmp_path) == 0, "dump ok");

  valk_lenv_t *registry = make_full_env();
  valk_lenv_t *overlay = valk_image_load_overlay(tmp_path, registry);
  VALK_TEST_ASSERT(overlay != NULL, "overlay load ok");

  valk_lval_t *result = valk_jit_eval_string(jit, overlay, "(double 21)");
  VALK_TEST_ASSERT(result != NULL, "jit call returned");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);

  valk_image_load_free_overlay(overlay);
  valk_jit_free(jit);
  unlink(tmp_path);
  VALK_PASS();
}

// Same pattern but the JIT defines a new function against the overlay after
// loading, proving that overlay-level defs coexist with image-loaded ones.
void test_image_jit_overlay_def(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *src_env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, src_env, "(def {triple} (\\ {x} {* x 3}))");
  VALK_TEST_ASSERT(valk_image_dump_env(src_env, tmp_path) == 0, "dump ok");

  valk_lenv_t *registry = make_full_env();
  valk_lenv_t *overlay = valk_image_load_overlay(tmp_path, registry);

  // Define a new fn on top of the overlay that composes with `triple`.
  valk_jit_eval_string(jit, overlay, "(def {sixth} (\\ {x} {triple (* x 2)}))");

  valk_lval_t *result = valk_jit_eval_string(jit, overlay, "(sixth 7)");
  VALK_TEST_ASSERT(result != NULL, "jit call returned");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 42);  // 7 * 2 * 3

  // Overlay should hold only `sixth`, not `triple` (which stayed in image).
  VALK_TEST_ASSERT(overlay->symbols.count == 1,
                   "overlay has exactly the new def");

  valk_image_load_free_overlay(overlay);
  valk_jit_free(jit);
  unlink(tmp_path);
  VALK_PASS();
}

// Recursive function defined before dump continues to recurse correctly
// after reload; the lambda's body cons tree is immortal and the self-ref
// is resolved via the closure env parent chain.
void test_image_jit_recursive_after_reload(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_lenv_t *src_env = make_full_env();
  valk_jit_t *jit = valk_jit_new();

  valk_jit_eval_string(jit, src_env,
    "(def {fact} (\\ {n} {if (== n 0) 1 (* n (fact (- n 1)))}))");
  VALK_TEST_ASSERT(valk_image_dump_env(src_env, tmp_path) == 0, "dump ok");

  valk_lenv_t *registry = make_full_env();
  valk_lenv_t *overlay = valk_image_load_overlay(tmp_path, registry);

  valk_lval_t *result = valk_jit_eval_string(jit, overlay, "(fact 5)");
  VALK_TEST_ASSERT(result != NULL, "jit call returned");
  ASSERT_LVAL_TYPE(result, LVAL_NUM);
  ASSERT_LVAL_NUM(result, 120);

  valk_image_load_free_overlay(overlay);
  valk_jit_free(jit);
  unlink(tmp_path);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_lval_init_singletons();

  setenv("VALK_TEST_NO_FORK", "1", 1);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "image_jit_roundtrip", test_image_jit_roundtrip);
  valk_testsuite_add_test(suite, "image_jit_overlay_def", test_image_jit_overlay_def);
  valk_testsuite_add_test(suite, "image_jit_recursive_after_reload", test_image_jit_recursive_after_reload);

  int result = valk_testsuite_run(suite);
  valk_testsuite_free(suite);
  return result;
}
