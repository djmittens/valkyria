#include "test_std.h"

#include "collections.h"
#include "common.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

void test_parsing_prelude(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lval_t *ast = VALK_FIXTURE("prelude");

  valk_lval_println(ast);
  VALK_EXPECT_SUCCESS(ast);
  VALK_PASS();
}

void test_prelude_definitions(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_lenv_t *env = VALK_FIXTURE("env");

  // Test 'fun' - should be a user-defined lambda, not builtin
  valk_lval_t *fun = valk_lenv_get(env, valk_lval_sym("fun"));
  VALK_TEST_ASSERT(LVAL_TYPE(fun) == LVAL_FUN,
                   "fun should be a function, got %s",
                   valk_ltype_name(LVAL_TYPE(fun)));
  VALK_TEST_ASSERT(fun->fun.builtin == nullptr,
                   "fun should be a lambda, not a builtin");
  VALK_TEST_ASSERT(valk_lval_list_count(fun->fun.formals) == 2,
                   "fun should take 2 args (f b), got %zu",
                   valk_lval_list_count(fun->fun.formals));

  // Test 'map' - should be a user-defined lambda
  valk_lval_t *map = valk_lenv_get(env, valk_lval_sym("map"));
  VALK_TEST_ASSERT(LVAL_TYPE(map) == LVAL_FUN,
                   "map should be a function, got %s",
                   valk_ltype_name(LVAL_TYPE(map)));
  VALK_TEST_ASSERT(map->fun.builtin == nullptr,
                   "map should be a lambda, not a builtin");
  VALK_TEST_ASSERT(valk_lval_list_count(map->fun.formals) == 2,
                   "map should take 2 args (f l), got %zu",
                   valk_lval_list_count(map->fun.formals));

  // Test 'foldl' - should be a user-defined lambda with 3 args
  valk_lval_t *foldl = valk_lenv_get(env, valk_lval_sym("foldl"));
  VALK_TEST_ASSERT(LVAL_TYPE(foldl) == LVAL_FUN,
                   "foldl should be a function, got %s",
                   valk_ltype_name(LVAL_TYPE(foldl)));
  VALK_TEST_ASSERT(foldl->fun.builtin == nullptr,
                   "foldl should be a lambda, not a builtin");
  VALK_TEST_ASSERT(valk_lval_list_count(foldl->fun.formals) == 3,
                   "foldl should take 3 args (f z l), got %zu",
                   valk_lval_list_count(foldl->fun.formals));

  // Test 'true' and 'false' - should be numbers
  valk_lval_t *true_val = valk_lenv_get(env, valk_lval_sym("true"));
  VALK_TEST_ASSERT(LVAL_TYPE(true_val) == LVAL_NUM,
                   "true should be a number, got %s",
                   valk_ltype_name(LVAL_TYPE(true_val)));
  VALK_TEST_ASSERT(true_val->num == 1,
                   "true should be 1, got %ld", true_val->num);

  valk_lval_t *false_val = valk_lenv_get(env, valk_lval_sym("false"));
  VALK_TEST_ASSERT(LVAL_TYPE(false_val) == LVAL_NUM,
                   "false should be a number, got %s",
                   valk_ltype_name(LVAL_TYPE(false_val)));
  VALK_TEST_ASSERT(false_val->num == 0,
                   "false should be 0, got %ld", false_val->num);

  // Test 'nil' - should be an empty list
  valk_lval_t *nil_val = valk_lenv_get(env, valk_lval_sym("nil"));
  VALK_TEST_ASSERT(valk_lval_list_is_empty(nil_val),
                   "nil should be an empty list");

  VALK_PASS();
}

// Removed redundant tests - these are all tested in test/test_prelude.valk
// Only keeping infrastructure tests (parsing, C linked lists)

void test_dynamic_lists(VALK_TEST_ARGS()) {
  VALK_TEST();
  struct node {
    struct node *next;
    struct node *prev;
    size_t val;
  };

  constexpr size_t size = 100;
  struct node buf[size] = {0};

  struct node *head = &buf[0];
  struct node *end = nullptr;

  {  // init list
    for (size_t i = 0; i < size; i++) {
      buf[i].val = i;
      valk_dll_insert_after(end, &buf[i]);
      end = &buf[i];
    }

    size_t count = valk_dll_count(head);

    VALK_TEST_ASSERT(count == size,
                     "Expected linked list count to be %d, but was %d", size,
                     count);

    valk_dll_foreach(head) {
      if (item->prev != nullptr) {
        VALK_TEST_ASSERT(item->prev->val == (item->val - 1),
                         "Items are out of order: %d < %d", item->prev->val,
                         item->val);
      }
    }
  }

  {  // test removing nodes
    size_t start = 15;
    size_t popNum = 25;

    size_t numPop = 0;
    while (true) {
      if (popNum == numPop) {
        break;
      }
      valk_dll_pop(valk_dll_at(head, start));
      numPop++;
    }

    VALK_TEST_ASSERT(
        popNum == numPop,
        "Expected to pop the exact number of elements  %d, but was %d", popNum,
        numPop);

    size_t count = valk_dll_count(head);

    VALK_TEST_ASSERT(count == (size - popNum),
                     "Expected linked list count to be %d, but was %d",
                     (size - popNum), count);

    valk_dll_foreach(head) {
      // check values pre-deletion
      if (item->val > (start)) {
        break;
      }
      if (item->prev != nullptr) {
        VALK_TEST_ASSERT(item->prev->val == (item->val - 1),
                         "Items are out of order: %d < %d", item->prev->val,
                         item->val);
      }
    }

    valk_dll_foreach(head) {
      // check remaining values after deletion ()
      if (item->val <= start || item->prev->val == (start - 1)) {
        continue;
      }
      if (item->prev != nullptr) {
        VALK_TEST_ASSERT(item->prev->val == (item->val - 1),
                         "Items are out of order: %d < %d", item->prev->val,
                         item->val);
      }
    }
  }

  {  // test inserting nodes
    struct node item = {0};
    item.val = 9999;

    size_t pos = 40;
    valk_dll_insert_after(valk_dll_at(head, pos), &item);

    struct node item2 = {0};
    item2.val = 8888;
    valk_dll_insert_after(valk_dll_at(head, pos), &item2);

    VALK_TEST_ASSERT(valk_dll_at(head, pos + 1)->val == item2.val,
                     "Inserted item is not in the expected position expected, "
                     "%d , but was %d",
                     valk_dll_at(head, pos + 1)->val, item2.val);

    VALK_TEST_ASSERT(valk_dll_at(head, pos + 2)->val == item.val,
                     "Inserted item is not in the expected position expected, "
                     "%d , but was %d",
                     valk_dll_at(head, pos + 2)->val, item.val);
  }
  VALK_PASS();
}

static void *__lval_retain(void *lval) { return (valk_lval_t *)lval; }
static void __lval_release(void *lval) { UNUSED(lval); }

static void *__lenv_retain(void *lenv) { return (valk_lenv_t *)lenv; }
static void __lenv_release(void *lenv) { UNUSED(lenv); }

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_gc_malloc_heap_t *gc_heap = valk_gc_malloc_heap_init(0);
  valk_thread_ctx.allocator = (void *)gc_heap;
  valk_thread_ctx.heap = gc_heap;

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_parsing_prelude", test_parsing_prelude);
  valk_testsuite_add_test(suite, "test_prelude_definitions", test_prelude_definitions);
  valk_testsuite_add_test(suite, "test_dynamic_lists", test_dynamic_lists);

  // All functional tests have been moved to test/test_prelude.valk
  // to avoid duplication and use the proper Lisp test framework

  // load fixtures
  valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);  // load the builtins

  // Evaluate prelude sequentially (program semantics)
  size_t expr_count = 0;
  while (valk_lval_list_count(ast)) {
    valk_lval_t *x = valk_lval_eval(env, valk_lval_pop(ast, 0));
    expr_count++;
    if (LVAL_TYPE(x) == LVAL_ERR) {
      // Stop early if prelude fails; tests will surface the error
      fprintf(stderr, "Prelude failed at expression %zu: ", expr_count);
      valk_lval_println(x);
      break;
    }
  }
  fprintf(stderr, "Prelude loaded %zu expressions successfully\n", expr_count);

  valk_testsuite_fixture_add(suite, "prelude", ast, __lval_retain,
                             __lval_release);
  valk_testsuite_fixture_add(suite, "env", env, __lenv_retain, __lenv_release);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_testsuite_free(suite);

  // Final GC collection before destroying heap
  // This collects any remaining unreachable objects
  valk_gc_malloc_set_root(gc_heap, nullptr);
  valk_gc_malloc_collect(gc_heap, nullptr);  // No additional roots in cleanup

  // Clean up GC heap to avoid memory leaks
  valk_gc_malloc_heap_destroy(gc_heap);

  return res;
}

valk_lval_t *valk_lval_find_error(valk_lval_t *ast) {
  switch (LVAL_TYPE(ast)) {
    case LVAL_ERR:
      return ast;
    case LVAL_CONS:
    case LVAL_QEXPR: {
      if(valk_lval_list_is_empty(ast)) return nullptr;
      valk_lval_t *err = valk_lval_find_error(ast->cons.head);
      if (err) return err;
      // If the tail is not found return null
      if (ast->cons.tail == nullptr) return nullptr;
      return valk_lval_find_error(ast->cons.tail);
    }
    case LVAL_NIL:
    case LVAL_STR:
    case LVAL_FUN:
    case LVAL_NUM:
    case LVAL_REF:
    case LVAL_SYM:
    case LVAL_FORWARD:
    case LVAL_UNDEFINED:
    case LVAL_HANDLE:
      return nullptr;
  }
  return nullptr;
}

valk_lval_t *valk_eval(valk_lenv_t *env, const char *expr) {
  int pos = 0;
  return valk_lval_eval(env, valk_lval_read(&pos, expr));
}
