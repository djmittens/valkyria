#include "test_std.h"

#include "collections.h"
#include "common.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

void test_parsing_prelude(VALK_TEST_ARGS()) {
  valk_lval_t *ast = VALK_FIXTURE("prelude");
  VALK_TEST();

  VALK_EXPECT_SUCCESS(ast);
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

  // Use GC heap for everything, including test suite
  size_t const GC_THRESHOLD_BYTES = 16 * 1024 * 1024;  // 16 MiB
  valk_gc_malloc_heap_t *gc_heap = valk_gc_malloc_heap_init(GC_THRESHOLD_BYTES);
  valk_thread_ctx.allocator = (void *)gc_heap;

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_parsing_prelude", test_parsing_prelude);
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

  // TODO: Re-enable freezing after debugging mutation issues
  // Freezing causes bugs with map/let where frozen structures are mutated
  // for (size_t i = 0; i < env->count; i++) {
  //   valk_lval_freeze(env->vals[i]);
  // }

  valk_testsuite_fixture_add(suite, "prelude", ast, __lval_retain,
                             __lval_release);
  valk_testsuite_fixture_add(suite, "env", env, __lenv_retain, __lenv_release);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);

  valk_testsuite_free(suite);

  // Final GC collection before destroying heap
  // This collects any remaining unreachable objects
  valk_gc_malloc_set_root(gc_heap, NULL);
  valk_gc_malloc_collect(gc_heap);

  // Clean up GC heap to avoid memory leaks
  valk_gc_malloc_heap_destroy(gc_heap);

  return res;
}

valk_lval_t *valk_lval_find_error(valk_lval_t *ast) {
  switch (LVAL_TYPE(ast)) {
    case LVAL_ERR:
      return ast;
    case LVAL_QEXPR:
    case LVAL_SEXPR: {
      for (size_t i = 0; i < valk_lval_list_count(ast); i++) {
        valk_lval_t* child = valk_lval_list_nth(ast, i);
        if (valk_lval_find_error(child)) {
          return child;
        }
      }
      return nullptr;
    }
    case LVAL_CONS: {
      valk_lval_t *err = valk_lval_find_error(ast->cons.head);
      if (err) return err;
      return valk_lval_find_error(ast->cons.tail);
    }
    case LVAL_NIL:
    case LVAL_STR:
    case LVAL_FUN:
    case LVAL_NUM:
    case LVAL_REF:
    case LVAL_SYM:
    case LVAL_ENV:
    case LVAL_UNDEFINED:
      return nullptr;
  }
  return nullptr;
}

valk_lval_t *valk_eval(valk_lenv_t *env, const char *expr) {
  int pos = 0;
  return valk_lval_eval(env, valk_lval_read(&pos, expr));
}
