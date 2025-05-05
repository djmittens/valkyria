#include "common.h"
#include "concurrency.h"
#include "memory.h"
#include "testing.h"
#include <time.h>

void test_implicit_alloc(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_thread_context_t ctxBackup = valk_thread_ctx;

  valk_mem_allocator_t alloc_old;
  valk_mem_allocator_t alloc_new;

  valk_thread_ctx.allocator = &alloc_old;
  valk_thread_context_t ctx = {.allocator = &alloc_new};
  VALK_WITH_CTX(ctx) {
    // The function gets context we set
    VALK_TEST_ASSERT(valk_thread_ctx.allocator == &alloc_new,
                     "expected some stuff %d", &alloc_new);
  }
  // VALK_WITH_CTX reset the context back to original
  VALK_TEST_ASSERT(valk_thread_ctx.allocator == &alloc_old,
                   "expected some stuff %d", &alloc_old);

  valk_thread_ctx = ctxBackup;
  VALK_PASS();
}

void test_slab_alloc(VALK_TEST_ARGS()) {
  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  printf("Seeding rand with %ld\n", ts.tv_sec);

  const char msg[] = "Get fucked\n";

  srand(1746481318);
  // srand(ts.tv_sec);

  VALK_TEST();

  int itemLen = sizeof(valk_arc_box) + sizeof(msg);
  size_t numItems = rand() % 1000;
  valk_slab_t *slab = valk_slab_new(itemLen, numItems);

  valk_arc_box *boxes[numItems];

  printf("Generating %ld items\n", numItems);
  // allocate everythign
  for (size_t i = 0; i < numItems; ++i) {
    if (rand() % 2) {
      boxes[i] = (valk_arc_box *)valk_slab_aquire(slab)->data;
      valk_arc_box_init(boxes[i], VALK_SUC, sizeof(msg));
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
        boxes[i] = valk_mem_alloc(99999);
        valk_arc_box_init(boxes[i], VALK_SUC, sizeof(msg));
      }
    }
    strncpy(boxes[i]->item, msg, sizeof(msg));
  }

  for (size_t i = 0; i < numItems; ++i) {
    char *result = (char *)boxes[i]->item;
    VALK_TEST_ASSERT(strcmp(result, msg) == 0, "Shit got corrupted %d %s", i,
                     result);
  }

  // ok now lets shuffle some dogshit
  const char newMsg[] = "XOXOXO\n"; // should be smaller than the other messge

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  // Use malloc for now, by default
  // probably should think of how to add this by default everywhere
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_implicit_alloc", test_implicit_alloc);

  valk_testsuite_add_test(suite, "test_slab_alloc", test_slab_alloc);
  // load fixtures
  // valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  // valk_lenv_t *env = valk_lenv_empty();
  // valk_lenv_builtins(env); // load the builtins
  // valk_lval_t *r = valk_lval_eval(env, valk_lval_copy(ast));
  // valk_lval_free(r);
  //
  // valk_testsuite_fixture_add(suite, "prelude", ast,
  //                            (_fixture_copy_f *)valk_lval_copy,
  //                            (_fixture_free_f *)valk_lval_free);
  // valk_testsuite_fixture_add(suite, "env", env,
  //                            (_fixture_copy_f *)valk_lenv_copy,
  //                            (_fixture_free_f *)valk_lenv_free);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
