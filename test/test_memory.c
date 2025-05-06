#include "common.h"
#include "concurrency.h"
#include "memory.h"
#include "testing.h"
#include <math.h>
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

  const char msg[] = "Get fucked";

  srand(1746481318);
  // srand(ts.tv_sec);

  VALK_TEST();

  int itemLen = sizeof(valk_arc_box) + sizeof(msg);
  size_t numItems = rand() % 1000;
  #if 0
  valk_slab_t *slab = valk_slab_new(itemLen, numItems + 1);
  #else
  valk_slab_t *slab = valk_slab_new(itemLen, numItems);
  #endif

  valk_arc_box *boxes[numItems];
  size_t slabIds[numItems];

  printf("Aquiring %ld boxes\n", numItems);
  // allocate everything
  for (size_t i = 0; i < numItems; ++i) {
    if (rand() % 2) {
      valk_slab_item_t *item = valk_slab_aquire(slab);
      boxes[i] = (valk_arc_box *)item->data;
      valk_arc_box_init(boxes[i], VALK_SUC, sizeof(msg));
      boxes[i]->allocator = (valk_mem_allocator_t *)slab;
      slabIds[i] = item->handle;
    } else {
      VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
        boxes[i] = valk_arc_box_new(VALK_SUC, sizeof(msg));
        slabIds[i] =
            valk_container_of(boxes[i], valk_slab_item_t, data)->handle;
      }
    }

    printf("Aquired box i: %ld ::: slabId: %ld\n", i, slabIds[i]);
    strncpy(boxes[i]->item, msg, sizeof(msg));
  }

  for (size_t i = 0; i < numItems; ++i) {
    char *result = (char *)boxes[i]->item;
    VALK_TEST_ASSERT(strcmp(result, msg) == 0, "Shit got corrupted %d %s", i,
                     result);
  }

  VALK_TEST_ASSERT(slab->numFree == 0, "Shit should be full %d", slab->numFree);

  // ok now lets shuffle some dogshit
  // reap at most 80 % of the items
  size_t reapNum = rand() % lrint(numItems * .8);
  printf("Reaping total of %ld boxes:\n", reapNum);

  // should be smaller than the other messge
  const char newMsg[] = "XOXOXO";
  valk_arc_box *newBoxes[reapNum];

  for (size_t i = 0; i < reapNum; ++i) {
    do {
      // Find us a good id to reaperunny
      size_t reapId = rand() % numItems;
      if (boxes[reapId]) {
        printf("Reaping  box n: %ld : slabId: %ld\n", reapId, slabIds[reapId]);

        if (1) {
          valk_slab_release_ptr(slab, boxes[reapId]);
        } else {
          VALK_WITH_ALLOC((valk_mem_allocator_t *)slab) {
            valk_mem_free(boxes[reapId]);
          }
        }
        boxes[reapId] = nullptr;
        break;
      }
    } while (true);
  }

  // ok we are done with the context one, just to keep things simple lets just
  // do the normal api
  for (size_t i = 0; i < reapNum; ++i) {
    newBoxes[i] = (valk_arc_box *)valk_slab_aquire(slab)->data;
    valk_arc_box_init(newBoxes[i], VALK_SUC, sizeof(newMsg));
    newBoxes[i]->allocator = (valk_mem_allocator_t *)slab;
    strncpy(newBoxes[i]->item, newMsg, sizeof(newMsg));
  }

  for (size_t i = 0; i < reapNum; ++i) {
    char *result = (char *)newBoxes[i]->item;
    VALK_TEST_ASSERT(strcmp(result, newMsg) == 0, "Shit got corrupted %d %s", i,
                     result);
  }

  for (size_t i = 0; i < numItems; ++i) {
    if (boxes[i]) {
      char *result = (char *)boxes[i]->item;
      VALK_TEST_ASSERT(strcmp(result, msg) == 0,
                       "Shit got corrupted %ld :: slabId: %ld :: %s", i,
                       slabIds[i], result);
    }
  }

  VALK_TEST_ASSERT(slab->numFree == 0, "Shit should be full %d", slab->numFree);

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
