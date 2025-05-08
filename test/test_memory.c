#include "test_memory.h"
#include "common.h"
#include "concurrency.h"
#include "memory.h"
#include "testing.h"
#include <math.h>
#include <pthread.h>
#include <time.h>
#include <unistd.h>

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

  const char msg[] = "Get fucked";

  VALK_TEST();

  int itemLen = sizeof(valk_arc_box) + sizeof(msg);
  size_t numItems = rand() % 1000;
  valk_slab_t *slab = valk_slab_new(itemLen, numItems);

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

        if (rand() % 2) {
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

typedef struct {
  size_t id;
  valk_slab_t *slab;
  valk_arc_box **boxes;
  size_t numItems;
  size_t rand;
} shuffle_thread_arg_t;

static size_t __next_thread_rand(size_t *state) {
  // TODO(networking): i dont trust chatgpt what the heck does this do?
  size_t x = *state;
  x ^= x << 13;
  x ^= x >> 17;
  x ^= x << 5;
  *state = x;
  return x;
}

void *slab_shuffle_thread(void *arg) {

  shuffle_thread_arg_t *params = arg;
  size_t numBoxes = 0;
  for (size_t j = 0; j < params->numItems; ++j) {
    if (params->boxes[j] != nullptr) {
      ++numBoxes;
    }
  }
  if (numBoxes > 0) {
    printf("[T%ld] Starting service thread with %ld boxes \n", params->id,
           numBoxes);

  } else {
    printf("[T%ld] Did not receive any boxes, shutting down\n", params->id);
    return nullptr;
  }

  // lets get to it
  valk_arc_box *myBoxes[numBoxes];
  for (size_t j = 0, remBoxes = numBoxes; j < params->numItems; ++j) {
    if (params->boxes[j] != nullptr) {
      myBoxes[--remBoxes] = params->boxes[j];
    }
  }

  for (size_t iteration = __next_thread_rand(&params->rand) % 100;
       iteration > 0; --iteration) {
    // randomly allocate / release the handles
    size_t randomBox = (__next_thread_rand(&params->rand)) % numBoxes;
    // Do something or skip it
    if ((__next_thread_rand(&params->rand)) % 2) {

      if (myBoxes[randomBox] == nullptr) {
        myBoxes[randomBox] =
            (valk_arc_box *)valk_slab_aquire(params->slab)->data;
      } else {
        valk_slab_release_ptr(params->slab, myBoxes[randomBox]);
        myBoxes[randomBox] = nullptr;
      }
    }

    // TODO(networking): maybe should ald some logic to randomly pause for
    // microsecs
  }

  return 0;
}

void test_slab_concurrency(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char msg[] = "Get fucked";
  int itemLen = sizeof(valk_arc_box) + sizeof(msg);
  size_t numItems = rand() % 1000;

  valk_slab_t *slab = valk_slab_new(itemLen, numItems);

  valk_arc_box *boxes[numItems];
  printf("Aquiring %ld boxes\n", numItems);

  size_t slabIds[numItems];

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
  VALK_TEST_ASSERT(slab->numFree == 0, "Shit should be full %d", slab->numFree);

  // Split the boxes randomly between threads
  size_t numThreads = 1 + rand() % 10;
  valk_arc_box *splitBoxes[numThreads][numItems];

  for (size_t i = 0; i < numThreads; ++i) {
    for (size_t j = 0; j < numItems; ++j) {
      splitBoxes[i][j] = nullptr;
    }
  }

  // TODO(networking): this is unix specific threading code using pthreads
  // Eventually want to support windows so should replace it with my own
  // conurrency

  for (size_t i = 0; i < numItems; ++i) {
    size_t tId = rand() % numThreads;
    do {
      size_t reapId = rand() % numItems;
      if (boxes[reapId] != nullptr) {
        printf("Select  box n: %ld : slabId: %ld : Tid: %ld\n", reapId,
               slabIds[reapId], tId);
        splitBoxes[tId][reapId] = boxes[reapId];
        boxes[reapId] = nullptr;
        break;
      }
    } while (true);
  }

  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_t threadIds[numThreads];

  shuffle_thread_arg_t args[numThreads];
  for (size_t i = 0; i < numThreads; ++i) {
    args[i].id = i;
    args[i].boxes = splitBoxes[i];
    args[i].slab = slab;
    args[i].numItems = numItems;
    args[i].rand = rand();

    int res =
        pthread_create(&threadIds[i], &attr, slab_shuffle_thread, &args[i]);
    if (res) {
      printf("Failed creating thread [%ld]\n", i);
    }
  }

  for (size_t i = 0; i < numThreads; ++i) {
    void *foo;
    pthread_join(threadIds[i], &foo);
    VALK_TEST_ASSERT(foo == 0,
                     "Expected the result of a thread to be success %d",
                     (size_t)foo);
  }

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  size_t seed;
#if 0
  // seed = 1746502782; // 8 threads with 1000 items
  // seed = 1746685013; // floating point exception
  seed = 1746685993; // crashig singlethreaded
#else

  struct timespec ts;
  timespec_get(&ts, TIME_UTC);
  seed = ts.tv_sec;
#endif
  srand(seed);
  printf("Seeding rand with %ld\n", seed);

  // Use malloc for now, by default
  // probably should think of how to add this by default everywhere
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_implicit_alloc", test_implicit_alloc);

  valk_testsuite_add_test(suite, "test_slab_alloc", test_slab_alloc);
  valk_testsuite_add_test(suite, "test_slab_concurrency",
                          test_slab_concurrency);
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
