#include <concurrency.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "common.h"
#include "memory.h"
#include "parser.h"
#include "testing.h"

typedef struct {
  valk_test_suite_t *suite;
  valk_test_result_t *result;
  int someArg;
} test__arg;

static valk_arc_box *test_callback(valk_arc_box *_arg) {
  test__arg *arg = _arg->item;
  // Unpack the test context from arg
  // valk_test_suite_t *_suite = arg->suite;
  valk_test_result_t *_result = arg->result;
  VALK_TEST_ASSERT(arg->someArg == 1337, "Expected the argument to be 1337");
  valk_arc_box *res = valk_arc_box_new(VALK_SUC, 0);
  res->item = (void *)1337;
  return res;
}

void test_task_queue(VALK_TEST_ARGS()) {
  // valk_lval_t *ast = VALK_FIXTURE("prelude");
  VALK_TEST();

  size_t maxSize = 5;

  // Should i make this a fixture ?
  test__arg testArg = {
      .suite = _suite,
      .result = _result,
      .someArg = 1337,
  };

  valk_arc_box *argBox = valk_arc_box_new(VALK_SUC, sizeof(test__arg));
  *(test__arg *)argBox->item = testArg;

  valk_task_queue queue = {0};
  valk_work_init(&queue, maxSize);

  // addd 7 items
  for (size_t i = 0; i < 8; i++) {
    valk_future *fut = valk_future_new();


    valk_task task = {.type = VALK_TASK,
                      .arg = argBox,
                      .func = test_callback,
                      .promise = {fut}};

    valk_arc_retain(argBox);
    int err = valk_work_add(&queue, task);

    if (i >= maxSize) {
      VALK_TEST_ASSERT(
          err == 1, "Expected add to return an error, if the queue is full ");
      // valk_arc_box *bres = valk_arc_box_err("Cancelled");
      // valk_promise_respond(&task.promise, bres);
      // // cleanup if there was an error
      // valk_arc_release(bres);
    } else {
      VALK_TEST_ASSERT(err == 0,
                       "Expected the add to return success  when it has space");
      VALK_TEST_ASSERT(
          ((test__arg *)queue.items[i].arg->item)->someArg == testArg.someArg,
          "Expected the arg to be the one we constructed [offset: %d] expected "
          "%d, but but got %d",
          i, testArg.someArg, ((test__arg *)queue.items[i].arg->item)->someArg);
      VALK_TEST_ASSERT(
          queue.items[i].func == test_callback,
          "Expected the item to be the test callback [offset: %d] [ptr: %ld]",
          i, queue.items[i].func);
      VALK_TEST_ASSERT(
          queue.count == i + 1,
          "Expected the count to be 1 more than item offset [offset: %d]", i);

    }

    // valk_arc_release(fut);
  }

  VALK_TEST_ASSERT(queue.count == maxSize,
                   "Expected the count to be the maximum size of the queue");

  VALK_TEST_ASSERT(queue.count == maxSize, "Expected the count to be 5");
  // pop 2 items
  for (size_t i = 0; i < 8; i++) {
    valk_task task = {0};

    int res = valk_work_pop(&queue, &task);
    if (i >= maxSize) {
      VALK_TEST_ASSERT(
          res == 1,
          "Expected pop to return an error, if the queue is empty [offset: %d]",
          i);
      VALK_TEST_ASSERT(
          queue.count == 0,
          "Expected pop to return an error, if the queue is empty [offset: %d]",
          i);
    } else {
      VALK_TEST_ASSERT(
          res == 0,
          "Expected the add to return success  when it has space [offset: %d]",
          i);
      VALK_TEST_ASSERT(
          task.func == test_callback,
          "Expected the item to be the test callback [offset: %d] [ptr: %ld]",
          i, task.func);
      VALK_TEST_ASSERT(
          (queue.items[i].arg) == argBox,
          "Expected the arg to be the one we constructed [offset: %d]", i);
      VALK_TEST_ASSERT(
          queue.count == (maxSize - i - 1),
          "Expected the count to be 1 more than item offset [offset: %d]", i);

      // Release the promise
      valk_arc_box *bres = valk_arc_box_new(VALK_SUC, 0);
      valk_promise_respond(&task.promise, bres);
      valk_arc_release(bres);
    }
  }

  VALK_PASS();
  // valk_lval_free(ast);
  valk_work_free(&queue);
}

// void test_futures_simple(VALK_TEST_ARGS()) {
//   valk_lval_t *ast = VALK_FIXTURE("prelude");
//   VALK_TEST();
//
//   VALK_PASS();
//   valk_lval_free(ast);
// }

void test_concurrency(VALK_TEST_ARGS()) {
  valk_lval_t *ast = VALK_FIXTURE("prelude");
  VALK_TEST();
  // Should i make this a fixture ?
  test__arg testArg = {
      .suite = _suite,
      .result = _result,
      .someArg = 1337,
  };

  valk_arc_box *argBox = valk_arc_box_new(VALK_SUC, sizeof(test__arg));
  *(test__arg *)argBox->item = testArg;

  valk_worker_pool pool;
  // NOLINTNEXTLINE(clang-analyzer-security.insecureAPI.DeprecatedOrUnsafeBufferHandling)
  memset(&pool, 0, sizeof(valk_worker_pool));

  int res = valk_start_pool(&pool);
  VALK_TEST_ASSERT(res == 0, "Threadpool didnt start [status: %d]", res);
  valk_arc_box *tst =
      valk_future_await(valk_schedule(&pool, argBox, test_callback));

  VALK_TEST_ASSERT(tst->type == VALK_SUC,
                   "Expected  successfull result [result: %d, %s]", tst->type,
                   tst->item);
  VALK_TEST_ASSERT(res == 0, "Threadpool didnt drain");
  printf("Got response: %p, %p\n", tst->item, (void *)1337);
  valk_drain_pool(&pool);
  valk_free_pool(&pool);
  VALK_PASS();
  valk_arc_release(tst);
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // valk_testsuite_add_test(suite, "test_concurrency", test_concurrency);
  // valk_testsuite_add_test(suite, "test_task_queue", test_task_queue);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
