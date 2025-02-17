#include "parser.h"
#include "testing.h"

#include <concurrency.h>
#include <sys/wait.h>
#include <unistd.h>

typedef struct {
  valk_test_suite_t *suite;
  valk_test_result_t *result;
  int someArg;
} test__arg;

static void _valk_void(void *v) {}

static valk_conc_res *test_callback(void *_arg) {
  test__arg *arg = _arg;
  // Unpack the test context from arg
  valk_test_suite_t *_suite = arg->suite;
  valk_test_result_t *_result = arg->result;
  printf("Getting called in the callback n shit \n");
  VALK_ASSERT(arg->someArg == 1337, "Expected the argument to be 1337");
  return valk_conc_res_suc((void *)1337, _valk_void);
}

void test_task_queue(VALK_TEST_ARGS()) {
  valk_lval_t *ast = VALK_FIXTURE("prelude");
  VALK_TEST();

  size_t maxSize = 5;

  // Should i make this a fixture ?
  test__arg arg = {
      .suite = _suite,
      .result = _result,
      .someArg = 1337,

  };

  printf("HTE FUCK\n");
  valk_task_queue queue = {0};
  valk_work_init(&queue, maxSize);

  printf("HTE FUCK 123 size: %ld %ld\n", queue.capacity, queue.count);
  // addd 7 items
  for (size_t i = 0; i < 8; i++) {

    valk_future *fut = valk_future_new();
    valk_promise *promise = valk_promise_new(fut);
    valk_task task = {.type = VALK_TASK,
                      .arg = &arg,
                      .func = test_callback,
                      .promise = promise};
    int err = valk_work_add(&queue, task);

    printf("WEll now %ld :: %ld\n", i, queue.count);

    if (err) {
      // cleanup if there was an error
      valk_promise_release(task.promise);
    }
    if (i >= maxSize) {
      VALK_ASSERT(err == 1,
                  "Expected add to return an error, if the queue is full ");
    } else {
      printf("WEll now %ld :: %d\n", i, queue.items[i].type);
      VALK_ASSERT(err == 0,
                  "Expected the add to return success  when it has space");
      VALK_ASSERT(((test__arg *)queue.items[i].arg)->someArg == arg.someArg,
                  "Expected the arg to be the one we constructed [offset: %d]",
                  i);
      VALK_ASSERT(
          queue.items[i].func == test_callback,
          "Expected the item to be the test callback [offset: %d] [ptr: %ld]",
          i, queue.items[i].func);
      VALK_ASSERT(
          queue.count == i + 1,
          "Expected the count to be 1 more than item offset [offset: %d]", i);
    }
  }

  VALK_ASSERT(queue.count == maxSize,
              "Expected the count to be the maximum size of the queue");

  VALK_ASSERT(queue.count == maxSize, "Expected the count to be 5");
  // pop 2 items
  valk_task task;
  for (size_t i = 0; i < 8; i++) {
    task.func = NULL;
    task.arg = NULL;
    task.promise = NULL;

    int res = valk_work_pop(&queue, &task);
    if (i >= maxSize) {
      VALK_ASSERT(
          res == 1,
          "Expected pop to return an error, if the queue is empty [offset: %d]",
          i);
      VALK_ASSERT(
          queue.count == 0,
          "Expected pop to return an error, if the queue is empty [offset: %d]",
          i);
    } else {
      VALK_ASSERT(
          res == 0,
          "Expected the add to return success  when it has space [offset: %d]",
          i);
      VALK_ASSERT(
          task.func == test_callback,
          "Expected the item to be the test callback [offset: %d] [ptr: %ld]",
          i, task.func);
      VALK_ASSERT(task.arg == (void *)&arg,
                  "Expected the arg to be the one we constructed [offset: %d]",
                  i);
      VALK_ASSERT(
          queue.count == (maxSize - i - 1),
          "Expected the count to be 1 more than item offset [offset: %d]", i);
      valk_promise_release(task.promise);
    }
  }

  VALK_PASS();
  valk_lval_free(ast);
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
  valk_worker_pool pool;
  test__arg arg;
  arg.suite = _suite;
  arg.result = _result;
  arg.someArg = 1337;
  int res = valk_start_pool(&pool);
  VALK_ASSERT(res == 0, "Threadpool didnt start [status: %d]", res);
  valk_conc_res *tst =
      valk_future_await(valk_schedule(&pool, &arg, test_callback));

  VALK_ASSERT(tst->type == VALK_SUC,
              "Expected  successfull result [result: %d, %s]", tst->type,
              tst->err.msg);
  VALK_ASSERT(res == 0, "Threadpool didnt drain");
  printf("Got response: %p, %p\n", tst->succ, (void *)1337);
  valk_drain_pool(&pool);
  printf("Bleeeh\n");
  valk_free_pool(&pool);
  VALK_PASS();
  valk_conc_res_release(tst);
  valk_lval_free(ast);
}

static void *__lval_copy(void *arg) { return valk_lval_copy(arg); }
static void __lval_free(void *arg) { valk_lval_free(arg); }
static void *__lenv_copy(void *arg) { return valk_lenv_copy(arg); }
static void __lenv_free(void *arg) { valk_lenv_free(arg); }

int main(int argc, const char **argv) {
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_concurrency", test_concurrency);
  valk_testsuite_add_test(suite, "test_task_queue", test_task_queue);

  // load fixtures
  // valk_lval_t *ast = valk_parse_file("src/prelude.valk");
  // valk_lenv_t *env = valk_lenv_empty();
  // valk_lenv_builtins(env); // load the builtins
  // valk_lval_t *r = valk_lval_eval(env, valk_lval_copy(ast));
  // valk_lval_free(r);

  // valk_testsuite_fixture_add(suite, "prelude", ast, __lval_copy,
  // __lval_free); valk_testsuite_fixture_add(suite, "env", env, __lenv_copy,
  // __lenv_free);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
