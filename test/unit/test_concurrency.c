#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/common.h"
#include "../../src/concurrency.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>

void test_arc_box_new(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 64);
  VALK_TEST_ASSERT(box != NULL, "arc_box_new should return non-NULL");
  VALK_TEST_ASSERT(box->type == VALK_SUC, "type should be VALK_SUC");
  VALK_TEST_ASSERT(box->refcount == 1, "refcount should be 1");
  VALK_TEST_ASSERT(box->capacity == 64, "capacity should be 64");
  VALK_TEST_ASSERT(box->item != NULL, "item pointer should be set");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  char buffer[sizeof(valk_arc_box) + 64];
  valk_arc_box *box = (valk_arc_box *)buffer;
  valk_arc_box_init(box, VALK_ERR, 64);

  VALK_TEST_ASSERT(box->type == VALK_ERR, "type should be VALK_ERR");
  VALK_TEST_ASSERT(box->refcount == 1, "refcount should be 1");
  VALK_TEST_ASSERT(box->capacity == 64, "capacity should be 64");
  VALK_TEST_ASSERT(box->allocator == NULL, "allocator should be NULL after init");
  VALK_TEST_ASSERT(box->free == NULL, "free should be NULL after init");

  VALK_PASS();
}

void test_arc_box_err(VALK_TEST_ARGS()) {
  VALK_TEST();

  const char *msg = "Test error message";
  valk_arc_box *box = valk_arc_box_err(msg);

  VALK_TEST_ASSERT(box != NULL, "arc_box_err should return non-NULL");
  VALK_TEST_ASSERT(box->type == VALK_ERR, "type should be VALK_ERR");
  VALK_TEST_ASSERT(box->refcount == 1, "refcount should be 1");
  VALK_TEST_ASSERT(strcmp(box->item, msg) == 0, "item should contain error message");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_retain_release(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 32);
  VALK_TEST_ASSERT(box->refcount == 1, "Initial refcount should be 1");

  valk_arc_retain(box);
  VALK_TEST_ASSERT(box->refcount == 2, "Refcount after retain should be 2");

  valk_arc_retain(box);
  VALK_TEST_ASSERT(box->refcount == 3, "Refcount after second retain should be 3");

  valk_arc_release(box);
  VALK_TEST_ASSERT(box->refcount == 2, "Refcount after release should be 2");

  valk_arc_release(box);
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount after second release should be 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_future_new(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  VALK_TEST_ASSERT(fut != NULL, "future_new should return non-NULL");
  VALK_TEST_ASSERT(fut->done == 0, "Future should not be done initially");
  VALK_TEST_ASSERT(fut->refcount == 1, "Initial refcount should be 1");
  VALK_TEST_ASSERT(fut->item == NULL, "item should be NULL initially");
  VALK_TEST_ASSERT(fut->andThen.count == 0, "andThen should be empty");

  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 8);
  valk_promise p = {.item = fut};
  valk_promise_respond(&p, result);
  valk_arc_release(result);

  valk_arc_release(fut);

  VALK_PASS();
}

void test_future_done(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 32);
  valk_future *fut = valk_future_done(box);

  VALK_TEST_ASSERT(fut != NULL, "future_done should return non-NULL");
  VALK_TEST_ASSERT(fut->done == 1, "Future should be done");
  VALK_TEST_ASSERT(fut->item == box, "item should be the provided box");

  valk_arc_release(fut);
  valk_arc_release(box);

  VALK_PASS();
}

void test_promise_respond(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 16);
  strcpy(result->item, "test");

  VALK_TEST_ASSERT(fut->done == 0, "Future should not be done before respond");

  valk_promise_respond(&p, result);

  VALK_TEST_ASSERT(fut->done == 1, "Future should be done after respond");
  VALK_TEST_ASSERT(fut->item == result, "Future item should be the result");

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_promise_respond_double(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  valk_arc_box *result1 = valk_arc_box_new(VALK_SUC, 16);
  valk_arc_box *result2 = valk_arc_box_new(VALK_SUC, 16);

  valk_promise_respond(&p, result1);
  valk_promise_respond(&p, result2);

  VALK_TEST_ASSERT(fut->item == result1, "First response should stick");

  valk_arc_release(result1);
  valk_arc_release(result2);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_future_await_resolved(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 32);
  strcpy(box->item, "awaited");
  valk_future *fut = valk_future_done(box);

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await(fut);

  VALK_TEST_ASSERT(result == box, "await should return the resolved value");
  VALK_TEST_ASSERT(strcmp(result->item, "awaited") == 0, "Value should be correct");

  valk_arc_release(fut);
  valk_arc_release(box);

  VALK_PASS();
}

void test_future_await_timeout_already_done(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 32);
  valk_future *fut = valk_future_done(box);

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await_timeout(fut, 100);

  VALK_TEST_ASSERT(result == box, "await_timeout on done future should return immediately");

  valk_arc_release(result);
  valk_arc_release(box);

  VALK_PASS();
}

static void *respond_after_delay(void *arg) {
  valk_mem_init_malloc();
  valk_promise *p = arg;
  usleep(10000);
  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 8);
  valk_promise_respond(p, result);
  valk_arc_release(result);
  return NULL;
}

void test_future_await_with_thread(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  pthread_t thread;
  pthread_create(&thread, NULL, respond_after_delay, &p);

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await(fut);

  VALK_TEST_ASSERT(result != NULL, "await should return result from thread");
  VALK_TEST_ASSERT(result->type == VALK_SUC, "Result type should be VALK_SUC");

  pthread_join(thread, NULL);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_res_type_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_SUC == 0, "VALK_SUC should be 0");
  VALK_TEST_ASSERT(VALK_ERR == 1, "VALK_ERR should be 1");

  VALK_PASS();
}

void test_task_type_enum(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT(VALK_TASK == 0, "VALK_TASK should be 0");
  VALK_TEST_ASSERT(VALK_POISON == 1, "VALK_POISON should be 1");

  VALK_PASS();
}

static bool and_then_called = false;
static valk_arc_box *and_then_result = NULL;

static void and_then_callback(void *arg, valk_arc_box *box) {
  (void)arg;
  and_then_called = true;
  and_then_result = box;
}

void test_future_and_then_immediate(VALK_TEST_ARGS()) {
  VALK_TEST();

  and_then_called = false;
  and_then_result = NULL;

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 16);
  valk_future *fut = valk_future_done(box);

  struct valk_future_and_then cb = {.arg = NULL, .cb = and_then_callback};
  valk_future_and_then(fut, &cb);

  VALK_TEST_ASSERT(and_then_called == true, "Callback should be called immediately for done future");
  VALK_TEST_ASSERT(and_then_result == box, "Callback should receive the result");

  valk_arc_release(box);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_future_and_then_pending(VALK_TEST_ARGS()) {
  VALK_TEST();

  and_then_called = false;
  and_then_result = NULL;

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  struct valk_future_and_then cb = {.arg = NULL, .cb = and_then_callback};
  valk_future_and_then(fut, &cb);

  VALK_TEST_ASSERT(and_then_called == false, "Callback should not be called for pending future");
  VALK_TEST_ASSERT(fut->andThen.count == 1, "andThen should have 1 callback");

  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 8);
  valk_promise_respond(&p, result);

  VALK_TEST_ASSERT(and_then_called == true, "Callback should be called after resolve");
  VALK_TEST_ASSERT(and_then_result == result, "Callback should receive the result");

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_arc_box_refcount_boundary(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 16);
  VALK_TEST_ASSERT(box->refcount == 1, "Initial refcount should be 1");

  for (int i = 0; i < 100; i++) {
    valk_arc_retain(box);
  }
  VALK_TEST_ASSERT(box->refcount == 101, "Refcount should be 101");

  for (int i = 0; i < 100; i++) {
    valk_arc_release(box);
  }
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount should be back to 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_future_multiple_and_then(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  static int callback_counts[3] = {0, 0, 0};
  callback_counts[0] = 0;
  callback_counts[1] = 0;
  callback_counts[2] = 0;

  struct valk_future_and_then cb1 = {.arg = &callback_counts[0], .cb = and_then_callback};
  struct valk_future_and_then cb2 = {.arg = &callback_counts[1], .cb = and_then_callback};
  struct valk_future_and_then cb3 = {.arg = &callback_counts[2], .cb = and_then_callback};

  valk_future_and_then(fut, &cb1);
  valk_future_and_then(fut, &cb2);
  valk_future_and_then(fut, &cb3);

  VALK_TEST_ASSERT(fut->andThen.count == 3, "Should have 3 callbacks registered");

  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 8);
  valk_promise_respond(&p, result);

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_arc_box_with_data(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 256);

  char *data = (char *)box->item;
  strcpy(data, "Hello, World!");

  VALK_TEST_ASSERT(strcmp(data, "Hello, World!") == 0, "Data should be preserved");
  VALK_TEST_ASSERT(box->capacity == 256, "Capacity should be 256");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_err_empty_message(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_err("");

  VALK_TEST_ASSERT(box != NULL, "Should create box for empty message");
  VALK_TEST_ASSERT(box->type == VALK_ERR, "Type should be VALK_ERR");
  VALK_TEST_ASSERT(strlen(box->item) == 0, "Message should be empty");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_err_long_message(VALK_TEST_ARGS()) {
  VALK_TEST();

  char long_msg[1024];
  memset(long_msg, 'A', sizeof(long_msg) - 1);
  long_msg[sizeof(long_msg) - 1] = '\0';

  valk_arc_box *box = valk_arc_box_err(long_msg);

  VALK_TEST_ASSERT(box != NULL, "Should create box for long message");
  VALK_TEST_ASSERT(box->type == VALK_ERR, "Type should be VALK_ERR");
  VALK_TEST_ASSERT(strcmp(box->item, long_msg) == 0, "Message should match");

  valk_arc_release(box);

  VALK_PASS();
}

void test_future_retain_release(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  VALK_TEST_ASSERT(fut->refcount == 1, "Initial refcount should be 1");

  valk_arc_retain(fut);
  VALK_TEST_ASSERT(fut->refcount == 2, "Refcount should be 2");

  valk_arc_retain(fut);
  VALK_TEST_ASSERT(fut->refcount == 3, "Refcount should be 3");

  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 8);
  valk_promise p = {.item = fut};
  valk_promise_respond(&p, result);
  valk_arc_release(result);

  valk_arc_release(fut);
  valk_arc_release(fut);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_arc_box_zero_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 0);

  VALK_TEST_ASSERT(box != NULL, "Should create box with zero capacity");
  VALK_TEST_ASSERT(box->capacity == 0, "Capacity should be 0");
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount should be 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_large_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 1024 * 1024);

  VALK_TEST_ASSERT(box != NULL, "Should create box with large capacity");
  VALK_TEST_ASSERT(box->capacity == 1024 * 1024, "Capacity should be 1MB");
  VALK_TEST_ASSERT(box->refcount == 1, "Refcount should be 1");

  valk_arc_release(box);

  VALK_PASS();
}

void test_arc_box_type_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *suc_box = valk_arc_box_new(VALK_SUC, 16);
  valk_arc_box *err_box = valk_arc_box_new(VALK_ERR, 16);

  VALK_TEST_ASSERT(suc_box->type == VALK_SUC, "Type should be VALK_SUC");
  VALK_TEST_ASSERT(err_box->type == VALK_ERR, "Type should be VALK_ERR");

  valk_arc_release(suc_box);
  valk_arc_release(err_box);

  VALK_PASS();
}

void test_future_multiple_retains(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 16);
  valk_future *fut = valk_future_done(box);

  for (int i = 0; i < 10; i++) {
    valk_arc_retain(fut);
  }
  VALK_TEST_ASSERT(fut->refcount == 11, "Refcount should be 11");

  for (int i = 0; i < 10; i++) {
    valk_arc_release(fut);
  }
  VALK_TEST_ASSERT(fut->refcount == 1, "Refcount should be 1");

  valk_arc_release(box);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_arc_box_item_pointer(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 128);

  VALK_TEST_ASSERT(box->item != NULL, "Item pointer should be set");
  VALK_TEST_ASSERT((char *)box->item > (char *)box, "Item should be after box header");

  valk_arc_release(box);

  VALK_PASS();
}

void test_future_done_refcount(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 16);
  VALK_TEST_ASSERT(box->refcount == 1, "Box initial refcount should be 1");

  valk_future *fut = valk_future_done(box);
  VALK_TEST_ASSERT(fut->refcount == 1, "Future initial refcount should be 1");
  VALK_TEST_ASSERT(box->refcount == 2, "Box refcount should be 2 after future_done");

  valk_arc_release(fut);
  valk_arc_release(box);

  VALK_PASS();
}

void test_promise_respond_null_result(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 0);
  valk_promise_respond(&p, result);

  VALK_TEST_ASSERT(fut->done == 1, "Future should be done");
  VALK_TEST_ASSERT(fut->item == result, "Future item should be result");

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_arc_retain_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_arc_box *box = valk_arc_box_new(VALK_SUC, 16);
  VALK_TEST_ASSERT(box != NULL, "Box should be created");

  valk_arc_retain(box);
  VALK_TEST_ASSERT(box->refcount == 2, "Refcount after retain should be 2");

  valk_arc_release(box);
  valk_arc_release(box);

  VALK_PASS();
}

void test_and_then_array_grows(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  VALK_TEST_ASSERT(fut->andThen.count == 0, "andThen should start empty");

  valk_arc_box *result = valk_arc_box_new(VALK_SUC, 8);
  valk_promise_respond(&p, result);

  VALK_TEST_ASSERT(fut->done == 1, "Future should be done");

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_task_types(VALK_TEST_ARGS()) {
  VALK_TEST();

  VALK_TEST_ASSERT((int)VALK_TASK == 0, "VALK_TASK should be 0");
  VALK_TEST_ASSERT((int)VALK_POISON == 1, "VALK_POISON should be 1");

  VALK_PASS();
}

static valk_arc_box *simple_work_func(valk_arc_box *arg) {
  int *val = (int *)arg->item;
  *val = *val * 2;
  return arg;
}

void test_worker_pool_lifecycle(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  int err = valk_start_pool(&pool);
  VALK_TEST_ASSERT(err == 0, "Pool should start successfully");
  VALK_TEST_ASSERT(pool.count == 4, "Pool should have 4 workers");

  valk_free_pool(&pool);

  VALK_PASS();
}

void test_schedule_work(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(int));
  *(int *)arg->item = 21;

  valk_future *fut = valk_schedule(&pool, arg, simple_work_func);
  VALK_TEST_ASSERT(fut != NULL, "Schedule should return a future");

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await(fut);
  VALK_TEST_ASSERT(result != NULL, "Result should not be NULL");
  VALK_TEST_ASSERT(result->type == VALK_SUC, "Result should be success");
  VALK_TEST_ASSERT(*(int *)result->item == 42, "Value should be doubled to 42");

  valk_arc_release(arg);
  valk_arc_release(fut);
  valk_free_pool(&pool);

  VALK_PASS();
}

void test_schedule_multiple_tasks(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_future *futures[10];
  valk_arc_box *args[10];

  for (int i = 0; i < 10; i++) {
    args[i] = valk_arc_box_new(VALK_SUC, sizeof(int));
    *(int *)args[i]->item = i + 1;
    futures[i] = valk_schedule(&pool, args[i], simple_work_func);
    valk_arc_retain(futures[i]);
  }

  for (int i = 0; i < 10; i++) {
    valk_arc_box *result = valk_future_await(futures[i]);
    VALK_TEST_ASSERT(result->type == VALK_SUC, "Task %d should succeed", i);
    VALK_TEST_ASSERT(*(int *)result->item == (i + 1) * 2, "Task %d result should be %d", i, (i + 1) * 2);
    valk_arc_release(args[i]);
    valk_arc_release(futures[i]);
  }

  valk_free_pool(&pool);

  VALK_PASS();
}

void test_drain_pool(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(int));
  *(int *)arg->item = 5;
  valk_future *fut = valk_schedule(&pool, arg, simple_work_func);
  valk_arc_retain(fut);

  valk_drain_pool(&pool);

  valk_arc_box *result = valk_future_await(fut);
  VALK_TEST_ASSERT(result != NULL, "Should get result after drain");

  valk_arc_release(arg);
  valk_arc_release(fut);
  valk_free_pool(&pool);

  VALK_PASS();
}

void test_schedule_after_shutdown(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);
  valk_drain_pool(&pool);

  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(int));
  *(int *)arg->item = 10;
  valk_future *fut = valk_schedule(&pool, arg, simple_work_func);

  VALK_TEST_ASSERT(fut != NULL, "Should return future even during shutdown");
  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await(fut);
  VALK_TEST_ASSERT(result->type == VALK_ERR, "Should return error during shutdown");

  valk_arc_release(arg);
  valk_arc_release(fut);
  valk_free_pool(&pool);

  VALK_PASS();
}



void test_future_await_timeout_expires(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await_timeout(fut, 10);

  VALK_TEST_ASSERT(result != NULL, "Should return result on timeout");
  VALK_TEST_ASSERT(result->type == VALK_ERR, "Should return error on timeout");
  VALK_TEST_ASSERT(strstr(result->item, "Timeout") != NULL, "Error should mention timeout");

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_future_await_timeout_large_ms(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();
  valk_promise p = {.item = fut};

  pthread_t thread;
  pthread_create(&thread, NULL, respond_after_delay, &p);

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await_timeout(fut, 5000);

  VALK_TEST_ASSERT(result != NULL, "Should return result");
  VALK_TEST_ASSERT(result->type == VALK_SUC, "Should succeed before timeout");

  pthread_join(thread, NULL);
  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_future_await_timeout_ns_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await_timeout(fut, 1999);

  VALK_TEST_ASSERT(result != NULL, "Should return result on timeout");
  VALK_TEST_ASSERT(result->type == VALK_ERR, "Should return error on timeout");

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}

void test_drain_pool_double_drain(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_drain_pool(&pool);
  valk_drain_pool(&pool);

  valk_free_pool(&pool);

  VALK_PASS();
}

void test_drain_pool_with_pending_work(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_arc_box *args[5];
  valk_future *futures[5];
  for (int i = 0; i < 5; i++) {
    args[i] = valk_arc_box_new(VALK_SUC, sizeof(int));
    *(int *)args[i]->item = i;
    futures[i] = valk_schedule(&pool, args[i], simple_work_func);
    valk_arc_retain(futures[i]);
  }

  valk_drain_pool(&pool);

  for (int i = 0; i < 5; i++) {
    valk_arc_box *result = valk_future_await(futures[i]);
    VALK_TEST_ASSERT(result != NULL, "Should get result for task %d", i);
    valk_arc_release(args[i]);
    valk_arc_release(futures[i]);
  }

  valk_free_pool(&pool);

  VALK_PASS();
}

void test_free_pool_with_pending_work(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(int));
  *(int *)arg->item = 42;
  valk_future *fut = valk_schedule(&pool, arg, simple_work_func);
  valk_arc_retain(fut);

  valk_arc_box *result = valk_future_await(fut);
  VALK_TEST_ASSERT(result != NULL, "Should get result");

  valk_arc_release(arg);
  valk_arc_release(fut);
  valk_free_pool(&pool);

  VALK_PASS();
}

static valk_arc_box *error_work_func(valk_arc_box *arg) {
  (void)arg;
  return valk_arc_box_err("Work failed");
}

void test_schedule_error_result(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(int));
  *(int *)arg->item = 10;
  valk_future *fut = valk_schedule(&pool, arg, error_work_func);
  valk_arc_retain(fut);

  valk_arc_box *result = valk_future_await(fut);
  VALK_TEST_ASSERT(result != NULL, "Should get error result");
  VALK_TEST_ASSERT(result->type == VALK_ERR, "Result should be error type");

  valk_arc_release(arg);
  valk_arc_release(fut);
  valk_free_pool(&pool);

  VALK_PASS();
}

void test_future_await_timeout_zero(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_future *fut = valk_future_new();

  valk_arc_retain(fut);
  valk_arc_box *result = valk_future_await_timeout(fut, 0);

  VALK_TEST_ASSERT(result != NULL, "Should return result on timeout");
  VALK_TEST_ASSERT(result->type == VALK_ERR, "Should return error on timeout");

  valk_arc_release(result);
  valk_arc_release(fut);

  VALK_PASS();
}



void test_multiple_futures_concurrent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_worker_pool pool = {0};
  valk_start_pool(&pool);

  valk_future *futures[20];
  valk_arc_box *args[20];

  for (int i = 0; i < 20; i++) {
    args[i] = valk_arc_box_new(VALK_SUC, sizeof(int));
    *(int *)args[i]->item = i;
    futures[i] = valk_schedule(&pool, args[i], simple_work_func);
    valk_arc_retain(futures[i]);
  }

  for (int i = 0; i < 20; i++) {
    valk_arc_box *result = valk_future_await(futures[i]);
    VALK_TEST_ASSERT(result != NULL, "Task %d should complete", i);
    valk_arc_release(args[i]);
    valk_arc_release(futures[i]);
  }

  valk_free_pool(&pool);

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_arc_box_new", test_arc_box_new);
  valk_testsuite_add_test(suite, "test_arc_box_init", test_arc_box_init);
  valk_testsuite_add_test(suite, "test_arc_box_err", test_arc_box_err);
  valk_testsuite_add_test(suite, "test_arc_retain_release", test_arc_retain_release);
  valk_testsuite_add_test(suite, "test_future_new", test_future_new);
  valk_testsuite_add_test(suite, "test_future_done", test_future_done);
  valk_testsuite_add_test(suite, "test_promise_respond", test_promise_respond);
  valk_testsuite_add_test(suite, "test_promise_respond_double", test_promise_respond_double);
  valk_testsuite_add_test(suite, "test_future_await_resolved", test_future_await_resolved);
  valk_testsuite_add_test(suite, "test_future_await_timeout_already_done", test_future_await_timeout_already_done);
  valk_testsuite_add_test(suite, "test_future_await_with_thread", test_future_await_with_thread);
  valk_testsuite_add_test(suite, "test_res_type_enum", test_res_type_enum);
  valk_testsuite_add_test(suite, "test_task_type_enum", test_task_type_enum);
  valk_testsuite_add_test(suite, "test_future_and_then_immediate", test_future_and_then_immediate);
  valk_testsuite_add_test(suite, "test_future_and_then_pending", test_future_and_then_pending);
  valk_testsuite_add_test(suite, "test_arc_box_refcount_boundary", test_arc_box_refcount_boundary);
  valk_testsuite_add_test(suite, "test_future_multiple_and_then", test_future_multiple_and_then);
  valk_testsuite_add_test(suite, "test_arc_box_with_data", test_arc_box_with_data);
  valk_testsuite_add_test(suite, "test_arc_box_err_empty_message", test_arc_box_err_empty_message);
  valk_testsuite_add_test(suite, "test_arc_box_err_long_message", test_arc_box_err_long_message);
  valk_testsuite_add_test(suite, "test_future_retain_release", test_future_retain_release);
  valk_testsuite_add_test(suite, "test_arc_box_zero_capacity", test_arc_box_zero_capacity);
  valk_testsuite_add_test(suite, "test_arc_box_large_capacity", test_arc_box_large_capacity);
  valk_testsuite_add_test(suite, "test_arc_box_type_values", test_arc_box_type_values);
  valk_testsuite_add_test(suite, "test_future_multiple_retains", test_future_multiple_retains);
  valk_testsuite_add_test(suite, "test_arc_box_item_pointer", test_arc_box_item_pointer);
  valk_testsuite_add_test(suite, "test_future_done_refcount", test_future_done_refcount);
  valk_testsuite_add_test(suite, "test_promise_respond_null_result", test_promise_respond_null_result);
  valk_testsuite_add_test(suite, "test_arc_retain_null", test_arc_retain_null);
  valk_testsuite_add_test(suite, "test_and_then_array_grows", test_and_then_array_grows);
  valk_testsuite_add_test(suite, "test_task_types", test_task_types);
  valk_testsuite_add_test(suite, "test_worker_pool_lifecycle", test_worker_pool_lifecycle);
  valk_testsuite_add_test(suite, "test_schedule_work", test_schedule_work);
  valk_testsuite_add_test(suite, "test_schedule_multiple_tasks", test_schedule_multiple_tasks);
  valk_testsuite_add_test(suite, "test_drain_pool", test_drain_pool);
  valk_testsuite_add_test(suite, "test_schedule_after_shutdown", test_schedule_after_shutdown);
  valk_testsuite_add_test(suite, "test_future_await_timeout_expires", test_future_await_timeout_expires);
  valk_testsuite_add_test(suite, "test_future_await_timeout_large_ms", test_future_await_timeout_large_ms);
  valk_testsuite_add_test(suite, "test_future_await_timeout_ns_overflow", test_future_await_timeout_ns_overflow);
  valk_testsuite_add_test(suite, "test_drain_pool_double_drain", test_drain_pool_double_drain);
  valk_testsuite_add_test(suite, "test_drain_pool_with_pending_work", test_drain_pool_with_pending_work);
  valk_testsuite_add_test(suite, "test_free_pool_with_pending_work", test_free_pool_with_pending_work);
  valk_testsuite_add_test(suite, "test_schedule_error_result", test_schedule_error_result);
  valk_testsuite_add_test(suite, "test_future_await_timeout_zero", test_future_await_timeout_zero);
  valk_testsuite_add_test(suite, "test_multiple_futures_concurrent", test_multiple_futures_concurrent);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
