#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/system/aio_chase_lev.h"

#include <pthread.h>
#include <stdlib.h>

void test_chase_lev_init_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  ASSERT_TRUE(valk_chase_lev_empty(&deque));
  ASSERT_EQ(valk_chase_lev_size(&deque), 0);

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_push_pop_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  int value = 42;
  valk_chase_lev_push(&deque, &value);

  ASSERT_FALSE(valk_chase_lev_empty(&deque));
  ASSERT_EQ(valk_chase_lev_size(&deque), 1);

  void *result = valk_chase_lev_pop(&deque);
  ASSERT_EQ(result, &value);
  ASSERT_TRUE(valk_chase_lev_empty(&deque));

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_push_pop_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  int values[5] = {1, 2, 3, 4, 5};
  for (int i = 0; i < 5; i++) {
    valk_chase_lev_push(&deque, &values[i]);
  }

  ASSERT_EQ(valk_chase_lev_size(&deque), 5);

  void *result = valk_chase_lev_pop(&deque);
  ASSERT_EQ(result, &values[4]);

  result = valk_chase_lev_pop(&deque);
  ASSERT_EQ(result, &values[3]);

  result = valk_chase_lev_pop(&deque);
  ASSERT_EQ(result, &values[2]);

  ASSERT_EQ(valk_chase_lev_size(&deque), 2);

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_pop_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  void *result = valk_chase_lev_pop(&deque);
  ASSERT_EQ(result, VALK_CHASE_LEV_EMPTY);

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_steal_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  int value = 42;
  valk_chase_lev_push(&deque, &value);

  void *result = valk_chase_lev_steal(&deque);
  ASSERT_EQ(result, &value);
  ASSERT_TRUE(valk_chase_lev_empty(&deque));

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_steal_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  void *result = valk_chase_lev_steal(&deque);
  ASSERT_EQ(result, VALK_CHASE_LEV_EMPTY);

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_steal_order(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  int values[3] = {1, 2, 3};
  for (int i = 0; i < 3; i++) {
    valk_chase_lev_push(&deque, &values[i]);
  }

  void *first = valk_chase_lev_steal(&deque);
  ASSERT_EQ(first, &values[0]);

  void *second = valk_chase_lev_steal(&deque);
  ASSERT_EQ(second, &values[1]);

  void *third = valk_chase_lev_steal(&deque);
  ASSERT_EQ(third, &values[2]);

  ASSERT_TRUE(valk_chase_lev_empty(&deque));

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_mixed_pop_steal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  int values[4] = {1, 2, 3, 4};
  for (int i = 0; i < 4; i++) {
    valk_chase_lev_push(&deque, &values[i]);
  }

  void *stolen = valk_chase_lev_steal(&deque);
  ASSERT_EQ(stolen, &values[0]);

  void *popped = valk_chase_lev_pop(&deque);
  ASSERT_EQ(popped, &values[3]);

  ASSERT_EQ(valk_chase_lev_size(&deque), 2);

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_grow(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 4);

  int values[10];
  for (int i = 0; i < 10; i++) {
    values[i] = i;
    valk_chase_lev_push(&deque, &values[i]);
  }

  ASSERT_EQ(valk_chase_lev_size(&deque), 10);

  for (int i = 9; i >= 0; i--) {
    void *result = valk_chase_lev_pop(&deque);
    ASSERT_EQ(result, &values[i]);
  }

  ASSERT_TRUE(valk_chase_lev_empty(&deque));

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_single_element_race(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 16);

  int value = 42;
  valk_chase_lev_push(&deque, &value);

  void *pop_result = valk_chase_lev_pop(&deque);

  if (pop_result == VALK_CHASE_LEV_EMPTY) {
    VALK_FAIL("Should have gotten the element on pop");
  }

  ASSERT_EQ(pop_result, &value);
  ASSERT_TRUE(valk_chase_lev_empty(&deque));

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

typedef struct {
  valk_chase_lev_deque_t *deque;
  int *values;
  int count;
  _Atomic int *stolen_count;
} stealer_arg_t;

static void *stealer_thread(void *arg) {
  stealer_arg_t *ctx = (stealer_arg_t *)arg;
  int stolen = 0;

  for (int i = 0; i < ctx->count * 2; i++) {
    void *item = valk_chase_lev_steal(ctx->deque);
    if (item != VALK_CHASE_LEV_EMPTY && item != VALK_CHASE_LEV_ABORT) {
      stolen++;
    }
  }

  atomic_fetch_add(ctx->stolen_count, stolen);
  return NULL;
}

void test_chase_lev_concurrent_steal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 64);

  int values[100];
  for (int i = 0; i < 100; i++) {
    values[i] = i;
    valk_chase_lev_push(&deque, &values[i]);
  }

  _Atomic int stolen_count = 0;
  stealer_arg_t arg = {
    .deque = &deque,
    .values = values,
    .count = 100,
    .stolen_count = &stolen_count,
  };

  pthread_t threads[4];
  for (int i = 0; i < 4; i++) {
    pthread_create(&threads[i], NULL, stealer_thread, &arg);
  }

  int popped = 0;
  void *item;
  while ((item = valk_chase_lev_pop(&deque)) != VALK_CHASE_LEV_EMPTY) {
    popped++;
  }

  for (int i = 0; i < 4; i++) {
    pthread_join(threads[i], NULL);
  }

  int total = popped + atomic_load(&stolen_count);
  ASSERT_EQ(total, 100);

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_stress_push_pop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 8);

  const int iterations = 1000;
  int *values[iterations];

  for (int i = 0; i < iterations; i++) {
    values[i] = malloc(sizeof(int));
    *values[i] = i;
    valk_chase_lev_push(&deque, values[i]);
  }

  for (int i = iterations - 1; i >= 0; i--) {
    void *result = valk_chase_lev_pop(&deque);
    ASSERT_NOT_NULL(result);
    free(result);
  }

  void *empty_result = valk_chase_lev_pop(&deque);
  ASSERT_EQ(empty_result, VALK_CHASE_LEV_EMPTY);

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

void test_chase_lev_interleaved_operations(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 8);

  int values[20];
  for (int i = 0; i < 20; i++) {
    values[i] = i;
  }

  valk_chase_lev_push(&deque, &values[0]);
  valk_chase_lev_push(&deque, &values[1]);

  void *p1 = valk_chase_lev_pop(&deque);
  ASSERT_EQ(p1, &values[1]);

  valk_chase_lev_push(&deque, &values[2]);
  valk_chase_lev_push(&deque, &values[3]);

  void *s1 = valk_chase_lev_steal(&deque);
  ASSERT_EQ(s1, &values[0]);

  void *p2 = valk_chase_lev_pop(&deque);
  ASSERT_EQ(p2, &values[3]);

  void *p3 = valk_chase_lev_pop(&deque);
  ASSERT_EQ(p3, &values[2]);

  ASSERT_TRUE(valk_chase_lev_empty(&deque));

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

typedef struct {
  valk_chase_lev_deque_t *deque;
  _Atomic int *pop_cas_failures;
  _Atomic int *steal_cas_failures;
  _Atomic int *iterations_done;
  int target_iterations;
} cas_contention_arg_t;

static void *cas_contention_stealer(void *arg) {
  cas_contention_arg_t *ctx = (cas_contention_arg_t *)arg;
  while (atomic_load(ctx->iterations_done) < ctx->target_iterations) {
    void *item = valk_chase_lev_steal(ctx->deque);
    if (item == VALK_CHASE_LEV_ABORT) {
      atomic_fetch_add(ctx->steal_cas_failures, 1);
    }
  }
  return NULL;
}

static void *cas_contention_popper(void *arg) {
  cas_contention_arg_t *ctx = (cas_contention_arg_t *)arg;
  int value = 42;
  for (int i = 0; i < ctx->target_iterations; i++) {
    valk_chase_lev_push(ctx->deque, &value);
    void *result = valk_chase_lev_pop(ctx->deque);
    if (result == VALK_CHASE_LEV_EMPTY) {
      atomic_fetch_add(ctx->pop_cas_failures, 1);
    }
    atomic_fetch_add(ctx->iterations_done, 1);
  }
  return NULL;
}

void test_chase_lev_cas_contention(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_chase_lev_deque_t deque;
  valk_chase_lev_init(&deque, 4);

  _Atomic int pop_cas_failures = 0;
  _Atomic int steal_cas_failures = 0;
  _Atomic int iterations_done = 0;
  const int target = 10000;

  cas_contention_arg_t arg = {
    .deque = &deque,
    .pop_cas_failures = &pop_cas_failures,
    .steal_cas_failures = &steal_cas_failures,
    .iterations_done = &iterations_done,
    .target_iterations = target,
  };

  pthread_t stealers[4];
  pthread_t popper;

  for (int i = 0; i < 4; i++) {
    pthread_create(&stealers[i], NULL, cas_contention_stealer, &arg);
  }
  pthread_create(&popper, NULL, cas_contention_popper, &arg);

  pthread_join(popper, NULL);
  for (int i = 0; i < 4; i++) {
    pthread_join(stealers[i], NULL);
  }

  valk_chase_lev_destroy(&deque);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_chase_lev_init_destroy", test_chase_lev_init_destroy);
  valk_testsuite_add_test(suite, "test_chase_lev_push_pop_single", test_chase_lev_push_pop_single);
  valk_testsuite_add_test(suite, "test_chase_lev_push_pop_multiple", test_chase_lev_push_pop_multiple);
  valk_testsuite_add_test(suite, "test_chase_lev_pop_empty", test_chase_lev_pop_empty);
  valk_testsuite_add_test(suite, "test_chase_lev_steal_single", test_chase_lev_steal_single);
  valk_testsuite_add_test(suite, "test_chase_lev_steal_empty", test_chase_lev_steal_empty);
  valk_testsuite_add_test(suite, "test_chase_lev_steal_order", test_chase_lev_steal_order);
  valk_testsuite_add_test(suite, "test_chase_lev_mixed_pop_steal", test_chase_lev_mixed_pop_steal);
  valk_testsuite_add_test(suite, "test_chase_lev_grow", test_chase_lev_grow);
  valk_testsuite_add_test(suite, "test_chase_lev_single_element_race", test_chase_lev_single_element_race);
  valk_testsuite_add_test(suite, "test_chase_lev_concurrent_steal", test_chase_lev_concurrent_steal);
  valk_testsuite_add_test(suite, "test_chase_lev_stress_push_pop", test_chase_lev_stress_push_pop);
  valk_testsuite_add_test(suite, "test_chase_lev_interleaved_operations", test_chase_lev_interleaved_operations);
  valk_testsuite_add_test(suite, "test_chase_lev_cas_contention", test_chase_lev_cas_contention);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
