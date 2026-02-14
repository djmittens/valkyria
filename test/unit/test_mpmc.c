#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/aio/system/aio_mpmc.h"

#include <pthread.h>
#include <stdlib.h>

void test_mpmc_init_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 16);

  ASSERT_TRUE(valk_mpmc_empty(&q));
  ASSERT_EQ(valk_mpmc_size(&q), 0);

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_push_pop_single(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 16);

  int value = 42;
  bool ok = valk_mpmc_push(&q, &value);
  ASSERT_TRUE(ok);
  ASSERT_FALSE(valk_mpmc_empty(&q));
  ASSERT_EQ(valk_mpmc_size(&q), 1);

  void *result = valk_mpmc_pop(&q);
  ASSERT_EQ(result, &value);
  ASSERT_TRUE(valk_mpmc_empty(&q));

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_push_pop_multiple(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 16);

  int values[5] = {1, 2, 3, 4, 5};
  for (int i = 0; i < 5; i++) {
    ASSERT_TRUE(valk_mpmc_push(&q, &values[i]));
  }

  ASSERT_EQ(valk_mpmc_size(&q), 5);

  for (int i = 0; i < 5; i++) {
    void *result = valk_mpmc_pop(&q);
    ASSERT_EQ(result, &values[i]);
  }

  ASSERT_TRUE(valk_mpmc_empty(&q));

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_pop_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 16);

  void *result = valk_mpmc_pop(&q);
  ASSERT_NULL(result);

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_fifo_order(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 64);

  int values[32];
  for (int i = 0; i < 32; i++) {
    values[i] = i;
    ASSERT_TRUE(valk_mpmc_push(&q, &values[i]));
  }

  for (int i = 0; i < 32; i++) {
    void *result = valk_mpmc_pop(&q);
    ASSERT_EQ(result, &values[i]);
  }

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_full_reject(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 4);

  int values[8];
  for (int i = 0; i < 8; i++) values[i] = i;

  ASSERT_TRUE(valk_mpmc_push(&q, &values[0]));
  ASSERT_TRUE(valk_mpmc_push(&q, &values[1]));
  ASSERT_TRUE(valk_mpmc_push(&q, &values[2]));
  ASSERT_TRUE(valk_mpmc_push(&q, &values[3]));

  bool ok = valk_mpmc_push(&q, &values[4]);
  ASSERT_FALSE(ok);

  void *result = valk_mpmc_pop(&q);
  ASSERT_EQ(result, &values[0]);

  ASSERT_TRUE(valk_mpmc_push(&q, &values[4]));

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_wrap_around(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 4);

  int values[16];
  for (int i = 0; i < 16; i++) values[i] = i;

  for (int round = 0; round < 4; round++) {
    for (int i = 0; i < 4; i++) {
      ASSERT_TRUE(valk_mpmc_push(&q, &values[round * 4 + i]));
    }
    for (int i = 0; i < 4; i++) {
      void *result = valk_mpmc_pop(&q);
      ASSERT_EQ(result, &values[round * 4 + i]);
    }
    ASSERT_TRUE(valk_mpmc_empty(&q));
  }

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_capacity_rounds_up(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 5);

  int values[8];
  for (int i = 0; i < 8; i++) values[i] = i;

  int pushed = 0;
  for (int i = 0; i < 8; i++) {
    if (valk_mpmc_push(&q, &values[i])) pushed++;
    else break;
  }

  ASSERT_EQ(pushed, 8);

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

typedef struct {
  valk_mpmc_queue_t *q;
  int id;
  int count;
  _Atomic int *push_success;
  _Atomic int *push_fail;
} producer_arg_t;

static void *producer_thread(void *arg) {
  producer_arg_t *ctx = (producer_arg_t *)arg;
  for (int i = 0; i < ctx->count; i++) {
    int *val = malloc(sizeof(int));
    *val = ctx->id * 100000 + i;
    while (!valk_mpmc_push(ctx->q, val)) {
      atomic_fetch_add(ctx->push_fail, 1);
    }
    atomic_fetch_add(ctx->push_success, 1);
  }
  return NULL;
}

typedef struct {
  valk_mpmc_queue_t *q;
  _Atomic int *pop_count;
  _Atomic bool *done;
} consumer_arg_t;

static void *consumer_thread(void *arg) {
  consumer_arg_t *ctx = (consumer_arg_t *)arg;
  while (true) {
    void *item = valk_mpmc_pop(ctx->q);
    if (item) {
      free(item);
      atomic_fetch_add(ctx->pop_count, 1);
    } else if (atomic_load(ctx->done)) {
      item = valk_mpmc_pop(ctx->q);
      if (item) {
        free(item);
        atomic_fetch_add(ctx->pop_count, 1);
      } else {
        break;
      }
    }
  }
  return NULL;
}

void test_mpmc_concurrent_2p_2c(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 256);

  _Atomic int push_success = 0;
  _Atomic int push_fail = 0;
  _Atomic int pop_count = 0;
  _Atomic bool done = false;

  const int items_per_producer = 10000;
  const int num_producers = 2;
  const int num_consumers = 2;

  producer_arg_t pargs[num_producers];
  consumer_arg_t cargs[num_consumers];
  pthread_t producers[num_producers];
  pthread_t consumers[num_consumers];

  for (int i = 0; i < num_consumers; i++) {
    cargs[i] = (consumer_arg_t){.q = &q, .pop_count = &pop_count, .done = &done};
    pthread_create(&consumers[i], NULL, consumer_thread, &cargs[i]);
  }

  for (int i = 0; i < num_producers; i++) {
    pargs[i] = (producer_arg_t){
      .q = &q, .id = i, .count = items_per_producer,
      .push_success = &push_success, .push_fail = &push_fail
    };
    pthread_create(&producers[i], NULL, producer_thread, &pargs[i]);
  }

  for (int i = 0; i < num_producers; i++) {
    pthread_join(producers[i], NULL);
  }

  atomic_store(&done, true);

  for (int i = 0; i < num_consumers; i++) {
    pthread_join(consumers[i], NULL);
  }

  ASSERT_EQ(atomic_load(&push_success), num_producers * items_per_producer);
  ASSERT_EQ(atomic_load(&pop_count), num_producers * items_per_producer);

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_concurrent_4p_4c(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 512);

  _Atomic int push_success = 0;
  _Atomic int push_fail = 0;
  _Atomic int pop_count = 0;
  _Atomic bool done = false;

  const int items_per_producer = 25000;
  const int num_producers = 4;
  const int num_consumers = 4;

  producer_arg_t pargs[num_producers];
  consumer_arg_t cargs[num_consumers];
  pthread_t producers[num_producers];
  pthread_t consumers[num_consumers];

  for (int i = 0; i < num_consumers; i++) {
    cargs[i] = (consumer_arg_t){.q = &q, .pop_count = &pop_count, .done = &done};
    pthread_create(&consumers[i], NULL, consumer_thread, &cargs[i]);
  }

  for (int i = 0; i < num_producers; i++) {
    pargs[i] = (producer_arg_t){
      .q = &q, .id = i, .count = items_per_producer,
      .push_success = &push_success, .push_fail = &push_fail
    };
    pthread_create(&producers[i], NULL, producer_thread, &pargs[i]);
  }

  for (int i = 0; i < num_producers; i++) {
    pthread_join(producers[i], NULL);
  }

  atomic_store(&done, true);

  for (int i = 0; i < num_consumers; i++) {
    pthread_join(consumers[i], NULL);
  }

  ASSERT_EQ(atomic_load(&push_success), num_producers * items_per_producer);
  ASSERT_EQ(atomic_load(&pop_count), num_producers * items_per_producer);

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

void test_mpmc_stress_wrap(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mpmc_queue_t q;
  valk_mpmc_init(&q, 8);

  int values[100000];
  for (int i = 0; i < 100000; i++) {
    values[i] = i;
    while (!valk_mpmc_push(&q, &values[i])) {
      valk_mpmc_pop(&q);
    }
  }

  while (valk_mpmc_pop(&q) != NULL) {}
  ASSERT_TRUE(valk_mpmc_empty(&q));

  valk_mpmc_destroy(&q);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_mpmc_init_destroy", test_mpmc_init_destroy);
  valk_testsuite_add_test(suite, "test_mpmc_push_pop_single", test_mpmc_push_pop_single);
  valk_testsuite_add_test(suite, "test_mpmc_push_pop_multiple", test_mpmc_push_pop_multiple);
  valk_testsuite_add_test(suite, "test_mpmc_pop_empty", test_mpmc_pop_empty);
  valk_testsuite_add_test(suite, "test_mpmc_fifo_order", test_mpmc_fifo_order);
  valk_testsuite_add_test(suite, "test_mpmc_full_reject", test_mpmc_full_reject);
  valk_testsuite_add_test(suite, "test_mpmc_wrap_around", test_mpmc_wrap_around);
  valk_testsuite_add_test(suite, "test_mpmc_capacity_rounds_up", test_mpmc_capacity_rounds_up);
  valk_testsuite_add_test(suite, "test_mpmc_concurrent_2p_2c", test_mpmc_concurrent_2p_2c);
  valk_testsuite_add_test(suite, "test_mpmc_concurrent_4p_4c", test_mpmc_concurrent_4p_4c);
  valk_testsuite_add_test(suite, "test_mpmc_stress_wrap", test_mpmc_stress_wrap);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
