#include "../testing.h"
#include "../../src/valk_thread.h"
#include "../../src/memory.h"

#include <string.h>
#include <unistd.h>
#include <stdatomic.h>
#include <errno.h>

static _Atomic int g_thread_counter = 0;

static void* thread_func(void* arg) {
  int* value = (int*)arg;
  atomic_fetch_add(&g_thread_counter, *value);
  return (void*)(intptr_t)(*value * 2);
}

void test_mutex_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mutex_t mutex;
  int res = valk_mutex_init(&mutex);
  ASSERT_EQ(res, 0);

  res = valk_mutex_lock(&mutex);
  ASSERT_EQ(res, 0);

  res = valk_mutex_unlock(&mutex);
  ASSERT_EQ(res, 0);

  res = valk_mutex_destroy(&mutex);
  ASSERT_EQ(res, 0);

  VALK_PASS();
}

void test_cond_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_cond_t cond;
  int res = valk_cond_init(&cond);
  ASSERT_EQ(res, 0);

  res = valk_cond_destroy(&cond);
  ASSERT_EQ(res, 0);

  VALK_PASS();
}

static _Atomic bool g_signal_received = false;
static valk_mutex_t g_signal_mutex;
static valk_cond_t g_signal_cond;

static void* wait_thread_func(void* arg) {
  (void)arg;
  valk_mutex_lock(&g_signal_mutex);
  while (!atomic_load(&g_signal_received)) {
    valk_cond_wait(&g_signal_cond, &g_signal_mutex);
  }
  valk_mutex_unlock(&g_signal_mutex);
  return NULL;
}

void test_cond_signal(VALK_TEST_ARGS()) {
  VALK_TEST();

  atomic_store(&g_signal_received, false);
  valk_mutex_init(&g_signal_mutex);
  valk_cond_init(&g_signal_cond);

  valk_thread_t thread;
  valk_thread_create(&thread, NULL, wait_thread_func, NULL);

  usleep(10000);

  valk_mutex_lock(&g_signal_mutex);
  atomic_store(&g_signal_received, true);
  valk_cond_signal(&g_signal_cond);
  valk_mutex_unlock(&g_signal_mutex);

  valk_thread_join(thread, NULL);

  valk_cond_destroy(&g_signal_cond);
  valk_mutex_destroy(&g_signal_mutex);

  VALK_PASS();
}

static _Atomic int g_broadcast_count = 0;
static valk_mutex_t g_broadcast_mutex;
static valk_cond_t g_broadcast_cond;
static _Atomic bool g_broadcast_go = false;

static void* broadcast_thread_func(void* arg) {
  (void)arg;
  valk_mutex_lock(&g_broadcast_mutex);
  while (!atomic_load(&g_broadcast_go)) {
    valk_cond_wait(&g_broadcast_cond, &g_broadcast_mutex);
  }
  atomic_fetch_add(&g_broadcast_count, 1);
  valk_mutex_unlock(&g_broadcast_mutex);
  return NULL;
}

void test_cond_broadcast(VALK_TEST_ARGS()) {
  VALK_TEST();

  atomic_store(&g_broadcast_count, 0);
  atomic_store(&g_broadcast_go, false);
  valk_mutex_init(&g_broadcast_mutex);
  valk_cond_init(&g_broadcast_cond);

  valk_thread_t threads[3];
  for (int i = 0; i < 3; i++) {
    valk_thread_create(&threads[i], NULL, broadcast_thread_func, NULL);
  }

  usleep(10000);

  valk_mutex_lock(&g_broadcast_mutex);
  atomic_store(&g_broadcast_go, true);
  valk_cond_broadcast(&g_broadcast_cond);
  valk_mutex_unlock(&g_broadcast_mutex);

  for (int i = 0; i < 3; i++) {
    valk_thread_join(threads[i], NULL);
  }

  ASSERT_EQ(atomic_load(&g_broadcast_count), 3);

  valk_cond_destroy(&g_broadcast_cond);
  valk_mutex_destroy(&g_broadcast_mutex);

  VALK_PASS();
}

void test_cond_timedwait(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mutex_t mutex;
  valk_cond_t cond;
  valk_mutex_init(&mutex);
  valk_cond_init(&cond);

  valk_mutex_lock(&mutex);
  int res = valk_cond_timedwait(&cond, &mutex, 10);
  valk_mutex_unlock(&mutex);

  ASSERT_EQ(res, ETIMEDOUT);

  valk_cond_destroy(&cond);
  valk_mutex_destroy(&mutex);

  VALK_PASS();
}

void test_cond_timedwait_overflow(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_mutex_t mutex;
  valk_cond_t cond;
  valk_mutex_init(&mutex);
  valk_cond_init(&cond);

  valk_mutex_lock(&mutex);
  int res = valk_cond_timedwait(&cond, &mutex, 1500);
  valk_mutex_unlock(&mutex);

  ASSERT_EQ(res, ETIMEDOUT);

  valk_cond_destroy(&cond);
  valk_mutex_destroy(&mutex);

  VALK_PASS();
}

void test_thread_create_join(VALK_TEST_ARGS()) {
  VALK_TEST();

  atomic_store(&g_thread_counter, 0);

  int value = 42;
  valk_thread_t thread;
  int res = valk_thread_create(&thread, NULL, thread_func, &value);
  ASSERT_EQ(res, 0);

  void* retval;
  res = valk_thread_join(thread, &retval);
  ASSERT_EQ(res, 0);
  ASSERT_EQ((intptr_t)retval, 84);
  ASSERT_EQ(atomic_load(&g_thread_counter), 42);

  VALK_PASS();
}

void test_thread_self_equal(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_thread_t self = valk_thread_self();
  ASSERT_TRUE(valk_thread_equal(self, self));

  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "mutex_basic", test_mutex_basic);
  valk_testsuite_add_test(suite, "cond_basic", test_cond_basic);
  valk_testsuite_add_test(suite, "cond_signal", test_cond_signal);
  valk_testsuite_add_test(suite, "cond_broadcast", test_cond_broadcast);
  valk_testsuite_add_test(suite, "cond_timedwait", test_cond_timedwait);
  valk_testsuite_add_test(suite, "cond_timedwait_overflow", test_cond_timedwait_overflow);
  valk_testsuite_add_test(suite, "thread_create_join", test_thread_create_join);
  valk_testsuite_add_test(suite, "thread_self_equal", test_thread_self_equal);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
