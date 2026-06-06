#include "../testing.h"
#include "../../src/conc_map.h"
#include "../../src/memory.h"

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// The map never dereferences values, so tests use small integer "values"
// cast to valk_lval_t* pointers.
static valk_lval_t *vptr(uintptr_t v) { return (valk_lval_t *)v; }
static uintptr_t vint(valk_lval_t *p) { return (uintptr_t)p; }

void test_cmap_basic_put_get(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_cmap_t *m = valk_cmap_new(valk_thread_ctx.allocator, 16);
  ASSERT_NOT_NULL(m);
  ASSERT_NULL(valk_cmap_get(m, "missing"));

  valk_cmap_put(m, "a", vptr(1));
  valk_cmap_put(m, "b", vptr(2));
  valk_cmap_put(m, "c", vptr(3));

  ASSERT_EQ(vint(valk_cmap_get(m, "a")), 1);
  ASSERT_EQ(vint(valk_cmap_get(m, "b")), 2);
  ASSERT_EQ(vint(valk_cmap_get(m, "c")), 3);
  ASSERT_NULL(valk_cmap_get(m, "d"));
  ASSERT_EQ(valk_cmap_count(m), 3);
  VALK_PASS();
}

void test_cmap_overwrite(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_cmap_t *m = valk_cmap_new(valk_thread_ctx.allocator, 16);
  valk_cmap_put(m, "k", vptr(10));
  ASSERT_EQ(vint(valk_cmap_get(m, "k")), 10);
  valk_cmap_put(m, "k", vptr(20));
  ASSERT_EQ(vint(valk_cmap_get(m, "k")), 20);
  ASSERT_EQ(valk_cmap_count(m), 1);  // overwrite does not grow count
  VALK_PASS();
}

void test_cmap_resize(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_cmap_t *m = valk_cmap_new(valk_thread_ctx.allocator, 16);
  char key[32];
  // Insert well past the initial capacity to force several resizes.
  for (int i = 0; i < 1000; i++) {
    snprintf(key, sizeof(key), "key_%d", i);
    valk_cmap_put(m, key, vptr((uintptr_t)(i + 1)));
  }
  ASSERT_EQ(valk_cmap_count(m), 1000);
  // All keys still resolve to their values after resizing.
  for (int i = 0; i < 1000; i++) {
    snprintf(key, sizeof(key), "key_%d", i);
    ASSERT_EQ(vint(valk_cmap_get(m, key)), (uintptr_t)(i + 1));
  }
  VALK_PASS();
}

static void cmap_sum_cb(char *k, _Atomic(valk_lval_t *) * slot, void *ctx) {
  (void)k;
  u64 *acc = ctx;
  *acc += vint(atomic_load(slot));
}

void test_cmap_foreach(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_cmap_t *m = valk_cmap_new(valk_thread_ctx.allocator, 16);
  for (int i = 0; i < 50; i++) {
    char key[32];
    snprintf(key, sizeof(key), "k%d", i);
    valk_cmap_put(m, key, vptr((uintptr_t)(i + 1)));
  }
  u64 sum = 0;
  valk_cmap_foreach(m, cmap_sum_cb, &sum);
  // sum of 1..50
  ASSERT_EQ(sum, 1275);
  VALK_PASS();
}

// ---------------------------------------------------------------------------
// Concurrency: many writers + many readers hammering the same map. Run under
// TSAN (make test-c-tsan) this proves the read/write paths are race-free.
// ---------------------------------------------------------------------------

#define CM_THREADS 8
#define CM_KEYS 256
#define CM_ITERS 20000

typedef struct {
  valk_cmap_t *m;
  int id;
} cm_worker_arg_t;

static void *cm_writer(void *arg) {
  cm_worker_arg_t *a = arg;
  char key[32];
  for (int i = 0; i < CM_ITERS; i++) {
    int k = (a->id * 31 + i) % CM_KEYS;
    snprintf(key, sizeof(key), "shared_%d", k);
    valk_cmap_put(a->m, key, vptr((uintptr_t)(k + 1)));
  }
  return nullptr;
}

static void *cm_reader(void *arg) {
  cm_worker_arg_t *a = arg;
  char key[32];
  volatile uintptr_t seen = 0;
  for (int i = 0; i < CM_ITERS; i++) {
    int k = (a->id * 17 + i) % CM_KEYS;
    snprintf(key, sizeof(key), "shared_%d", k);
    valk_lval_t *v = valk_cmap_get(a->m, key);
    if (v) {
      // Value, when present, must equal the only value ever written for k.
      seen = vint(v);
      if (seen != (uintptr_t)(k + 1)) {
        // Torn/garbage value would indicate a race.
        return (void *)(uintptr_t)1;
      }
    }
  }
  return nullptr;
}

void test_cmap_concurrent_readers_writers(VALK_TEST_ARGS()) {
  VALK_TEST();
  valk_cmap_t *m = valk_cmap_new(valk_thread_ctx.allocator, 16);

  pthread_t threads[CM_THREADS * 2];
  cm_worker_arg_t args[CM_THREADS * 2];

  for (int i = 0; i < CM_THREADS; i++) {
    args[i] = (cm_worker_arg_t){.m = m, .id = i};
    pthread_create(&threads[i], nullptr, cm_writer, &args[i]);
  }
  for (int i = 0; i < CM_THREADS; i++) {
    int j = CM_THREADS + i;
    args[j] = (cm_worker_arg_t){.m = m, .id = i};
    pthread_create(&threads[j], nullptr, cm_reader, &args[j]);
  }

  bool reader_saw_garbage = false;
  for (int i = 0; i < CM_THREADS * 2; i++) {
    void *ret = nullptr;
    pthread_join(threads[i], &ret);
    if (ret != nullptr) reader_saw_garbage = true;
  }

  ASSERT_FALSE(reader_saw_garbage);
  // Every key should be present with its canonical value at the end.
  char key[32];
  for (int k = 0; k < CM_KEYS; k++) {
    snprintf(key, sizeof(key), "shared_%d", k);
    ASSERT_EQ(vint(valk_cmap_get(m, key)), (uintptr_t)(k + 1));
  }
  ASSERT_EQ(valk_cmap_count(m), CM_KEYS);
  VALK_PASS();
}

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_cmap_basic_put_get", test_cmap_basic_put_get);
  valk_testsuite_add_test(suite, "test_cmap_overwrite", test_cmap_overwrite);
  valk_testsuite_add_test(suite, "test_cmap_resize", test_cmap_resize);
  valk_testsuite_add_test(suite, "test_cmap_foreach", test_cmap_foreach);
  valk_testsuite_add_test(suite, "test_cmap_concurrent_readers_writers",
                          test_cmap_concurrent_readers_writers);

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return result;
}
