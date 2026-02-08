#include "testing.h"
#include "pool_metrics.h"
#include "metrics_v2.h"
#include "memory.h"
#include <string.h>

void test_pool_metrics_init_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init(&pm, "test_pool");

  ASSERT_TRUE(ok);
  ASSERT_NOT_NULL(pm.used);
  ASSERT_NOT_NULL(pm.total);
  ASSERT_NOT_NULL(pm.peak);
  ASSERT_NOT_NULL(pm.overflow);
  ASSERT_STR_EQ(pm.pool_name, "test_pool");

  VALK_PASS();
}

void test_pool_metrics_init_custom_prefix(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init_custom(&pm, "my_slab", "slab");

  ASSERT_TRUE(ok);
  ASSERT_NOT_NULL(pm.used);
  ASSERT_NOT_NULL(pm.total);
  ASSERT_NOT_NULL(pm.peak);
  ASSERT_NOT_NULL(pm.overflow);
  ASSERT_STR_EQ(pm.pool_name, "my_slab");

  VALK_PASS();
}

void test_pool_metrics_init_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pool_metrics_t pm;

  bool ok1 = valk_pool_metrics_init(nullptr, "test");
  ASSERT_FALSE(ok1);

  bool ok2 = valk_pool_metrics_init(&pm, nullptr);
  ASSERT_FALSE(ok2);

  bool ok3 = valk_pool_metrics_init_custom(&pm, "test", nullptr);
  ASSERT_FALSE(ok3);

  bool ok4 = valk_pool_metrics_init_custom(nullptr, "test", "prefix");
  ASSERT_FALSE(ok4);

  VALK_PASS();
}

void test_pool_metrics_update(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init(&pm, "update_test");
  ASSERT_TRUE(ok);

  valk_pool_metrics_update(&pm, 100, 1000, 150, 5);

  i64 used_val = atomic_load(&pm.used->value);
  i64 total_val = atomic_load(&pm.total->value);
  i64 peak_val = atomic_load(&pm.peak->value);
  u64 overflow_val = atomic_load(&pm.overflow->value);

  ASSERT_EQ(used_val, 100);
  ASSERT_EQ(total_val, 1000);
  ASSERT_EQ(peak_val, 150);
  ASSERT_EQ(overflow_val, 5);

  VALK_PASS();
}

void test_pool_metrics_update_slab(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init(&pm, "slab_test");
  ASSERT_TRUE(ok);

  valk_pool_metrics_update_slab(&pm, 100, 30, 80, 2);

  i64 used_val = atomic_load(&pm.used->value);
  i64 total_val = atomic_load(&pm.total->value);
  i64 peak_val = atomic_load(&pm.peak->value);
  u64 overflow_val = atomic_load(&pm.overflow->value);

  ASSERT_EQ(used_val, 70);
  ASSERT_EQ(total_val, 100);
  ASSERT_EQ(peak_val, 80);
  ASSERT_EQ(overflow_val, 2);

  VALK_PASS();
}

void test_pool_metrics_update_arena(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init(&pm, "arena_test");
  ASSERT_TRUE(ok);

  valk_pool_metrics_update_arena(&pm, 65536, 32768, 40000, 1);

  i64 used_val = atomic_load(&pm.used->value);
  i64 total_val = atomic_load(&pm.total->value);
  i64 peak_val = atomic_load(&pm.peak->value);
  u64 overflow_val = atomic_load(&pm.overflow->value);

  ASSERT_EQ(used_val, 32768);
  ASSERT_EQ(total_val, 65536);
  ASSERT_EQ(peak_val, 40000);
  ASSERT_EQ(overflow_val, 1);

  VALK_PASS();
}

void test_pool_metrics_update_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pool_metrics_update(nullptr, 100, 1000, 150, 5);
  valk_pool_metrics_update_slab(nullptr, 100, 30, 80, 2);
  valk_pool_metrics_update_arena(nullptr, 65536, 32768, 40000, 1);

  VALK_PASS();
}

void test_pool_metrics_overflow_delta(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init(&pm, "overflow_delta_test");
  ASSERT_TRUE(ok);

  valk_pool_metrics_update(&pm, 10, 100, 15, 5);
  u64 overflow_1 = atomic_load(&pm.overflow->value);
  ASSERT_EQ(overflow_1, 5);

  valk_pool_metrics_update(&pm, 20, 100, 25, 10);
  u64 overflow_2 = atomic_load(&pm.overflow->value);
  ASSERT_EQ(overflow_2, 10);

  valk_pool_metrics_update(&pm, 25, 100, 30, 10);
  u64 overflow_3 = atomic_load(&pm.overflow->value);
  ASSERT_EQ(overflow_3, 10);

  valk_pool_metrics_update(&pm, 30, 100, 35, 8);
  u64 overflow_4 = atomic_load(&pm.overflow->value);
  ASSERT_EQ(overflow_4, 10);

  VALK_PASS();
}

void test_pool_metrics_persistent(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t pm;
  bool ok = valk_pool_metrics_init(&pm, "persistent_test");
  ASSERT_TRUE(ok);

  ASSERT_FALSE(pm.used->evictable);
  ASSERT_FALSE(pm.total->evictable);
  ASSERT_FALSE(pm.peak->evictable);
  ASSERT_FALSE(pm.overflow->evictable);

  VALK_PASS();
}

int main(int argc, const char **argv) {
  (void)argc;
  (void)argv;

  valk_mem_init_malloc();

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_pool_metrics_init_basic", test_pool_metrics_init_basic);
  valk_testsuite_add_test(suite, "test_pool_metrics_init_custom_prefix", test_pool_metrics_init_custom_prefix);
  valk_testsuite_add_test(suite, "test_pool_metrics_init_null_args", test_pool_metrics_init_null_args);
  valk_testsuite_add_test(suite, "test_pool_metrics_update", test_pool_metrics_update);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_slab", test_pool_metrics_update_slab);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_arena", test_pool_metrics_update_arena);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_null", test_pool_metrics_update_null);
  valk_testsuite_add_test(suite, "test_pool_metrics_overflow_delta", test_pool_metrics_overflow_delta);
  valk_testsuite_add_test(suite, "test_pool_metrics_persistent", test_pool_metrics_persistent);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
