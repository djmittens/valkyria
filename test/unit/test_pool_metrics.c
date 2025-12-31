#include "../testing.h"
#include "../../src/memory.h"
#include "../../src/common.h"

#include <pthread.h>

#ifdef VALK_METRICS_ENABLED
#include "../../src/pool_metrics.h"
#include "../../src/metrics_v2.h"

void test_pool_metrics_init_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(nullptr, "test");
  VALK_TEST_ASSERT(result == false, "Should return false for nullptr metrics");

  result = valk_pool_metrics_init(&m, nullptr);
  VALK_TEST_ASSERT(result == false, "Should return false for nullptr pool name");

  VALK_PASS();
}

void test_pool_metrics_init_custom_null_args(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init_custom(nullptr, "test", "pool");
  VALK_TEST_ASSERT(result == false, "Should return false for nullptr metrics");

  result = valk_pool_metrics_init_custom(&m, nullptr, "pool");
  VALK_TEST_ASSERT(result == false, "Should return false for nullptr pool name");

  result = valk_pool_metrics_init_custom(&m, "test", nullptr);
  VALK_TEST_ASSERT(result == false, "Should return false for nullptr prefix");

  VALK_PASS();
}

void test_pool_metrics_init_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "test_pool");
  VALK_TEST_ASSERT(result == true, "Should return true on success");

  VALK_TEST_ASSERT(m.pool_name != nullptr, "pool_name should be set");
  VALK_TEST_ASSERT(m.used != nullptr, "used gauge should be created");
  VALK_TEST_ASSERT(m.total != nullptr, "total gauge should be created");
  VALK_TEST_ASSERT(m.peak != nullptr, "peak gauge should be created");
  VALK_TEST_ASSERT(m.overflow != nullptr, "overflow counter should be created");

  VALK_PASS();
}

void test_pool_metrics_init_custom_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init_custom(&m, "custom_pool", "slab");
  VALK_TEST_ASSERT(result == true, "Should return true on success");

  VALK_TEST_ASSERT(m.pool_name != nullptr, "pool_name should be set");
  VALK_TEST_ASSERT(strcmp(m.pool_name, "custom_pool") == 0, "pool_name should match");

  VALK_PASS();
}

void test_pool_metrics_update_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pool_metrics_update(nullptr, 100, 1000, 500, 0);
  valk_pool_metrics_update_slab(nullptr, 100, 50, 75, 0);
  valk_pool_metrics_update_arena(nullptr, 4096, 1024, 2048, 0);

  VALK_PASS();
}

void test_pool_metrics_update_slab(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "slab_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update_slab(&m, 100, 25, 80, 5);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == 75, "used should be total - free = 75, got %lld", (long long)used_val);

  i64 total_val = atomic_load(&m.total->value);
  VALK_TEST_ASSERT(total_val == 100, "total should be 100, got %lld", (long long)total_val);

  i64 peak_val = atomic_load(&m.peak->value);
  VALK_TEST_ASSERT(peak_val == 80, "peak should be 80, got %lld", (long long)peak_val);

  u64 overflow_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(overflow_val == 5, "overflow should be 5, got %llu", (unsigned long long)overflow_val);

  VALK_PASS();
}

void test_pool_metrics_update_arena(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "arena_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update_arena(&m, 4096, 1024, 2048, 3);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == 1024, "used should be 1024, got %lld", (long long)used_val);

  i64 total_val = atomic_load(&m.total->value);
  VALK_TEST_ASSERT(total_val == 4096, "total should be 4096, got %lld", (long long)total_val);

  i64 peak_val = atomic_load(&m.peak->value);
  VALK_TEST_ASSERT(peak_val == 2048, "peak should be 2048, got %lld", (long long)peak_val);

  u64 overflow_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(overflow_val == 3, "overflow should be 3, got %llu", (unsigned long long)overflow_val);

  VALK_PASS();
}

void test_pool_metrics_update_generic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "generic_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, 500, 1000, 750, 10);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == 500, "used should be 500, got %lld", (long long)used_val);

  i64 total_val = atomic_load(&m.total->value);
  VALK_TEST_ASSERT(total_val == 1000, "total should be 1000, got %lld", (long long)total_val);

  i64 peak_val = atomic_load(&m.peak->value);
  VALK_TEST_ASSERT(peak_val == 750, "peak should be 750, got %lld", (long long)peak_val);

  u64 overflow_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(overflow_val == 10, "overflow should be 10, got %llu", (unsigned long long)overflow_val);

  VALK_PASS();
}

void test_pool_metrics_overflow_increment(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "overflow_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, 100, 100, 100, 5);
  u64 first_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(first_val == 5, "First overflow should be 5");

  valk_pool_metrics_update(&m, 100, 100, 100, 8);
  u64 second_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(second_val == 8, "Second overflow should be 8");

  valk_pool_metrics_update(&m, 100, 100, 100, 6);
  u64 third_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(third_val == 8, "Overflow should not decrease, expected 8, got %llu",
                   (unsigned long long)third_val);

  VALK_PASS();
}

void test_pool_metrics_multiple_pools(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m1, m2, m3;
  bool r1 = valk_pool_metrics_init(&m1, "pool_one");
  bool r2 = valk_pool_metrics_init(&m2, "pool_two");
  bool r3 = valk_pool_metrics_init(&m3, "pool_three");

  VALK_TEST_ASSERT(r1 == true, "pool_one init should succeed");
  VALK_TEST_ASSERT(r2 == true, "pool_two init should succeed");
  VALK_TEST_ASSERT(r3 == true, "pool_three init should succeed");

  valk_pool_metrics_update(&m1, 100, 1000, 100, 0);
  valk_pool_metrics_update(&m2, 200, 2000, 200, 0);
  valk_pool_metrics_update(&m3, 300, 3000, 300, 0);

  VALK_TEST_ASSERT(atomic_load(&m1.used->value) == 100, "m1 used should be 100");
  VALK_TEST_ASSERT(atomic_load(&m2.used->value) == 200, "m2 used should be 200");
  VALK_TEST_ASSERT(atomic_load(&m3.used->value) == 300, "m3 used should be 300");

  VALK_PASS();
}

static valk_pool_metrics_t *concurrent_test_metrics = nullptr;
static _Atomic int concurrent_threads_done = 0;

static void *concurrent_update_thread(void *arg) {
  int thread_id = *(int *)arg;
  for (int i = 0; i < 1000; i++) {
    valk_pool_metrics_update(concurrent_test_metrics,
                              (i64)(thread_id * 1000 + i),
                              1000,
                              (i64)(thread_id * 1000 + i),
                              (u64)(thread_id * 100 + i));
  }
  atomic_fetch_add(&concurrent_threads_done, 1);
  return nullptr;
}

void test_pool_metrics_concurrent_updates(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "concurrent_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  concurrent_test_metrics = &m;
  atomic_store(&concurrent_threads_done, 0);

  pthread_t threads[4];
  int thread_ids[4] = {0, 1, 2, 3};

  for (int i = 0; i < 4; i++) {
    pthread_create(&threads[i], nullptr, concurrent_update_thread, &thread_ids[i]);
  }

  for (int i = 0; i < 4; i++) {
    pthread_join(threads[i], nullptr);
  }

  VALK_TEST_ASSERT(atomic_load(&concurrent_threads_done) == 4, "All threads should complete");

  i64 final_used = atomic_load(&m.used->value);
  i64 final_total = atomic_load(&m.total->value);
  VALK_TEST_ASSERT(final_total == 1000, "total should be 1000");
  VALK_TEST_ASSERT(final_used >= 0, "used should be non-negative: %lld", (long long)final_used);

  VALK_PASS();
}

void test_pool_metrics_zero_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "zero_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, 0, 0, 0, 0);

  VALK_TEST_ASSERT(atomic_load(&m.used->value) == 0, "used should be 0");
  VALK_TEST_ASSERT(atomic_load(&m.total->value) == 0, "total should be 0");
  VALK_TEST_ASSERT(atomic_load(&m.peak->value) == 0, "peak should be 0");
  VALK_TEST_ASSERT(atomic_load(&m.overflow->value) == 0, "overflow should be 0");

  VALK_PASS();
}

void test_pool_metrics_large_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "large_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  i64 large_val = 1LL << 40;
  u64 large_overflow = 1ULL << 50;

  valk_pool_metrics_update(&m, large_val, large_val * 2, large_val, large_overflow);

  VALK_TEST_ASSERT(atomic_load(&m.used->value) == large_val, "used should be large value");
  VALK_TEST_ASSERT(atomic_load(&m.total->value) == large_val * 2, "total should be 2x large value");
  VALK_TEST_ASSERT(atomic_load(&m.overflow->value) == large_overflow, "overflow should be large");

  VALK_PASS();
}

void test_pool_metrics_rapid_updates(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "rapid_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  for (int i = 0; i < 10000; i++) {
    valk_pool_metrics_update(&m, i, 10000, i, (u64)i);
  }

  VALK_TEST_ASSERT(atomic_load(&m.used->value) == 9999, "used should be 9999");
  VALK_TEST_ASSERT(atomic_load(&m.peak->value) == 9999, "peak should be 9999");

  VALK_PASS();
}

void test_pool_metrics_negative_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "negative_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, -100, 1000, 500, 0);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == -100, "used should accept negative value");

  VALK_PASS();
}

void test_pool_metrics_update_decreasing(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "decreasing_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, 1000, 2000, 1000, 5);
  valk_pool_metrics_update(&m, 500, 2000, 1000, 5);
  valk_pool_metrics_update(&m, 100, 2000, 1000, 5);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == 100, "used should update to 100");

  VALK_PASS();
}

void test_pool_metrics_slab_full_capacity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "slab_full_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update_slab(&m, 100, 0, 100, 0);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == 100, "used should be 100 (all slots used)");

  i64 total_val = atomic_load(&m.total->value);
  VALK_TEST_ASSERT(total_val == 100, "total should be 100");

  VALK_PASS();
}

void test_pool_metrics_arena_empty(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "arena_empty_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update_arena(&m, 4096, 0, 0, 0);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == 0, "used should be 0");

  i64 total_val = atomic_load(&m.total->value);
  VALK_TEST_ASSERT(total_val == 4096, "total should be 4096");

  VALK_PASS();
}

void test_pool_metrics_arena_full(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "arena_full_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update_arena(&m, 4096, 4096, 4096, 10);

  i64 used_val = atomic_load(&m.used->value);
  VALK_TEST_ASSERT(used_val == 4096, "used should be 4096");

  i64 peak_val = atomic_load(&m.peak->value);
  VALK_TEST_ASSERT(peak_val == 4096, "peak should be 4096");

  VALK_PASS();
}

void test_pool_metrics_custom_prefix_long(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init_custom(&m, "test_pool", "memory_subsystem");
  VALK_TEST_ASSERT(result == true, "Init with long prefix should succeed");

  VALK_TEST_ASSERT(m.used != nullptr, "used gauge should be created");
  VALK_TEST_ASSERT(m.total != nullptr, "total gauge should be created");

  VALK_PASS();
}

void test_pool_metrics_reinit_same_name(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m1, m2;
  bool r1 = valk_pool_metrics_init(&m1, "reuse_pool");
  bool r2 = valk_pool_metrics_init(&m2, "reuse_pool");

  VALK_TEST_ASSERT(r1 == true, "First init should succeed");
  VALK_TEST_ASSERT(r2 == true, "Second init with same name should succeed (reuses metrics)");

  VALK_PASS();
}

void test_pool_metrics_all_fields_null_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_pool_metrics_t m = {0};
  m.used = nullptr;
  m.total = nullptr;
  m.peak = nullptr;
  m.overflow = nullptr;

  valk_pool_metrics_update(&m, 100, 200, 150, 5);

  VALK_PASS();
}

void test_pool_metrics_overflow_never_decreases(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "overflow_monotonic_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, 100, 100, 100, 10);
  valk_pool_metrics_update(&m, 100, 100, 100, 5);
  valk_pool_metrics_update(&m, 100, 100, 100, 15);
  valk_pool_metrics_update(&m, 100, 100, 100, 12);

  u64 overflow_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(overflow_val == 15, "overflow should be max seen (15), got %llu",
                   (unsigned long long)overflow_val);

  VALK_PASS();
}

void test_pool_metrics_partial_null_fields(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "partial_null_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_gauge_v2_t *saved_used = m.used;
  valk_gauge_v2_t *saved_total = m.total;
  valk_gauge_v2_t *saved_peak = m.peak;
  valk_counter_v2_t *saved_overflow = m.overflow;

  m.used = nullptr;
  valk_pool_metrics_update(&m, 100, 200, 150, 5);

  m.used = saved_used;
  m.total = nullptr;
  valk_pool_metrics_update(&m, 100, 200, 150, 6);

  m.total = saved_total;
  m.peak = nullptr;
  valk_pool_metrics_update(&m, 100, 200, 150, 7);

  m.peak = saved_peak;
  m.overflow = nullptr;
  valk_pool_metrics_update(&m, 100, 200, 150, 8);

  m.overflow = saved_overflow;

  VALK_PASS();
}

void test_pool_metrics_overflow_same_value(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "overflow_same_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, 100, 100, 100, 10);
  valk_pool_metrics_update(&m, 100, 100, 100, 10);

  u64 overflow_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(overflow_val == 10, "overflow should stay at 10");

  VALK_PASS();
}

void test_pool_metrics_overflow_decrease_ignored(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_pool_metrics_t m;
  bool result = valk_pool_metrics_init(&m, "overflow_decrease_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_pool_metrics_update(&m, 100, 100, 100, 20);
  u64 first_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(first_val == 20, "overflow should be 20");

  valk_pool_metrics_update(&m, 100, 100, 100, 5);
  u64 second_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(second_val == 20, "overflow should NOT decrease to 5");

  valk_pool_metrics_update(&m, 100, 100, 100, 0);
  u64 third_val = atomic_load(&m.overflow->value);
  VALK_TEST_ASSERT(third_val == 20, "overflow should NOT decrease to 0");

  VALK_PASS();
}

#else

void test_pool_metrics_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Pool metrics tests require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_pool_metrics_init_null_args", test_pool_metrics_init_null_args);
  valk_testsuite_add_test(suite, "test_pool_metrics_init_custom_null_args", test_pool_metrics_init_custom_null_args);
  valk_testsuite_add_test(suite, "test_pool_metrics_init_success", test_pool_metrics_init_success);
  valk_testsuite_add_test(suite, "test_pool_metrics_init_custom_success", test_pool_metrics_init_custom_success);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_null", test_pool_metrics_update_null);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_slab", test_pool_metrics_update_slab);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_arena", test_pool_metrics_update_arena);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_generic", test_pool_metrics_update_generic);
  valk_testsuite_add_test(suite, "test_pool_metrics_overflow_increment", test_pool_metrics_overflow_increment);
  valk_testsuite_add_test(suite, "test_pool_metrics_multiple_pools", test_pool_metrics_multiple_pools);
  valk_testsuite_add_test(suite, "test_pool_metrics_concurrent_updates", test_pool_metrics_concurrent_updates);
  valk_testsuite_add_test(suite, "test_pool_metrics_zero_values", test_pool_metrics_zero_values);
  valk_testsuite_add_test(suite, "test_pool_metrics_large_values", test_pool_metrics_large_values);
  valk_testsuite_add_test(suite, "test_pool_metrics_rapid_updates", test_pool_metrics_rapid_updates);
  valk_testsuite_add_test(suite, "test_pool_metrics_negative_values", test_pool_metrics_negative_values);
  valk_testsuite_add_test(suite, "test_pool_metrics_update_decreasing", test_pool_metrics_update_decreasing);
  valk_testsuite_add_test(suite, "test_pool_metrics_slab_full_capacity", test_pool_metrics_slab_full_capacity);
  valk_testsuite_add_test(suite, "test_pool_metrics_arena_empty", test_pool_metrics_arena_empty);
  valk_testsuite_add_test(suite, "test_pool_metrics_arena_full", test_pool_metrics_arena_full);
  valk_testsuite_add_test(suite, "test_pool_metrics_custom_prefix_long", test_pool_metrics_custom_prefix_long);
  valk_testsuite_add_test(suite, "test_pool_metrics_reinit_same_name", test_pool_metrics_reinit_same_name);
  valk_testsuite_add_test(suite, "test_pool_metrics_all_fields_null_metrics", test_pool_metrics_all_fields_null_metrics);
  valk_testsuite_add_test(suite, "test_pool_metrics_overflow_never_decreases", test_pool_metrics_overflow_never_decreases);
  valk_testsuite_add_test(suite, "test_pool_metrics_partial_null_fields", test_pool_metrics_partial_null_fields);
  valk_testsuite_add_test(suite, "test_pool_metrics_overflow_same_value", test_pool_metrics_overflow_same_value);
  valk_testsuite_add_test(suite, "test_pool_metrics_overflow_decrease_ignored", test_pool_metrics_overflow_decrease_ignored);
#else
  valk_testsuite_add_test(suite, "test_pool_metrics_disabled", test_pool_metrics_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
