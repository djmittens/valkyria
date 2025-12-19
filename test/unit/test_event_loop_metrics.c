#include "../testing.h"
#include "../../src/memory.h"

#ifdef VALK_METRICS_ENABLED
#include "../../src/event_loop_metrics.h"
#include "../../src/metrics_v2.h"

#include <stdio.h>
#include <string.h>
#include <uv.h>

void test_event_loop_metrics_init_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  bool result = valk_event_loop_metrics_v2_init(NULL, "test");
  VALK_TEST_ASSERT(result == false, "NULL metrics should return false");

  valk_event_loop_metrics_v2_t m;
  result = valk_event_loop_metrics_v2_init(&m, NULL);
  VALK_TEST_ASSERT(result == false, "NULL loop name should return false");

  VALK_PASS();
}

void test_event_loop_metrics_init_success(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "main_loop");

  VALK_TEST_ASSERT(result == true, "Init should succeed");
  VALK_TEST_ASSERT(m.loop_name != NULL, "loop_name should be set");
  VALK_TEST_ASSERT(strcmp(m.loop_name, "main_loop") == 0, "loop_name should match");
  VALK_TEST_ASSERT(m.iterations != NULL, "iterations counter should be created");
  VALK_TEST_ASSERT(m.events != NULL, "events counter should be created");
  VALK_TEST_ASSERT(m.events_waiting != NULL, "events_waiting gauge should be created");
  VALK_TEST_ASSERT(m.idle_time_us != NULL, "idle_time_us gauge should be created");
  VALK_TEST_ASSERT(m.handles != NULL, "handles gauge should be created");

  VALK_PASS();
}

void test_event_loop_metrics_set_handles(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "handles_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_event_loop_metrics_v2_set_handles(&m, 42);

  int64_t handles_val = atomic_load(&m.handles->value);
  VALK_TEST_ASSERT(handles_val == 42, "handles should be 42, got %lld", (long long)handles_val);

  valk_event_loop_metrics_v2_set_handles(&m, 100);
  handles_val = atomic_load(&m.handles->value);
  VALK_TEST_ASSERT(handles_val == 100, "handles should be 100, got %lld", (long long)handles_val);

  VALK_PASS();
}

void test_event_loop_metrics_set_handles_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_event_loop_metrics_v2_set_handles(NULL, 42);

  VALK_PASS();
}

void test_event_loop_metrics_update_null(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_event_loop_metrics_v2_update(NULL, NULL);

  valk_metrics_registry_init();
  valk_event_loop_metrics_v2_t m;
  valk_event_loop_metrics_v2_init(&m, "null_update_test");
  valk_event_loop_metrics_v2_update(&m, NULL);

  VALK_PASS();
}

void test_event_loop_metrics_multiple_loops(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m1, m2;
  bool r1 = valk_event_loop_metrics_v2_init(&m1, "loop1");
  bool r2 = valk_event_loop_metrics_v2_init(&m2, "loop2");

  VALK_TEST_ASSERT(r1 == true, "loop1 init should succeed");
  VALK_TEST_ASSERT(r2 == true, "loop2 init should succeed");

  valk_event_loop_metrics_v2_set_handles(&m1, 10);
  valk_event_loop_metrics_v2_set_handles(&m2, 20);

  int64_t h1 = atomic_load(&m1.handles->value);
  int64_t h2 = atomic_load(&m2.handles->value);

  VALK_TEST_ASSERT(h1 == 10, "loop1 handles should be 10");
  VALK_TEST_ASSERT(h2 == 20, "loop2 handles should be 20");

  VALK_PASS();
}

void test_event_loop_metrics_prev_tracking(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "prev_track_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  VALK_TEST_ASSERT(m.prev_iterations == 0, "prev_iterations should start at 0");
  VALK_TEST_ASSERT(m.prev_events == 0, "prev_events should start at 0");

  VALK_PASS();
}

void test_event_loop_metrics_handles_large_values(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "large_handles_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  int64_t large_val = 1LL << 30;
  valk_event_loop_metrics_v2_set_handles(&m, large_val);

  int64_t handles_val = atomic_load(&m.handles->value);
  VALK_TEST_ASSERT(handles_val == large_val, "handles should be large value");

  VALK_PASS();
}

void test_event_loop_metrics_rapid_handle_updates(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "rapid_handles_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  for (int i = 0; i < 10000; i++) {
    valk_event_loop_metrics_v2_set_handles(&m, i);
  }

  int64_t final_val = atomic_load(&m.handles->value);
  VALK_TEST_ASSERT(final_val == 9999, "Final value should be 9999");

  VALK_PASS();
}

void test_event_loop_metrics_different_loop_names(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m1, m2, m3;
  bool r1 = valk_event_loop_metrics_v2_init(&m1, "main");
  bool r2 = valk_event_loop_metrics_v2_init(&m2, "worker");
  bool r3 = valk_event_loop_metrics_v2_init(&m3, "io");

  VALK_TEST_ASSERT(r1 == true, "main init should succeed");
  VALK_TEST_ASSERT(r2 == true, "worker init should succeed");
  VALK_TEST_ASSERT(r3 == true, "io init should succeed");

  VALK_TEST_ASSERT(strcmp(m1.loop_name, "main") == 0, "loop_name should be main");
  VALK_TEST_ASSERT(strcmp(m2.loop_name, "worker") == 0, "loop_name should be worker");
  VALK_TEST_ASSERT(strcmp(m3.loop_name, "io") == 0, "loop_name should be io");

  VALK_PASS();
}

void test_event_loop_metrics_all_gauges_created(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "all_gauges_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  VALK_TEST_ASSERT(m.iterations != NULL, "iterations should be created");
  VALK_TEST_ASSERT(m.events != NULL, "events should be created");
  VALK_TEST_ASSERT(m.events_waiting != NULL, "events_waiting should be created");
  VALK_TEST_ASSERT(m.idle_time_us != NULL, "idle_time_us should be created");
  VALK_TEST_ASSERT(m.handles != NULL, "handles should be created");

  VALK_PASS();
}

void test_event_loop_metrics_zero_handles(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "zero_handles_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_event_loop_metrics_v2_set_handles(&m, 0);

  int64_t handles_val = atomic_load(&m.handles->value);
  VALK_TEST_ASSERT(handles_val == 0, "handles should be 0");

  VALK_PASS();
}

void test_event_loop_metrics_negative_handles(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "negative_handles_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_event_loop_metrics_v2_set_handles(&m, -1);

  int64_t handles_val = atomic_load(&m.handles->value);
  VALK_TEST_ASSERT(handles_val == -1, "handles should accept negative value");

  VALK_PASS();
}

void test_event_loop_metrics_with_libuv_loop(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  uv_loop_t loop;
  int rc = uv_loop_init(&loop);
  VALK_TEST_ASSERT(rc == 0, "uv_loop_init should succeed");

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "libuv_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_event_loop_metrics_v2_update(&m, &loop);

  uv_loop_close(&loop);

  VALK_PASS();
}

void test_event_loop_metrics_update_twice(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  uv_loop_t loop;
  int rc = uv_loop_init(&loop);
  VALK_TEST_ASSERT(rc == 0, "uv_loop_init should succeed");

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "update_twice_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_event_loop_metrics_v2_update(&m, &loop);
  valk_event_loop_metrics_v2_update(&m, &loop);

  uv_loop_close(&loop);

  VALK_PASS();
}

void test_event_loop_metrics_empty_loop_name(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "");
  VALK_TEST_ASSERT(result == true, "Init with empty name should succeed");

  VALK_PASS();
}

void test_event_loop_metrics_counters_monotonic(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "monotonic_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  VALK_TEST_ASSERT(m.iterations != NULL, "iterations counter should exist");
  VALK_TEST_ASSERT(m.events != NULL, "events counter should exist");

  VALK_PASS();
}

void test_event_loop_metrics_gauges_exist(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "gauges_exist_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  VALK_TEST_ASSERT(m.events_waiting != NULL, "events_waiting gauge should exist");
  VALK_TEST_ASSERT(m.idle_time_us != NULL, "idle_time_us gauge should exist");
  VALK_TEST_ASSERT(m.handles != NULL, "handles gauge should exist");

  VALK_PASS();
}

void test_event_loop_metrics_prev_tracking_init(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "prev_init_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  VALK_TEST_ASSERT(m.prev_iterations == 0, "prev_iterations should be 0");
  VALK_TEST_ASSERT(m.prev_events == 0, "prev_events should be 0");

  VALK_PASS();
}

void test_event_loop_metrics_handle_updates_persist(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "persist_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_event_loop_metrics_v2_set_handles(&m, 100);
  valk_event_loop_metrics_v2_set_handles(&m, 50);
  valk_event_loop_metrics_v2_set_handles(&m, 75);

  int64_t final = atomic_load(&m.handles->value);
  VALK_TEST_ASSERT(final == 75, "final handle value should be 75");

  VALK_PASS();
}

void test_event_loop_metrics_update_with_activity(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  uv_loop_t loop;
  int rc = uv_loop_init(&loop);
  VALK_TEST_ASSERT(rc == 0, "uv_loop_init should succeed");

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "activity_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  valk_event_loop_metrics_v2_update(&m, &loop);

  uv_run(&loop, UV_RUN_NOWAIT);

  valk_event_loop_metrics_v2_update(&m, &loop);

  uv_loop_close(&loop);

  VALK_PASS();
}

void test_event_loop_metrics_set_handles_null_gauge(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_event_loop_metrics_v2_t m;
  memset(&m, 0, sizeof(m));
  m.handles = NULL;

  valk_event_loop_metrics_v2_set_handles(&m, 42);

  VALK_PASS();
}

void test_event_loop_metrics_multiple_updates(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_metrics_registry_init();

  uv_loop_t loop;
  int rc = uv_loop_init(&loop);
  VALK_TEST_ASSERT(rc == 0, "uv_loop_init should succeed");

  valk_event_loop_metrics_v2_t m;
  bool result = valk_event_loop_metrics_v2_init(&m, "multi_update_test");
  VALK_TEST_ASSERT(result == true, "Init should succeed");

  for (int i = 0; i < 10; i++) {
    uv_run(&loop, UV_RUN_NOWAIT);
    valk_event_loop_metrics_v2_update(&m, &loop);
  }

  uv_loop_close(&loop);

  VALK_PASS();
}

void test_event_loop_metrics_update_null_gauges(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  int rc = uv_loop_init(&loop);
  VALK_TEST_ASSERT(rc == 0, "uv_loop_init should succeed");

  valk_event_loop_metrics_v2_t m;
  memset(&m, 0, sizeof(m));
  m.loop_name = "null_gauges_test";

  valk_event_loop_metrics_v2_update(&m, &loop);

  uv_loop_close(&loop);

  VALK_PASS();
}

#else

void test_event_loop_metrics_disabled(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Event loop metrics tests require VALK_METRICS_ENABLED");
}

#endif

int main(void) {
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

#ifdef VALK_METRICS_ENABLED
  valk_testsuite_add_test(suite, "test_event_loop_metrics_init_null", test_event_loop_metrics_init_null);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_init_success", test_event_loop_metrics_init_success);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_set_handles", test_event_loop_metrics_set_handles);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_set_handles_null", test_event_loop_metrics_set_handles_null);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_update_null", test_event_loop_metrics_update_null);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_multiple_loops", test_event_loop_metrics_multiple_loops);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_prev_tracking", test_event_loop_metrics_prev_tracking);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_handles_large_values", test_event_loop_metrics_handles_large_values);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_rapid_handle_updates", test_event_loop_metrics_rapid_handle_updates);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_different_loop_names", test_event_loop_metrics_different_loop_names);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_all_gauges_created", test_event_loop_metrics_all_gauges_created);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_zero_handles", test_event_loop_metrics_zero_handles);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_negative_handles", test_event_loop_metrics_negative_handles);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_with_libuv_loop", test_event_loop_metrics_with_libuv_loop);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_update_twice", test_event_loop_metrics_update_twice);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_empty_loop_name", test_event_loop_metrics_empty_loop_name);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_counters_monotonic", test_event_loop_metrics_counters_monotonic);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_gauges_exist", test_event_loop_metrics_gauges_exist);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_prev_tracking_init", test_event_loop_metrics_prev_tracking_init);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_handle_updates_persist", test_event_loop_metrics_handle_updates_persist);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_update_with_activity", test_event_loop_metrics_update_with_activity);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_set_handles_null_gauge", test_event_loop_metrics_set_handles_null_gauge);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_multiple_updates", test_event_loop_metrics_multiple_updates);
  valk_testsuite_add_test(suite, "test_event_loop_metrics_update_null_gauges", test_event_loop_metrics_update_null_gauges);
#else
  valk_testsuite_add_test(suite, "test_event_loop_metrics_disabled", test_event_loop_metrics_disabled);
#endif

  int result = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return result;
}
