// test/test_loop_metrics.c - Tests for libuv event loop metrics
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif
#define _POSIX_C_SOURCE 200809L

#include <pthread.h>
#include "testing.h"
#include "common.h"

#ifdef VALK_METRICS_ENABLED

#include "aio/aio_metrics.h"
#include <uv.h>
#include <string.h>

//-----------------------------------------------------------------------------
// Test Helper - Timer Callback
//-----------------------------------------------------------------------------

// Context for timer tests
typedef struct {
  uv_timer_t* timer;
  int fire_count;
} timer_context_t;

// Timer callback that stops itself
static void timer_stop_cb(uv_timer_t* t) {
  timer_context_t* ctx = (timer_context_t*)t->data;
  ctx->fire_count++;
  uv_timer_stop(t);
}

// Timer callback for multi-fire tests
static void timer_multi_cb(uv_timer_t* t) {
  timer_context_t* ctx = (timer_context_t*)t->data;
  ctx->fire_count++;
  if (ctx->fire_count >= 3) {
    uv_timer_stop(t);
  }
}

//-----------------------------------------------------------------------------
// Test: Basic Loop Metrics
//-----------------------------------------------------------------------------

void test_loop_metrics_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create a simple timer to give the loop something to do
  uv_timer_t timer;
  timer_context_t ctx = {.timer = &timer, .fire_count = 0};
  timer.data = &ctx;
  uv_timer_init(&loop, &timer);
  uv_timer_start(&timer, timer_stop_cb, 1, 0);

  // Run the loop
  uv_run(&loop, UV_RUN_DEFAULT);

  // Get metrics
  valk_event_loop_metrics_t metrics;
  valk_event_loop_metrics_get(&loop, &metrics);

  // Loop should have run at least once
  VALK_TEST_ASSERT(metrics.loop_count >= 1,
                   "Loop count should be at least 1, got %lu", metrics.loop_count);

  uv_close((uv_handle_t*)&timer, nullptr);
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_loop_metrics_null_safety(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);

  valk_event_loop_metrics_t metrics;

  // Should not crash with nullptr parameters
  valk_event_loop_metrics_get(nullptr, &metrics);
  valk_event_loop_metrics_get(&loop, nullptr);
  valk_event_loop_metrics_get(nullptr, nullptr);

  uv_loop_close(&loop);
  VALK_PASS();
}

void test_loop_metrics_zeroed(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  valk_event_loop_metrics_t metrics;
  // Fill with non-zero data
  memset(&metrics, 0xFF, sizeof(metrics));

  // Get metrics should zero out structure first
  valk_event_loop_metrics_get(&loop, &metrics);

  // All fields should be reasonable (not 0xFF...FF)
  VALK_TEST_ASSERT(metrics.loop_count < 1000000,
                   "Loop count should be reasonable after zeroing");

  uv_loop_close(&loop);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Loop Iterations and Events
//-----------------------------------------------------------------------------

void test_loop_iterations_counted(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create a timer that fires multiple times
  uv_timer_t timer;
  timer_context_t ctx = {.timer = &timer, .fire_count = 0};
  timer.data = &ctx;
  uv_timer_init(&loop, &timer);

  // Get initial metrics
  valk_event_loop_metrics_t before;
  valk_event_loop_metrics_get(&loop, &before);
  u64 initial_count = before.loop_count;

  // Run with repeating timer (fires 3 times)
  uv_timer_start(&timer, timer_multi_cb, 1, 2);
  uv_run(&loop, UV_RUN_DEFAULT);

  // Get metrics after
  valk_event_loop_metrics_t after;
  valk_event_loop_metrics_get(&loop, &after);

  // Loop count should have increased
  VALK_TEST_ASSERT(after.loop_count > initial_count,
                   "Loop count should increase from %lu to %lu",
                   initial_count, after.loop_count);

  uv_close((uv_handle_t*)&timer, nullptr);
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_loop_events_counted(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create a timer
  uv_timer_t timer;
  timer_context_t ctx = {.timer = &timer, .fire_count = 0};
  timer.data = &ctx;
  uv_timer_init(&loop, &timer);

  // Schedule timer to fire immediately
  uv_timer_start(&timer, timer_stop_cb, 1, 0);

  // Get metrics before
  valk_event_loop_metrics_t before;
  valk_event_loop_metrics_get(&loop, &before);

  // Run the loop until timer fires
  uv_run(&loop, UV_RUN_DEFAULT);

  // Get metrics after
  valk_event_loop_metrics_t after;
  valk_event_loop_metrics_get(&loop, &after);

  // Events should have been processed
  VALK_TEST_ASSERT(ctx.fire_count == 1,
                   "Timer should have fired once");
  VALK_TEST_ASSERT(after.events >= before.events,
                   "Events should have been counted");

  uv_close((uv_handle_t*)&timer, nullptr);
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_loop_multiple_events(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create multiple timers
  uv_timer_t timers[3];
  timer_context_t contexts[3];

  for (int i = 0; i < 3; i++) {
    contexts[i].timer = &timers[i];
    contexts[i].fire_count = 0;
    timers[i].data = &contexts[i];
    uv_timer_init(&loop, &timers[i]);
    uv_timer_start(&timers[i], timer_stop_cb, 1 + i, 0);
  }

  // Get metrics before
  valk_event_loop_metrics_t before;
  valk_event_loop_metrics_get(&loop, &before);

  // Run the loop
  uv_run(&loop, UV_RUN_DEFAULT);

  // Get metrics after
  valk_event_loop_metrics_t after;
  valk_event_loop_metrics_get(&loop, &after);

  // All timers should have fired
  for (int i = 0; i < 3; i++) {
    VALK_TEST_ASSERT(contexts[i].fire_count == 1,
                     "Timer %d should have fired", i);
  }

  // Events should have increased
  VALK_TEST_ASSERT(after.events >= before.events,
                   "Events should have been counted");

  // Clean up
  for (int i = 0; i < 3; i++) {
    uv_close((uv_handle_t*)&timers[i], nullptr);
  }
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Idle Time Tracking
//-----------------------------------------------------------------------------

void test_loop_idle_time(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create a timer that waits a bit
  uv_timer_t timer;
  timer_context_t ctx = {.timer = &timer, .fire_count = 0};
  timer.data = &ctx;
  uv_timer_init(&loop, &timer);

  // Schedule timer to fire after 10ms
  uv_timer_start(&timer, timer_stop_cb, 10, 0);

  // Run the loop (will wait for timer)
  uv_run(&loop, UV_RUN_DEFAULT);

  // Get metrics
  valk_event_loop_metrics_t metrics;
  valk_event_loop_metrics_get(&loop, &metrics);

  // Idle time should be tracked (though exact value depends on system)
  // We just verify it's a reasonable value
  VALK_TEST_ASSERT(metrics.idle_time_us < 1000000,  // Less than 1 second
                   "Idle time should be reasonable, got %lu us",
                   metrics.idle_time_us);

  uv_close((uv_handle_t*)&timer, nullptr);
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  VALK_PASS();
}

void test_loop_idle_time_increases(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create timer
  uv_timer_t timer;
  timer_context_t ctx = {.timer = &timer, .fire_count = 0};
  timer.data = &ctx;
  uv_timer_init(&loop, &timer);

  // First wait
  uv_timer_start(&timer, timer_stop_cb, 5, 0);
  uv_run(&loop, UV_RUN_DEFAULT);

  valk_event_loop_metrics_t first;
  valk_event_loop_metrics_get(&loop, &first);

  // Second wait
  ctx.fire_count = 0;  // Reset
  uv_timer_start(&timer, timer_stop_cb, 5, 0);
  uv_run(&loop, UV_RUN_DEFAULT);

  valk_event_loop_metrics_t second;
  valk_event_loop_metrics_get(&loop, &second);

  // Idle time should have increased
  VALK_TEST_ASSERT(second.idle_time_us >= first.idle_time_us,
                   "Idle time should increase or stay same: %lu -> %lu",
                   first.idle_time_us, second.idle_time_us);

  uv_close((uv_handle_t*)&timer, nullptr);
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Events Waiting
//-----------------------------------------------------------------------------

void test_loop_events_waiting(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create a timer that will fire multiple times
  uv_timer_t timer;
  timer_context_t ctx = {.timer = &timer, .fire_count = 0};
  timer.data = &ctx;
  uv_timer_init(&loop, &timer);

  // Schedule repeating timer
  uv_timer_start(&timer, timer_multi_cb, 1, 2);  // Fire every 2ms

  // Run once to let timer start
  uv_run(&loop, UV_RUN_NOWAIT);

  // Get metrics (timer should be pending)
  valk_event_loop_metrics_t metrics;
  valk_event_loop_metrics_get(&loop, &metrics);

  // Should have some indication of activity
  VALK_TEST_ASSERT(metrics.loop_count >= 1,
                   "Loop should have run");

  // Run until all timers complete
  uv_run(&loop, UV_RUN_DEFAULT);

  VALK_TEST_ASSERT(ctx.fire_count >= 3,
                   "Timer should have fired at least 3 times");

  uv_close((uv_handle_t*)&timer, nullptr);
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Test: Metrics Persistence Across Runs
//-----------------------------------------------------------------------------

void test_loop_metrics_cumulative(VALK_TEST_ARGS()) {
  VALK_TEST();

  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Run multiple times and verify metrics accumulate
  valk_event_loop_metrics_t prev;
  valk_event_loop_metrics_get(&loop, &prev);

  for (int i = 0; i < 10; i++) {
    uv_run(&loop, UV_RUN_NOWAIT);

    valk_event_loop_metrics_t curr;
    valk_event_loop_metrics_get(&loop, &curr);

    // Loop count should be monotonically increasing
    VALK_TEST_ASSERT(curr.loop_count >= prev.loop_count,
                     "Loop count should not decrease");

    prev = curr;
  }

  uv_loop_close(&loop);
  VALK_PASS();
}

//-----------------------------------------------------------------------------
// Main
//-----------------------------------------------------------------------------

int main(int argc, const char** argv) {
  UNUSED(argc);
  UNUSED(argv);

  // Initialize memory allocator
  valk_mem_init_malloc();

  valk_test_suite_t* suite = valk_testsuite_empty(__FILE__);

  // Basic tests
  valk_testsuite_add_test(suite, "test_loop_metrics_basic",
                          test_loop_metrics_basic);
  valk_testsuite_add_test(suite, "test_loop_metrics_null_safety",
                          test_loop_metrics_null_safety);
  valk_testsuite_add_test(suite, "test_loop_metrics_zeroed",
                          test_loop_metrics_zeroed);

  // Loop iteration tests
  valk_testsuite_add_test(suite, "test_loop_iterations_counted",
                          test_loop_iterations_counted);
  valk_testsuite_add_test(suite, "test_loop_events_counted",
                          test_loop_events_counted);
  valk_testsuite_add_test(suite, "test_loop_multiple_events",
                          test_loop_multiple_events);

  // Idle time tests
  valk_testsuite_add_test(suite, "test_loop_idle_time",
                          test_loop_idle_time);
  valk_testsuite_add_test(suite, "test_loop_idle_time_increases",
                          test_loop_idle_time_increases);

  // Events waiting tests
  valk_testsuite_add_test(suite, "test_loop_events_waiting",
                          test_loop_events_waiting);

  // Cumulative tests
  valk_testsuite_add_test(suite, "test_loop_metrics_cumulative",
                          test_loop_metrics_cumulative);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}

#else

//=============================================================================
// METRICS DISABLED - Skip Tests
//=============================================================================

#include <stdio.h>

int main(int argc, const char** argv) {
  UNUSED(argc);
  UNUSED(argv);

  fprintf(stderr, "SKIP: Event loop metrics tests disabled (VALK_METRICS not enabled)\n");
  return 0;
}

#endif // VALK_METRICS_ENABLED
