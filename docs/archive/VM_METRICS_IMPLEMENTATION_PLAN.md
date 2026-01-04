# Valkyria VM Metrics Implementation Plan

## Overview

This plan adds three new metrics subsystems to complement the existing AIO/HTTP metrics:
1. **GC Metrics** - Garbage collector performance
2. **Interpreter Metrics** - Evaluator/parser statistics
3. **libuv Event Loop Metrics** - Event loop performance

### Industry Frameworks Applied

- **RED Method** (Rate, Errors, Duration) - for request-oriented metrics
- **USE Method** (Utilization, Saturation, Errors) - for resource-oriented metrics
- **Four Golden Signals** (Latency, Traffic, Errors, Saturation) - for SRE dashboards

---

## Current State

### Already Implemented (in `src/aio_metrics.{h,c}`)

| Category | Metrics |
|----------|---------|
| HTTP Requests | `requests_total`, `requests_active`, `requests_errors`, `request_duration_us_sum` |
| Connections | `connections_total`, `connections_active`, `connections_failed` |
| Streams | `streams_total`, `streams_active` |
| Bandwidth | `bytes_sent_total`, `bytes_recv_total` |
| System | `servers_count`, `clients_count`, `handles_count` |
| Memory Pools | `arenas_used/total`, `tcp_buffers_used/total` |
| Event Loop | `queue_depth`, `pending_requests`, `pending_responses` |

### Missing (To Be Implemented)

| Category | Metrics | Priority |
|----------|---------|----------|
| **GC** | cycles, pause times, heap utilization | High |
| **Interpreter** | evals, call depth, closures | High |
| **libuv** | loop_count, idle_time from `uv_metrics_t` | Medium |

---

## Phase 1: GC Metrics

### 1.1 Add GC Runtime Metrics Structure

**File:** `src/gc.h` (after line 31, after `valk_gc_heap_stats_t`)

```c
// GC runtime metrics for observability (live counters, not telemetry snapshots)
typedef struct {
  _Atomic uint64_t cycles_total;           // Total GC collections
  _Atomic uint64_t pause_us_total;         // Cumulative pause time (microseconds)
  _Atomic uint64_t pause_us_max;           // Worst-case pause time
  _Atomic uint64_t reclaimed_bytes_total;  // Total bytes reclaimed across all cycles
  _Atomic uint64_t objects_marked;         // Objects marked in last cycle
  _Atomic uint64_t objects_swept;          // Objects swept in last cycle
  uint64_t last_cycle_start_us;            // Timing for current cycle (internal)
} valk_gc_runtime_metrics_t;
```

**Add to `valk_gc_malloc_heap_t` struct (line 47, after `stats`):**

```c
  valk_gc_runtime_metrics_t runtime_metrics; // Live runtime metrics for observability
```

### 1.2 Add GC Metrics Export API

**File:** `src/gc.h` (after line 77, after `valk_gc_malloc_heap_destroy`)

```c
// Get GC runtime metrics for export (thread-safe reads)
void valk_gc_get_runtime_metrics(valk_gc_malloc_heap_t* heap,
                                  uint64_t* cycles, uint64_t* pause_us_total,
                                  uint64_t* pause_us_max, uint64_t* reclaimed,
                                  size_t* heap_used, size_t* heap_total);
```

### 1.3 Initialize GC Metrics

**File:** `src/gc.c` (in `valk_gc_malloc_heap_init()`, after line 69)

```c
  // Initialize runtime metrics
  atomic_store(&heap->runtime_metrics.cycles_total, 0);
  atomic_store(&heap->runtime_metrics.pause_us_total, 0);
  atomic_store(&heap->runtime_metrics.pause_us_max, 0);
  atomic_store(&heap->runtime_metrics.reclaimed_bytes_total, 0);
  atomic_store(&heap->runtime_metrics.objects_marked, 0);
  atomic_store(&heap->runtime_metrics.objects_swept, 0);
  heap->runtime_metrics.last_cycle_start_us = 0;
```

### 1.4 Instrument GC Collection

**File:** `src/gc.c` (modify `valk_gc_malloc_collect()` starting at line 964)

```c
size_t valk_gc_malloc_collect(valk_gc_malloc_heap_t* heap, valk_lval_t* additional_root) {
  if (heap->root_env == NULL) {
    VALK_WARN("GC collect called with no root environment");
    return 0;
  }

  // ===== START METRICS TIMING =====
  uint64_t gc_start_us = uv_hrtime() / 1000;

  size_t before = heap->allocated_bytes;

  VALK_INFO("GC: Starting collection #%zu (allocated: %zu/%zu bytes, %.1f%% full)",
            heap->num_collections + 1,
            before,
            heap->gc_threshold,
            100.0 * before / heap->gc_threshold);

  // Set thread-local heap pointer for safe marking checks
  gc_current_heap = heap;

  // Phase 1: Mark reachable objects from root environment and any additional roots
  valk_gc_mark_env(heap->root_env);
  if (additional_root != NULL) {
    valk_gc_mark_lval(additional_root);
  }

  // Phase 2: Sweep unreachable objects
  size_t reclaimed = valk_gc_malloc_sweep(heap);

  // Clear thread-local heap pointer
  gc_current_heap = NULL;

  // Phase 3: Clear marks for next collection
  for (valk_gc_header_t* header = heap->objects; header != NULL; header = header->gc_next) {
    header->origin_allocator = (void*)((uintptr_t)header->origin_allocator & ~(uintptr_t)1);
    if (header->size == heap->lval_size) {
      void* user_data = (void*)(header + 1);
      valk_lval_t* obj = (valk_lval_t*)user_data;
      obj->flags &= ~LVAL_FLAG_GC_MARK;
    }
  }

  size_t after = heap->allocated_bytes;
  heap->num_collections++;

  // ===== END METRICS TIMING =====
  uint64_t gc_end_us = uv_hrtime() / 1000;
  uint64_t pause_us = gc_end_us - gc_start_us;

  // Update runtime metrics (lock-free)
  atomic_fetch_add(&heap->runtime_metrics.cycles_total, 1);
  atomic_fetch_add(&heap->runtime_metrics.pause_us_total, pause_us);
  atomic_fetch_add(&heap->runtime_metrics.reclaimed_bytes_total, reclaimed);

  // Update max pause using compare-exchange
  uint64_t current_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  while (pause_us > current_max) {
    if (atomic_compare_exchange_weak(&heap->runtime_metrics.pause_us_max,
                                      &current_max, pause_us)) {
      break;
    }
  }

  VALK_INFO("GC: Complete - reclaimed %zu bytes (before: %zu, after: %zu, %.1f%% freed, pause: %lu us)",
            reclaimed, before, after,
            before > 0 ? 100.0 * reclaimed / before : 0.0,
            pause_us);

  return reclaimed;
}
```

### 1.5 Implement Metrics Export Function

**File:** `src/gc.c` (add after `valk_gc_malloc_heap_destroy`, around line 1133)

```c
// Get GC runtime metrics for export
void valk_gc_get_runtime_metrics(valk_gc_malloc_heap_t* heap,
                                  uint64_t* cycles, uint64_t* pause_us_total,
                                  uint64_t* pause_us_max, uint64_t* reclaimed,
                                  size_t* heap_used, size_t* heap_total) {
  if (!heap) return;

  if (cycles) *cycles = atomic_load(&heap->runtime_metrics.cycles_total);
  if (pause_us_total) *pause_us_total = atomic_load(&heap->runtime_metrics.pause_us_total);
  if (pause_us_max) *pause_us_max = atomic_load(&heap->runtime_metrics.pause_us_max);
  if (reclaimed) *reclaimed = atomic_load(&heap->runtime_metrics.reclaimed_bytes_total);
  if (heap_used) *heap_used = heap->allocated_bytes;
  if (heap_total) *heap_total = heap->hard_limit;
}
```

### 1.6 Test Cases

**File:** `test/test_gc_metrics.c` (new file)

```c
#include "testing.h"
#include "gc.h"
#include "parser.h"
#include "memory.h"
#include <uv.h>

// Test: GC metrics initialize to zero
void test_gc_metrics_init(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 0);
  TEST_ASSERT(heap != NULL, "Heap should be created");

  uint64_t cycles, pause_total, pause_max, reclaimed;
  size_t used, total;
  valk_gc_get_runtime_metrics(heap, &cycles, &pause_total, &pause_max,
                               &reclaimed, &used, &total);

  TEST_ASSERT(cycles == 0, "Initial cycles should be 0");
  TEST_ASSERT(pause_total == 0, "Initial pause_total should be 0");
  TEST_ASSERT(pause_max == 0, "Initial pause_max should be 0");
  TEST_ASSERT(reclaimed == 0, "Initial reclaimed should be 0");
  TEST_ASSERT(total == heap->hard_limit, "Total should match hard_limit");

  valk_gc_malloc_heap_destroy(heap);
  TEST_PASS();
}

// Test: GC metrics increment after collection
void test_gc_metrics_after_collection(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(64 * 1024, 0);
  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // Allocate some garbage (not stored anywhere, will be collected)
  VALK_WITH_ALLOC((void*)heap) {
    for (int i = 0; i < 100; i++) {
      valk_lval_num(i);
    }
  }

  // Force collection
  valk_gc_malloc_collect(heap, NULL);

  uint64_t cycles;
  valk_gc_get_runtime_metrics(heap, &cycles, NULL, NULL, NULL, NULL, NULL);
  TEST_ASSERT(cycles == 1, "Should have 1 collection cycle");

  // Second collection
  valk_gc_malloc_collect(heap, NULL);
  valk_gc_get_runtime_metrics(heap, &cycles, NULL, NULL, NULL, NULL, NULL);
  TEST_ASSERT(cycles == 2, "Should have 2 collection cycles");

  valk_gc_malloc_heap_destroy(heap);
  TEST_PASS();
}

// Test: Pause time is recorded
void test_gc_pause_time_recorded(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(64 * 1024, 0);
  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  valk_gc_malloc_collect(heap, NULL);

  uint64_t pause_total, pause_max;
  valk_gc_get_runtime_metrics(heap, NULL, &pause_total, &pause_max, NULL, NULL, NULL);

  TEST_ASSERT(pause_total > 0, "Pause time should be recorded");
  TEST_ASSERT(pause_max > 0, "Max pause should be recorded");
  TEST_ASSERT(pause_max <= pause_total, "Max should be <= total after 1 cycle");

  valk_gc_malloc_heap_destroy(heap);
  TEST_PASS();
}

// Test: Reclaimed bytes are tracked
void test_gc_reclaimed_bytes(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(1024 * 1024, 0);
  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // Allocate garbage
  size_t allocated_before = heap->allocated_bytes;
  VALK_WITH_ALLOC((void*)heap) {
    for (int i = 0; i < 1000; i++) {
      valk_lval_num(i);
    }
  }
  size_t allocated_after = heap->allocated_bytes;
  TEST_ASSERT(allocated_after > allocated_before, "Should have allocated memory");

  // Collect garbage
  size_t reclaimed = valk_gc_malloc_collect(heap, NULL);

  uint64_t reclaimed_total;
  valk_gc_get_runtime_metrics(heap, NULL, NULL, NULL, &reclaimed_total, NULL, NULL);

  TEST_ASSERT(reclaimed_total >= reclaimed, "Reclaimed total should include this cycle");

  valk_gc_malloc_heap_destroy(heap);
  TEST_PASS();
}

// Test: Max pause tracks worst case across multiple collections
void test_gc_max_pause_tracking(void) {
  valk_gc_malloc_heap_t* heap = valk_gc_malloc_heap_init(64 * 1024, 0);
  valk_lenv_t* env = valk_lenv_empty();
  valk_gc_malloc_set_root(heap, env);

  // Run multiple collections
  for (int i = 0; i < 5; i++) {
    valk_gc_malloc_collect(heap, NULL);
  }

  uint64_t pause_total, pause_max;
  valk_gc_get_runtime_metrics(heap, NULL, &pause_total, &pause_max, NULL, NULL, NULL);

  TEST_ASSERT(pause_max <= pause_total, "Max pause should be <= total pause");
  TEST_ASSERT(pause_max > 0, "Max pause should be recorded");

  valk_gc_malloc_heap_destroy(heap);
  TEST_PASS();
}

int main(void) {
  TEST_SUITE_BEGIN("GC Metrics");

  RUN_TEST(test_gc_metrics_init);
  RUN_TEST(test_gc_metrics_after_collection);
  RUN_TEST(test_gc_pause_time_recorded);
  RUN_TEST(test_gc_reclaimed_bytes);
  RUN_TEST(test_gc_max_pause_tracking);

  TEST_SUITE_END();
}
```

---

## Phase 2: Interpreter Metrics

### 2.1 Add Interpreter Metrics Structure

**File:** `src/parser.h` (after line 195, at end of file)

```c
// ============================================================================
// Interpreter Runtime Metrics
// ============================================================================

// Interpreter metrics for observability
typedef struct {
  _Atomic uint64_t evals_total;        // Total lval_eval() calls
  _Atomic uint64_t function_calls;     // User-defined function invocations
  _Atomic uint64_t builtin_calls;      // Builtin function invocations
  _Atomic uint32_t stack_depth;        // Current call stack depth
  uint32_t stack_depth_max;            // Peak call stack depth ever reached
  _Atomic uint64_t closures_created;   // Lambda closures created
  _Atomic uint64_t env_lookups;        // Symbol resolution lookups
} valk_eval_metrics_t;

// Global interpreter metrics instance
extern valk_eval_metrics_t g_eval_metrics;

// Initialize interpreter metrics (call at startup)
void valk_eval_metrics_init(void);

// Get current interpreter metrics (thread-safe)
void valk_eval_metrics_get(uint64_t* evals, uint64_t* func_calls,
                            uint64_t* builtin_calls, uint32_t* stack_max,
                            uint64_t* closures, uint64_t* lookups);
```

### 2.2 Implement Metrics and Instrument Evaluator

**File:** `src/parser.c`

**Add near top (after includes, around line 30):**

```c
// Global interpreter metrics instance
valk_eval_metrics_t g_eval_metrics = {0};

void valk_eval_metrics_init(void) {
  atomic_store(&g_eval_metrics.evals_total, 0);
  atomic_store(&g_eval_metrics.function_calls, 0);
  atomic_store(&g_eval_metrics.builtin_calls, 0);
  atomic_store(&g_eval_metrics.stack_depth, 0);
  g_eval_metrics.stack_depth_max = 0;
  atomic_store(&g_eval_metrics.closures_created, 0);
  atomic_store(&g_eval_metrics.env_lookups, 0);
}

void valk_eval_metrics_get(uint64_t* evals, uint64_t* func_calls,
                            uint64_t* builtin_calls, uint32_t* stack_max,
                            uint64_t* closures, uint64_t* lookups) {
  if (evals) *evals = atomic_load(&g_eval_metrics.evals_total);
  if (func_calls) *func_calls = atomic_load(&g_eval_metrics.function_calls);
  if (builtin_calls) *builtin_calls = atomic_load(&g_eval_metrics.builtin_calls);
  if (stack_max) *stack_max = g_eval_metrics.stack_depth_max;
  if (closures) *closures = atomic_load(&g_eval_metrics.closures_created);
  if (lookups) *lookups = atomic_load(&g_eval_metrics.env_lookups);
}
```

**Instrument `valk_lval_eval()` (line 766):**

```c
valk_lval_t* valk_lval_eval(valk_lenv_t* env, valk_lval_t* lval) {
  // ===== METRICS: Track evaluations =====
  atomic_fetch_add(&g_eval_metrics.evals_total, 1);

  // ... rest of existing function unchanged ...
```

**Instrument `valk_lval_eval_call()` (line 867):**

```c
valk_lval_t* valk_lval_eval_call(valk_lenv_t* env, valk_lval_t* func,
                                  valk_lval_t* args) {
  // ===== METRICS: Track call depth =====
  uint32_t depth = atomic_fetch_add(&g_eval_metrics.stack_depth, 1) + 1;
  if (depth > g_eval_metrics.stack_depth_max) {
    g_eval_metrics.stack_depth_max = depth;  // Non-atomic OK, only increases
  }

  // ===== METRICS: Track builtin vs user function =====
  if (func->fun.builtin != NULL) {
    atomic_fetch_add(&g_eval_metrics.builtin_calls, 1);
  } else {
    atomic_fetch_add(&g_eval_metrics.function_calls, 1);
  }

  // ... existing function code ...

  // Before each return statement, add:
  // atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);

  // At end before final return:
  atomic_fetch_sub(&g_eval_metrics.stack_depth, 1);
  return result;
}
```

**Instrument `valk_lval_lambda()` (find the function, around line 450):**

```c
valk_lval_t* valk_lval_lambda(valk_lenv_t* env, valk_lval_t* formals, valk_lval_t* body) {
  // ===== METRICS: Track closure creation =====
  atomic_fetch_add(&g_eval_metrics.closures_created, 1);

  // ... rest of existing function unchanged ...
```

**Instrument `valk_lenv_get()` (find the function, around line 1100):**

```c
valk_lval_t* valk_lenv_get(valk_lenv_t* env, valk_lval_t* key) {
  // ===== METRICS: Track symbol lookups =====
  atomic_fetch_add(&g_eval_metrics.env_lookups, 1);

  // ... rest of existing function unchanged ...
```

### 2.3 Test Cases

**File:** `test/test_eval_metrics.c` (new file)

```c
#include "testing.h"
#include "parser.h"
#include "memory.h"

// Test: Metrics initialize to zero
void test_eval_metrics_init(void) {
  valk_eval_metrics_init();

  uint64_t evals, func_calls, builtin_calls, closures, lookups;
  uint32_t stack_max;
  valk_eval_metrics_get(&evals, &func_calls, &builtin_calls, &stack_max, &closures, &lookups);

  TEST_ASSERT(evals == 0, "Initial evals should be 0");
  TEST_ASSERT(func_calls == 0, "Initial func_calls should be 0");
  TEST_ASSERT(builtin_calls == 0, "Initial builtin_calls should be 0");
  TEST_ASSERT(stack_max == 0, "Initial stack_max should be 0");
  TEST_ASSERT(closures == 0, "Initial closures should be 0");
  TEST_ASSERT(lookups == 0, "Initial lookups should be 0");

  TEST_PASS();
}

// Test: Eval counter increments
void test_eval_counter(void) {
  valk_eval_metrics_init();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, "(+ 1 2)");
  valk_lval_t* result = valk_lval_eval(env, expr);

  uint64_t evals;
  valk_eval_metrics_get(&evals, NULL, NULL, NULL, NULL, NULL);

  TEST_ASSERT(evals >= 1, "Should have at least 1 eval");
  TEST_ASSERT(result->num == 3, "Result should be 3");

  TEST_PASS();
}

// Test: Builtin calls are tracked
void test_builtin_calls(void) {
  valk_eval_metrics_init();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, "(+ 1 2 3 4 5)");
  valk_lval_eval(env, expr);

  uint64_t builtin_calls;
  valk_eval_metrics_get(NULL, NULL, &builtin_calls, NULL, NULL, NULL);

  TEST_ASSERT(builtin_calls >= 1, "Should have at least 1 builtin call");

  TEST_PASS();
}

// Test: Stack depth tracking with recursion
void test_stack_depth(void) {
  valk_eval_metrics_init();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  // Define recursive countdown function
  int pos = 0;
  valk_lval_t* def = valk_lval_read(&pos,
    "(def {countdown} (\\ {n} (if (== n 0) 0 (countdown (- n 1)))))");
  valk_lval_eval(env, def);

  // Call with depth 10
  pos = 0;
  valk_lval_t* call = valk_lval_read(&pos, "(countdown 10)");
  valk_lval_eval(env, call);

  uint32_t stack_max;
  valk_eval_metrics_get(NULL, NULL, NULL, &stack_max, NULL, NULL);

  TEST_ASSERT(stack_max >= 10, "Stack should reach depth >= 10");

  TEST_PASS();
}

// Test: Closure creation is counted
void test_closure_counting(void) {
  valk_eval_metrics_init();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  uint64_t before;
  valk_eval_metrics_get(NULL, NULL, NULL, NULL, &before, NULL);

  // Create a lambda
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, "(\\ {x} (* x x))");
  valk_lval_eval(env, expr);

  uint64_t after;
  valk_eval_metrics_get(NULL, NULL, NULL, NULL, &after, NULL);

  TEST_ASSERT(after > before, "Closure count should increase");

  TEST_PASS();
}

// Test: Symbol lookups are tracked
void test_env_lookups(void) {
  valk_eval_metrics_init();

  valk_lenv_t* env = valk_lenv_empty();
  valk_lenv_builtins(env);

  uint64_t before;
  valk_eval_metrics_get(NULL, NULL, NULL, NULL, NULL, &before);

  // Access some builtins
  int pos = 0;
  valk_lval_t* expr = valk_lval_read(&pos, "(+ 1 2)");
  valk_lval_eval(env, expr);

  uint64_t after;
  valk_eval_metrics_get(NULL, NULL, NULL, NULL, NULL, &after);

  TEST_ASSERT(after > before, "Lookup count should increase");

  TEST_PASS();
}

int main(void) {
  TEST_SUITE_BEGIN("Interpreter Metrics");

  RUN_TEST(test_eval_metrics_init);
  RUN_TEST(test_eval_counter);
  RUN_TEST(test_builtin_calls);
  RUN_TEST(test_stack_depth);
  RUN_TEST(test_closure_counting);
  RUN_TEST(test_env_lookups);

  TEST_SUITE_END();
}
```

---

## Phase 3: libuv Event Loop Metrics

### 3.1 Add Event Loop Metrics Structure

**File:** `src/aio_metrics.h` (after line 57, after `valk_aio_system_stats_t`)

```c
// Event loop metrics (from libuv uv_metrics_t)
// See: https://docs.libuv.org/en/v1.x/metrics.html
typedef struct {
  uint64_t loop_count;         // Number of event loop iterations
  uint64_t events;             // Total events processed
  uint64_t events_waiting;     // Events currently waiting
  uint64_t idle_time_us;       // Time spent idle in kernel poll (epoll/kqueue)
} valk_event_loop_metrics_t;

// Get current event loop metrics from libuv
void valk_event_loop_metrics_get(uv_loop_t* loop, valk_event_loop_metrics_t* out);
```

### 3.2 Implement Event Loop Metrics

**File:** `src/aio_metrics.c` (add at end, before `#endif`)

```c
// Get event loop metrics from libuv
void valk_event_loop_metrics_get(uv_loop_t* loop, valk_event_loop_metrics_t* out) {
  if (!loop || !out) return;

  // Zero out first
  memset(out, 0, sizeof(*out));

  // Get metrics from libuv (available since libuv 1.39.0)
  uv_metrics_t metrics;
  if (uv_metrics_info(loop, &metrics) == 0) {
    out->loop_count = metrics.loop_count;
    out->events = metrics.events;
    out->events_waiting = metrics.events_waiting;
  }

  // Get idle time (requires UV_METRICS_IDLE_TIME option)
  // Returns nanoseconds, convert to microseconds
  out->idle_time_us = uv_metrics_idle_time(loop) / 1000;
}
```

### 3.3 Enable Metrics Collection in Event Loop

**File:** `src/aio_uv.c` (find where `uv_loop_init()` is called)

After the loop is initialized, add:

```c
  // Enable metrics collection on event loop
  // This enables uv_metrics_idle_time() to track time spent in epoll/kqueue
  int rc = uv_loop_configure(loop, UV_METRICS_IDLE_TIME);
  if (rc != 0) {
    VALK_WARN("Failed to enable loop metrics: %s", uv_strerror(rc));
  }
```

### 3.4 Test Cases

**File:** `test/test_loop_metrics.c` (new file)

```c
#include "testing.h"
#include "aio_metrics.h"
#include <uv.h>
#include <unistd.h>

// Test: Can collect basic loop metrics
void test_loop_metrics_basic(void) {
  uv_loop_t loop;
  uv_loop_init(&loop);

  // Enable idle time tracking
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Run loop once (no-op, but increments loop_count)
  uv_run(&loop, UV_RUN_NOWAIT);

  valk_event_loop_metrics_t metrics;
  valk_event_loop_metrics_get(&loop, &metrics);

  TEST_ASSERT(metrics.loop_count >= 1, "Loop should have run at least once");

  uv_loop_close(&loop);
  TEST_PASS();
}

// Test: Idle time is tracked
void test_loop_idle_time(void) {
  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create a timer that fires after 10ms
  uv_timer_t timer;
  uv_timer_init(&loop, &timer);
  uv_timer_start(&timer, [](uv_timer_t* t) { uv_timer_stop(t); }, 10, 0);

  // Run until timer fires (will spend time in poll)
  uv_run(&loop, UV_RUN_DEFAULT);

  valk_event_loop_metrics_t metrics;
  valk_event_loop_metrics_get(&loop, &metrics);

  // Should have some idle time from waiting for timer
  TEST_ASSERT(metrics.idle_time_us > 0, "Should have recorded idle time");

  uv_close((uv_handle_t*)&timer, NULL);
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  TEST_PASS();
}

// Test: Events are counted
void test_loop_events_counted(void) {
  uv_loop_t loop;
  uv_loop_init(&loop);
  uv_loop_configure(&loop, UV_METRICS_IDLE_TIME);

  // Create multiple timers
  uv_timer_t timers[5];
  for (int i = 0; i < 5; i++) {
    uv_timer_init(&loop, &timers[i]);
    uv_timer_start(&timers[i], [](uv_timer_t* t) { uv_timer_stop(t); }, 1, 0);
  }

  // Run until all timers fire
  uv_run(&loop, UV_RUN_DEFAULT);

  valk_event_loop_metrics_t metrics;
  valk_event_loop_metrics_get(&loop, &metrics);

  TEST_ASSERT(metrics.events >= 5, "Should have processed at least 5 events");

  for (int i = 0; i < 5; i++) {
    uv_close((uv_handle_t*)&timers[i], NULL);
  }
  uv_run(&loop, UV_RUN_DEFAULT);
  uv_loop_close(&loop);
  TEST_PASS();
}

int main(void) {
  TEST_SUITE_BEGIN("Event Loop Metrics");

  RUN_TEST(test_loop_metrics_basic);
  RUN_TEST(test_loop_idle_time);
  RUN_TEST(test_loop_events_counted);

  TEST_SUITE_END();
}
```

---

## Phase 4: Unified VM Metrics Export

### 4.1 Add Combined VM Metrics Structure

**File:** `src/aio_metrics.h` (add after event loop metrics)

```c
// Forward declarations
struct valk_gc_malloc_heap_t;

// Combined VM metrics (all subsystems in one structure)
typedef struct {
  // GC metrics
  uint64_t gc_cycles;
  uint64_t gc_pause_us_total;
  uint64_t gc_pause_us_max;
  uint64_t gc_reclaimed_bytes;
  size_t gc_heap_used;
  size_t gc_heap_total;

  // Interpreter metrics
  uint64_t eval_total;
  uint64_t function_calls;
  uint64_t builtin_calls;
  uint32_t stack_depth_max;
  uint64_t closures_created;
  uint64_t env_lookups;

  // Event loop metrics
  uint64_t loop_count;
  uint64_t events_processed;
  uint64_t idle_time_us;
} valk_vm_metrics_t;

// Collect all VM metrics into a single structure
void valk_vm_metrics_collect(valk_vm_metrics_t* out,
                              struct valk_gc_malloc_heap_t* heap,
                              uv_loop_t* loop);

// Export VM metrics as JSON string
char* valk_vm_metrics_to_json(const valk_vm_metrics_t* m,
                               struct valk_mem_allocator_t* alloc);

// Export VM metrics in Prometheus format
char* valk_vm_metrics_to_prometheus(const valk_vm_metrics_t* m,
                                     struct valk_mem_allocator_t* alloc);
```

### 4.2 Implement Combined Export

**File:** `src/aio_metrics.c` (add before final `#endif`)

```c
#include "gc.h"
#include "parser.h"

// Collect all VM metrics
void valk_vm_metrics_collect(valk_vm_metrics_t* out,
                              valk_gc_malloc_heap_t* heap,
                              uv_loop_t* loop) {
  if (!out) return;
  memset(out, 0, sizeof(*out));

  // GC metrics
  if (heap) {
    valk_gc_get_runtime_metrics(heap,
      &out->gc_cycles, &out->gc_pause_us_total, &out->gc_pause_us_max,
      &out->gc_reclaimed_bytes, &out->gc_heap_used, &out->gc_heap_total);
  }

  // Interpreter metrics
  valk_eval_metrics_get(
    &out->eval_total, &out->function_calls, &out->builtin_calls,
    &out->stack_depth_max, &out->closures_created, &out->env_lookups);

  // Event loop metrics
  if (loop) {
    valk_event_loop_metrics_t loop_m;
    valk_event_loop_metrics_get(loop, &loop_m);
    out->loop_count = loop_m.loop_count;
    out->events_processed = loop_m.events;
    out->idle_time_us = loop_m.idle_time_us;
  }
}

// Export VM metrics as JSON
char* valk_vm_metrics_to_json(const valk_vm_metrics_t* m,
                               valk_mem_allocator_t* alloc) {
  if (!m) return NULL;

  size_t buf_size = 2048;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return NULL;

  double heap_util = m->gc_heap_total > 0
    ? 100.0 * (double)m->gc_heap_used / (double)m->gc_heap_total
    : 0.0;

  int written = snprintf(buf, buf_size,
    "{\n"
    "  \"gc\": {\n"
    "    \"cycles_total\": %lu,\n"
    "    \"pause_us_total\": %lu,\n"
    "    \"pause_us_max\": %lu,\n"
    "    \"pause_ms_avg\": %.3f,\n"
    "    \"reclaimed_bytes_total\": %lu,\n"
    "    \"heap_used_bytes\": %zu,\n"
    "    \"heap_total_bytes\": %zu,\n"
    "    \"heap_utilization_pct\": %.2f\n"
    "  },\n"
    "  \"interpreter\": {\n"
    "    \"evals_total\": %lu,\n"
    "    \"function_calls\": %lu,\n"
    "    \"builtin_calls\": %lu,\n"
    "    \"stack_depth_max\": %u,\n"
    "    \"closures_created\": %lu,\n"
    "    \"env_lookups\": %lu\n"
    "  },\n"
    "  \"event_loop\": {\n"
    "    \"iterations\": %lu,\n"
    "    \"events_processed\": %lu,\n"
    "    \"idle_time_us\": %lu,\n"
    "    \"idle_time_pct\": %.2f\n"
    "  }\n"
    "}",
    m->gc_cycles,
    m->gc_pause_us_total,
    m->gc_pause_us_max,
    m->gc_cycles > 0 ? (double)m->gc_pause_us_total / m->gc_cycles / 1000.0 : 0.0,
    m->gc_reclaimed_bytes,
    m->gc_heap_used,
    m->gc_heap_total,
    heap_util,
    m->eval_total,
    m->function_calls,
    m->builtin_calls,
    m->stack_depth_max,
    m->closures_created,
    m->env_lookups,
    m->loop_count,
    m->events_processed,
    m->idle_time_us,
    0.0  // TODO: Calculate idle percentage when we have total runtime
  );

  (void)written;
  return buf;
}

// Export VM metrics in Prometheus format
char* valk_vm_metrics_to_prometheus(const valk_vm_metrics_t* m,
                                     valk_mem_allocator_t* alloc) {
  if (!m) return NULL;

  size_t buf_size = 4096;
  char* buf = alloc ? valk_mem_allocator_alloc(alloc, buf_size) : malloc(buf_size);
  if (!buf) return NULL;

  int written = snprintf(buf, buf_size,
    "# HELP valk_gc_cycles_total Total garbage collection cycles\n"
    "# TYPE valk_gc_cycles_total counter\n"
    "valk_gc_cycles_total %lu\n"
    "\n"
    "# HELP valk_gc_pause_seconds_total Total GC pause time in seconds\n"
    "# TYPE valk_gc_pause_seconds_total counter\n"
    "valk_gc_pause_seconds_total %.6f\n"
    "\n"
    "# HELP valk_gc_pause_seconds_max Maximum single GC pause in seconds\n"
    "# TYPE valk_gc_pause_seconds_max gauge\n"
    "valk_gc_pause_seconds_max %.6f\n"
    "\n"
    "# HELP valk_gc_reclaimed_bytes_total Total bytes reclaimed by GC\n"
    "# TYPE valk_gc_reclaimed_bytes_total counter\n"
    "valk_gc_reclaimed_bytes_total %lu\n"
    "\n"
    "# HELP valk_gc_heap_used_bytes Current heap memory in use\n"
    "# TYPE valk_gc_heap_used_bytes gauge\n"
    "valk_gc_heap_used_bytes %zu\n"
    "\n"
    "# HELP valk_gc_heap_total_bytes Total heap capacity\n"
    "# TYPE valk_gc_heap_total_bytes gauge\n"
    "valk_gc_heap_total_bytes %zu\n"
    "\n"
    "# HELP valk_eval_total Total expression evaluations\n"
    "# TYPE valk_eval_total counter\n"
    "valk_eval_total %lu\n"
    "\n"
    "# HELP valk_function_calls_total User function invocations\n"
    "# TYPE valk_function_calls_total counter\n"
    "valk_function_calls_total %lu\n"
    "\n"
    "# HELP valk_builtin_calls_total Builtin function invocations\n"
    "# TYPE valk_builtin_calls_total counter\n"
    "valk_builtin_calls_total %lu\n"
    "\n"
    "# HELP valk_stack_depth_max Peak call stack depth\n"
    "# TYPE valk_stack_depth_max gauge\n"
    "valk_stack_depth_max %u\n"
    "\n"
    "# HELP valk_closures_created_total Lambda closures created\n"
    "# TYPE valk_closures_created_total counter\n"
    "valk_closures_created_total %lu\n"
    "\n"
    "# HELP valk_env_lookups_total Symbol resolution lookups\n"
    "# TYPE valk_env_lookups_total counter\n"
    "valk_env_lookups_total %lu\n"
    "\n"
    "# HELP valk_loop_iterations_total Event loop iterations\n"
    "# TYPE valk_loop_iterations_total counter\n"
    "valk_loop_iterations_total %lu\n"
    "\n"
    "# HELP valk_events_processed_total Events processed by event loop\n"
    "# TYPE valk_events_processed_total counter\n"
    "valk_events_processed_total %lu\n"
    "\n"
    "# HELP valk_loop_idle_seconds_total Time spent idle in event loop\n"
    "# TYPE valk_loop_idle_seconds_total counter\n"
    "valk_loop_idle_seconds_total %.6f\n",
    m->gc_cycles,
    (double)m->gc_pause_us_total / 1e6,
    (double)m->gc_pause_us_max / 1e6,
    m->gc_reclaimed_bytes,
    m->gc_heap_used,
    m->gc_heap_total,
    m->eval_total,
    m->function_calls,
    m->builtin_calls,
    m->stack_depth_max,
    m->closures_created,
    m->env_lookups,
    m->loop_count,
    m->events_processed,
    (double)m->idle_time_us / 1e6
  );

  (void)written;
  return buf;
}
```

---

## Phase 5: Lisp Builtins and Dashboard Integration

### 5.1 Add Lisp Builtin for VM Metrics

**File:** `src/parser.c` (in the builtins section)

```c
// Builtin: (vm/metrics-json) -> Returns VM metrics as JSON string
static valk_lval_t* builtin_vm_metrics_json(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  UNUSED(a);

  valk_vm_metrics_t vm;
  valk_vm_metrics_collect(&vm,
    (valk_gc_malloc_heap_t*)valk_thread_ctx.heap,
    NULL);  // TODO: Get loop from AIO system

  char* json = valk_vm_metrics_to_json(&vm, NULL);
  if (!json) {
    return valk_lval_err("Failed to generate VM metrics JSON");
  }

  valk_lval_t* result = valk_lval_str(json);
  free(json);
  return result;
}

// Builtin: (vm/metrics-prometheus) -> Returns VM metrics in Prometheus format
static valk_lval_t* builtin_vm_metrics_prometheus(valk_lenv_t* e, valk_lval_t* a) {
  (void)e;
  UNUSED(a);

  valk_vm_metrics_t vm;
  valk_vm_metrics_collect(&vm,
    (valk_gc_malloc_heap_t*)valk_thread_ctx.heap,
    NULL);

  char* prom = valk_vm_metrics_to_prometheus(&vm, NULL);
  if (!prom) {
    return valk_lval_err("Failed to generate VM metrics Prometheus");
  }

  valk_lval_t* result = valk_lval_str(prom);
  free(prom);
  return result;
}
```

**In `valk_lenv_builtins()` function, add:**

```c
  valk_lenv_put_builtin(env, "vm/metrics-json", builtin_vm_metrics_json);
  valk_lenv_put_builtin(env, "vm/metrics-prometheus", builtin_vm_metrics_prometheus);
```

### 5.2 Update Debug Module

**File:** `src/modules/aio/debug.valk`

Update the metrics merging function:

```lisp
;; Merge AIO metrics with VM metrics into combined JSON
(defn aio/debug-get-full-metrics [sys]
  (let [aio-json (aio/debug-merge-metrics-json sys)
        vm-json  (vm/metrics-json)]
    (str "{\"aio_metrics\": " aio-json ", \"vm_metrics\": " vm-json "}")))
```

### 5.3 Update Dashboard JavaScript

**File:** `src/modules/aio/debug/script.js`

Add VM metrics rendering (add after existing render functions):

```javascript
// Format microseconds to human-readable
function fmtUs(us) {
  if (!us || us === 0) return '0';
  if (us < 1000) return us + 'µs';
  if (us < 1000000) return (us / 1000).toFixed(1) + 'ms';
  return (us / 1000000).toFixed(2) + 's';
}

// Render VM metrics section
function renderVmMetrics(vm) {
  if (!vm) return '';

  const gc = vm.gc || {};
  const interp = vm.interpreter || {};
  const loop = vm.event_loop || {};

  return `
    <div class="node lvl1">
      <div class="node-hdr">
        <span class="node-name">Garbage Collector</span>
      </div>
      <div class="sub-grid">
        <div class="sub-card">
          <div class="lbl">GC Cycles</div>
          <div class="val">${gc.cycles_total || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Total Pause</div>
          <div class="val">${fmtUs(gc.pause_us_total)}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Max Pause</div>
          <div class="val">${fmtUs(gc.pause_us_max)}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Avg Pause</div>
          <div class="val">${gc.pause_ms_avg ? gc.pause_ms_avg.toFixed(2) + 'ms' : '0'}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Heap Used</div>
          <div class="val">${fmtB(gc.heap_used_bytes)}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Heap Total</div>
          <div class="val">${fmtB(gc.heap_total_bytes)}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Utilization</div>
          <div class="val">${(gc.heap_utilization_pct || 0).toFixed(1)}%</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Reclaimed</div>
          <div class="val">${fmtB(gc.reclaimed_bytes_total)}</div>
        </div>
      </div>
    </div>
    <div class="node lvl1">
      <div class="node-hdr">
        <span class="node-name">Interpreter</span>
      </div>
      <div class="sub-grid">
        <div class="sub-card">
          <div class="lbl">Evaluations</div>
          <div class="val">${interp.evals_total || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Function Calls</div>
          <div class="val">${interp.function_calls || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Builtin Calls</div>
          <div class="val">${interp.builtin_calls || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Max Stack</div>
          <div class="val">${interp.stack_depth_max || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Closures</div>
          <div class="val">${interp.closures_created || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Env Lookups</div>
          <div class="val">${interp.env_lookups || 0}</div>
        </div>
      </div>
    </div>
    <div class="node lvl1">
      <div class="node-hdr">
        <span class="node-name">Event Loop</span>
      </div>
      <div class="sub-grid">
        <div class="sub-card">
          <div class="lbl">Iterations</div>
          <div class="val">${loop.iterations || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Events</div>
          <div class="val">${loop.events_processed || 0}</div>
        </div>
        <div class="sub-card">
          <div class="lbl">Idle Time</div>
          <div class="val">${fmtUs(loop.idle_time_us)}</div>
        </div>
      </div>
    </div>
  `;
}

// In the main render function, add after existing content:
// const vmHtml = data.vm_metrics ? renderVmMetrics(data.vm_metrics) : '';
// Append vmHtml to the dashboard output
```

---

## Build Integration

### CMakeLists.txt Updates

Add new test targets:

```cmake
# GC Metrics Tests
add_executable(test_gc_metrics test/test_gc_metrics.c)
target_link_libraries(test_gc_metrics valk_lib uv pthread)
add_test(NAME test_gc_metrics COMMAND test_gc_metrics)

# Interpreter Metrics Tests
add_executable(test_eval_metrics test/test_eval_metrics.c)
target_link_libraries(test_eval_metrics valk_lib uv pthread)
add_test(NAME test_eval_metrics COMMAND test_eval_metrics)

# Event Loop Metrics Tests
add_executable(test_loop_metrics test/test_loop_metrics.c)
target_link_libraries(test_loop_metrics valk_lib uv pthread)
add_test(NAME test_loop_metrics COMMAND test_loop_metrics)
```

---

## File Change Summary

| File | Action | Estimated Lines |
|------|--------|-----------------|
| `src/gc.h` | Add `valk_gc_runtime_metrics_t`, export API | +25 |
| `src/gc.c` | Init, instrument, export function | +70 |
| `src/parser.h` | Add `valk_eval_metrics_t`, export API | +25 |
| `src/parser.c` | Global, init, instrument eval/call/lambda/lookup, builtins | +100 |
| `src/aio_metrics.h` | Add event loop and VM structs | +50 |
| `src/aio_metrics.c` | Event loop, combined export, JSON, Prometheus | +200 |
| `src/aio_uv.c` | Enable `UV_METRICS_IDLE_TIME` | +5 |
| `src/modules/aio/debug.valk` | Merge VM metrics | +10 |
| `src/modules/aio/debug/script.js` | Render VM metrics | +80 |
| `test/test_gc_metrics.c` | New test file | +100 |
| `test/test_eval_metrics.c` | New test file | +100 |
| `test/test_loop_metrics.c` | New test file | +60 |
| `CMakeLists.txt` | Add test targets | +15 |

**Total: ~840 lines of new/modified code**

---

## Validation Checklist

### Build
- [ ] `make build` succeeds with no warnings
- [ ] `make test` passes all existing tests

### Unit Tests
- [ ] `./build/test_gc_metrics` passes
- [ ] `./build/test_eval_metrics` passes
- [ ] `./build/test_loop_metrics` passes

### Integration Tests
- [ ] Start webserver: `./build/valk examples/webserver_demo.valk`
- [ ] Verify `/debug/metrics` returns VM metrics in JSON
- [ ] Verify `/metrics` includes Prometheus format VM metrics
- [ ] Dashboard at `/debug/` shows GC and Interpreter sections

### Performance
- [ ] Metrics overhead < 1% (benchmark before/after)
- [ ] No lock contention on hot paths (all atomic operations)

---

## Future Enhancements

1. **Histogram for GC pause times** - Track distribution, not just max
2. **Per-function call stats** - Which functions are called most
3. **Memory allocation breakdown** - By type (cons, string, etc.)
4. **Thread pool metrics** - For libuv thread pool operations
5. **Alerting thresholds** - Warn when GC time > 10% or heap > 90%
