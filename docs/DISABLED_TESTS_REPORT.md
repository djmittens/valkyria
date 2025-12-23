# Disabled, Skipped, and Unused Tests Report

**Generated:** December 2024  
**Status:** Analysis of hidden problems in the test suite

## Executive Summary

This analysis identified **significant hidden problems** masked by disabled, skipped, or unused tests:

| Category | Count | Severity | Impact |
|----------|-------|----------|--------|
| Crashing tests | 1 | 🔴 Critical | CI is broken |
| Phantom test references | 1 | 🔴 Critical | Build may fail |
| Orphan test files | 1 | 🔴 Critical | Regression risk |
| Race condition bugs | 4 | 🟠 High | Production bugs |
| Use-after-free bugs | 2 | 🟠 High | Memory safety |
| Missing test coverage | 6+ | 🟡 Medium | Coverage gaps |
| Conditional skips | 300+ | 🟢 Low | By design |

---

## Table of Contents

1. [Critical Issues (P0)](#p0-critical-issues)
2. [High Priority Issues (P1)](#p1-high-priority-race-conditions--use-after-free)
3. [Medium Priority Issues (P2)](#p2-medium-priority-missing-test-coverage)
4. [Low Priority Issues (P3)](#p3-low-priority-conditional-skips)
5. [Code Quality Issues (P4)](#p4-code-quality-issues)

---

## P0: Critical Issues

### Issue 1: Crashing Test - `test_backpressure_connections_survive`

**File:** `test/test_aio_load_shedding.c:962`  
**Status:** 🌀 CRSH - Times out after 30 seconds  
**Impact:** `make test` fails with exit code 1

#### Problem Description

The test creates 12 HTTP/2 clients with constrained resources and sends batched requests. It hangs indefinitely and is killed after 30 seconds. The warning message suggests a memory management issue:

```
[WARN] test_aio_load_shedding.c:821:create_request | Reinitializing array (items not cleaned up?)
```

#### Root Cause Analysis

The test uses these constrained settings:
```c
cfg.tcp_buffer_pool_size = 20;
cfg.max_connections = 16;
cfg.arena_pool_size = 32;
cfg.backpressure_timeout_ms = 10000;
```

With 12 concurrent clients and batched requests, the system likely enters a deadlock state where:
1. TCP buffer pool is exhausted
2. Backpressure is applied
3. Clients wait for buffers that will never be freed
4. The 10-second backpressure timeout is longer than the 30-second test timeout

#### Solution

**Option A (Immediate - Unblock CI):**
```c
static void test_backpressure_connections_survive(VALK_TEST_ARGS()) {
  VALK_TEST();
  VALK_SKIP("Backpressure timeout conflict with test timeout - TODO fix resource constraints");
  return;
  // ... existing code
}
```

**Option B (Proper Fix):**
1. Reduce `backpressure_timeout_ms` to 2000ms (2 seconds)
2. Reduce test timeout or increase it to 60 seconds
3. Add proper cleanup on timeout
4. Investigate the deadlock in `valk_aio_wait_for_shutdown`

#### Path Forward

```bash
# Step 1: Skip the test to unblock CI immediately
# Edit test/test_aio_load_shedding.c:962

# Step 2: Create issue to properly fix the backpressure handling
# The real bug is likely in src/aio_uv.c backpressure logic
```

---

### Issue 2: Phantom Test Reference - `test_tco_suite.valk`

**File:** `Makefile:194`  
**Status:** File does not exist  
**Impact:** `make test-valk` will fail when it reaches this line

#### Problem Description

The Makefile contains:
```makefile
$(1)/valk test/test_tco_suite.valk
```

But the file `test/test_tco_suite.valk` does not exist. It's documented extensively in archived docs, suggesting it was accidentally deleted.

#### Solution

**Option A (Remove reference):**
```makefile
# In Makefile, delete line 194:
# $(1)/valk test/test_tco_suite.valk
```

**Option B (Restore the file):**

Based on the archived documentation, `test_tco_suite.valk` should test tail-call optimization. Create a new file:

```lisp
; test/test_tco_suite.valk
; Tail Call Optimization Tests

(load "src/prelude.valk")

(defun test-simple-tco ()
  "Test simple tail recursion"
  (defun count-down (n)
    (if (<= n 0)
        0
        (count-down (- n 1))))
  (assert (= (count-down 10000) 0) "Should handle deep recursion via TCO"))

(defun test-mutual-tco ()
  "Test mutual tail recursion"
  (defun even? (n)
    (if (= n 0) true (odd? (- n 1))))
  (defun odd? (n)
    (if (= n 0) false (even? (- n 1))))
  (assert (even? 1000) "Should handle mutual recursion via TCO"))

(defun test-accumulator-tco ()
  "Test tail recursion with accumulator"
  (defun factorial-acc (n acc)
    (if (<= n 1)
        acc
        (factorial-acc (- n 1) (* n acc))))
  (defun factorial (n) (factorial-acc n 1))
  (assert (= (factorial 10) 3628800) "Factorial should use TCO"))

(defun run-tests ()
  (test-simple-tco)
  (test-mutual-tco)
  (test-accumulator-tco)
  (print "All TCO tests passed!"))

(run-tests)
```

#### Path Forward

```bash
# Immediate: Remove the reference
sed -i '' '/test_tco_suite.valk/d' Makefile

# Or restore the file if TCO tests are needed
# Create test/test_tco_suite.valk with the content above
```

---

### Issue 3: Orphan Test File - `test_large_str.c`

**File:** `test/test_large_str.c` (94 lines)  
**Status:** Never compiled or executed  
**Impact:** 2MB string concatenation regression risk

#### Problem Description

This complete test file validates large string concatenation (up to 2MB). It was written to test a specific fix for a 64KB limit bug. The test is **not in CMakeLists.txt** and therefore never runs.

The test covers:
- 1KB → 4KB → 64KB → 256KB → 1MB → 2MB string concatenation
- Line 50 comment: "this would have crashed with old 64KB limit!"

#### Solution

**Add to CMakeLists.txt** (after line 214):

```cmake
add_executable(test_large_str test/test_large_str.c test/testing.c)
target_link_libraries(test_large_str PRIVATE "-lc" valkyria)
include_directories(test_large_str src/)
```

**Add to Makefile** (in `run_tests_c`, around line 140):

```makefile
$(1)/test_large_str
```

#### Path Forward

```bash
# Add to CMakeLists.txt after line 214
cat >> CMakeLists.txt << 'EOF'
add_executable(test_large_str test/test_large_str.c test/testing.c)
target_link_libraries(test_large_str PRIVATE "-lc" valkyria)
include_directories(test_large_str src/)
EOF

# Add to Makefile run_tests_c section
# Then verify:
make build && build/test_large_str
```

---

## P1: High Priority - Race Conditions & Use-After-Free

These tests have complete implementations but are skipped due to known concurrency bugs. **These represent real bugs in production code that need fixing.**

### Issue 4: `valk_pool_resolve_promise` Race Condition

**Tests Affected:**
- `test/unit/test_concurrency.c:897` - `test_pool_resolve_promise`
- `test/unit/test_concurrency.c:902` - `test_pool_resolve_promise_with_error`

**Skip Message:** "valk_pool_resolve_promise has a known race condition - internal future released before resolution"

#### Root Cause Analysis

Looking at `src/concurrency.c:447-457`:

```c
void valk_pool_resolve_promise(valk_worker_pool *pool, valk_promise *promise,
                               valk_arc_box *result) {
  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(__valk_resolve_promise));
  __valk_resolve_promise *pair = arg->item;
  pair->promise = promise;
  pair->result = result;

  valk_future *res = valk_schedule(pool, arg, __valk_pool_resolve_promise_cb);
  valk_arc_release(res);  // <-- BUG: releasing before callback completes
}
```

**The Problem:** The future `res` is released immediately after scheduling. If the scheduled work hasn't started yet and this release drops the refcount to zero, the future will be freed. When the worker thread later tries to complete the future, it accesses freed memory.

#### Solution

**Option A (Retain until callback completes):**

```c
void valk_pool_resolve_promise(valk_worker_pool *pool, valk_promise *promise,
                               valk_arc_box *result) {
  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(__valk_resolve_promise));
  __valk_resolve_promise *pair = arg->item;
  pair->promise = promise;
  pair->result = result;
  valk_arc_retain(result);  // Retain result since callback will release it

  valk_future *res = valk_schedule(pool, arg, __valk_pool_resolve_promise_cb);
  // Don't release here - the future will be released by the worker when done
  // Or: await the future to ensure completion
  valk_arc_box *completion = valk_future_await(res);
  valk_arc_release(completion);
  valk_arc_release(res);
}
```

**Option B (Fire-and-forget pattern with proper lifecycle):**

If we truly don't care about the result, the callback itself should handle cleanup:

```c
typedef struct {
  valk_promise *promise;
  valk_arc_box *result;
  valk_future *self_future;  // Reference to own future for cleanup
} __valk_resolve_promise;

static valk_arc_box *__valk_pool_resolve_promise_cb(valk_arc_box *arg) {
  __valk_resolve_promise *a = arg->item;
  valk_promise_respond(a->promise, a->result);
  valk_arc_release(a->result);
  valk_arc_release(a->self_future);  // Release the future reference
  return arg;
}

void valk_pool_resolve_promise(valk_worker_pool *pool, valk_promise *promise,
                               valk_arc_box *result) {
  valk_arc_box *arg = valk_arc_box_new(VALK_SUC, sizeof(__valk_resolve_promise));
  __valk_resolve_promise *pair = arg->item;
  pair->promise = promise;
  pair->result = result;
  valk_arc_retain(result);

  valk_future *res = valk_schedule(pool, arg, __valk_pool_resolve_promise_cb);
  pair->self_future = res;  // Store for later cleanup
  // Don't release here - callback will do it
}
```

#### Path Forward

```bash
# 1. Write a minimal reproducer
# 2. Fix src/concurrency.c with Option A or B
# 3. Re-enable the tests
# 4. Run with ASAN to verify no UAF
make test-c-asan
```

---

### Issue 5: Connection Refused Use-After-Free

**Test:** `test/test_aio_integration.c:414` - `test_connect_to_nonexistent_server`  
**Skip Message:** "connection refused error handling has use-after-free - TODO fix"

#### Root Cause Analysis

The test connects to a port with no server:

```c
valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
valk_arc_box *clientBox = valk_future_await(fclient);
ASSERT_EQ(clientBox->type, VALK_ERR);  // Expected to fail
```

When the connection fails, the error handling path likely frees the connection structure, but something else still holds a reference to it.

#### Solution

The fix is in `src/aio_uv.c` connection error handling. Look for the `on_connect` callback and ensure proper reference counting:

```c
// In the connection error path, ensure we:
// 1. Don't free the connection until all references are released
// 2. Properly resolve the future with an error before cleanup
// 3. Don't access the connection after calling valk_arc_release
```

#### Path Forward

```bash
# 1. Run with ASAN to get the exact UAF location
ASAN_OPTIONS=detect_leaks=1 build-asan/test_aio_integration 2>&1 | grep -A 20 "use-after-free"

# 2. Fix the identified location in src/aio_uv.c
# 3. Re-enable the test
# 4. Verify with ASAN
```

---

### Issue 6: AIO Initialization Race Conditions

**Tests Affected:**
- `test/test_aio_integration.c:151` - `test_minimal_config`
- `test/test_aio_load_shedding.c:575` - `test_buffer_pool_usage`

**Skip Messages:**
- "minimal config has race condition in initialization"
- "race condition accessing tcp_slab before fully initialized"

#### Root Cause Analysis

Both tests access `tcp_slab` immediately after `valk_aio_start_with_config()`. The slab is initialized on a background thread and may not be ready when accessed.

Looking at `src/aio_uv.c:4326`:
```c
valk_slab_t* valk_aio_get_tcp_buffer_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  return sys->tcpBufferSlab;  // May be NULL if init not complete
}
```

The initialization at line 1051:
```c
sys->tcpBufferSlab = tcp_buffer_slab;  // Store for metrics access
```

This store happens during async initialization, but tests access it synchronously.

#### Solution

**Option A (Add initialization barrier):**

```c
// In src/aio_uv.c, add a ready flag
typedef struct valk_aio_system_s {
  // ...existing fields...
  atomic_bool initialized;  // Add this
} valk_aio_system_t;

// Set at end of initialization
__atomic_store_n(&sys->initialized, true, __ATOMIC_RELEASE);

// Getter waits for init
valk_slab_t* valk_aio_get_tcp_buffer_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  while (!__atomic_load_n(&sys->initialized, __ATOMIC_ACQUIRE)) {
    usleep(1000);  // Wait for init
  }
  return sys->tcpBufferSlab;
}
```

**Option B (Synchronous initialization for critical slabs):**

Initialize the slab allocators synchronously before returning from `valk_aio_start_with_config()`.

#### Path Forward

```bash
# 1. Add atomic initialized flag to valk_aio_system_t
# 2. Set flag at end of initialization
# 3. Check flag in all getters
# 4. Re-enable tests
```

---

### Issue 7: Shutdown Race Condition

**Test:** `test/test_aio_integration.c:376` - `test_server_shutdown_with_active_clients`  
**Skip Message:** "shutdown race condition when client not disconnected - TODO fix"

#### Root Cause Analysis

The test:
1. Creates a server
2. Connects a client
3. Releases client/server references
4. Calls `valk_aio_stop()` and `valk_aio_wait_for_shutdown()`

The race: The client connection may not be fully closed when shutdown is initiated, causing cleanup to access freed resources.

#### Solution

Ensure `valk_aio_wait_for_shutdown()` properly waits for all connections to close:

```c
void valk_aio_wait_for_shutdown(valk_aio_system_t* sys) {
  // Wait for all active connections to close
  while (__atomic_load_n(&sys->active_connections, __ATOMIC_ACQUIRE) > 0) {
    usleep(1000);
  }
  
  // Then proceed with shutdown
  // ...existing shutdown code...
}
```

---

## P2: Medium Priority - Missing Test Coverage

### Issue 8: .valk Tests Not in Test Suite

These files exist but are not executed by `make test-valk`:

| File | Purpose | Recommendation |
|------|---------|----------------|
| `test_delay_continuation_error.valk` | Async error handling | **Add to Makefile** |
| `test_delay_error.valk` | Delay error path | **Add to Makefile** |
| `test_make_string.valk` | make-string builtin | **Add to Makefile** |
| `test_metrics_prometheus.valk` | Prometheus format | Add (conditional on VALK_METRICS) |
| `test_coverage_integration.valk` | Coverage tests | Add (conditional on VALK_COVERAGE) |
| `test_large_response.valk` | Large responses | Add to stress tests |

#### Solution

Add to `Makefile` in `run_tests_valk` section:

```makefile
$(1)/valk test/test_delay_error.valk
$(1)/valk test/test_delay_continuation_error.valk
$(1)/valk test/test_make_string.valk
if [ "$(VALK_METRICS)" = "1" ]; then $(1)/valk test/test_metrics_prometheus.valk; fi
```

---

### Issue 9: C Tests Built But Not Run

| Test | Status |
|------|--------|
| `test_demo_server` | Built, never run |
| `test_gc_metrics` | Built, never run |
| `test_source_loc` | Built with VALK_COVERAGE, never run |

#### Solution

Either add to `run_tests_c` or remove from CMakeLists.txt if they're not meant to be automated tests.

---

## P3: Low Priority - Conditional Skips

These tests are intentionally skipped when feature flags are disabled. This is **correct behavior**.

### When `VALK_METRICS_ENABLED` is not defined (~300 tests)

| Test File | Approx Tests |
|-----------|--------------|
| `test_aio_metrics.c` | 25 |
| `test_metrics_v2.c` | 45 |
| `test_loop_metrics.c` | 24 |
| `test_sse_diagnostics.c` | 50 |
| `test/unit/test_sse_core.c` | 70 |
| `test/unit/test_pool_metrics.c` | 26 |
| `test/unit/test_event_loop_metrics.c` | 24 |
| `test/unit/test_metrics_builtins.c` | 58 |
| `test/unit/test_metrics_delta.c` | 45 |
| `test/unit/test_sse_builtins.c` | 35 |

### When `VALK_COVERAGE` is not defined (~30 tests)

| Test File | Approx Tests |
|-----------|--------------|
| `test_source_loc.c` | 7 |
| `test/unit/test_source_loc.c` | 26 |

#### Recommendation

Ensure CI runs with both flags enabled:

```yaml
# In .github/workflows/test.yml
jobs:
  test:
    strategy:
      matrix:
        config:
          - { metrics: 1, coverage: 1 }  # Full test suite
          - { metrics: 0, coverage: 0 }  # Minimal build
```

---

## P4: Code Quality Issues

### Issue 10: Tests With Only Print Statements

| File | Issue |
|------|-------|
| `test_aio_builtins.valk` | Only prints, no assertions |
| `test_metrics_builtins.valk` | Claims "passed" without testing |

**Recommendation:** Add actual assertions or mark as demos.

### Issue 11: Tests Using Exit Codes Instead of Framework

| File | Issue |
|------|-------|
| `test_backpressure.valk` | Uses `exit 0/1` |
| `test_pending_streams.valk` | Uses `exit 0/1` |
| `test_concurrent_requests.valk` | Always passes |

**Recommendation:** Convert to use the test framework macros.

### Issue 12: TODO Comments in Test Code

| Location | Issue |
|----------|-------|
| `test_networking.c:108` | Closing connections issue |
| `test_networking.c:122` | Needs refactoring |
| `test_memory.c:147` | Untrusted code |
| `test_http_integration.valk:135` | JSON parsing TODO |

---

## Implementation Checklist

### Immediate (This Week)

- [ ] Skip `test_backpressure_connections_survive` to unblock CI
- [ ] Remove or restore `test_tco_suite.valk` reference
- [ ] Add `test_large_str.c` to build system
- [ ] Verify CI passes

### Short Term (This Sprint)

- [ ] Fix `valk_pool_resolve_promise` race condition
- [ ] Fix connection-refused UAF bug
- [ ] Add missing .valk tests to Makefile
- [ ] Run full test suite with ASAN

### Medium Term (Next Sprint)

- [ ] Fix AIO initialization race conditions
- [ ] Fix shutdown race condition
- [ ] Convert exit-code tests to framework
- [ ] Add assertions to print-only tests

### Long Term (Backlog)

- [ ] Ensure CI runs with all feature flags
- [ ] Audit all TODO comments in tests
- [ ] Document test conventions

---

## Appendix: Quick Reference

### Commands to Run

```bash
# Run full test suite
make test

# Run with ASAN
make test-c-asan

# Run specific test
build/test_aio_integration

# Check for missing files
for f in $(grep -oP 'test/test_\w+\.valk' Makefile); do
  [ -f "$f" ] || echo "MISSING: $f"
done
```

### Files to Modify

| Issue | File(s) to Modify |
|-------|-------------------|
| Crashing test | `test/test_aio_load_shedding.c` |
| Phantom reference | `Makefile` |
| Orphan test | `CMakeLists.txt`, `Makefile` |
| Promise race | `src/concurrency.c` |
| Connection UAF | `src/aio_uv.c` |
| Init race | `src/aio_uv.c` |
| Shutdown race | `src/aio_uv.c` |
