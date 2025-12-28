# Disabled, Skipped, and Unused Tests Report

**Generated:** December 2024  
**Updated:** December 27, 2025  
**Status:** Comprehensive analysis with definitive fixes

## Executive Summary

| Category | Count | Severity | Status |
|----------|-------|----------|--------|
| Skipped tests (real bugs) | 5 | 🔴 Critical | Needs code fixes |
| Missing from test suite | 4 | 🟠 High | Needs Makefile updates |
| Flaky timing tests | 25+ | 🟡 Medium | Needs timeout adjustments |
| CI configuration gaps | 3 | 🟡 Medium | Needs workflow updates |
| Print-only tests | 3 | 🟢 Low | Convert or remove |
| Conditional skips | 300+ | ✅ OK | By design |

---

## Part 1: Definitive Fixes

### Fix 1: Add Missing Tests to Makefile

**Problem:** 4 valid test files exist but are never run.

**Files affected:** `Makefile`

**Change:** Add these lines to the `run_tests_c` macro (after line 177):

```makefile
if [ -f $(1)/test_large_str ]; then $(1)/test_large_str; fi
```

**Change:** Add these lines to the `run_tests_valk` macro (after line 224):

```makefile
$(1)/valk test/test_delay_error.valk
$(1)/valk test/test_delay_continuation_error.valk
$(1)/valk test/test_make_string.valk
```

**Verification:**
```bash
make build && build/test_large_str
make build && build/valk test/test_delay_error.valk
make build && build/valk test/test_delay_continuation_error.valk
make build && build/valk test/test_make_string.valk
```

---

### Fix 2: AIO Initialization Race Condition

**Problem:** `tcp_slab` accessed before async initialization completes.

**Tests affected:**
- `test/test_aio_integration.c:151` - `test_minimal_config`
- `test/test_aio_load_shedding.c:575` - `test_buffer_pool_usage`

**Root cause:** `valk_aio_start_with_config()` returns before slab allocators are initialized on the event loop thread.

**File:** `src/aio/aio_uv.c`

**Fix:** Add initialization barrier to `valk_aio_system_t`:

```c
// In struct valk_aio_system_s, add:
_Atomic bool fully_initialized;

// At end of __valk_aio_run_loop initialization (after tcpBufferSlab is set):
atomic_store(&sys->fully_initialized, true);

// In valk_aio_get_tcp_buffer_slab:
valk_slab_t* valk_aio_get_tcp_buffer_slab(valk_aio_system_t* sys) {
  if (!sys) return nullptr;
  while (!atomic_load(&sys->fully_initialized)) {
    usleep(100);
  }
  return sys->tcpBufferSlab;
}
```

**After fix:** Remove `VALK_SKIP` from both tests.

---

### Fix 3: Connection Refused Use-After-Free

**Problem:** Connection structure freed before error callback completes.

**Test:** `test/test_aio_integration.c:414` - `test_connect_to_nonexistent_server`

**File:** `src/aio/aio_http2_client.c`

**Fix:** In `__http2_client_request_connect_cb`, ensure proper reference counting:

```c
static void __http2_client_request_connect_cb(uv_connect_t* req, int status) {
  valk_http2_client_request_t* creq = req->data;
  
  if (status < 0) {
    // Retain before creating error result
    valk_arc_box* error = valk_arc_box_new(VALK_ERR, sizeof(valk_lval));
    // ... create error ...
    
    // Resolve promise BEFORE releasing any references
    valk_promise_resolve(creq->promise, error);
    
    // Now safe to cleanup
    valk_arc_release(error);
    // DO NOT access creq after this point
    return;
  }
  // ... success path ...
}
```

**Verification:**
```bash
make build-asan && ASAN_OPTIONS=detect_leaks=1 build-asan/test_aio_integration
```

**After fix:** Remove `VALK_SKIP` from `test_connect_to_nonexistent_server`.

---

### Fix 4: Shutdown Race Condition

**Problem:** Shutdown proceeds before all connections are closed.

**Test:** `test/test_aio_integration.c:376` - `test_server_shutdown_with_active_clients`

**File:** `src/aio/aio_uv.c`

**Fix:** Add connection counter and wait in shutdown:

```c
// In struct valk_aio_system_s:
_Atomic int32_t active_connection_count;

// When connection opens:
atomic_fetch_add(&sys->active_connection_count, 1);

// When connection closes:
atomic_fetch_sub(&sys->active_connection_count, 1);

// In valk_aio_wait_for_shutdown:
void valk_aio_wait_for_shutdown(valk_aio_system_t* sys) {
  int max_wait_ms = 5000;
  int waited = 0;
  while (atomic_load(&sys->active_connection_count) > 0 && waited < max_wait_ms) {
    usleep(1000);
    waited++;
  }
  // ... existing shutdown code ...
}
```

**After fix:** Remove `VALK_SKIP` from `test_server_shutdown_with_active_clients`.

---

### Fix 5: Backpressure Test Timeout Conflict

**Problem:** Test uses 10s backpressure timeout but coverage has 30s test timeout, causing deadlock.

**Test:** `test/test_aio_load_shedding.c` - `test_backpressure_connections_survive`

**Current status:** Already SKIPPED with message "Flaky timeout under coverage instrumentation"

**Fix:** Reduce backpressure timeout in test:

```c
static void test_backpressure_connections_survive(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Remove VALK_SKIP
  
  valk_aio_config cfg = valk_aio_config_defaults();
  cfg.tcp_buffer_pool_size = 20;
  cfg.max_connections = 16;
  cfg.arena_pool_size = 32;
  cfg.backpressure_timeout_ms = 2000;  // Changed from 10000
  // ... rest of test ...
}
```

---

### Fix 6: Improve CI Configuration

**Problem:** CI only runs coverage build, missing regular tests and ASAN.

**File:** `.github/workflows/coverage.yml`

**Fix:** Add comprehensive test matrix:

```yaml
name: Tests

on:
  pull_request:
    paths:
      - 'src/**'
      - 'test/**'
      - 'CMakeLists.txt'
      - '.github/workflows/*.yml'
  push:
    branches:
      - main

jobs:
  # Fast tests (no ASAN, no coverage)
  test:
    runs-on: macos-latest
    steps:
      - uses: actions/checkout@v4
        with:
          submodules: recursive
      - name: Install Dependencies
        run: |
          brew install llvm cmake ninja pkg-config openssl@3 libuv nghttp2
          echo "/opt/homebrew/opt/llvm/bin" >> $GITHUB_PATH
      - name: Build
        run: make build
      - name: Run Tests
        run: make test

  # ASAN tests (catches memory errors)
  test-asan:
    runs-on: macos-latest
    steps:
      - uses: actions/checkout@v4
        with:
          submodules: recursive
      - name: Install Dependencies
        run: |
          brew install llvm cmake ninja pkg-config openssl@3 libuv nghttp2
          echo "/opt/homebrew/opt/llvm/bin" >> $GITHUB_PATH
      - name: Build with ASAN
        run: make build-asan
      - name: Run ASAN Tests
        run: make test-c-asan && make test-valk-asan

  # Coverage (existing job, unchanged)
  coverage:
    runs-on: macos-latest
    steps:
      - uses: actions/checkout@v4
        with:
          submodules: recursive
      - name: Install Dependencies
        run: |
          brew install llvm cmake ninja pkg-config openssl@3 libuv nghttp2
          echo "/opt/homebrew/opt/llvm/bin" >> $GITHUB_PATH
      - name: Build with Coverage
        run: make build-coverage
      - name: Run Tests
        run: make coverage-tests
      - name: Generate Coverage Report
        run: make coverage-report
      - name: Check Runtime Coverage Requirements
        run: python3 bin/check-coverage.py --build-dir build-coverage
      - name: Upload Coverage Report
        uses: actions/upload-artifact@v4
        if: always()
        with:
          name: coverage-report
          path: coverage-report/
          retention-days: 30
      - name: Upload Coverage to Codecov
        if: github.event_name == 'push' && github.ref == 'refs/heads/main'
        uses: codecov/codecov-action@v4
        with:
          files: ./coverage-report/coverage.xml
          fail_ci_if_error: false
          verbose: true
```

---

### Fix 7: Normalize Test Timeouts

**Problem:** Standalone uses 5s timeout, coverage uses 30s, creating inconsistent behavior.

**Recommendation:** Use 10s for both, with explicit override for known slow tests.

**File:** `Makefile`

**Change:**
```makefile
# Line 249 and 257: Change from 5 to 10
test-c: export VALK_TEST_TIMEOUT_SECONDS=10
test-valk: export VALK_TEST_TIMEOUT_SECONDS=10

# Line 372: Change from 30 to 15 (with slower CI, use env override)
coverage-tests: export VALK_TEST_TIMEOUT_SECONDS=15
```

---

## Part 2: Flaky Tests Analysis

### High-Risk Timing-Dependent Tests

These tests use short sleeps/timeouts that may fail under load:

| Test | Timing Pattern | Risk | Recommendation |
|------|---------------|------|----------------|
| `test_backpressure.valk` | 50ms sleeps | HIGH | Increase to 200ms |
| `test_backpressure_timeout.valk` | 800ms vs 1000ms timeout | HIGH | Use 2000ms timeout |
| `test_pending_streams.valk` | 100ms sleeps | HIGH | Increase to 300ms |
| `test_pending_stream_headers.valk` | 50/200ms schedules | HIGH | Increase to 200/500ms |
| `test_arena_out_of_order.valk` | 10/50/100ms for ordering | MEDIUM | Use 100/200/400ms |
| `test_async_http_handlers.valk` | 5-100ms sleeps throughout | HIGH | Minimum 100ms |

**General fix pattern for Valk timing tests:**

```lisp
; Before (flaky):
(aio/sleep 50)
(aio/schedule 100 callback)

; After (stable):
(aio/sleep 200)
(aio/schedule 300 callback)
```

---

## Part 3: Tests That Should NOT Be in Test Suite

These are correctly excluded - do NOT add them:

| File | Reason |
|------|--------|
| `test_50mb_server.valk` | Runs indefinitely, manual demo |
| `test_50mb_file_server.valk` | Runs indefinitely, needs external file |
| `test_2mb_server.valk` | Runs indefinitely, manual demo |
| `test_overload.valk` | Runs indefinitely, manual testing |
| `test_overload_metrics.valk` | Runs indefinitely, manual testing |
| `test_custom_error_handler.valk` | Runs indefinitely, manual demo |
| `test_large_response.valk` | Needs external file `test/test_large_response_data.txt` |
| `test_large_response_handler.valk` | Memory stress, move to stress/ |
| `test_lisp_50mb_handler.valk` | Memory stress, move to stress/ |

---

## Part 4: Print-Only Tests to Convert

These tests exist but have no assertions:

| File | Current State | Fix |
|------|--------------|-----|
| `test_aio_builtins.valk` | Only prints | Add assertions or remove |
| `test_metrics_builtins.valk` | Claims "passed" without testing | Add assertions or remove |
| `test_metrics_prometheus.valk` | Prints format, no validation | Add format assertions |

**Example conversion:**

```lisp
; Before (print-only):
(print (metrics/format-prometheus))
(print "PASS")

; After (with assertions):
(test/define "prometheus-format-valid"
  (let ((output (metrics/format-prometheus)))
    (test/assert (string? output) "Should return string")
    (test/assert (str/contains? output "# HELP") "Should have HELP comments")
    (test/assert (str/contains? output "# TYPE") "Should have TYPE comments")))
```

---

## Part 5: Conditional Skips (Correct Behavior)

These tests are intentionally skipped when feature flags are disabled:

### When `VALK_METRICS_ENABLED` not defined (~300 tests)
- All `test_*_metrics*.c` files
- All `test_sse*.c` files  
- `test_aio_backpressure.c`, `test_aio_integration.c`, etc.

### When `VALK_COVERAGE` not defined (~30 tests)
- `test_source_loc.c`
- `test/unit/test_source_loc.c`

**This is correct.** CI runs with `VALK_METRICS=1` by default.

---

## Part 6: Implementation Checklist

### Immediate (< 1 hour)

- [ ] Add `test_large_str` to Makefile run_tests_c
- [ ] Add 3 missing .valk tests to Makefile run_tests_valk
- [ ] Run `make test` to verify

### Short-term (< 1 day)

- [ ] Fix AIO initialization race (add `fully_initialized` atomic)
- [ ] Remove VALK_SKIP from `test_minimal_config` and `test_buffer_pool_usage`
- [ ] Fix backpressure test timeout (reduce to 2000ms)
- [ ] Remove VALK_SKIP from `test_backpressure_connections_survive`
- [ ] Run `make test-c-asan` to verify no ASAN errors

### Medium-term (< 1 week)

- [ ] Fix connection refused UAF
- [ ] Fix shutdown race condition
- [ ] Update CI workflow with test + test-asan jobs
- [ ] Increase timing values in flaky .valk tests
- [ ] Convert print-only tests to have assertions

### Verification Commands

```bash
# After all fixes, this should pass:
make test              # Regular tests
make test-c-asan       # ASAN C tests
make test-valk-asan    # ASAN Valk tests
make coverage          # Coverage tests

# Check for remaining skips:
grep -r "VALK_SKIP" test/ --include="*.c" | grep -v "VALK_METRICS\|VALK_COVERAGE\|heap2"

# Should show 0 skipped tests (except feature-flag ones):
make test 2>&1 | grep -c "SKIP"
```

---

## Appendix: All Skipped Tests with Reasons

### Real Bugs (Need Code Fixes)

| Location | Skip Reason | Fix Location |
|----------|-------------|--------------|
| `test_aio_integration.c:151` | "minimal config has race condition in initialization" | `src/aio/aio_uv.c` |
| `test_aio_integration.c:376` | "shutdown race condition when client not disconnected" | `src/aio/aio_uv.c` |
| `test_aio_integration.c:414` | "connection refused error handling has use-after-free" | `src/aio/aio_http2_client.c` |
| `test_aio_load_shedding.c:575` | "race condition accessing tcp_slab before fully initialized" | `src/aio/aio_uv.c` |
| `test_aio_load_shedding.c:962` | "Flaky timeout under coverage instrumentation" | Test config |

### Feature-Flag Skips (Correct Behavior)

| Pattern | Reason | When Active |
|---------|--------|-------------|
| "VALK_METRICS_ENABLED not defined" | Metrics tests need metrics build | `VALK_METRICS=1` |
| "VALK_COVERAGE not defined" | Coverage tests need coverage build | `-DVALK_COVERAGE=1` |

### Architecture Skips (Correct Behavior)

| Location | Skip Reason | Notes |
|----------|-------------|-------|
| `test/unit/test_gc.c` (4 tests) | "heap2 uses page-based allocation" | Old heap1 tests, heap2 is current |
| `test_memory.c` | "heap2 TLABs are thread-local static" | Test isolation issue |

---

## Quick Reference: Files to Modify

| Fix | Files |
|-----|-------|
| Add missing tests | `Makefile` |
| Init race | `src/aio/aio_uv.c`, `src/aio/aio_uv.h` |
| Connection UAF | `src/aio/aio_http2_client.c` |
| Shutdown race | `src/aio/aio_uv.c` |
| Backpressure timeout | `test/test_aio_load_shedding.c` |
| CI config | `.github/workflows/coverage.yml` |
| Test timeouts | `Makefile` |
| Flaky valk tests | `test/test_backpressure*.valk`, `test/test_pending*.valk`, etc. |
