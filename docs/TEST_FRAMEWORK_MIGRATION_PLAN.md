# Test Framework Migration Plan

This document outlines why some Valkyria Lisp integration tests don't use the standard test framework, what's missing from the framework, and how to migrate non-conforming tests.

## Table of Contents
1. [Current Test Framework Features](#current-test-framework-features)
2. [Why Tests Don't Use the Framework](#why-tests-dont-use-the-framework)
3. [Non-Conforming Test Categories](#non-conforming-test-categories)
4. [Test Stability Issues](#test-stability-issues)
5. [Debugging Tests](#debugging-tests)
6. [Missing Framework Features](#missing-framework-features)
7. [Migration Guide](#migration-guide)
8. [Implementation Plan](#implementation-plan)

---

## Current Test Framework Features

**Location:** `src/modules/test.valk`

| Feature | Function | Description |
|---------|----------|-------------|
| Suite naming | `test/suite name` | Sets suite name for output |
| Test definition | `test/define name body` | Registers test with name and body |
| Boolean assert | `test/assert cond msg` | Returns `true` if passes, `error` otherwise |
| Equality assert | `test/assert-eq expected actual msg` | Compares two values |
| Skip suite | `test/skip reason` | Skips all tests with reason |
| Expected exit | `test/expect-exit code` | For testing error paths |
| Debug mode | `test/debug enabled` | Verbose output |
| Run tests | `test/run` | Executes all tests, prints summary, exits |

### Output Format

```
🧪 [N/N] Suite Name
✅ test-name.............................................  PASS : in 123(µs)
❌ test-name.............................................  FAIL : in 456(µs)

🏁 Test Results: ✨ All N tests passed! ✨
```

---

## Why Tests Don't Use the Framework

### Root Cause: No Async Test Support

The test framework is **synchronous-only**. It evaluates `test/define` bodies immediately and expects a boolean return:

```lisp
; Framework runs test like this:
(= {result} (eval test-body))
(= {passed} (if (== result true) {1} {0}))
```

**Problem:** Integration tests need to:
1. Start an HTTP/2 server
2. Wait for server to be ready
3. Make async HTTP requests
4. Wait for responses in callbacks
5. Assert on response data
6. Chain multiple async operations
7. Clean up server

The framework can't handle callbacks or delayed assertions.

---

## Non-Conforming Test Categories

### Category A: Print-Only Tests (No Assertions)

**Files:**
- `test/test_aio_builtins.valk` (12 lines)
- `test/test_metrics_builtins.valk` (38 lines)
- `test/test_metrics_prometheus.valk` (14 lines)
- `test/test_overload.valk` (20 lines)

**Pattern:**
```lisp
(load "src/prelude.valk")
(println "Test 1: metrics/json returns string")
(println (metrics/json))
(println "All tests passed!")  ; Claims success without verification!
```

**Issues:**
- No test framework loaded
- Uses `print`/`println` instead of assertions
- Always exits 0 regardless of actual behavior
- No structured pass/fail tracking
- **Silent failures**: `test_metrics_builtins.valk` uses an outdated API (`metrics/counter-inc "name"`) that returns errors, but prints "All tests passed!" anyway

---

### Category B: Custom Test Harness (Async Tests)

**Files:**
- `test/test_async_http_handlers.valk` (849 lines, 52 tests)
- `test/test_http_api_network.valk`
- `test/test_http_client_server.valk`
- `test/test_http2_client_request_errors.valk`
- `test/test_sse_integration.valk`
- `test/test_large_download.valk` (129 lines)
- `test/test_pending_streams.valk`
- `test/test_backpressure.valk`

**Pattern:**
```lisp
; Custom state tracking
(def {tests-passed} 0)
(def {tests-failed} 0)
(def {tests-run} 0)

; Custom assertion helper
(fun {check-response name resp expected-status expected-body} {
  (def {tests-run} (+ tests-run 1))
  (if (error? resp)
    {(do
       (def {tests-failed} (+ tests-failed 1))
       (printf "  ❌ %s: FAIL (error: %s)\n" name (str resp)))}
    {(do
       (= {status} (http2/response-status resp))
       (= {body} (http2/response-body resp))
       (if (and (== status expected-status) (== body expected-body))
         {(do
            (def {tests-passed} (+ tests-passed 1))
            (printf "  ✅ %s: PASS\n" name))}
         {(do
            (def {tests-failed} (+ tests-failed 1))
            (printf "  ❌ %s: FAIL (got status=%s body=%s)\n" name status body))}))})
})

; Test execution via callback chaining
(aio/schedule aio 200 (\ {} {
  (test-request "/endpoint" "test name" "expected-body" (\ {} {
    (test-request "/next" "another test" "body" (\ {} {
      (finish-tests)
    }))
  }))
}))

(aio/run aio)
(exit (if (== tests-failed 0) {0} {1}))
```

**Issues:**
- Duplicated test tracking code across files
- Custom output format (different from standard)
- Manual pass/fail counting
- Deeply nested callback chains (50+ levels in test_async_http_handlers.valk)
- No integration with framework metrics

---

### Category C: Improper Framework Usage

**Files:**
- `test/test_http_integration.valk` (411 lines)

**Pattern:**
```lisp
(load "src/modules/test.valk")
(test/suite "HTTP Integration Tests")

; Uses framework BUT with bare boolean returns (no error message on failure)
(test/define "http2/response-ok? returns true for 200"
  {do
    (def {resp} (http2/mock-response "200" "OK"))
    (== 1 (http2/response-ok? resp))  ; Just returns boolean, no message!
  })
```

**Issues:**
- Tests pass/fail correctly BUT no diagnostic on failure
- Framework shows `FAIL` but not what actual vs expected were
- Easy to fix - just add `test/assert-eq` with message

---

## Test Stability Issues

### Timing-Dependent Tests (Flaky)

Many async tests use short sleep/delay values that can fail under system load:

| Pattern | Files | Issue |
|---------|-------|-------|
| `aio/sleep 5` | test_async_http_handlers.valk | 5ms sleep may not complete before assertion |
| `aio/sleep 50-100` | test_pending_streams.valk, test_backpressure.valk | Marginal delays on slow CI |
| `aio/schedule aio 200` | Most integration tests | 200ms server startup may be insufficient |

**Recommendations:**
1. Increase minimum sleep values from 5ms to 50ms for reliability
2. Increase server startup delay from 200ms to 500ms
3. Use exponential backoff for retry tests
4. Add `test/retry count` for known flaky tests

### Timeout Values

Current timeouts in integration tests:

| Test File | Timeout | Risk |
|-----------|---------|------|
| test_async_http_handlers.valk | 30s | OK for 52 tests |
| test_large_download.valk | 15s | OK for 3 tests |
| test_backpressure.valk | 10s | Too short for load tests |
| test_sse_integration.valk | 10s | Borderline |

**Recommendations:**
1. Minimum 30s timeout for integration tests
2. Minimum 60s for load/stress tests  
3. Add configurable timeout via environment variable `VALK_TEST_TIMEOUT`

### Race Conditions

Some tests have inherent race conditions:

1. **Port allocation**: ~~`net/get-available-port` may return a port that's taken by the time server starts~~ **RESOLVED** - Use port 0 + `http2/server-port` pattern
2. **Server startup**: Tests may send requests before server is fully listening
3. **Callback ordering**: Async callbacks may fire in unexpected order under load

**Mitigations:**
- ~~Add retry logic for port binding failures~~ **RESOLVED** - Port 0 binding is atomic
- Use explicit "server ready" signaling instead of fixed delays
- Add sequence numbers to verify callback order in tests

**New Port Allocation Pattern (Recommended):**
```lisp
; OLD (removed - had TOCTOU race condition):
; (def {TEST_PORT} (net/get-available-port))
; (http2/server-listen aio TEST_PORT handler)

; NEW (atomic - no race condition):
(def {server} (http2/server-listen aio 0 handler))
(def {TEST_PORT} (http2/server-port server))
```

---

## Debugging Tests

### Existing Debug Features

#### Valk Test Framework Debug Mode

```lisp
(load "src/modules/test.valk")
(test/debug 1)  ; Enable before test/run

; Output includes:
; [DEBUG] Running test: ...
; [DEBUG] Test name: test-name
; [DEBUG] Test body: {do ...}
; [DEBUG] Result: true
; [DEBUG] Result is an ERROR!  (if applicable)
```

#### C Test Framework

The C framework (`test/testing.h`) provides:
- File:line locations on failure (`VALK_FAIL` macro)
- Captured stdout/stderr per test (`valk_ring_t *_stdout/_stderr`)
- Detailed assertion messages (e.g., `ASSERT_EQ: expected 5 == 10`)

### New Debug Features to Add

#### 1. Environment Variable Debug Mode

```bash
# Run with verbose output without modifying test file
VALK_TEST_DEBUG=1 build/valk test/test_prelude.valk

# Run single test by name
VALK_TEST_FILTER="test-name-pattern" build/valk test/test_prelude.valk
```

**Implementation in test.valk:**
```lisp
; Check environment at load time
(if (env/get "VALK_TEST_DEBUG")
  {(test/debug 1)}
  {nil})
```

#### 2. Verbose Failure Output

Current failure output:
```
❌ test-name.............  FAIL : in 123(µs)
```

Improved failure output:
```
❌ test-name.............  FAIL : in 123(µs)
   Assertion failed: expected 5, got 10
   Message: "counter should be incremented"
   At: test/test_metrics.valk:42
```

**Implementation:**
```lisp
(fun {test/assert-eq expected actual msg} {
  (if (== expected actual)
    {true}
    {do
      (if (== *test-debug* 1)
        {do
          (printf "   Expected: %s\n" (str expected))
          (printf "   Actual:   %s\n" (str actual))
          (printf "   Message:  %s\n" msg)}
        {nil})
      (error msg)})
})
```

#### 3. Async Test Debug Tracing

For async/integration tests, add trace points:

```lisp
(fun {test/trace msg} {
  (if (== *test-debug* 1)
    {(printf "[TRACE %ld] %s\n" (time-us {}) msg)}
    {nil})
})

; Usage in async test:
(http2/client-request aio host port path (\ {resp} {
  (test/trace "Received response")
  (test/trace (str "Status: " (http2/response-status resp)))
  ; ... assertions
}))
```

#### 4. Test Isolation Diagnostics

Add memory/state tracking between tests:

```lisp
(fun {*test-check-leaks*} {
  (if (== *test-debug* 1)
    {do
      (= {mem} (gc/stats))
      (printf "[DEBUG] Memory after test: alloc=%ld, freed=%ld\n"
        (plist/get mem :allocated)
        (plist/get mem :freed))}
    {nil})
})
```

#### 5. Integration with AIO Debug Dashboard

For async tests, can leverage the existing debug dashboard:

```lisp
; Start debug handler alongside test server
(load "src/modules/aio/debug.valk")

(def {test-handler} (\ {req} {
  ; Try debug routes first
  (= {debug-resp} (aio/debug-handle-request aio req))
  (if (!= debug-resp nil)
    {debug-resp}
    {(test-router req)})
}))

; Access http://localhost:PORT/debug/ during test run
```

### Debug Checklist for Test Failures

1. **Enable debug mode:**
   ```lisp
   (test/debug 1)
   ```

2. **Check for timing issues:**
   - Increase sleep/delay values
   - Add trace points around async operations

3. **Check for port conflicts:**
   ```bash
   lsof -i :PORT  # See what's using the port
   ```

4. **Run with ASAN:**
   ```bash
   make test-valk-asan  # Catch memory issues
   ```

5. **Run single test in isolation:**
   ```bash
   build/valk test/specific_test.valk
   ```

6. **Check for GC-related issues:**
   ```lisp
   (gc/collect)  ; Force collection before assertions
   ```

---

## Missing Framework Features

### Critical for Async Migration

| Feature | Priority | Description | Status |
|---------|----------|-------------|--------|
| **Async test support** | P0 | `test/async name body-fn` - body receives done callback | ✅ Implemented |
| **Async test runner** | P0 | `test/run-async aio` - runs on event loop | ✅ Implemented |
| **Async timeout** | P0 | `test/async-timeout ms` - configurable timeout | ✅ Implemented |
| **HTTP response helper** | P1 | `test/check-response` for common pattern | ✅ Implemented |
| **Setup/teardown** | P1 | `test/before-all`, `test/after-all` for server start/stop | Pending |
| **Test context** | P1 | Pass shared state (aio system, port) to tests | Pending |

### Nice to Have

| Feature | Priority | Description | Status |
|---------|----------|-------------|--------|
| `test/assert-neq` | P2 | Assert not equal | Pending |
| `test/assert-error` | P2 | Assert expression returns error | Pending |
| `test/assert-contains` | P2 | Assert substring/element containment | Pending |
| `test/async-assert` | P2 | Assert with done callback | ✅ Implemented |
| `test/async-assert-eq` | P2 | Assert equality with done callback | ✅ Implemented |
| `test/before-each` | P3 | Per-test setup | Pending |
| `test/after-each` | P3 | Per-test cleanup | Pending |
| Timeout per test | P3 | Kill long-running tests | ✅ Via `test/async-timeout` |
| Test filtering | P3 | Run subset by name pattern | Pending |
| Verbose failure output | P3 | Show actual vs expected on fail | Pending |

---

## Migration Guide

### Migrating Category A (Print-Only Tests)

**Before:**
```lisp
(load "src/prelude.valk")

(println "Test 1: metrics/json returns string")
(println (metrics/json))
(println "All tests passed!")
```

**After:**
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "Metrics Builtins Tests")

(test/define "metrics-json-returns-string"
  {do
    (= {result} (metrics/json))
    (test/assert (string? result) "metrics/json should return a string")
    true
  })

(test/define "metrics-prometheus-returns-string"
  {do
    (= {result} (metrics/prometheus))
    (test/assert (string? result) "metrics/prometheus should return a string")
    true
  })

(test/define "metrics-counter-inc-without-labels"
  {do
    (metrics/counter-inc "test_counter")
    (= {json} (metrics/json))
    (test/assert (string? json) "JSON output after counter-inc should be string")
    true
  })

(test/run {})
```

**Effort:** Low - straightforward rewrite

---

### Migrating Category B (Async Tests) - REQUIRES FRAMEWORK EXTENSION

**Current (test_large_download.valk):**
```lisp
(def {tests-passed} 0)
(def {tests-failed} 0)

(aio/schedule aio 200 (\ {} {
  (http2/client-request aio "127.0.0.1" test-port "/10kb"
    (\ {resp} {
      (if (error? resp)
        {(def {tests-failed} (+ tests-failed 1))}
        {(if (== (len (http2/response-body resp)) 10240)
           {(def {tests-passed} (+ tests-passed 1))}
           {(def {tests-failed} (+ tests-failed 1))})})
      ; ... chain next test
    }))
}))
```

**After (with framework extension):**
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "Large Download Tests")

; Setup runs once before all tests
(test/before-all {
  (def {aio} (aio/start))
  (def {server} (http2/server-listen aio 0 server-handler))
  (def {test-port} (http2/server-port server))
  ; Return context
  {:aio aio :port test-port :server server}
})

; Teardown runs once after all tests
(test/after-all (\ {ctx} {
  (aio/stop (plist/get ctx :aio))
}))

; Async test with timeout
(test/define-async "download-10kb" 5000 (\ {ctx done} {
  (= {aio} (plist/get ctx :aio))
  (= {port} (plist/get ctx :port))
  (http2/client-request aio "127.0.0.1" port "/10kb"
    (\ {resp} {
      (test/assert-eq 10240 (len (http2/response-body resp)) "10KB body length")
      (done true)
    }))
}))

(test/define-async "download-50kb" 5000 (\ {ctx done} {
  ; Similar pattern
}))

(test/run-async aio {})
```

**Key changes:**
- `test/define-async name timeout body` - body receives `(ctx done)` args
- `done` callback signals test completion with pass/fail
- `test/run-async aio {}` - runs tests on event loop
- Context passed through from `before-all`

---

### Migrating Category C (Improper Usage)

**Before:**
```lisp
(test/define "http2/response-ok? returns true for 200"
  {do
    (def {resp} (http2/mock-response "200" "OK"))
    (== 1 (http2/response-ok? resp))
  })
```

**After:**
```lisp
(test/define "http2/response-ok? returns true for 200"
  {do
    (def {resp} (http2/mock-response "200" "OK"))
    (test/assert-eq 1 (http2/response-ok? resp) "200 should return 1 (truthy)")
    true
  })
```

**Effort:** Very low - add `test/assert-eq` and message

---

## Implementation Plan

### Phase 1: Fix Category C (1 hour)

Update `test/test_http_integration.valk` to use proper assertions:

1. Replace bare `(== ...)` returns with `(test/assert-eq ... msg)`
2. Ensure all tests return `true` on success
3. Run `make test` to verify

### Phase 2: Migrate Category A (2 hours)

Rewrite print-only tests to use framework:

| File | Tests | Effort |
|------|-------|--------|
| `test_aio_builtins.valk` | 3 | 15 min |
| `test_metrics_builtins.valk` | 5 | 30 min |
| `test_metrics_prometheus.valk` | 2 | 15 min |
| `test_overload.valk` | 3 | 15 min |

### Phase 3: Add Debug and Stability Features (2 hours)

Add to `src/modules/test.valk`:

```lisp
; ============================================================================
; Environment-based configuration
; ============================================================================

; Auto-enable debug from environment
(if (env/get "VALK_TEST_DEBUG")
  {(def {*test-debug*} 1)}
  {nil})

; Test filter pattern from environment
(def {*test-filter*} (env/get "VALK_TEST_FILTER"))

; Configurable timeout multiplier for slow CI
(def {*test-timeout-multiplier*} 
  (if (env/get "VALK_TEST_SLOW")
    {3}
    {1}))

; ============================================================================
; Enhanced assertions with verbose output
; ============================================================================

(fun {test/assert-eq expected actual msg} {
  (if (== expected actual)
    {true}
    {do
      (printf "\n   ╔═ Assertion Failed ═══════════════════════════════════════╗\n")
      (printf "   ║ Expected: %s\n" (str expected))
      (printf "   ║ Actual:   %s\n" (str actual))
      (printf "   ║ Message:  %s\n" msg)
      (printf "   ╚════════════════════════════════════════════════════════════╝\n")
      (error msg)})
})

(fun {test/assert-neq not-expected actual msg} {
  (if (!= not-expected actual)
    {true}
    {do
      (printf "\n   ╔═ Assertion Failed ═══════════════════════════════════════╗\n")
      (printf "   ║ Should NOT equal: %s\n" (str not-expected))
      (printf "   ║ Actual:           %s\n" (str actual))
      (printf "   ║ Message:          %s\n" msg)
      (printf "   ╚════════════════════════════════════════════════════════════╝\n")
      (error msg)})
})

(fun {test/assert-error result msg} {
  (if (error? result)
    {true}
    {do
      (printf "\n   ╔═ Assertion Failed ═══════════════════════════════════════╗\n")
      (printf "   ║ Expected: error\n")
      (printf "   ║ Actual:   %s (%s)\n" (type result) (str result))
      (printf "   ║ Message:  %s\n" msg)
      (printf "   ╚════════════════════════════════════════════════════════════╝\n")
      (error msg)})
})

(fun {test/assert-contains haystack needle msg} {
  (if (str-contains haystack needle)
    {true}
    {do
      (printf "\n   ╔═ Assertion Failed ═══════════════════════════════════════╗\n")
      (printf "   ║ Haystack: %s\n" (str haystack))
      (printf "   ║ Needle:   %s (not found)\n" (str needle))
      (printf "   ║ Message:  %s\n" msg)
      (printf "   ╚════════════════════════════════════════════════════════════╝\n")
      (error msg)})
})

; ============================================================================
; Debug tracing
; ============================================================================

(fun {test/trace msg} {
  (if (== *test-debug* 1)
    {(printf "[TRACE %ld] %s\n" (time-us {}) msg)}
    {nil})
})

(fun {test/trace-value name val} {
  (if (== *test-debug* 1)
    {(printf "[TRACE %ld] %s = %s\n" (time-us {}) name (str val))}
    {nil})
})

; ============================================================================
; Test filtering
; ============================================================================

(fun {*test-matches-filter* name} {
  (if (nil? *test-filter*)
    {true}  ; No filter, run all
    {(str-contains name *test-filter*)}))

; Updated test runner to respect filter
(fun {*test-run-one* test} {
  (= {test-name} (eval (head test)))
  (if (not (*test-matches-filter* test-name))
    {do
      (def {*test-skipped*} (+ *test-skipped* 1))
      true}  ; Skip silently
    {; ... existing run logic
    })
})

; ============================================================================
; Retry support for flaky tests
; ============================================================================

(def {*test-retry-count*} 0)

(fun {test/retry count} {
  (def {*test-retry-count*} count)
})

; Run test with retries (in *test-run-one*)
(fun {*test-run-with-retry* test-body max-retries} {
  (= {attempt} 0)
  (= {result} (error "not run"))
  (while (and (error? result) (< attempt max-retries))
    (do
      (= {result} (eval test-body))
      (= {attempt} (+ attempt 1))
      (if (and (error? result) (< attempt max-retries))
        {(if (== *test-debug* 1)
          {(printf "[DEBUG] Retry %d/%d for test\n" attempt max-retries)}
          {nil})}
        {nil})))
  result
})
```

### Phase 4: Extend Framework for Async (4 hours)

Add to `src/modules/test.valk`:

```lisp
; New globals
(def {*test-async-registry*} {})
(def {*test-before-all*} nil)
(def {*test-after-all*} nil)
(def {*test-context*} {})

; Setup/teardown hooks
(fun {test/before-all body} {
  (def {*test-before-all*} body)
})

(fun {test/after-all fn} {
  (def {*test-after-all*} fn)
})

; Async test definition
(fun {test/define-async name timeout body} {
  (def {*test-async-registry*} 
    (join *test-async-registry* 
          (list (list name timeout body))))
})

; Run async tests on event loop
(fun {test/run-async aio args} {
  ; Execute before-all, get context
  (= {ctx} (if (nil? *test-before-all*) 
              {{}} 
              {(eval *test-before-all*)}))
  (def {*test-context*} ctx)
  
  ; Chain test execution via aio/schedule
  (*run-async-tests* aio *test-async-registry* ctx)
})
```

### Phase 5: Migrate Category B (8 hours)

Migrate async tests using new framework extensions:

| File | Tests | Complexity | Effort |
|------|-------|------------|--------|
| `test_large_download.valk` | 3 | Low | 30 min |
| `test_http_api_network.valk` | ~10 | Medium | 1 hr |
| `test_pending_streams.valk` | ~5 | Medium | 45 min |
| `test_backpressure.valk` | ~5 | Medium | 45 min |
| `test_sse_integration.valk` | ~10 | Medium | 1 hr |
| `test_http_client_server.valk` | ~15 | Medium | 1.5 hr |
| `test_http2_client_request_errors.valk` | ~10 | Medium | 1 hr |
| `test_async_http_handlers.valk` | 52 | High | 2 hr |

---

## Implementation Status

### ✅ Phase 1-2: Category A & C Migration (COMPLETED)

**Category C (Improper Framework Usage):**
- `test_http_integration.valk` - Updated all 38 tests to use `test/assert-eq` with messages

**Category A (Print-Only Tests):**
- `test_aio_builtins.valk` - Migrated 3 tests
- `test_metrics_builtins.valk` - Migrated 5 tests  
- `test_metrics_prometheus.valk` - Migrated 2 tests
- `test_overload.valk` - Marked as demo (not a test, runs server forever)

### ✅ Phase 3: Debug and Stability Features (COMPLETED)

Added to `src/modules/test.valk`:

**Environment-Based Configuration:**
```lisp
; Auto-enabled from environment variables:
; VALK_TEST_DEBUG=1   - Enable debug output
; VALK_TEST_FILTER=x  - Filter tests by name
; VALK_TEST_SLOW=1    - 3x timeout multiplier
```

**New Assertions with Verbose Output:**
```lisp
(test/assert-neq not-expected actual msg)  ; Assert not equal
(test/assert-error result msg)              ; Assert error type
```

**Debug Tracing:**
```lisp
(test/trace "message")                      ; Trace with timestamp
(test/trace-value "name" value)             ; Trace with value
```

**Failure Tracking:**
- Added `*test-current-failed*` flag to track assertion failures within `do` blocks
- Assertions now set the flag and print verbose output on failure

### ✅ Phase 4: Async Test Framework Extension (COMPLETED)

Added async test support to `src/modules/test.valk`:

**New Functions:**
| Function | Description |
|----------|-------------|
| `test/async name body-fn` | Register async test (body-fn receives `done` callback) |
| `test/run-async aio` | Run async tests with given AIO system |
| `test/async-timeout ms` | Set timeout for async tests (default 30s) |
| `test/check-response resp status body done` | HTTP response assertion helper |
| `test/async-assert cond done` | Assert with done callback |
| `test/async-assert-eq expected actual done` | Assert equality with done callback |

**Usage Pattern:**
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "My Async Tests")
(test/async-timeout 30000)

(def {aio} (aio/start))

(test/async "test-name" (\ {done} {
  (http2/client-request aio host port path (\ {resp} {
    (test/check-response resp "200" "expected-body" done)
  }))
}))

; Start server if needed
(http2/server-listen aio PORT handler)

; Run tests and event loop
(test/run-async aio)
(aio/run aio)
```

### ✅ Phase 5: Async Test Migration (PARTIAL)

**Migrated Tests:**
| File | Tests | Status |
|------|-------|--------|
| `test_async_http_handlers.valk` | 52 | ✅ Migrated |
| `test_backpressure.valk` | 5 | ✅ Migrated |
| `test_backpressure_timeout.valk` | 5 | ✅ Migrated |
| `test_http_api_network.valk` | 24 | ✅ Migrated |
| `test_http_client_server.valk` | 2 | ✅ Migrated |
| `test_http2_client_request_errors.valk` | 17 | ✅ Migrated |
| `test_large_download.valk` | 3 | ✅ Migrated |
| `test_pending_streams.valk` | 1 | ✅ Migrated |
| `test_client_headers.valk` | 1 | ✅ Migrated |
| `test_concurrent_requests.valk` | 1 | ✅ Migrated |
| `test_custom_error_handler.valk` | 2 | ✅ Migrated |
| `test_arena_out_of_order.valk` | 1 | ✅ Migrated |
| `test_overload_metrics.valk` | 4 | ✅ Migrated |
| `test_pending_stream_headers.valk` | 1 | ✅ Migrated |
| `test_sse_async_timeout.valk` | 1 | ✅ Migrated |
| `test_sse_diagnostics_endpoint.valk` | 1 | ✅ Fixed |
| `test_delay_error.valk` | 1 | ✅ Migrated |
| `test_delay_continuation_error.valk` | 1 | ✅ Migrated |
| `test_make_string.valk` | 4 | ✅ Migrated |

**Remaining (demos, not tests):**
| File | Notes |
|------|-------|
| `test_2mb_server.valk` | Demo server - runs forever |
| `test_50mb_file_server.valk` | Demo server - runs forever |
| `test_50mb_server.valk` | Demo server - runs forever |
| `test_large_response_handler.valk` | Demo server - runs forever |
| `test_lisp_50mb_handler.valk` | Demo server - runs forever |
| `test_overload.valk` | Demo server - runs forever |

**Already Migrated (removed from list):**
- `test_aio_builtins.valk` - ✅ Migrated
- `test_metrics_builtins.valk` - ✅ Migrated  
- `test_metrics_prometheus.valk` - ✅ Migrated
- `test_sse_integration.valk` - ✅ Already using correct pattern

---

## Summary

| Category | Files | Root Cause | Fix | Status |
|----------|-------|------------|-----|--------|
| A: Print-only | 4 | Lazy/demo tests | Rewrite with assertions | ✅ **Completed** |
| B: Custom harness | 8 | No async support | Extend framework, then migrate | ✅ **Completed** |
| C: Improper usage | 1 | Missing messages | Add `test/assert-eq` | ✅ **Completed** |

**Completed:**
- ✅ Phase 1: Category C tests fixed with proper assertions (test_http_integration.valk)
- ✅ Phase 2: Category A print-only tests migrated (test_aio_builtins.valk, test_metrics_builtins.valk, test_metrics_prometheus.valk)
- ✅ Phase 3: Debug and stability features added (environment variables, verbose assertions, trace functions)
- ✅ Phase 4: Async test framework extension
- ✅ Phase 5: All async tests migrated (~122 test cases total)
- ✅ Added `getenv` builtin for environment-based configuration

**New Features Implemented:**
- `VALK_TEST_DEBUG=1` - Enable debug output via environment variable
- `VALK_TEST_FILTER=name` - Filter tests by name
- `VALK_TEST_SLOW=1` - Increase timeout multiplier for slow CI
- `test/assert-neq` - Assert not equal
- `test/assert-error` - Assert expression returns error  
- `test/trace msg` - Debug trace with timestamp
- `test/trace-value name val` - Debug trace with value
- Verbose assertion failure output showing expected/actual values

**Bugs Discovered During Migration:**
- Prometheus metrics output is empty (metrics/prometheus returns "")
- Debug handler matches paths it shouldn't (case-insensitive, query strings)
- Histogram creation with numeric label key doesn't fail (should validate)

**Infrastructure Fixes (Dec 2024):**
- ✅ **SSE + HTTP/2 Protocol Error** - Removed prohibited `connection: keep-alive` header from SSE responses (RFC 7540 Section 8.1.2.2)
- ✅ **SSE Stream EOF** - Added `nghttp2_session_resume_data()` call in `valk_sse_stream_close()` to properly terminate streams
- ✅ **Slab Allocator Alignment** - Added `_Alignas(16)` to `valk_slab_item_t.data[]` to fix UBSAN crashes on ARM64
- ✅ **Port Allocation Race** - Removed `net/get-available-port` builtin; all tests now use port 0 + `http2/server-port` pattern
- ✅ **SSE Test Response Fix** - SSE handlers must return `:deferred`, not a normal response (sse/open already submits HTTP response)
- ✅ **SSE Test Pattern** - SSE tests cannot wait for client response callbacks; must use timer-based server-side state checking

**Current Test Status (Dec 28, 2024):**
- ✅ All Valk tests passing
- C tests: 1 known crash (`test_many_parallel_clients` - stress test)

**Migration Complete!**

---

## Appendix: Good Test Examples

### Unit Test Pattern
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "Feature Name Tests")

(test/define "descriptive-test-name"
  {do
    ; Setup
    (= {input} (prepare-data))
    
    ; Execute
    (= {result} (function-under-test input))
    
    ; Assert
    (test/assert-eq expected result "what this tests")
    true
  })

(test/run {})
```

### Error Path Testing
```lisp
(test/define "function-returns-error-on-invalid-input"
  {do
    (= {result} (function-under-test "invalid"))
    (test/assert (error? result) "should return error for invalid input")
    true
  })
```

### Files Using Framework Correctly
- `test/test_prelude.valk`
- `test/test_quasiquote.valk`
- `test/test_gc_suite.valk`
- `test/test_do_suite.valk`
- `test/test_aio_config.valk`
- `test/test_sse_builtins.valk`
- `test/test_aio_builtins_coverage.valk`
- `test/test_aio_debug.valk`

---

## Appendix B: Quick Reference - Debugging Commands

### Running Tests with Debug Output

```bash
# Enable debug mode via environment
VALK_TEST_DEBUG=1 build/valk test/test_prelude.valk

# Run only tests matching pattern
VALK_TEST_FILTER="counter" build/valk test/test_metrics.valk

# Increase timeouts for slow CI
VALK_TEST_SLOW=1 build/valk test/test_async_http_handlers.valk

# Combine options
VALK_TEST_DEBUG=1 VALK_TEST_FILTER="download" build/valk test/test_large_download.valk
```

### Running Tests with Sanitizers

```bash
# Address Sanitizer (catches memory errors)
make test-valk-asan

# Single test with ASAN
./build-asan/valk test/test_specific.valk

# Undefined Behavior Sanitizer
make test-valk-ubsan
```

### Debugging Async Tests

```bash
# Run integration test with server debug dashboard enabled
build/valk test/test_async_http_handlers.valk &
curl http://localhost:PORT/debug/  # Access debug dashboard
curl http://localhost:PORT/debug/metrics  # Get metrics JSON
```

### Investigating Test Failures

```bash
# Check if port is in use
lsof -i :8080

# Run test multiple times to check for flakiness
for i in {1..10}; do build/valk test/test_flaky.valk || echo "FAIL on run $i"; done

# Check for memory leaks
valgrind --leak-check=full build/valk test/test_memory.valk

# Check test output in detail
build/valk test/test_file.valk 2>&1 | tee test_output.log
```

### In-Code Debugging

```lisp
; Enable debug at start of test file
(test/debug 1)

; Add trace points in async callbacks
(test/trace "Before request")
(http2/client-request aio host port path (\ {resp} {
  (test/trace "Got response")
  (test/trace-value "status" (http2/response-status resp))
  (test/trace-value "body-len" (len (http2/response-body resp)))
  ; ... assertions
}))

; Force GC before assertions to catch dangling references
(gc/collect)
(test/assert-eq expected actual "after GC")

; Print intermediate values
(printf "[DEBUG] result = %s\n" (str result))
```

### C Test Debugging

```c
// test/testing.h provides these macros:
VALK_FAIL("Message with %s", args);  // Fail with formatted message
VALK_SKIP("Reason");                  // Skip test
VALK_PASS();                          // Explicit pass

// All ASSERT_* macros print file:line on failure
ASSERT_EQ(a, b);              // expected 5 == 10
ASSERT_STR_EQ(s1, s2);        // expected "foo", got "bar"
ASSERT_STR_CONTAINS(s, sub);  // "needle" not found in "haystack"
```
