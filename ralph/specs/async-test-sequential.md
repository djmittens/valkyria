# Async Test Framework: Sequential Execution Mode

## Problem

The `test/run-async` framework starts **all tests simultaneously** (line 534 in `src/modules/test.valk`). This causes resource exhaustion when test files have many tests that create HTTP servers, interval timers, or SSE connections.

**Observed Symptoms:**
1. `test_debug_handler.valk` has 35 tests, ~6 timeout each run
2. Which tests timeout varies randomly due to race conditions
3. Tests pass when run in smaller isolated batches
4. Each test creates HTTP servers on ephemeral ports - 35 servers simultaneously exhaust resources

**Root Cause Analysis:**
```lisp
; Line 534 in src/modules/test.valk
(map (\ {test} {(*test-start-async-one* aio timeout-ms test)}) tests)
```
This starts ALL tests at once. With 35 tests each creating servers/timers:
- 35+ HTTP servers listening simultaneously
- 35+ interval timers firing every 100ms
- 35+ SSE streams with callbacks
- Event loop overwhelmed, tests starve and timeout

## Scope

Add a sequential execution mode to `test/run-async` that runs one test at a time, waiting for each to complete before starting the next. The parallel mode should remain available for tests that don't have resource conflicts.

---

## Phase 1: Add Sequential Test Runner

### Goal
Add `test/run-async-sequential` function that executes tests one at a time.

- [ ] **Task 1.1: Design sequential runner state machine**
  - Track current test index
  - Track completion callback chain
  - Design: Each test completion triggers next test start
  - Reuse existing `*test-start-async-one*` for individual test execution

- [ ] **Task 1.2: Implement `test/run-async-sequential`**
  - File: `src/modules/test.valk`
  - Same API as `test/run-async`: `(test/run-async-sequential aio tests config)`
  - Runs tests one at a time in list order
  - Each test has full per-test timeout (no resource contention)
  - Suite timeout applies to total time

- [ ] **Task 1.3: Add helper to chain test completion**
  - After test completes (pass/fail/timeout), start next test
  - Use `aio/schedule aio 0 (\ {} {...})` to avoid stack depth issues
  - Track pending count, complete when all done

- [ ] **Task 1.4: Unit test the sequential runner**
  - File: `test/test_test_framework_sequential.valk`
  - Verify: Tests run in order
  - Verify: Each test completes before next starts
  - Verify: Timeout on one test doesn't affect others
  - Verify: Pass/fail counts correct

---

## Phase 2: Fix test_debug_handler.valk

### Goal
Convert `test_debug_handler.valk` to use sequential execution, fixing the timeout issue.

- [ ] **Task 2.1: Change test_debug_handler.valk to sequential**
  - Replace `test/run-async` with `test/run-async-sequential`
  - Keep same test definitions
  - Verify: All 35 tests pass consistently

- [ ] **Task 2.2: Run test_debug_handler.valk 5 times**
  - Must pass all 5 runs with no timeouts
  - No flaky tests

- [ ] **Task 2.3: Add cleanup between tests**
  - Call `debug/reset-state` at start of broadcaster tests
  - Ensure no state leakage between tests
  - Already partially done - verify completeness

---

## Phase 3: Configuration Option for Parallel vs Sequential

### Goal
Allow test files to specify execution mode via config.

- [ ] **Task 3.1: Add `:sequential` config option**
  - `(test/run-async aio tests {:sequential true})` → runs sequentially
  - Default remains parallel for backward compatibility
  - Modify `test/run-async` to check config and dispatch

- [ ] **Task 3.2: Document the option**
  - Add comment in test.valk explaining when to use sequential
  - Guidance: Use sequential when tests create servers/timers

- [ ] **Task 3.3: Update test_debug_handler.valk to use config**
  - Change from `test/run-async-sequential` to `test/run-async ... {:sequential true}`
  - Cleaner API, single entry point

---

## Phase 4: Validate Fix

### Goal
Ensure the fix works reliably and doesn't break other tests.

- [ ] **Task 4.1: Run full test suite 3 times**
  - `make test` must pass all 3 runs
  - No new flaky tests introduced

- [ ] **Task 4.2: Verify test_debug_handler.valk timing**
  - Sequential mode will be slower (tests run one-at-a-time)
  - Verify total time is acceptable (< 2 minutes for 35 tests)
  - Each test is ~5 seconds max, so ~3 minutes worst case is acceptable

- [ ] **Task 4.3: Check other large async test files**
  - `test_async_http_handlers.valk` - review if needs sequential
  - `test_sse_integration.valk` - review if needs sequential
  - Only convert if they show timeout issues

---

## Acceptance Criteria

### Phase 1 (Sequential Runner)
- [ ] `test/run-async-sequential` function exists
- [ ] Tests run one at a time (verify with print statements)
- [ ] Timeout on one test doesn't block others
- [ ] Pass/fail/timeout counts are correct

### Phase 2 (Debug Handler Fixed)
- [ ] `test_debug_handler.valk` passes 5 consecutive runs
- [ ] No TIMEOUT lines in output
- [ ] All 35 tests pass

### Phase 3 (Config Option)
- [ ] `{:sequential true}` config option works
- [ ] Default behavior unchanged (parallel)
- [ ] Documented in test.valk

### Phase 4 (Validation)
- [ ] `make test` passes 3 consecutive runs
- [ ] No new test failures introduced
- [ ] Sequential test runtime is acceptable

---

## Files to Create/Modify

| File | Action | Phase |
|------|--------|-------|
| `src/modules/test.valk` | MODIFY - add sequential runner | 1, 3 |
| `test/test_test_framework_sequential.valk` | NEW - unit tests | 1 |
| `test/test_debug_handler.valk` | MODIFY - use sequential | 2 |

---

## Implementation Notes

### Sequential Runner Pseudocode
```lisp
(fun {test/run-async-sequential aio & args} {
  ; Parse args same as test/run-async
  (= {tests} ...)
  (= {ctx} ...)
  
  ; Track state
  (= {current-index} (atom 0))
  (= {total} (len tests))
  
  ; Define recursive runner
  (fun {run-next} {
    (= {idx} (atom/get current-index))
    (if (>= idx total)
      {; All done, print results and exit
       (*test-async-print-results* ...)}
      {; Run test at idx, on completion call run-next
       (= {test} (nth tests idx))
       (*test-start-async-one-with-callback* aio timeout-ms test 
         (\ {} {
           (atom/add! current-index 1)
           (aio/schedule aio 0 run-next)}))})})
  
  ; Start first test
  (run-next)
  (aio/run aio)
})
```

### Alternative: Batch Mode
Instead of pure sequential, could run in batches of N tests. This would be faster but more complex. Start with sequential, optimize later if needed.

---

## Notes

- The parallel mode should remain the default - most test files work fine with it
- Sequential mode trades speed for reliability
- The 35 tests in test_debug_handler.valk will take ~3 minutes sequentially vs ~30 seconds parallel (when it works)
- This is acceptable for correctness
- Long-term, tests should be designed to not create heavy resources, but that's a larger refactor
