# Async Test Framework: Sequential Execution Mode

## Overview

Add a sequential execution mode to the `test/run-async` framework to prevent resource exhaustion when test files have many tests that create HTTP servers, interval timers, or SSE connections. Currently, all tests start simultaneously (line 534 in `src/modules/test.valk`), causing timeouts when 35+ tests each create heavy resources. Sequential mode runs one test at a time, trading speed for reliability.

## Requirements

### Problem Analysis

**Root Cause** (line 534 in `src/modules/test.valk`):
```lisp
(map (\ {test} {(*test-start-async-one* aio timeout-ms test)}) tests)
```

This starts ALL tests at once. With 35 tests each creating servers/timers:
- 35+ HTTP servers listening simultaneously
- 35+ interval timers firing every 100ms
- 35+ SSE streams with callbacks
- Event loop overwhelmed, tests starve and timeout

**Observed Symptoms:**
- `test_debug_handler.valk` has 35 tests, ~6 timeout each run
- Which tests timeout varies randomly (race conditions)
- Tests pass when run in smaller isolated batches

### Sequential Runner Design

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Test 1    │────>│   Test 2    │────>│   Test N    │────> Results
│  (complete) │     │  (complete) │     │  (complete) │
└─────────────┘     └─────────────┘     └─────────────┘
```

**State Machine:**
1. Track current test index
2. Run test at index
3. On completion (pass/fail/timeout), increment index
4. Use `aio/schedule aio 0 (\ {} {...})` to avoid stack depth issues
5. When index reaches total, print results and exit

### API

**New Function:**
```lisp
(test/run-async-sequential aio tests config)
```

Same API as `test/run-async`. Runs tests one at a time in list order.

**Config Option:**
```lisp
(test/run-async aio tests {:sequential true})
```

Default remains parallel for backward compatibility.

### Implementation Pseudocode

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

### Files to Modify

| File | Action | Description |
|------|--------|-------------|
| `src/modules/test.valk` | MODIFY | Add `test/run-async-sequential`, add `:sequential` config dispatch |
| `test/test_test_framework_sequential.valk` | NEW | Unit tests for sequential runner |
| `test/test_debug_handler.valk` | MODIFY | Use sequential mode |

### Test Cleanup

Each test should call `debug/reset-state` at start of broadcaster tests to ensure no state leakage between tests.

### Timing Expectations

- Sequential mode will be slower (tests run one-at-a-time)
- 35 tests × ~5 seconds max each = ~3 minutes worst case
- Acceptable tradeoff for reliability

## Acceptance Criteria

### Core Functionality
- [ ] `test/run-async-sequential` function exists in `src/modules/test.valk`
- [ ] Tests run one at a time (verify with print statements showing sequential execution)
- [ ] Timeout on one test does not block subsequent tests
- [ ] Pass/fail/timeout counts are correct at end of run
- [ ] `aio/schedule` used for chaining to prevent stack overflow

### Configuration
- [ ] `{:sequential true}` config option dispatches to sequential runner
- [ ] Default behavior unchanged (parallel execution)
- [ ] Documentation comment in `test.valk` explains when to use sequential mode

### Debug Handler Fix
- [ ] `test_debug_handler.valk` uses sequential mode
- [ ] `test_debug_handler.valk` passes 5 consecutive runs with no timeouts
- [ ] All 35 tests pass in each run
- [ ] No TIMEOUT lines in output

### Validation
- [ ] `make test` passes 3 consecutive runs
- [ ] No new test failures introduced
- [ ] Sequential test runtime < 3 minutes for `test_debug_handler.valk`

### Unit Tests
- [ ] `test/test_test_framework_sequential.valk` exists
- [ ] Tests verify execution order
- [ ] Tests verify completion chaining
- [ ] Tests verify timeout isolation
