# Debug Dashboard Validation

## Problem

The debug dashboard SSE system lacks test coverage at critical layers, and manual testing reveals concurrency issues. Trust in the implementation is low.

**Observed Issues:**
1. Concurrency problems during manual testing (specifics TBD from user)
2. Per-connection timers create O(N) overhead for N connections
3. No tests verify correctness of SSE wire format
4. Debug handler has only 1 integration test, no unit tests
5. Stream body integration paths are untested (LCOV excluded)

## Architecture Layers

```
Layer 4: Dashboard JavaScript (script.js)         - NO TESTS
Layer 3: Debug Handler (debug.valk)               - 1 test (minimal)
Layer 2: SSE Wrapper (sse.valk)                   - 55 tests (good)
Layer 1: Stream Builtins (aio_stream_builtins.c)  - 58 tests (arg validation only)
Layer 0: Stream Body (aio_stream_body.c)          - 47 tests (unit, no integration)
```

Trust must be built bottom-up: fix and test foundational layers before optimizing higher layers.

## Scope

### Phase 1: Verify Layer 0-1 (Stream Infrastructure)

Ensure the C stream infrastructure is correct under concurrent use.

### Phase 2: Verify Layer 2 (SSE Wire Format)

Ensure SSE formatting produces spec-compliant output.

### Phase 3: Verify Layer 3 (Debug Handler)

Add unit and integration tests for the debug handler.

### Phase 4: Fix Concurrency Issues

Identify and fix the race conditions observed in manual testing.

### Phase 5: Optimize with Global Timer

Replace per-connection timers with shared broadcaster (only after correctness verified).

---

## Phase 1: Stream Infrastructure Verification

### Goal
Verify that `stream/*` builtins and `valk_stream_body_t` work correctly, especially under concurrent writes and connection close scenarios.

- [ ] **Task 1.1: Add stream body integration test**
  - File: `test/test_stream_body_integration.c`
  - Test actual data flow through nghttp2 (not just state management)
  - Verify: Write queues data, read callback dequeues it
  - Verify: Close triggers on-close callback
  - Verify: Backpressure when queue full

- [ ] **Task 1.2: Test stream/write under connection close race**
  - In integration test: Start write, close connection mid-write
  - Verify: No crash, no use-after-free
  - Verify: Error returned to caller
  - Run under TSAN and ASAN

- [ ] **Task 1.3: Test concurrent writes to same stream**
  - Multiple rapid writes from same context
  - Verify: All data delivered in order
  - Verify: No corruption

- [ ] **Task 1.4: Test on-close callback timing**
  - Verify: Callback fires exactly once
  - Verify: Callback fires before stream body freed
  - Verify: Callback can safely access stream state

---

## Phase 2: SSE Wire Format Verification

### Goal
Verify that `sse/*` functions produce SSE-spec-compliant wire format.

- [ ] **Task 2.1: Test sse/send wire format**
  - File: `test/test_sse_format.valk`
  - `(sse/send stream "hello")` → verify output is `"data: hello\n\n"`
  - `(sse/send stream "a\nb")` → verify output is `"data: a\ndata: b\n\n"`
  - `(sse/send stream "")` → verify output is `"data: \n\n"`

- [ ] **Task 2.2: Test sse/event wire format**
  - `(sse/event stream "msg" "data")` → `"event: msg\ndata: data\n\n"`
  - `(sse/event stream "msg" "a\nb")` → `"event: msg\ndata: a\ndata: b\n\n"`

- [ ] **Task 2.3: Test sse/id and sse/full wire format**
  - `(sse/id stream "123" "data")` → `"id: 123\ndata: data\n\n"`
  - `(sse/full stream "msg" "123" "data")` → `"id: 123\nevent: msg\ndata: data\n\n"`

- [ ] **Task 2.4: Test sse/retry and sse/comment**
  - `(sse/retry stream 5000)` → `"retry: 5000\n\n"`
  - `(sse/comment stream "ping")` → `": ping\n"`
  - `(sse/heartbeat stream)` → `":\n"`

---

## Phase 3: Debug Handler Verification

### Goal
Add comprehensive tests for `debug.valk` handler logic.

- [ ] **Task 3.1: Test route matching**
  - File: `test/test_debug_handler.valk`
  - Test all routes: `/debug`, `/debug/`, `/debug/metrics`, `/debug/metrics/state`, `/metrics`, `/debug/diagnostics/memory`, `/debug/slab/buckets`
  - Verify: Correct handler invoked for each
  - Verify: Unknown routes return redirect to /debug/

- [ ] **Task 3.2: Test /debug/metrics/state JSON structure**
  - Request endpoint, parse JSON response
  - Verify: Has `metrics.aio`, `metrics.modular`, `metrics.vm`, `metrics.registry`
  - Verify: Has `memory` key
  - Verify: All values are correct types (numbers, objects)

- [ ] **Task 3.3: Test /debug/diagnostics/memory SSE events**
  - Connect to SSE endpoint
  - Verify: First event is `diagnostics` with full state
  - Verify: Subsequent events are `diagnostics-delta`
  - Verify: Events are valid JSON
  - Parse and validate structure matches expected schema

- [ ] **Task 3.4: Test SSE handler lifecycle**
  - Connect, receive events, disconnect
  - Verify: Timer stops after disconnect (check via side effect or log)
  - Verify: No errors after disconnect
  - Verify: Reconnect works

- [ ] **Task 3.5: Test /metrics Prometheus format**
  - Request endpoint
  - Verify: Contains expected metric names
  - Verify: Format matches Prometheus exposition format
  - Verify: No duplicate metrics

---

## Phase 4: Concurrency Issue Investigation and Fix

### Goal
Identify and fix the race conditions observed in manual testing.

- [ ] **Task 4.1: Document observed concurrency issues**
  - Capture specific symptoms from manual testing
  - Note: Which operations trigger the issue?
  - Note: Error messages, crashes, or incorrect behavior?

- [ ] **Task 4.2: Add stress test for SSE connections**
  - File: `test/stress/test_sse_concurrency.valk`
  - 10 concurrent SSE connections
  - Rapid connect/disconnect cycles
  - Run for 60 seconds
  - Verify: No crashes, no hangs, no resource leaks

- [ ] **Task 4.3: Test delta baseline isolation**
  - Two SSE connections active
  - Increment metrics between their events
  - Verify: Each connection sees correct deltas for its timeline
  - This tests whether `metrics/collect-delta` uses shared or per-connection state

- [ ] **Task 4.4: Run under TSAN**
  - Run stress test with ThreadSanitizer
  - Identify any data races
  - Fix races found

- [ ] **Task 4.5: Run under ASAN**
  - Run stress test with AddressSanitizer
  - Identify any memory errors
  - Fix errors found

- [ ] **Task 4.6: Fix identified issues**
  - Create subtasks for each issue found
  - Verify fix with regression test

---

## Phase 5: Global Timer Optimization

### Goal
Replace per-connection timers with a single shared timer (only after Phase 1-4 complete).

**Prerequisite**: All Phase 1-4 tests pass.

- [ ] **Task 5.1: Create debug-broadcaster.valk**
  - File: `src/modules/aio/debug-broadcaster.valk`
  - Single timer (100ms) shared across all subscribers
  - Subscriber list as atom
  - On tick: collect once, broadcast to all

- [ ] **Task 5.2: Implement per-subscriber baseline**
  - Each subscriber tracks its own delta baseline
  - First event sends full state
  - Subsequent events send delta from that subscriber's baseline

- [ ] **Task 5.3: Implement subscribe/unsubscribe API**
  - `debug/subscribe sys stream` - Add to list, start timer if first
  - `debug/unsubscribe stream` - Remove from list, stop timer if last
  - Auto-unsubscribe on stream close

- [ ] **Task 5.4: Implement backpressure handling**
  - Track consecutive failed writes per subscriber
  - Disconnect subscriber after 10 failures (1 second)
  - Log disconnection

- [ ] **Task 5.5: Update debug.valk to use broadcaster**
  - Replace `aio/interval` with `debug/subscribe`
  - Verify dashboard still works

- [ ] **Task 5.6: Add broadcaster tests**
  - Verify: Single timer for multiple connections
  - Verify: Timer stops when last subscriber leaves
  - Verify: Slow subscriber disconnected, fast subscribers unaffected

---

## Acceptance Criteria

### Phase 1-3 (Correctness)
- [ ] All new tests pass
- [ ] No TSAN warnings
- [ ] No ASAN errors
- [ ] SSE wire format matches spec
- [ ] Debug handler returns correct data

### Phase 4 (Stability)
- [ ] 60-second stress test passes
- [ ] No crashes under concurrent connections
- [ ] No resource leaks (memory stable)
- [ ] Concurrency issues identified and fixed

### Phase 5 (Performance)
- [ ] Single timer regardless of connection count
- [ ] Metrics collected once per tick (not N times)
- [ ] Slow clients disconnected without affecting fast clients

---

## Files to Create/Modify

| File | Action | Phase |
|------|--------|-------|
| `test/test_stream_body_integration.c` | NEW | 1 |
| `test/test_sse_format.valk` | NEW | 2 |
| `test/test_debug_handler.valk` | NEW | 3 |
| `test/stress/test_sse_concurrency.valk` | NEW | 4 |
| `src/modules/aio/debug-broadcaster.valk` | NEW | 5 |
| `src/modules/aio/debug.valk` | MODIFY | 5 |

---

## Notes

- Phase 1-4 must complete before Phase 5 - don't optimize broken code
- The user is seeing concurrency issues in manual testing - Phase 4 is critical
- `metrics/collect-delta` may need investigation for thread safety
- Stream close callbacks need careful verification for timing
