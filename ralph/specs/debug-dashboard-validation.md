# Debug Dashboard Validation

## Overview

Build trust in the debug dashboard SSE system through comprehensive testing at all architecture layers. Manual testing reveals concurrency issues and the system lacks test coverage at critical layers. This spec establishes correctness from the bottom up (stream infrastructure → SSE format → debug handler) before optimizing with a shared broadcaster.

## Requirements

### Architecture Layers

```
┌─────────────────────────────────────────────────────────────────┐
│ Layer 4: Dashboard JavaScript (script.js)         - NO TESTS    │
├─────────────────────────────────────────────────────────────────┤
│ Layer 3: Debug Handler (debug.valk)               - 1 test      │
├─────────────────────────────────────────────────────────────────┤
│ Layer 2: SSE Wrapper (sse.valk)                   - 55 tests    │
├─────────────────────────────────────────────────────────────────┤
│ Layer 1: Stream Builtins (aio_stream_builtins.c)  - 58 tests    │
├─────────────────────────────────────────────────────────────────┤
│ Layer 0: Stream Body (aio_stream_body.c)          - 47 tests    │
└─────────────────────────────────────────────────────────────────┘
```

**Trust must be built bottom-up.** Fix and test foundational layers before optimizing higher layers.

### Known Issues

| Issue | Layer | Severity |
|-------|-------|----------|
| Concurrency problems in manual testing | TBD | High |
| Per-connection timers create O(N) overhead | 3 | Medium |
| No tests for SSE wire format correctness | 2 | Medium |
| Debug handler has only 1 integration test | 3 | Medium |
| Stream body integration paths untested | 0-1 | High |

### SSE Wire Format Specification

| Function | Input | Expected Output |
|----------|-------|-----------------|
| `sse/send` | `"hello"` | `"data: hello\n\n"` |
| `sse/send` | `"a\nb"` | `"data: a\ndata: b\n\n"` |
| `sse/send` | `""` | `"data: \n\n"` |
| `sse/event` | `"msg" "data"` | `"event: msg\ndata: data\n\n"` |
| `sse/event` | `"msg" "a\nb"` | `"event: msg\ndata: a\ndata: b\n\n"` |
| `sse/id` | `"123" "data"` | `"id: 123\ndata: data\n\n"` |
| `sse/full` | `"msg" "123" "data"` | `"id: 123\nevent: msg\ndata: data\n\n"` |
| `sse/retry` | `5000` | `"retry: 5000\n\n"` |
| `sse/comment` | `"ping"` | `": ping\n"` |
| `sse/heartbeat` | (none) | `":\n"` |

### Debug Handler Routes

| Route | Response Type | Description |
|-------|---------------|-------------|
| `/debug` | HTML | Dashboard page |
| `/debug/` | HTML | Dashboard page |
| `/debug/metrics` | JSON | Current metrics snapshot |
| `/debug/metrics/state` | JSON | Full state with `metrics.aio`, `metrics.modular`, `metrics.vm`, `metrics.registry`, `memory` |
| `/metrics` | Text | Prometheus exposition format |
| `/debug/diagnostics/memory` | SSE | First event: `diagnostics` (full), then `diagnostics-delta` |
| `/debug/slab/buckets` | JSON | Slab allocator bucket info |
| Unknown routes | Redirect | 302 to `/debug/` |

### Global Timer Broadcaster Design (Phase 5)

Replace per-connection timers with single shared timer:

```
┌─────────────────────────────────────────────────────────┐
│                  BROADCASTER                             │
│                                                          │
│  ┌──────────┐     ┌─────────────────────────────────┐   │
│  │  Timer   │────>│     Collect Metrics Once        │   │
│  │ (100ms)  │     │     Broadcast to All            │   │
│  └──────────┘     └─────────────────────────────────┘   │
│                              │                           │
│         ┌────────────────────┼────────────────────┐     │
│         v                    v                    v     │
│    ┌─────────┐         ┌─────────┐         ┌─────────┐ │
│    │ Stream1 │         │ Stream2 │         │ Stream3 │ │
│    │baseline1│         │baseline2│         │baseline3│ │
│    └─────────┘         └─────────┘         └─────────┘ │
└─────────────────────────────────────────────────────────┘
```

**API:**
- `debug/subscribe sys stream` - Add to list, start timer if first subscriber
- `debug/unsubscribe stream` - Remove from list, stop timer if last subscriber
- Auto-unsubscribe on stream close

**Backpressure:**
- Track consecutive failed writes per subscriber
- Disconnect after 10 failures (1 second at 100ms tick)
- Log disconnection

### Files to Create/Modify

| File | Action | Phase |
|------|--------|-------|
| `test/test_stream_body_integration.c` | NEW | 1 |
| `test/test_sse_format.valk` | NEW | 2 |
| `test/test_debug_handler.valk` | NEW | 3 |
| `test/stress/test_sse_concurrency.valk` | NEW | 4 |
| `src/modules/aio/debug-broadcaster.valk` | NEW | 5 |
| `src/modules/aio/debug.valk` | MODIFY | 5 |

### Phase Dependencies

```
Phase 1 ──┐
          ├──> Phase 4 ──> Phase 5
Phase 2 ──┤
          │
Phase 3 ──┘
```

Phases 1-3 can run in parallel. Phase 4 requires all of 1-3. Phase 5 requires Phase 4.

## Acceptance Criteria

### Phase 1: Stream Infrastructure
- [ ] `test/test_stream_body_integration.c` exists
- [ ] Integration test verifies write queues data, read callback dequeues
- [ ] Integration test verifies close triggers on-close callback
- [ ] Integration test verifies backpressure when queue full
- [ ] Test verifies no crash when write during connection close (run under ASAN)
- [ ] Test verifies no use-after-free on connection close (run under ASAN)
- [ ] Test verifies concurrent writes deliver data in order without corruption
- [ ] Test verifies on-close callback fires exactly once
- [ ] Test verifies on-close callback fires before stream body freed
- [ ] All tests pass under TSAN with no warnings

### Phase 2: SSE Wire Format
- [ ] `test/test_sse_format.valk` exists
- [ ] `sse/send` produces correct wire format for simple string
- [ ] `sse/send` produces correct wire format for multi-line string
- [ ] `sse/send` produces correct wire format for empty string
- [ ] `sse/event` produces correct wire format
- [ ] `sse/id` produces correct wire format
- [ ] `sse/full` produces correct wire format
- [ ] `sse/retry` produces correct wire format
- [ ] `sse/comment` produces correct wire format
- [ ] `sse/heartbeat` produces correct wire format

### Phase 3: Debug Handler
- [ ] `test/test_debug_handler.valk` exists
- [ ] Test verifies all routes return correct handler (see Routes table)
- [ ] Test verifies unknown routes redirect to `/debug/`
- [ ] Test verifies `/debug/metrics/state` JSON has required keys
- [ ] Test verifies `/debug/diagnostics/memory` first event is `diagnostics`
- [ ] Test verifies subsequent events are `diagnostics-delta`
- [ ] Test verifies SSE events are valid JSON
- [ ] Test verifies timer stops after client disconnect
- [ ] Test verifies reconnect works after disconnect
- [ ] Test verifies `/metrics` contains expected metric names in Prometheus format

### Phase 4: Concurrency
- [ ] `test/stress/test_sse_concurrency.valk` exists
- [ ] 10 concurrent SSE connections handled without crash
- [ ] Rapid connect/disconnect cycles (60 seconds) handled without crash
- [ ] No resource leaks (memory stable during stress test)
- [ ] Delta baseline isolation verified (two connections see correct individual deltas)
- [ ] TSAN stress test shows no data races
- [ ] ASAN stress test shows no memory errors
- [ ] All concurrency issues identified and fixed with regression tests

### Phase 5: Global Timer
- [ ] `src/modules/aio/debug-broadcaster.valk` exists
- [ ] Single timer runs regardless of connection count
- [ ] Metrics collected once per tick (not N times for N connections)
- [ ] Each subscriber maintains independent delta baseline
- [ ] First event sends full state, subsequent events send delta
- [ ] Timer starts on first subscribe, stops on last unsubscribe
- [ ] Slow subscribers (10 consecutive write failures) auto-disconnected
- [ ] Fast subscribers unaffected by slow subscriber disconnection
- [ ] `src/modules/aio/debug.valk` updated to use broadcaster
- [ ] Dashboard still functions correctly after refactor
