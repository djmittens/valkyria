# Runtime Coverage Improvement Plan

## Executive Summary

**Current State**: Runtime C code at 50.3% line coverage, 21 of 26 files failing 90% requirement
**Target State**: All runtime files at 90% line, 85% branch coverage
**Estimated Effort**: 6-8 weeks for systematic coverage improvement
**Priority**: CRITICAL - runtime robustness is foundational

## Problem Analysis

### Coverage Gap Breakdown

| Priority | Coverage Range | Files | Total LOC | Gap to 90% |
|----------|---------------|-------|-----------|------------|
| **P0 Critical** | 0-30% | 6 files | 2,092 | 60-90% |
| **P1 High** | 30-70% | 9 files | 15,823 | 20-60% |
| **P2 Medium** | 70-90% | 4 files | 3,180 | 5-20% |
| **P3 Passing** | 90%+ | 5 files | - | Maintain |

**Total Coverage Debt**: ~21,000 lines requiring new tests

### Root Causes

1. **Test Focus Mismatch**: Tests verify high-level functionality, not runtime robustness
2. **Error Path Neglect**: Happy paths covered, error recovery largely untested
3. **Subsystem Gaps**: Some features (SSE, metrics, debug) have minimal test coverage
4. **C vs Valk Testing**: Valk tests don't expose internal C runtime paths
5. **Integration Over Unit**: Most tests are end-to-end, missing granular C unit tests

## Strategic Approach

### Phase 1: Foundation (Weeks 1-2)
**Goal**: Enable rapid C unit test development

#### 1.1 Test Infrastructure
- [ ] Create `test/unit/` directory for C-level unit tests
- [ ] Add CMake support for unit test discovery
- [ ] Create test harness helpers in `test/testing.h`:
  - `ASSERT_LVAL_TYPE(lval, expected_type)`
  - `ASSERT_LVAL_NUM(lval, expected_num)`
  - `ASSERT_LVAL_ERROR(lval, expected_substr)`
  - `MOCK_AIO_CONTEXT()` for async testing
  - `MOCK_HTTP_RESPONSE(status, body)` for network testing

#### 1.2 Mock Infrastructure
- [ ] Create `test/mocks/` for stubbing complex dependencies
- [ ] Mock libuv callbacks: `mock_uv.c`
- [ ] Mock nghttp2 sessions: `mock_nghttp2.c`
- [ ] Mock SSL/TLS: `mock_ssl.c`
- [ ] Failure injection framework for error path testing

#### 1.3 Coverage Tooling
- [ ] Add per-file coverage target: `make coverage-file FILE=src/aio_sse.c`
- [ ] Create coverage diff tool: shows lines added/removed since last run
- [ ] Add coverage visualization: `bin/coverage-viz.py --file src/gc.c`

**Deliverable**: Test infrastructure enabling 10x faster C unit test development

---

## Phase 2: Critical Files (Weeks 3-4)
**Goal**: Bring 0-30% coverage files to 90%+

### P0.1: debug.c (0% → 90%)
**Current**: 0 lines covered
**Estimate**: 2 days

**Test Cases Needed**:
```c
// test/unit/test_debug.c
test_debug_print_stack_trace()
test_debug_signal_handler_segv()
test_debug_signal_handler_abort()
test_debug_format_backtrace()
test_debug_backtrace_with_symbols()
test_debug_backtrace_without_symbols()
```

**Approach**: Mock signal handlers, capture output, verify format

---

### P0.2: pool_metrics.c (0% → 90%)
**Current**: 0 lines covered
**Estimate**: 1 day

**Test Cases Needed**:
```c
// test/unit/test_pool_metrics.c
test_pool_metrics_init()
test_pool_metrics_alloc()
test_pool_metrics_free()
test_pool_metrics_total_allocated()
test_pool_metrics_total_freed()
test_pool_metrics_concurrent_updates()
```

**Approach**: Direct C unit tests with thread safety validation

---

### P0.3: aio_sse_builtins.c (6% → 90%)
**Current**: Only basic `sse/open` tested
**Estimate**: 3 days

**Test Cases Needed**:
```valk
;; test/test_sse_coverage.valk
(test/group "SSE Stream Lifecycle"
  (test "sse/open creates valid stream handle"
    (= {ctx} (mock-http-context))
    (= {stream} (sse/open ctx))
    (assert (sse/writable? stream)))
  
  (test "sse/send with valid data"
    (= {stream} (create-test-sse-stream))
    (assert-ok (sse/send stream "data" "hello")))
  
  (test "sse/send with event type"
    (= {stream} (create-test-sse-stream))
    (assert-ok (sse/send stream "event: custom\ndata: payload")))
  
  (test "sse/send to closed stream returns error"
    (= {stream} (create-test-sse-stream))
    (sse/close stream)
    (assert-error (sse/send stream "data" "fail")))
  
  (test "sse/on-drain callback invoked when writable"
    (= {stream} (create-backpressured-stream))
    (= {called} 0)
    (sse/on-drain stream (\ {} {(= {called} 1)}))
    (trigger-drain stream)
    (assert (== called 1)))
  
  (test "sse/writable? returns false when backpressured"
    (= {stream} (create-backpressured-stream))
    (assert (! (sse/writable? stream))))
  
  (test "sse/close idempotent"
    (= {stream} (create-test-sse-stream))
    (sse/close stream)
    (assert-ok (sse/close stream)))
)
```

**C Unit Tests**:
```c
// test/unit/test_sse_builtins.c
test_sse_builtin_error_invalid_args()
test_sse_builtin_error_wrong_type()
test_sse_builtin_error_null_context()
test_sse_send_format_validation()
test_sse_send_size_limits()
test_sse_cleanup_on_lval_free()
```

---

### P0.4: aio_sse_stream_registry.c (11.4% → 90%)
**Current**: Registry init only
**Estimate**: 2 days

**Test Cases**:
```c
// test/unit/test_sse_registry.c
test_registry_init()
test_registry_register_stream()
test_registry_unregister_stream()
test_registry_lookup_stream()
test_registry_lookup_nonexistent()
test_registry_concurrent_register()
test_registry_concurrent_unregister()
test_registry_full_lifecycle()
test_registry_cleanup_on_connection_close()
test_registry_iteration()
test_registry_max_streams()
```

---

### P0.5: aio_sse.c (17.6% → 90%)
**Current**: Basic stream creation
**Estimate**: 4 days

**Test Cases**:
```c
// test/unit/test_sse_core.c
test_sse_stream_create()
test_sse_stream_write_data()
test_sse_stream_write_event()
test_sse_stream_write_id()
test_sse_stream_write_retry()
test_sse_stream_flush()
test_sse_stream_backpressure()
test_sse_stream_resume_after_backpressure()
test_sse_stream_close()
test_sse_stream_error_handling()
test_sse_stream_memory_cleanup()
```

**Integration Tests**:
```valk
;; test/test_sse_integration.valk
(test/group "SSE End-to-End"
  (test "client receives SSE events"
    (= {server} (create-sse-test-server))
    (= {client} (create-sse-test-client))
    (= {events} ())
    (client-on-message client (\ {msg} {
      (= {events} (cons msg events))
    }))
    (server-send server "data: test1")
    (server-send server "data: test2")
    (wait-for-events client 2)
    (assert (== (len events) 2)))
)
```

---

### P0.6: concurrency.c (29.5% → 90%)
**Current**: Basic shift/reset only
**Estimate**: 5 days

**Test Cases**:
```c
// test/unit/test_concurrency.c
test_continuation_create()
test_continuation_capture()
test_continuation_restore()
test_continuation_nested()
test_continuation_multi_shot()
test_continuation_one_shot()
test_async_shift()
test_async_reset()
test_async_compose()
test_async_error_propagation()
test_continuation_stack_overflow()
test_continuation_memory_leak()
test_continuation_gc_interaction()
```

**Integration Tests**:
```valk
;; test/test_concurrency_suite.valk
(test/group "Delimited Continuations"
  (test "basic shift/reset"
    (= {result} (async-reset (\ {}
      (+ 1 (async-shift (\ {k} (k 5)))))))
    (assert (== result 6)))
  
  (test "multi-shot continuation"
    (= {results} ())
    (async-reset (\ {}
      (async-shift (\ {k}
        (= {results} (cons (k 1) results))
        (= {results} (cons (k 2) results))
        (k 3)))))
    (assert (== (len results) 2)))
  
  (test "nested shift/reset"
    (= {result} (async-reset (\ {}
      (+ 1 (async-reset (\ {}
        (+ 2 (async-shift (\ {k} (k 3))))))))))
    (assert (== result 6)))
  
  (test "error in continuation"
    (assert-error
      (async-reset (\ {}
        (async-shift (\ {k}
          (k (error "test error"))))))))
)
```

---

## Phase 3: High Priority Files (Weeks 5-6)
**Goal**: Bring 30-70% coverage files to 90%+

### P1.1: aio_uv.c (37.6% → 90%)
**Current**: Happy path HTTP only
**Estimate**: 7 days

**Major Gaps**:
- Connection failure paths
- SSL/TLS handshake errors
- Timeout handling
- Backpressure management
- Connection pool exhaustion
- DNS resolution failures

**Test Strategy**:
```c
// test/unit/test_aio_uv_errors.c
test_connection_refused()
test_connection_timeout()
test_dns_lookup_failure()
test_ssl_handshake_failure()
test_ssl_certificate_error()
test_read_timeout()
test_write_timeout()
test_connection_reset()
test_connection_closed_mid_request()
test_max_connections_exceeded()
test_memory_exhaustion()

// test/unit/test_aio_uv_backpressure.c
test_write_buffer_full()
test_backpressure_pause()
test_backpressure_resume()
test_backpressure_multiple_streams()

// test/unit/test_aio_uv_lifecycle.c
test_connection_create_destroy()
test_connection_reuse()
test_connection_cleanup_on_error()
test_graceful_shutdown()
test_forced_shutdown()
```

**Mock Strategy**:
- Inject failures via `mock_uv_tcp_connect` returning errors
- Control timing via `mock_uv_timer` for timeouts
- Simulate backpressure via `mock_uv_write` buffer limits

---

### P1.2: metrics_builtins.c (33.3% → 90%)
**Estimate**: 3 days

**Test Cases**:
```valk
;; test/test_metrics_comprehensive.valk
(test/group "Metrics Builtins"
  (test "counter increment"
    (= {c} (metrics/counter "test" "counter"))
    (metrics/counter-inc c)
    (metrics/counter-inc c)
    (= {json} (metrics/json))
    (assert (str-contains? json "\"test_counter\":2")))
  
  (test "gauge set/inc/dec"
    (= {g} (metrics/gauge "test" "gauge"))
    (metrics/gauge-set g 100)
    (metrics/gauge-inc g)
    (metrics/gauge-dec g)
    (= {json} (metrics/json))
    (assert (str-contains? json "\"test_gauge\":100")))
  
  (test "histogram observe"
    (= {h} (metrics/histogram "test" "histogram")}
    (metrics/histogram-observe h 1.5)
    (metrics/histogram-observe h 2.5)
    (metrics/histogram-observe h 3.5)
    (= {json} (metrics/json))
    (assert (str-contains? json "histogram")))
  
  (test "concurrent counter updates"
    (= {c} (metrics/counter "concurrent" "counter"))
    (= {threads} 10)
    (= {increments} 1000)
    (parallel-map (\ {i} {
      (repeat increments (\ {} (metrics/counter-inc c)))
    }) (range 1 threads))
    (= {expected} (* threads increments))
    (= {actual} (metrics-get-counter-value c))
    (assert (== actual expected)))
)
```

---

### P1.3: metrics_delta.c (35.2% → 90%)
**Estimate**: 3 days

**Focus**: Delta aggregation logic, overflow handling, concurrent access

---

### P1.4: event_loop_metrics.c (42.6% → 90%)
**Estimate**: 2 days

**Focus**: Event loop latency tracking, queue depth, tick duration

---

### P1.5: aio_ssl.c (60.0% → 90%)
**Estimate**: 4 days

**Test Cases**:
```c
// test/unit/test_ssl_errors.c
test_ssl_handshake_timeout()
test_ssl_certificate_expired()
test_ssl_certificate_invalid()
test_ssl_certificate_self_signed()
test_ssl_protocol_error()
test_ssl_renegotiation()
test_ssl_cipher_mismatch()
test_ssl_hostname_verification()
test_ssl_alpn_negotiation()
```

---

### P1.6-P1.9: Remaining High Priority
- **source_loc.c** (60.6% → 90%): 2 days
- **memory.c** (67.8% → 90%): 4 days
- **parser.c** (66.9% → 90%): 5 days
- **aio_metrics.c** (63.5% → 90%): 3 days

---

## Phase 4: Medium Priority Files (Week 7)
**Goal**: Final push to 90%+

### P2 Files (70-90% coverage)
- **gc.c** (79.0% → 90%): 2 days - Add cycle detection, large object tests
- **log.c** (69.8% → 90%): 2 days - Error path logging, concurrent writes
- **coverage.c** (73.0% → 90%): 1 day - Edge cases in expression tracking
- **aio_alloc.c** (84.8% → 90%): 1 day - OOM scenarios, alignment edge cases

---

## Phase 5: Maintenance & Automation (Week 8)

### 5.1 CI Integration
- [ ] Enable coverage requirements in CI (currently disabled)
- [ ] Block PRs that reduce coverage
- [ ] Generate coverage reports on all PRs
- [ ] Add coverage badges to README

### 5.2 Documentation
- [ ] Update TESTING.md with new test patterns
- [ ] Create TEST_WRITING_GUIDE.md with examples
- [ ] Document mock usage patterns
- [ ] Add coverage improvement playbook

### 5.3 Monitoring
- [ ] Track coverage trends over time
- [ ] Alert on coverage regressions
- [ ] Weekly coverage reports
- [ ] Per-subsystem dashboards

---

## Test Development Guidelines

### Principle 1: Test C Code in C
**Don't**: Write Valk tests hoping they hit C paths
**Do**: Write direct C unit tests for runtime functions

```c
// GOOD: Direct unit test
void test_gc_mark_cycles(void) {
  valk_lenv_t *env = valk_lenv_new();
  valk_lval_t *a = valk_lval_qexpr();
  valk_lval_t *b = valk_lval_qexpr();
  valk_lval_add(a, b);
  valk_lval_add(b, a);  // Create cycle
  valk_gc_collect();     // Should not crash
  ASSERT_GC_COLLECTED(a);
}
```

### Principle 2: Test Error Paths Explicitly
**Don't**: Assume error paths work if happy path passes
**Do**: Write dedicated error path tests

```c
// GOOD: Explicit error testing
void test_http_connection_timeout(void) {
  mock_uv_tcp_connect_set_error(UV_ETIMEDOUT);
  valk_lval_t *result = make_http_request("example.com", 443, "/");
  ASSERT_LVAL_ERROR(result, "connection timeout");
}
```

### Principle 3: Use Mocks for External Dependencies
**Don't**: Rely on actual network/SSL/file I/O in tests
**Do**: Mock external systems for deterministic testing

```c
// GOOD: Mocked dependencies
void test_ssl_handshake_failure(void) {
  mock_ssl_connect_set_error(SSL_ERROR_PROTOCOL);
  valk_lval_t *result = connect_ssl("example.com", 443);
  ASSERT_LVAL_ERROR(result, "SSL protocol error");
}
```

### Principle 4: Test Concurrency Explicitly
**Don't**: Hope concurrent code works without testing it
**Do**: Write multi-threaded stress tests

```c
// GOOD: Concurrent stress test
void test_metrics_concurrent_updates(void) {
  valk_metric_counter_t *counter = valk_metric_counter_new("test");
  pthread_t threads[10];
  for (int i = 0; i < 10; i++) {
    pthread_create(&threads[i], NULL, increment_counter, counter);
  }
  for (int i = 0; i < 10; i++) {
    pthread_join(threads[i], NULL);
  }
  ASSERT_COUNTER_VALUE(counter, 10000);
}
```

### Principle 5: Test Resource Cleanup
**Don't**: Forget to test memory leaks and resource exhaustion
**Do**: Verify cleanup in error paths

```c
// GOOD: Cleanup verification
void test_connection_cleanup_on_error(void) {
  size_t mem_before = valk_heap_usage();
  mock_uv_tcp_connect_set_error(UV_ECONNREFUSED);
  valk_lval_t *result = make_http_request("example.com", 443, "/");
  valk_lval_del(result);
  size_t mem_after = valk_heap_usage();
  ASSERT_EQ(mem_before, mem_after);  // No leak
}
```

---

## Success Metrics

### Primary Metrics
- **Runtime Coverage**: 50.3% → 90.0% line (target)
- **Branch Coverage**: 34.0% → 85.0% (target)
- **Passing Files**: 5/26 → 26/26

### Secondary Metrics
- **Test Count**: ~60 tests → ~300 tests
- **C Unit Tests**: 18 files → 50+ files
- **Error Path Coverage**: ~20% → 85%
- **Concurrency Tests**: ~5 → ~30

### Quality Metrics
- **Bugs Found**: Track runtime bugs discovered during test development
- **Test Execution Time**: Keep under 5 minutes for full suite
- **Flaky Tests**: Zero tolerance for non-deterministic tests
- **Code Coverage Per PR**: New code must meet 90% requirement

---

## Risk Mitigation

### Risk 1: Test Development Slower Than Expected
**Mitigation**: 
- Start with smallest files (debug.c, pool_metrics.c)
- Build reusable test infrastructure first
- Parallelize work across files

### Risk 2: Mocking Too Complex
**Mitigation**:
- Use real components where feasible
- Invest in mock framework early (Phase 1)
- Document mock patterns thoroughly

### Risk 3: Coverage vs Quality Tradeoff
**Mitigation**:
- Don't chase meaningless coverage (e.g., `COVERAGE_EXEMPT` for unreachable code)
- Focus on high-value paths: error handling, concurrency, resource cleanup
- Require code review for all new tests

### Risk 4: Test Maintenance Burden
**Mitigation**:
- Keep tests simple and focused
- Avoid over-mocking (prefer integration where possible)
- Establish test naming conventions
- Use test harness helpers to reduce boilerplate

---

## Estimated Timeline

```
Week 1-2: Test Infrastructure
├─ Unit test framework
├─ Mock infrastructure  
├─ Coverage tooling
└─ Documentation

Week 3-4: Critical Files (P0)
├─ debug.c, pool_metrics.c
├─ aio_sse_*.c
└─ concurrency.c

Week 5-6: High Priority Files (P1)
├─ aio_uv.c
├─ metrics_*.c
├─ parser.c, memory.c
└─ aio_ssl.c

Week 7: Medium Priority Files (P2)
├─ gc.c
├─ log.c
├─ coverage.c
└─ aio_alloc.c

Week 8: Polish & Automation
├─ CI integration
├─ Documentation
└─ Monitoring
```

---

## Resource Requirements

### Engineering Time
- **1 Senior Engineer**: 6-8 weeks full-time
- **OR 2 Engineers**: 4 weeks full-time
- **Code Review**: 5-10 hours/week

### Infrastructure
- **CI Compute**: +30% for coverage builds
- **Storage**: +500MB for coverage artifacts

### Tooling
- No new external dependencies
- Leverage existing: gcov, lcov, Python

---

## Next Steps

1. **Review & Approve Plan**: Engineering lead sign-off
2. **Allocate Resources**: Assign engineer(s) to coverage improvement
3. **Setup Tracking**: Create GitHub project board with all tasks
4. **Start Phase 1**: Test infrastructure (2 weeks)
5. **Weekly Check-ins**: Review progress, adjust timeline
6. **Celebrate**: 90% coverage is a major milestone!

---

## Conclusion

Bringing runtime coverage from 50% to 90% is **achievable but requires sustained focus**. The systematic approach above balances:
- **Quick wins** (P0 files are small and isolated)
- **High impact** (P1 files cover majority of LOC)
- **Sustainability** (infrastructure investment pays off long-term)

**The alternative** - continuing with 50% coverage - is **unacceptable for a production runtime**. Every untested line is a potential production outage.

**The payoff** - 90% coverage brings:
- ✅ Confidence in error handling
- ✅ Safety for refactoring
- ✅ Protection against regressions
- ✅ Production-ready robustness

This is not optional work. This is **foundational engineering** for a language runtime.
