# Detailed Coverage Improvement Plan

## Executive Summary

**Current State (Dec 2024):**
- Runtime C code: **67.5% line coverage** (target: 90%)
- Branch coverage: **48.7%** (target: 85%)
- Stdlib Valk code: **97.8% expr** (target: 90%) ✅
- **18 files failing** coverage requirements

**Key Principle**: Prioritize integration tests with real connections/resources over mocking.

## Current Coverage by File (Sorted by Priority)

### Critical Priority (P0) - Under 50% Line Coverage

| File | Line % | Branch % | LOC | Gap |
|------|--------|----------|-----|-----|
| `aio_uv.c` | **40.0%** | 25.8% | 3,799 | -50.0% |
| `aio_sse_stream_registry.c` | **49.9%** | 41.7% | 369 | -40.1% |

### High Priority (P1) - 50-80% Line Coverage

| File | Line % | Branch % | LOC | Gap |
|------|--------|----------|-----|-----|
| `aio_sse_diagnostics.c` | 66.9% | 45.8% | 1,464 | -23.1% |
| `aio_ssl.c` | 70.8% | 60.4% | 240 | -19.2% |
| `parser.c` | 74.9% | 48.9% | 2,816 | -15.1% |
| `metrics_v2.c` | 78.4% | 55.8% | 399 | -11.6% |
| `aio_sse.c` | 79.2% | 71.6% | 221 | -10.8% |
| `coverage.c` | 79.3% | 64.8% | 430 | -10.7% |

### Medium Priority (P2) - 80-90% Line Coverage

| File | Line % | Branch % | LOC | Gap |
|------|--------|----------|-----|-----|
| `gc.c` | 83.1% | 67.4% | 1,291 | -6.9% |
| `memory.c` | 84.4% | 64.0% | 410 | -5.6% |
| `event_loop_metrics.c` | 85.2% | 63.2% | 54 | -4.8% |
| `aio_sse_builtins.c` | 87.3% | 79.7% | 134 | -2.7% |
| `concurrency.c` | 87.7% | 50.6% | 268 | -2.3% |

### Branch-Only Failures (Line ≥90%, Branch <85%)

| File | Line % | Branch % | Gap |
|------|--------|----------|-----|
| `aio_alloc.c` | 93.5% | 66.7% | -18.3% branch |
| `aio_metrics.c` | 94.3% | 72.9% | -12.1% branch |
| `metrics_delta.c` | 99.8% | 66.5% | -18.5% branch |
| `debug.c` | 100.0% | 62.5% | -22.5% branch |

---

## Phase 1: Critical Priority Files (Week 1-2)

### 1.1 aio_uv.c (40% → 90%) - Estimated 7 days

**This is the largest file with lowest coverage - all async I/O lives here.**

#### Uncovered Code Paths:

1. **Backpressure Management** (lines 376-520)
   - `__backpressure_list_add()` / `__backpressure_list_remove()`
   - `__backpressure_try_resume_one()` / `__backpressure_timer_cb()`

2. **Pending Stream Pool** (lines 553-620)
   - Stream queuing under high load

3. **HTTP/2 Client Functions** (lines 3477+)
   - `__http_client_on_frame_recv_callback()`
   - `__http_client_on_stream_close_callback()`

4. **TLS/ALPN Handling** (lines 3276-3290)
   - `__alpn_select_proto_cb()` - Protocol negotiation

5. **Connection Lifecycle Edge Cases**
   - Error paths in connection establishment
   - SSL handshake failures
   - Connection timeout handling

#### Integration Tests (Real Connections):

```c
// test/integration/test_aio_uv_real.c

// Test 1: Concurrent connection load
void test_concurrent_connections_100() {
  valk_aio_t *aio = create_test_aio_system();
  start_test_https_server(8500);
  
  // Fire 100 concurrent requests
  for (int i = 0; i < 100; i++) {
    valk_http_client_request(aio, "127.0.0.1", 8500, "/test", on_response, NULL);
  }
  
  run_until_complete(aio, 100);
  ASSERT_EQ(responses_received, 100);
  ASSERT_EQ(errors_received, 0);
}

// Test 2: Backpressure under slow client
void test_backpressure_slow_client() {
  valk_aio_t *aio = create_test_aio_system();
  start_test_https_server_with_slow_client(8501); // Server delays reads
  
  // Send many events that will queue up
  for (int i = 0; i < 10000; i++) {
    valk_sse_send(stream, "data", "event");
  }
  
  // Verify backpressure activated
  ASSERT_FALSE(valk_sse_is_writable(stream));
  
  // Resume client, verify recovery
  resume_slow_client();
  run_until(aio, valk_sse_is_writable(stream));
  ASSERT_TRUE(valk_sse_is_writable(stream));
}

// Test 3: Connection failure handling
void test_connection_refused() {
  valk_aio_t *aio = create_test_aio_system();
  // No server running on this port
  
  valk_http_client_request(aio, "127.0.0.1", 9999, "/", on_response, NULL);
  run_until_complete(aio, 1);
  
  ASSERT_EQ(errors_received, 1);
  ASSERT_STR_CONTAINS(last_error, "ECONNREFUSED");
}

// Test 4: SSL handshake timeout
void test_ssl_handshake_timeout() {
  valk_aio_t *aio = create_test_aio_system();
  start_hanging_ssl_server(8502); // Accepts but never completes handshake
  
  valk_http_client_request(aio, "127.0.0.1", 8502, "/", on_response, NULL);
  
  // Wait for timeout (default 30s, use shorter in test)
  run_with_timeout(aio, 5000); // 5s timeout
  
  ASSERT_EQ(errors_received, 1);
  ASSERT_STR_CONTAINS(last_error, "timeout");
}

// Test 5: Large response streaming (50MB+)
void test_large_response_streaming() {
  valk_aio_t *aio = create_test_aio_system();
  start_test_https_server(8503);
  
  size_t total_received = 0;
  valk_http_client_request(aio, "127.0.0.1", 8503, "/large-50mb",
    on_data_chunk, &total_received);
  
  run_until_complete(aio, 1);
  
  ASSERT_EQ(total_received, 50 * 1024 * 1024);
}

// Test 6: HTTP/2 multiplexing
void test_http2_multiplexing() {
  valk_aio_t *aio = create_test_aio_system();
  start_test_https_server(8504);
  
  // Single connection, multiple streams
  valk_http2_connection_t *conn = valk_http2_connect(aio, "127.0.0.1", 8504);
  
  for (int i = 0; i < 100; i++) {
    valk_http2_request(conn, "/stream", on_response, NULL);
  }
  
  run_until_complete(aio, 100);
  ASSERT_EQ(responses_received, 100);
  // Verify single TCP connection used
  ASSERT_EQ(connection_count(), 1);
}
```

#### Valk Integration Tests:

```lisp
;; test/test_aio_uv_integration.valk

(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "AIO Real Connection Tests")

;; Test server that echoes back
(def TEST_PORT 8510)

(test/define "concurrent-fetch-10-requests"
  {do
    (= {aio} (aio/start))
    (= {server} (http2/server aio TEST_PORT
      (\ {ctx} {(http2/respond ctx 200 "ok")})))
    
    (= {responses} ())
    (= {pending} 10)
    
    ;; Fire 10 concurrent requests
    (map (\ {i} {
      (http2/client-request aio "127.0.0.1" TEST_PORT "/"
        (\ {resp} {
          (= {responses} (cons resp responses))
          (= {pending} (- pending 1))
          (if (== pending 0) {(aio/stop aio)} {nil})
        }))
    }) (range 1 10))
    
    (aio/run aio)
    (test/assert (== (len responses) 10) "Should receive 10 responses")
    true
  })

(test/define "handles-connection-refused"
  {do
    (= {aio} (aio/start))
    (= {got-error} false)
    
    ;; Connect to port with no server
    (http2/client-request aio "127.0.0.1" 59999 "/"
      (\ {resp} {
        (if (error? resp)
          {(= {got-error} true)}
          {nil})
        (aio/stop aio)
      }))
    
    (aio/run aio)
    (test/assert got-error "Should receive connection error")
    true
  })

(test/define "sse-backpressure-detection"
  {do
    (= {aio} (aio/start))
    (= {stream} nil)
    (= {writable-initially} nil)
    
    (= {server} (http2/server aio 8511
      (\ {ctx} {
        (= {stream} (sse/open ctx))
        (= {writable-initially} (sse/writable? stream))
        ;; Send many events to trigger backpressure
        (map (\ {i} {(sse/send stream "data" (str "event-" i))}) (range 1 1000))
        nil
      })))
    
    ;; Make request that triggers SSE stream
    (http2/client-request aio "127.0.0.1" 8511 "/" (\ {r} {(aio/stop aio)}))
    (aio/delay aio 100 (\ {} {(aio/stop aio)}))
    (aio/run aio)
    
    (test/assert writable-initially "Stream should be writable initially")
    true
  })

(test/run {})
```

### 1.2 aio_sse_stream_registry.c (49.9% → 90%) - Estimated 2 days

#### Uncovered Code Paths:

1. **Registry Timer Callback** (`sse_registry_timer_cb()`, line 347+)
2. **Data Read Callback** (`sse_registry_data_read_callback()`, line 418+)
3. **Subscription Management** - partial coverage
4. **Timer Start/Stop** (lines 633-680)

#### Integration Tests:

```c
// test/integration/test_sse_registry_real.c

void test_sse_registry_with_real_timer() {
  valk_aio_t *aio = create_test_aio_system();
  valk_sse_registry_t *reg = valk_sse_registry_new(aio);
  
  // Start timer (triggers sse_registry_timer_cb)
  valk_sse_registry_timer_start(reg, 10); // 10ms interval
  
  // Subscribe to updates
  int callback_count = 0;
  valk_sse_registry_subscribe(reg, "test-topic", on_update, &callback_count);
  
  // Let timer fire several times
  run_for_ms(aio, 100);
  
  ASSERT_GT(callback_count, 5);
  
  valk_sse_registry_timer_stop(reg);
  valk_sse_registry_free(reg);
}

void test_sse_registry_multiple_subscribers() {
  valk_aio_t *aio = create_test_aio_system();
  valk_sse_registry_t *reg = valk_sse_registry_new(aio);
  
  int counts[10] = {0};
  
  // 10 subscribers
  for (int i = 0; i < 10; i++) {
    valk_sse_registry_subscribe(reg, "topic", increment_counter, &counts[i]);
  }
  
  // Publish event
  valk_sse_registry_publish(reg, "topic", "data");
  
  // Verify all subscribers received
  for (int i = 0; i < 10; i++) {
    ASSERT_EQ(counts[i], 1);
  }
}

void test_sse_registry_unsubscribe_on_disconnect() {
  valk_aio_t *aio = create_test_aio_system();
  start_test_https_server(8520);
  
  valk_sse_registry_t *reg = valk_sse_registry_new(aio);
  
  // Simulate client connection
  valk_http2_connection_t *conn = simulate_client_connection(aio, 8520);
  valk_sse_registry_subscribe_connection(reg, conn, "topic");
  
  ASSERT_EQ(valk_sse_registry_subscriber_count(reg, "topic"), 1);
  
  // Simulate disconnect
  simulate_client_disconnect(conn);
  
  // Subscriber should be removed
  ASSERT_EQ(valk_sse_registry_subscriber_count(reg, "topic"), 0);
}
```

---

## Phase 2: High Priority Files (Week 3-4)

### 2.1 aio_sse_diagnostics.c (66.9% → 90%) - Estimated 3 days

#### Uncovered Areas:
- JSON formatting for complex types
- RLE bitmap encoding optimization paths
- Linux-specific `/proc/self/smaps` parsing
- GC tier formatting (multi-tier statistics)

#### Integration Tests:

```c
// test/integration/test_diagnostics_real.c

void test_diagnostics_full_snapshot_with_gc() {
  valk_gc_t *gc = create_test_gc();
  valk_aio_t *aio = create_test_aio_system();
  
  // Allocate various objects
  for (int i = 0; i < 1000; i++) {
    valk_lval_num(i);
    valk_lval_str("test string");
    valk_lval_qexpr();
  }
  
  // Trigger GC
  valk_gc_collect(gc);
  
  // Collect full snapshot
  valk_diag_snapshot_t *snap = valk_diag_snapshot_collect(aio, gc);
  
  // Format as JSON
  char *json = valk_diag_format_json(snap);
  
  // Verify JSON structure
  ASSERT_STR_CONTAINS(json, "\"gc\":");
  ASSERT_STR_CONTAINS(json, "\"memory\":");
  ASSERT_STR_CONTAINS(json, "\"slab\":");
  
  free(json);
  valk_diag_snapshot_free(snap);
}

void test_diagnostics_delta_encoding() {
  valk_aio_t *aio = create_test_aio_system();
  
  // First snapshot
  valk_diag_snapshot_t *snap1 = valk_diag_snapshot_collect(aio, NULL);
  
  // Make changes
  for (int i = 0; i < 100; i++) {
    valk_lval_num(i);
  }
  
  // Second snapshot
  valk_diag_snapshot_t *snap2 = valk_diag_snapshot_collect(aio, NULL);
  
  // Compute delta
  valk_diag_delta_t *delta = valk_diag_compute_delta(snap1, snap2);
  
  // Delta should be smaller than full snapshot
  size_t delta_size = valk_diag_delta_size(delta);
  size_t full_size = valk_diag_snapshot_size(snap2);
  ASSERT_LT(delta_size, full_size);
}

void test_rle_bitmap_encoding() {
  // Create bitmap with long runs
  uint8_t bitmap[1024] = {0};
  memset(bitmap, 0xFF, 512);  // First half all 1s
  // Second half all 0s
  
  // Encode with RLE
  size_t encoded_size;
  uint8_t *encoded = valk_diag_rle_encode(bitmap, 1024, &encoded_size);
  
  // Should be much smaller than original
  ASSERT_LT(encoded_size, 100);
  
  // Decode and verify
  uint8_t *decoded = valk_diag_rle_decode(encoded, encoded_size, 1024);
  ASSERT_MEM_EQ(decoded, bitmap, 1024);
}
```

### 2.2 aio_ssl.c (70.8% → 90%) - Estimated 3 days

#### Uncovered Areas:
- SSL error handling paths
- Certificate verification failures
- Handshake retry logic
- Non-blocking I/O edge cases

#### Integration Tests:

```c
// test/integration/test_ssl_real.c

void test_ssl_valid_certificate() {
  valk_aio_t *aio = create_test_aio_system();
  
  // Server with valid self-signed cert
  SSL_CTX *ctx = create_test_ssl_ctx("test/certs/valid.pem", "test/certs/valid.key");
  start_ssl_server(aio, 8530, ctx);
  
  // Client should connect successfully
  valk_ssl_connection_t *conn = valk_ssl_connect(aio, "127.0.0.1", 8530);
  run_until_connected(aio, conn);
  
  ASSERT_TRUE(valk_ssl_is_connected(conn));
  ASSERT_EQ(valk_ssl_get_error(conn), SSL_ERROR_NONE);
}

void test_ssl_expired_certificate() {
  valk_aio_t *aio = create_test_aio_system();
  
  // Server with expired cert
  SSL_CTX *ctx = create_test_ssl_ctx("test/certs/expired.pem", "test/certs/expired.key");
  start_ssl_server(aio, 8531, ctx);
  
  // Client with verification enabled
  valk_ssl_connection_t *conn = valk_ssl_connect_verify(aio, "127.0.0.1", 8531);
  run_until_error_or_connected(aio, conn);
  
  ASSERT_FALSE(valk_ssl_is_connected(conn));
  ASSERT_EQ(valk_ssl_get_error(conn), SSL_ERROR_CERTIFICATE_EXPIRED);
}

void test_ssl_hostname_mismatch() {
  valk_aio_t *aio = create_test_aio_system();
  
  // Cert is for "localhost", connect to "127.0.0.1"
  SSL_CTX *ctx = create_test_ssl_ctx("test/certs/localhost.pem", "test/certs/localhost.key");
  start_ssl_server(aio, 8532, ctx);
  
  // Client with hostname verification
  valk_ssl_connection_t *conn = valk_ssl_connect_hostname(aio, "wrong.example.com", 8532);
  run_until_error_or_connected(aio, conn);
  
  ASSERT_FALSE(valk_ssl_is_connected(conn));
}

void test_ssl_alpn_negotiation() {
  valk_aio_t *aio = create_test_aio_system();
  
  // Server supporting h2 and http/1.1
  SSL_CTX *ctx = create_test_ssl_ctx_with_alpn("h2,http/1.1");
  start_ssl_server(aio, 8533, ctx);
  
  // Client requesting h2
  valk_ssl_connection_t *conn = valk_ssl_connect_alpn(aio, "127.0.0.1", 8533, "h2");
  run_until_connected(aio, conn);
  
  const char *negotiated = valk_ssl_get_alpn_protocol(conn);
  ASSERT_STR_EQ(negotiated, "h2");
}
```

### 2.3 parser.c (74.9% → 90%) - Estimated 4 days

#### Uncovered Areas:
- Quasiquote expansion edge cases
- Less common string escape sequences
- Environment deep copy
- Type checking error paths

#### Integration Tests:

```lisp
;; test/test_parser_edge_cases.valk

(test/suite "Parser Edge Cases")

;; Quasiquote tests
(test/define "quasiquote-nested-unquote-splice"
  {do
    (= {inner} '(1 2 3))
    (= {result} `(a ,@inner b))
    (test/assert-eq result '(a 1 2 3 b) "Nested unquote-splice")
    true
  })

(test/define "quasiquote-deeply-nested"
  {do
    (= {x} 1)
    (= {result} `(a `(b ,,x c) d))
    ;; Result should be (a `(b ,1 c) d)
    (test/assert (list? result) "Should be list")
    true
  })

;; String escape sequences
(test/define "string-escape-tab"
  {do
    (= {s} "hello\tworld")
    (test/assert (== (len s) 11) "Tab is single char")
    true
  })

(test/define "string-escape-carriage-return"
  {do
    (= {s} "line1\r\nline2")
    (test/assert (== (len s) 12) "CRLF is two chars")
    true
  })

;; Error paths
(test/define "eval-invalid-function-call"
  {do
    (= {result} (try (eval '(123 456)) (\ {e} {e})))
    (test/assert (error? result) "Should error on invalid call")
    true
  })

(test/define "eval-undefined-symbol"
  {do
    (= {result} (try (eval 'undefined_symbol_xyz) (\ {e} {e})))
    (test/assert (error? result) "Should error on undefined symbol")
    true
  })

(test/run {})
```

### 2.4 metrics_v2.c (78.4% → 90%) - Estimated 2 days

#### Uncovered Areas:
- Histogram bucket boundary edge cases
- Overflow handling
- Large metric sets
- Label escaping for special characters

#### Integration Tests:

```c
// test/integration/test_metrics_real.c

void test_histogram_boundary_values() {
  valk_metrics_t *m = valk_metrics_new();
  valk_histogram_t *h = valk_histogram_new(m, "latency", "ms");
  
  // Test boundary values
  valk_histogram_observe(h, 0.0);
  valk_histogram_observe(h, DBL_MIN);
  valk_histogram_observe(h, DBL_MAX);
  valk_histogram_observe(h, INFINITY);
  
  // Should not crash, histogram should have valid state
  char *prom = valk_metrics_prometheus(m);
  ASSERT_NOT_NULL(prom);
  ASSERT_STR_CONTAINS(prom, "latency_count 4");
}

void test_metrics_concurrent_updates() {
  valk_metrics_t *m = valk_metrics_new();
  valk_counter_t *c = valk_counter_new(m, "requests", "total");
  
  pthread_t threads[10];
  for (int i = 0; i < 10; i++) {
    pthread_create(&threads[i], NULL, increment_counter_1000, c);
  }
  
  for (int i = 0; i < 10; i++) {
    pthread_join(threads[i], NULL);
  }
  
  ASSERT_EQ(valk_counter_value(c), 10000);
}

void test_label_escaping_special_chars() {
  valk_metrics_t *m = valk_metrics_new();
  valk_counter_t *c = valk_counter_with_labels(m, "http", "requests",
    "path", "/api/v1?foo=bar&baz=\"quoted\"",
    "method", "GET",
    NULL);
  
  valk_counter_inc(c);
  
  char *prom = valk_metrics_prometheus(m);
  
  // Labels should be properly escaped
  ASSERT_STR_CONTAINS(prom, "path=\"/api/v1?foo=bar&baz=\\\"quoted\\\"\"");
}
```

---

## Phase 3: Medium Priority Files (Week 5-6)

### 3.1 gc.c (83.1% → 90%) - Estimated 3 days

#### Uncovered Areas:
- Mark phase correctness (reachable objects survive)
- Evacuation correctness (checkpoint)
- Emergency GC at hard limit
- Deep environment chains

#### Integration Tests:

```c
// test/integration/test_gc_correctness.c

void test_gc_mark_preserves_reachable() {
  valk_gc_t *gc = create_test_gc();
  valk_lenv_t *env = valk_lenv_new();
  
  // Create object graph
  valk_lval_t *root = valk_lval_qexpr();
  for (int i = 0; i < 100; i++) {
    valk_lval_add(root, valk_lval_num(i));
  }
  valk_lenv_put(env, valk_lval_sym("root"), root);
  
  // Mark root environment
  valk_gc_set_root_env(gc, env);
  
  // Collect
  valk_gc_collect(gc);
  
  // Root and all children should survive
  valk_lval_t *retrieved = valk_lenv_get(env, valk_lval_sym("root"));
  ASSERT_EQ(retrieved->count, 100);
  
  for (int i = 0; i < 100; i++) {
    ASSERT_EQ(retrieved->cell[i]->num, i);
  }
}

void test_gc_evacuation_from_scratch() {
  valk_gc_t *gc = create_test_gc();
  
  // Allocate in scratch arena
  valk_lval_t *scratch_val = valk_lval_str_scratch("test string");
  const char *original_ptr = scratch_val->str;
  
  // Checkpoint (evacuates scratch to heap)
  valk_checkpoint(gc, scratch_val);
  
  // String should be in different location
  ASSERT_NE(scratch_val->str, original_ptr);
  
  // But content should be same
  ASSERT_STR_EQ(scratch_val->str, "test string");
}

void test_gc_emergency_collection() {
  valk_gc_t *gc = create_test_gc();
  valk_gc_set_hard_limit(gc, 1024 * 1024); // 1MB limit
  
  // Allocate until we hit limit
  int allocations = 0;
  while (valk_gc_heap_usage(gc) < 900 * 1024) {
    valk_lval_str("test string that takes some space");
    allocations++;
  }
  
  // This should trigger emergency GC
  size_t before = valk_gc_heap_usage(gc);
  valk_lval_str("one more allocation");
  size_t after = valk_gc_heap_usage(gc);
  
  // GC should have run (memory usage should have decreased or stayed similar)
  ASSERT_LE(after, before + 1024);
}

void test_gc_deep_environment_chain() {
  valk_gc_t *gc = create_test_gc();
  
  // Create 100 nested environments
  valk_lenv_t *env = valk_lenv_new();
  for (int i = 0; i < 100; i++) {
    valk_lenv_t *child = valk_lenv_new();
    child->par = env;
    valk_lenv_put(child, valk_lval_sym("level"), valk_lval_num(i));
    env = child;
  }
  
  valk_gc_set_root_env(gc, env);
  valk_gc_collect(gc);
  
  // All environments should survive
  valk_lenv_t *current = env;
  for (int i = 99; i >= 0; i--) {
    valk_lval_t *level = valk_lenv_get(current, valk_lval_sym("level"));
    ASSERT_EQ(level->num, i);
    current = current->par;
  }
}
```

#### Valk Integration Tests:

```lisp
;; test/test_gc_integration.valk

(test/suite "GC Integration Tests")

(test/define "gc-survives-deep-recursion"
  {do
    ;; Function that creates deep stack + allocations
    (fun {deep-recurse n acc}
      {if (<= n 0)
        {acc}
        {deep-recurse (- n 1) (cons n acc)}})
    
    (= {result} (deep-recurse 1000 ()))
    (test/assert (== (len result) 1000) "All elements preserved")
    true
  })

(test/define "gc-preserves-closures"
  {do
    ;; Create closures that capture values
    (= {closures} (map (\ {i} {(\ {} {i})}) (range 1 100)))
    
    ;; Force GC by allocating
    (= {_} (range 1 10000))
    
    ;; All closures should still work
    (= {results} (map (\ {f} {(f)}) closures))
    (test/assert (== results (range 1 100)) "Closures preserved")
    true
  })

(test/define "gc-handles-cyclic-structures"
  {do
    ;; Create mutual references via environments
    (= {a} (list 1 2))
    (= {b} (list a 3))
    (= {a} (list b 4))  ;; Now a references b which references old a
    
    ;; Force GC
    (= {_} (range 1 10000))
    
    ;; Structure should still be accessible
    (test/assert (list? a) "a is still list")
    (test/assert (list? b) "b is still list")
    true
  })

(test/run {})
```

### 3.2 memory.c (84.4% → 90%) - Estimated 2 days

#### Integration Tests:

```c
// test/integration/test_memory_real.c

void test_slab_allocator_under_pressure() {
  valk_slab_t *slab = valk_slab_new(64, 1000); // 1000 items of 64 bytes
  
  void *ptrs[1000];
  
  // Allocate all
  for (int i = 0; i < 1000; i++) {
    ptrs[i] = valk_slab_acquire(slab);
    ASSERT_NOT_NULL(ptrs[i]);
  }
  
  // Next allocation should fail (exhausted)
  void *overflow = valk_slab_acquire(slab);
  ASSERT_NULL(overflow);
  
  // Free half
  for (int i = 0; i < 500; i++) {
    valk_slab_release(slab, ptrs[i]);
  }
  
  // Should be able to allocate again
  for (int i = 0; i < 500; i++) {
    ptrs[i] = valk_slab_acquire(slab);
    ASSERT_NOT_NULL(ptrs[i]);
  }
}

void test_arena_overflow_to_heap() {
  valk_arena_t *arena = valk_arena_new(1024); // Small arena
  
  // Fill arena
  void *small = valk_arena_alloc(arena, 512);
  ASSERT_NOT_NULL(small);
  
  // This should overflow to heap
  void *large = valk_arena_alloc(arena, 2048);
  ASSERT_NOT_NULL(large); // Should still succeed via malloc fallback
  
  // Verify arena stats reflect overflow
  ASSERT_GT(valk_arena_overflow_count(arena), 0);
}
```

### 3.3 concurrency.c (87.7% → 90%) - Estimated 2 days

#### Integration Tests:

```lisp
;; test/test_concurrency_integration.valk

(test/suite "Concurrency Integration")

(test/define "shift-reset-multi-shot"
  {do
    (= {results} ())
    
    (async-reset (\ {}
      {do
        (= {x} (async-shift (\ {k}
          {do
            (= {results} (cons (k 1) results))
            (= {results} (cons (k 2) results))
            (k 3)
          })))
        (* x 10)
      }))
    
    (test/assert (== (len results) 2) "Two invocations")
    (test/assert (== (fst results) 20) "Second call result")
    (test/assert (== (snd results) 10) "First call result")
    true
  })

(test/define "nested-reset-isolation"
  {do
    (= {outer-k} nil)
    
    (= {result} 
      (async-reset (\ {}
        {do
          (= {x} (async-shift (\ {k} {(= {outer-k} k) 1})))
          (+ x 
             (async-reset (\ {}
               {(async-shift (\ {k} {(k 10)}))})))
        })))
    
    (test/assert (== result 11) "Nested reset works")
    (test/assert (== (outer-k 5) 15) "Outer continuation works")
    true
  })

(test/run {})
```

---

## Phase 4: Branch Coverage Focus (Week 7)

### Files with Line ≥90% but Branch <85%

These files need targeted tests for specific branches, not broad coverage.

### 4.1 aio_alloc.c (93.5% line, 66.7% branch)

```c
// Focus: NULL checks, edge cases
void test_alloc_null_inputs() {
  ASSERT_NULL(valk_alloc_acquire(NULL));
  valk_alloc_release(NULL, NULL);  // Should not crash
}

void test_alloc_zero_size() {
  void *p = valk_alloc_acquire_size(0);
  // Behavior depends on implementation
}
```

### 4.2 aio_metrics.c (94.3% line, 72.9% branch)

```c
// Focus: Overflow, concurrent edge cases
void test_metrics_counter_overflow() {
  valk_metric_counter_t *c = valk_metric_counter_new("test");
  
  // Set near max
  valk_metric_counter_set(c, UINT64_MAX - 1);
  
  // Increment should handle overflow
  valk_metric_counter_inc(c);
  valk_metric_counter_inc(c);
  
  // Verify behavior (wrap or saturate)
  ASSERT_EQ(valk_metric_counter_value(c), 0); // If wrapping
}
```

### 4.3 metrics_delta.c (99.8% line, 66.5% branch)

```c
// Focus: Delta computation edge cases
void test_delta_no_changes() {
  valk_metrics_snapshot_t *s1 = create_snapshot();
  valk_metrics_snapshot_t *s2 = create_snapshot(); // Identical
  
  valk_metrics_delta_t *d = valk_metrics_compute_delta(s1, s2);
  
  ASSERT_EQ(valk_metrics_delta_size(d), 0);
}

void test_delta_all_new() {
  valk_metrics_snapshot_t *s1 = create_empty_snapshot();
  valk_metrics_snapshot_t *s2 = create_snapshot_with_100_metrics();
  
  valk_metrics_delta_t *d = valk_metrics_compute_delta(s1, s2);
  
  ASSERT_EQ(valk_metrics_delta_added_count(d), 100);
}
```

### 4.4 debug.c (100% line, 62.5% branch)

```c
// Focus: Platform-specific branches
void test_debug_backtrace_no_symbols() {
  // Intentionally call from a frame without symbols
  void (*fn)(void) = get_symbolless_function();
  fn();  // Should trigger backtrace
  
  // Verify it doesn't crash
}

void test_debug_signal_handler_reentry() {
  // Signal handler should be reentrant-safe
  raise(SIGSEGV);
  raise(SIGSEGV);  // Second signal during handling
}
```

---

## Phase 5: Valk Stdlib Coverage (Week 8)

Current: 97.8% - Already passing, but gaps exist.

### 5.1 modules/aio/sse.valk (80% → 90%)

```lisp
;; test/test_sse_valk_coverage.valk

(test/suite "SSE Valk Module Coverage")

(test/define "sse-message-helper"
  {do
    (= {aio} (aio/start))
    (= {stream} nil)
    
    (= {server} (http2/server aio 8540
      (\ {ctx} {
        (= {stream} (sse/open ctx))
        (sse/message stream "hello")  ;; Uses sse/message helper
        (sse/event stream "custom" "world")  ;; Uses sse/event helper
        nil
      })))
    
    (http2/client-request aio "127.0.0.1" 8540 "/" (\ {r} {(aio/stop aio)}))
    (aio/delay aio 100 (\ {} {(aio/stop aio)}))
    (aio/run aio)
    
    (test/assert (not (nil? stream)) "Stream was created")
    true
  })

(test/run {})
```

### 5.2 Missing Valk Tests: plist functions

```lisp
;; test/test_plist.valk

(test/suite "Property List Functions")

(test/define "plist-get-set-has"
  {do
    (= {pl} (plist/new))
    (= {pl} (plist/set pl "key1" "value1"))
    (= {pl} (plist/set pl "key2" 42))
    
    (test/assert (plist/has? pl "key1") "has key1")
    (test/assert (plist/has? pl "key2") "has key2")
    (test/assert (not (plist/has? pl "key3")) "doesn't have key3")
    
    (test/assert-eq (plist/get pl "key1") "value1" "get key1")
    (test/assert-eq (plist/get pl "key2") 42 "get key2")
    true
  })

(test/define "plist-keys-vals"
  {do
    (= {pl} (plist/new))
    (= {pl} (plist/set pl "a" 1))
    (= {pl} (plist/set pl "b" 2))
    
    (= {keys} (plist/keys pl))
    (= {vals} (plist/vals pl))
    
    (test/assert (== (len keys) 2) "2 keys")
    (test/assert (== (len vals) 2) "2 vals")
    true
  })

(test/run {})
```

### 5.3 Missing Valk Tests: async_handles.valk

```lisp
;; test/test_async_handles.valk

(test/suite "Async Handle Functions")

(test/define "with-timeout-success"
  {do
    (= {aio} (aio/start))
    (= {result} nil)
    
    (with-timeout aio 1000  ;; 1 second timeout
      (async/pure 42)
      (\ {r} {
        (= {result} r)
        (aio/stop aio)
      }))
    
    (aio/run aio)
    (test/assert-eq result 42 "Got result before timeout")
    true
  })

(test/define "with-timeout-expires"
  {do
    (= {aio} (aio/start))
    (= {got-timeout} false)
    
    (with-timeout aio 10  ;; 10ms timeout
      (aio/delay 1000 (\ {} {42}))  ;; Would take 1 second
      (\ {r} {
        (if (error? r)
          {(= {got-timeout} true)}
          {nil})
        (aio/stop aio)
      }))
    
    (aio/run aio)
    (test/assert got-timeout "Timeout occurred")
    true
  })

(test/define "retry-backoff-success-on-third"
  {do
    (= {aio} (aio/start))
    (= {attempts} 0)
    (= {result} nil)
    
    (retry-backoff aio
      3  ;; max attempts
      100  ;; base delay ms
      (\ {} {
        (= {attempts} (+ attempts 1))
        (if (< attempts 3)
          {(error "not yet")}
          {42})
      })
      (\ {r} {
        (= {result} r)
        (aio/stop aio)
      }))
    
    (aio/run aio)
    (test/assert-eq attempts 3 "Made 3 attempts")
    (test/assert-eq result 42 "Got success result")
    true
  })

(test/run {})
```

---

## Test Infrastructure Requirements

### New Test Helpers Needed

```c
// test/helpers/test_server.h

// Create a test HTTPS server
void start_test_https_server(int port);
void stop_test_https_server(int port);

// Create server with specific behavior
void start_test_https_server_slow_response(int port, int delay_ms);
void start_test_https_server_large_response(int port, size_t bytes);
void start_test_https_server_error_after_n(int port, int n);

// Create hanging/broken servers
void start_hanging_ssl_server(int port);
void start_connection_reset_server(int port);

// Test utilities
void run_until_complete(valk_aio_t *aio, int expected_responses);
void run_for_ms(valk_aio_t *aio, int milliseconds);
void run_with_timeout(valk_aio_t *aio, int timeout_ms);
```

### New Test Certificate Infrastructure

```
test/certs/
├── valid.pem           # Valid self-signed cert
├── valid.key           # Private key
├── expired.pem         # Expired certificate
├── expired.key
├── localhost.pem       # Cert for "localhost" only
├── localhost.key
└── generate-certs.sh   # Script to regenerate
```

### CMake Test Targets

```cmake
# test/CMakeLists.txt additions

# Integration tests (use real connections)
add_test(NAME integration_aio_uv 
  COMMAND test_aio_uv_integration
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})

add_test(NAME integration_ssl
  COMMAND test_ssl_integration
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})

add_test(NAME integration_sse
  COMMAND test_sse_integration  
  WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})

# Mark as requiring network
set_tests_properties(integration_aio_uv integration_ssl integration_sse
  PROPERTIES LABELS "integration;network")
```

---

## Summary: Prioritized Test Plan

### Week 1-2: Critical (Biggest Impact)

| File | Current | Target | New Tests |
|------|---------|--------|-----------|
| `aio_uv.c` | 40% | 90% | 15+ integration tests |
| `aio_sse_stream_registry.c` | 50% | 90% | 8+ integration tests |

### Week 3-4: High Priority

| File | Current | Target | New Tests |
|------|---------|--------|-----------|
| `aio_sse_diagnostics.c` | 67% | 90% | 6+ tests |
| `aio_ssl.c` | 71% | 90% | 8+ tests |
| `parser.c` | 75% | 90% | 10+ tests |
| `metrics_v2.c` | 78% | 90% | 5+ tests |

### Week 5-6: Medium Priority

| File | Current | Target | New Tests |
|------|---------|--------|-----------|
| `gc.c` | 83% | 90% | 8+ tests |
| `memory.c` | 84% | 90% | 5+ tests |
| `concurrency.c` | 88% | 90% | 4+ tests |

### Week 7: Branch Coverage Focus

| File | Line % | Branch % | Focus |
|------|--------|----------|-------|
| `aio_alloc.c` | 94% | 67% | NULL checks, edge cases |
| `aio_metrics.c` | 94% | 73% | Overflow, concurrency |
| `metrics_delta.c` | 100% | 67% | Delta edge cases |
| `debug.c` | 100% | 63% | Platform branches |

### Week 8: Valk Stdlib + Polish

- `modules/aio/sse.valk` → 90%
- Add plist tests
- Add async_handles tests
- CI enforcement enabled

---

## Expected Outcome

After implementing this plan:

| Metric | Before | After |
|--------|--------|-------|
| Runtime Line Coverage | 67.5% | 90%+ |
| Runtime Branch Coverage | 48.7% | 85%+ |
| Failing Files | 18 | 0 |
| Integration Tests | ~20 | 100+ |
| Test Execution Time | ~2 min | ~5 min |

---

## Key Principles

1. **Real connections over mocks** - Tests use actual servers, sockets, and SSL
2. **Error paths matter** - Test connection failures, timeouts, certificate errors
3. **Stress under load** - Test concurrent connections, backpressure, large payloads
4. **GC correctness** - Verify data survives collection, evacuation works
5. **Branch coverage** - Target specific uncovered branches, not just lines
