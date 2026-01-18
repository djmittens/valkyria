# 16KB Data Loss Fix Plan

## Issue Summary

**Test:** `test_lisp_50mb_response` in `test/test_networking.c:155-322`

| Metric | Value |
|--------|-------|
| Expected bytes | 52,428,800 (50MB) |
| Received bytes | 52,412,416 |
| Missing bytes | 16,384 (exactly 1 TLS record) |

**Error output:**
```
[DEBUG] Client stream 1 closed, response bodyLen=52412416
/home/xyzyx/src/valkyria/test/test_networking.c:295 || Expected 52428800 bytes, got 52412416 bytes
```

---

## Root Cause Analysis

### The Bug: Buffer Size Mismatch

The issue is a **buffer size mismatch** between the main send path and the continuation send path:

| Path | Function | Buffer Size | Location |
|------|----------|-------------|----------|
| Main path | `__http_tcp_read_cb` | `HTTP_SLAB_ITEM_SIZE` (~33KB) | `src/aio_uv.c:1183` |
| Continuation path | `__http_continue_pending_send` | `SSL3_RT_MAX_PACKET_SIZE` (16KB) | `src/aio_uv.c:1063-1066` |

### Data Flow That Causes the Loss

```
1. Server sends 50MB via __http_byte_body_cb (line 626-656)
                    │
                    ▼
2. nghttp2 produces HTTP/2 DATA frames
                    │
                    ▼
3. __http2_flush_frames() buffers frames (line 1016-1048)
                    │
                    ▼
4. Buffer fills up → pending_write = true, loop breaks (line 1028-1033)
                    │
                    ▼
5. Write callback triggers __http_continue_pending_send() (line 614-615)
                    │
                    ▼
6. BUG: Continuation uses 16KB buffer, sends ONE chunk, no loop (line 1077-1091)
                    │
                    ▼
7. If nghttp2 has >16KB pending, only first 16KB sent
                    │
                    ▼
8. Final chunk: pending_write becomes false, but 16KB encrypted data never sent
```

### Key Code Comparison

**Main path (works correctly) - has a loop:**
```c
// src/aio_uv.c:1198-1226
while (In.count > 0) {
  valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
  if (Out.count > 0) {
    // ... send data ...
    if (In.count > 0) {
      slabItem = (void *)valk_slab_aquire(tcp_buffer_slab)->data;
      // ... get new buffer and continue loop ...
    }
  }
}
```

**Continuation path (BUG) - no loop:**
```c
// src/aio_uv.c:1077-1091
if (In.count > 0) {
  valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
  if (Out.count > 0) {
    // ... send data ...
    return;  // ← Returns immediately, remaining data dropped!
  }
}
```

---

## Fix Plan

### Fix 1: Add Loop to `__http_continue_pending_send()` (Primary Fix)

**File:** `src/aio_uv.c`
**Lines:** 1052-1096

#### Current Code (Buggy)

```c
static void __http_continue_pending_send(struct valk_aio_http_conn *conn) {
  if (!conn || !conn->session || !SSL_is_init_finished(conn->ssl.ssl)) {
    return;
  }

  if (uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
    return;
  }

  // BUG: Buffer too small (16KB instead of 33KB)
  char buf[SSL3_RT_MAX_PACKET_SIZE];
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = SSL3_RT_MAX_PACKET_SIZE};

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  __http2_flush_frames(&In, conn);

  // BUG: Only sends one chunk, no loop!
  if (In.count > 0) {
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    if (Out.count > 0) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;
      slabItem->conn = conn;

      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);
      return;  // ← Remaining data in In is dropped!
    }
  }

  valk_slab_release_ptr(tcp_buffer_slab, slabItem);
}
```

#### Fixed Code

```c
static void __http_continue_pending_send(struct valk_aio_http_conn *conn) {
  if (!conn || !conn->session || !SSL_is_init_finished(conn->ssl.ssl)) {
    return;
  }

  if (uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
    return;
  }

  // FIX 1: Use same buffer size as main path
  char buf[HTTP_SLAB_ITEM_SIZE];
  memset(buf, 0, sizeof(buf));
  valk_buffer_t In = {
      .items = buf, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  __tcp_buffer_slab_item_t *slabItem =
      (void *)valk_slab_aquire(tcp_buffer_slab)->data;

  valk_buffer_t Out = {
      .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};

  __http2_flush_frames(&In, conn);

  // FIX 2: Add loop to handle all pending data (matches main path pattern)
  while (In.count > 0) {
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);

    if (Out.count > 0) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;
      slabItem->conn = conn;

      VALK_TRACE("Continuation send: %ld bytes (remaining: %zu, pending: %d)",
                 Out.count, In.count, conn->pending_write);
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);

      // If there's more data to encrypt, get a new buffer
      if (In.count > 0) {
        slabItem = (void *)valk_slab_aquire(tcp_buffer_slab)->data;
        Out = (valk_buffer_t){
            .items = slabItem->data, .count = 0, .capacity = HTTP_SLAB_ITEM_SIZE};
      } else {
        slabItem = NULL;  // Mark as used
      }
    } else {
      VALK_WARN("SSL encrypt produced no output with %zu bytes remaining", In.count);
      break;
    }
  }

  // Handle final encryption flush if slabItem still valid
  if (slabItem != NULL && In.count == 0) {
    valk_aio_ssl_encrypt(&conn->ssl, &In, &Out);
    if (Out.count > 0) {
      slabItem->buf.base = Out.items;
      slabItem->buf.len = Out.count;
      slabItem->conn = conn;
      uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
               &slabItem->buf, 1, __http_tcp_on_write_cb);
    } else {
      valk_slab_release_ptr(tcp_buffer_slab, slabItem);
    }
  } else if (slabItem != NULL) {
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
  }
}
```

### Summary of Changes

| Line | Change |
|------|--------|
| 1063 | `char buf[SSL3_RT_MAX_PACKET_SIZE]` → `char buf[HTTP_SLAB_ITEM_SIZE]` |
| 1066 | `.capacity = SSL3_RT_MAX_PACKET_SIZE` → `.capacity = HTTP_SLAB_ITEM_SIZE` |
| 1077-1091 | `if (In.count > 0) { ... return; }` → `while (In.count > 0) { ... }` with buffer refresh |

---

## Test Plan

### Test 1: Verify 50MB Response Fix (Primary Verification)

**File:** `test/test_networking.c:155-322`
**Function:** `test_lisp_50mb_response`

```bash
# Build and run
make build && ASAN_OPTIONS=detect_leaks=0 ./build/test_networking
```

**Expected output after fix:**
```
[test] Response received: 52428800 bytes
[test] SUCCESS: Received full 50MB response!
✅ test_lisp_50mb_response..........  PASS
```

**Verification point (lines 292-298):**
```c
if (response->bodyLen != LISP_50MB_RESPONSE_SIZE) {
  VALK_FAIL("Expected %d bytes, got %zu bytes",
            LISP_50MB_RESPONSE_SIZE, response->bodyLen);
} else {
  printf("[test] SUCCESS: Received full 50MB response!\n");
}
```

---

### Test 2: Boundary Size Tests (New Test)

**File:** `test/test_networking.c` (add after line 322)

```c
// Test response sizes at TLS record boundaries
void test_response_boundary_sizes(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Sizes that hit critical boundaries
  typedef struct { size_t size; const char *desc; } test_case_t;
  test_case_t cases[] = {
    {16383,    "1 TLS record - 1"},
    {16384,    "1 TLS record exact (SSL3_RT_MAX_PLAIN_LENGTH)"},
    {16385,    "1 TLS record + 1"},
    {32767,    "2 TLS records - 1"},
    {32768,    "2 TLS records exact (HTTP_SLAB_ITEM_SIZE)"},
    {32769,    "2 TLS records + 1"},
    {49152,    "3 TLS records exact"},
    {1048576,  "1MB"},
    {10485760, "10MB"},
  };

  for (size_t i = 0; i < sizeof(cases)/sizeof(cases[0]); i++) {
    printf("[test] Testing size: %zu (%s)\n", cases[i].size, cases[i].desc);

    // Create request for /size/{n} endpoint
    // ... setup client, send request ...

    if (response->bodyLen != cases[i].size) {
      VALK_FAIL("Size %s: expected %zu, got %zu (diff: %zd)",
                cases[i].desc, cases[i].size, response->bodyLen,
                (ssize_t)response->bodyLen - (ssize_t)cases[i].size);
    }
  }

  VALK_PASS();
}
```

**Add to test suite (after line 337):**
```c
valk_testsuite_add_test(suite, "test_response_boundary_sizes",
                        test_response_boundary_sizes);
```

---

### Test 3: End-of-Response Content Verification

**File:** `test/test_networking.c` (add after line 304)

```c
// Verify content at the END of response (catches 16KB loss specifically)
if (response->bodyLen >= LISP_50MB_RESPONSE_SIZE) {
  // Check last 64 bytes match expected pattern
  size_t offset = LISP_50MB_RESPONSE_SIZE - 64;
  const char *pattern = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdefghijklmnopqrstuvwxyz./";
  size_t pattern_len = 64;

  // Calculate expected content at offset
  char expected[65];
  for (size_t i = 0; i < 64; i++) {
    expected[i] = pattern[(offset + i) % pattern_len];
  }
  expected[64] = '\0';

  if (memcmp((char*)response->body + offset, expected, 64) != 0) {
    VALK_FAIL("Content mismatch at end of response (bytes %zu-%zu)",
              offset, offset + 64);
  }
  printf("[test] End-of-response content verified\n");
}
```

---

### Test 4: Full Test Suite Regression

```bash
# Run all networking tests
make test

# Run with AddressSanitizer
ASAN_OPTIONS=detect_leaks=0 ./build/test_networking

# Run with full leak detection (after confirming basic functionality)
ASAN_OPTIONS=detect_leaks=1 ./build/test_networking
```

---

## Verification Commands

```bash
# Clean build
make clean && make build

# Run specific test with debug output
VALK_TRACE=1 ASAN_OPTIONS=detect_leaks=0 ./build/test_networking test_lisp_50mb_response

# Run all networking tests
make test

# Check for memory issues
valgrind --leak-check=full ./build/test_networking test_lisp_50mb_response
```

---

## Risk Assessment

| Risk | Level | Mitigation |
|------|-------|------------|
| Regression in small responses | Low | Fix aligns continuation with main path which works |
| Memory allocation increase | Low | Buffer on stack, same size already used elsewhere |
| Performance impact | None | Same number of operations, just correct buffer size |
| API compatibility | None | Internal change only |

---

## Files Modified

| File | Lines | Description |
|------|-------|-------------|
| `src/aio_uv.c` | 1063-1066 | Increase buffer size to `HTTP_SLAB_ITEM_SIZE` |
| `src/aio_uv.c` | 1077-1091 | Add `while` loop to drain all pending data |
| `test/test_networking.c` | ~305 | Add end-of-response content verification |
| `test/test_networking.c` | ~340 | Add boundary size test (optional) |

---

## Related Code References

| Component | File | Lines |
|-----------|------|-------|
| Buffer constants | `src/aio_uv.c` | 67-71 |
| Body callback | `src/aio_uv.c` | 626-656 |
| Frame flush | `src/aio_uv.c` | 1016-1048 |
| Write callback | `src/aio_uv.c` | 599-617 |
| Main send loop | `src/aio_uv.c` | 1198-1226 |
| Continuation (bug) | `src/aio_uv.c` | 1052-1096 |
| SSL encryption | `src/aio_ssl.c` | 305-384 |
| Test definition | `test/test_networking.c` | 155-322 |
| Handler definition | `test/test_lisp_50mb_handler.valk` | 1-34 |
