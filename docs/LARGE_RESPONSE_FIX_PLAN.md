# Large Response Handling Fix Plan

This document details the issues found during 50MB response testing and provides a comprehensive plan to resolve them.

## Executive Summary

Two critical bugs prevent proper handling of large HTTP responses:

| Issue | Severity | Impact | File(s) |
|-------|----------|--------|---------|
| Issue 1: 16KB Data Loss on EOF | CRITICAL | Final TLS record lost, 16KB short on large responses | `src/aio_uv.c`, `src/aio_ssl.c` |
| Issue 2: Invalid Pointer Arithmetic | CRITICAL | SIGSEGV crash on stream close | `src/aio_uv.c` |

---

## Issue 1: 16KB Data Loss on Large Responses

### Symptom
Test receives 52,412,416 bytes instead of 52,428,800 (exactly 16,384 bytes short).

### Root Cause
When the TCP socket receives EOF, the code at line 1122 immediately closes the connection without processing any remaining encrypted data in the SSL BIO buffer. The final TLS record (up to 16KB per `SSL3_RT_MAX_PLAIN_LENGTH`) is lost.

### Location
**File:** `/home/xyzyx/src/valkyria/src/aio_uv.c`
**Function:** `__http_tcp_read_cb()`
**Lines:** 1117-1140

### Current Buggy Code
```c
static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {
  valk_aio_handle_t *hndl = stream->data;
  struct valk_aio_http_conn *conn = hndl->arg;

  if (nread < 0) {                           // Line 1122
    if (nread == UV_EOF) {                   // Line 1124
      printf("[DEBUG] Received EOF on tcp stream\n");
    } else {
      fprintf(stderr, "[DEBUG] Read error: %s\n", uv_strerror((int)nread));
    }
    // ... debug prints ...
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    }
    return;  // ⚠️ BUG: RETURNS WITHOUT PROCESSING PENDING SSL DATA
  }
  // ... normal data processing ...
}
```

### Why This Happens
1. Client finishes sending data and closes write side → `nread == UV_EOF`
2. libuv calls `__http_tcp_read_cb()` with EOF
3. Code closes socket immediately without calling `valk_aio_ssl_on_read()`
4. Final TLS `close_notify` alert and any pending data in SSL BIO is lost

### Secondary Issue in SSL Layer
**File:** `/home/xyzyx/src/valkyria/src/aio_ssl.c`
**Function:** `valk_aio_ssl_on_read()`
**Lines:** 226-228

```c
valk_err_e valk_aio_ssl_on_read(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out, void *arg,
                                void(onRead)(void *, const valk_buffer_t *)) {
  if (In->count == 0) {
    printf("Didnt receive any data ??? just return then i guess\n");
    return VALK_ERR_SUCCESS;  // ⚠️ Returns without processing pending BIO data!
  }
  // ...
}
```

This early return prevents processing of pending SSL BIO data when called with `In->count == 0`.

---

### Fix Plan for Issue 1

#### Step 1: Modify `valk_aio_ssl_on_read()` to Support Flush Mode

**File:** `src/aio_ssl.c`
**Lines:** 226-232

**Change:**
```c
valk_err_e valk_aio_ssl_on_read(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out, void *arg,
                                void(onRead)(void *, const valk_buffer_t *)) {
  int n, err;

  // Feed new data to BIO if available
  if (In->count > 0) {
    n = BIO_write(ssl->read_bio, In->items, In->count);
    VALK_ASSERT(n >= 0, "BIO_write failed %d", n);
    VALK_ASSERT((size_t)n == In->count, "BIO_write incomplete %d != %zu", n, In->count);
    In->count = 0;
  } else {
    // No new data - check if there's pending data in SSL layer
    int pending = SSL_pending(ssl->ssl);
    if (pending == 0 && !SSL_is_init_finished(ssl->ssl)) {
      // No pending data and handshake incomplete - nothing to do
      return VALK_ERR_SUCCESS;
    }
    // If there IS pending data, fall through to process it
  }

  // Continue with handshake if needed...
```

#### Step 2: Modify EOF Handler in `__http_tcp_read_cb()`

**File:** `src/aio_uv.c`
**Lines:** 1122-1140

**Replace the entire `if (nread < 0)` block with:**

```c
if (nread < 0) {
    bool is_eof = (nread == UV_EOF);

    if (is_eof) {
      printf("[DEBUG] Received EOF on tcp stream\n");

      // CRITICAL: Process any pending data in SSL BIO before closing
      // The final TLS close_notify alert may be waiting in the BIO
      valk_buffer_t In = {
          .items = buf->base,
          .count = 0,  // No new TCP data, but SSL BIO may have pending data
          .capacity = HTTP_SLAB_ITEM_SIZE
      };

      __tcp_buffer_slab_item_t *slabItem =
          (void *)valk_slab_aquire(tcp_buffer_slab)->data;

      valk_buffer_t Out = {
          .items = slabItem->data,
          .count = 0,
          .capacity = HTTP_SLAB_ITEM_SIZE
      };

      // Process pending SSL data (close_notify, final records, etc.)
      int ssl_err = valk_aio_ssl_on_read(&conn->ssl, &In, &Out, conn,
                                         __http_tcp_unencrypted_read_cb);

      // Send any pending encrypted response data
      if (!ssl_err && Out.count > 0) {
        slabItem->buf.base = Out.items;
        slabItem->buf.len = Out.count;
        slabItem->conn = conn;

        VALK_TRACE("Sending %ld bytes on EOF", Out.count);
        uv_write(&slabItem->req, (uv_stream_t *)&conn->handle->uv.tcp,
                 &slabItem->buf, 1, __http_tcp_on_write_cb);
      } else {
        valk_slab_release_ptr(tcp_buffer_slab, slabItem);
      }
    } else {
      // Real error (not EOF)
      fprintf(stderr, "[DEBUG] Read error: %s\n", uv_strerror((int)nread));
    }

    // Close the connection
    if (!uv_is_closing((uv_handle_t *)&conn->handle->uv.tcp)) {
      printf("[DEBUG] Calling uv_close\n");
      uv_close((uv_handle_t *)&conn->handle->uv.tcp, __uv_handle_closed_cb);
    }
    return;
}
```

---

## Issue 2: Invalid Pointer Arithmetic in Stream Close

### Symptom
`test_demo_socket_server` crashes with SIGSEGV when closing HTTP/2 streams.

### Root Cause
The code attempts to recover the `valk_arc_box` pointer from the `box->item` pointer using invalid pointer arithmetic. While the math happens to work, the pattern is fragile and error-prone.

### Location
**File:** `/home/xyzyx/src/valkyria/src/aio_uv.c`
**Function:** `__http_client_on_stream_close_callback()`
**Line:** 1645

### Current Code
```c
static int __http_client_on_stream_close_callback(nghttp2_session *session,
                                                  int32_t stream_id,
                                                  uint32_t error_code,
                                                  void *user_data) {
  __http2_req_res_t *reqres =
      nghttp2_session_get_stream_user_data(session, stream_id);
  if (reqres) {
    if (error_code != NGHTTP2_NO_ERROR) {
      // ... error handling ...
    } else {
      // Normal close - resolve with the response
      valk_arc_box *box = ((valk_arc_box *)reqres->res) - 1;  // ⚠️ BUG HERE
      valk_promise_respond(&reqres->promise, box);
    }
    // ...
  }
  return 0;
}
```

### Memory Layout Context
The `valk_arc_box` allocation pattern (from `src/concurrency.c:39-56`):
```
[Box Header (sizeof(valk_arc_box)) | Item Data (capacity bytes)]
 ^                                  ^
 |                                  |
box                                 box->item
```

The `item` pointer is computed as: `self->item = &((char *)self)[sizeof(valk_arc_box)]`

### Why the Current Code is Fragile
The expression `((valk_arc_box *)reqres->res) - 1` relies on:
1. Casting `void*` to `valk_arc_box*`
2. Subtracting 1 (which subtracts `sizeof(valk_arc_box)` bytes)
3. Assuming this recovers the original box pointer

While mathematically correct, this is:
- Non-obvious to readers
- Breaks silently if structure layout changes
- Against C best practices for pointer recovery

---

### Fix Plan for Issue 2

#### Step 1: Modify `__http2_req_res_t` Structure

**File:** `src/aio_uv.c`
**Lines:** 100-105

**Current:**
```c
typedef struct __http2_req_res_t {
  size_t streamid;
  valk_http2_request_t *req;
  valk_http2_response_t *res;
  valk_promise promise;
} __http2_req_res_t;
```

**Change to:**
```c
typedef struct __http2_req_res_t {
  size_t streamid;
  valk_http2_request_t *req;
  valk_arc_box *res_box;      // ← NEW: Store the arc_box pointer
  valk_http2_response_t *res; // Keep for convenience
  valk_promise promise;
} __http2_req_res_t;
```

#### Step 2: Store Box Pointer at Allocation

**File:** `src/aio_uv.c`
**Lines:** 2100-2114 (in `valk_aio_http2_request_send()`)

**Current:**
```c
valk_arc_box *box =
    valk_arc_box_new(VALK_SUC, sizeof(valk_http2_response_t));
box->free = __valk_http2_response_free;

reqres->res = box->item;
```

**Change to:**
```c
valk_arc_box *box =
    valk_arc_box_new(VALK_SUC, sizeof(valk_http2_response_t));
box->free = __valk_http2_response_free;

reqres->res_box = box;        // ← Store the box pointer
reqres->res = box->item;      // Keep for convenience
```

#### Step 3: Use Stored Pointer in Stream Close

**File:** `src/aio_uv.c`
**Line:** 1645 (in `__http_client_on_stream_close_callback()`)

**Current:**
```c
valk_arc_box *box = ((valk_arc_box *)reqres->res) - 1;
```

**Change to:**
```c
valk_arc_box *box = reqres->res_box;
```

---

## Test Plan

### Test 1: Verify 16KB Data Loss Fix

**File:** `test/test_networking.c`
**Test:** `test_lisp_50mb_response`

**Steps:**
1. Run the existing 50MB test: `make test`
2. Verify received bytes equals expected: 52,428,800 bytes
3. Verify content pattern matches

**Expected result after fix:**
```
[TEST] test_lisp_50mb_response: Response size: 52428800 (expected 52428800)
[TEST] test_lisp_50mb_response: PASSED
```

### Test 2: Verify Pointer Arithmetic Fix

**File:** `test/test_networking.c`
**Test:** `test_demo_socket_server`

**Steps:**
1. Run the demo server test: `make test`
2. Verify no SIGSEGV crash
3. Verify HTTP/2 stream properly closes with response

**Expected result after fix:**
```
[TEST] test_demo_socket_server: PASSED
```

### Test 3: Edge Case - Small Response Still Works

**File:** `test/test_networking.c`
**Test:** `test_http2_simple_get` (or similar)

**Steps:**
1. Run all networking tests
2. Verify small responses (<1KB) still work correctly
3. Verify EOF handling doesn't break normal cases

### Test 4: Stress Test - Multiple Large Responses

**Create new test (optional):**
```c
// test/test_networking.c - add new test
void test_multiple_large_responses() {
  // Send 5 concurrent 10MB requests
  // Verify all complete with correct size
  // Tests that slab allocation/release works under load
}
```

---

## Implementation Order

1. **Issue 2 first** (pointer arithmetic) - simpler fix, blocks other tests
2. **Issue 1 second** (16KB data loss) - requires both file changes

### Estimated Changes

| File | Lines Changed | Complexity |
|------|---------------|------------|
| `src/aio_uv.c` | ~50 lines | Medium |
| `src/aio_ssl.c` | ~15 lines | Low |
| Total | ~65 lines | Medium |

---

## Verification Commands

```bash
# Build with debug symbols
make clean && make build

# Run specific test
ASAN_OPTIONS=detect_leaks=0 ./build/test_networking test_lisp_50mb_response

# Run all networking tests
make test

# Run with verbose output
VALK_TRACE=1 ./build/test_networking test_demo_socket_server
```

---

## Rollback Plan

If the fix introduces regressions:

1. Revert changes to `src/aio_uv.c` and `src/aio_ssl.c`
2. Keep `HTTP_MAX_RESPONSE_SIZE_BYTES = 64e6` (already committed)
3. Document the 16KB limitation in the test as a known issue

---

## Related Constants Reference

```c
// src/aio_uv.c lines 64-81
HTTP_MAX_RESPONSE_SIZE_BYTES = 64e6   // 64 MB client buffer
HTTP_SLAB_ITEM_SIZE = SSL3_RT_MAX_PACKET_SIZE * 2  // ~32KB per TLS record
SSL3_RT_MAX_PACKET_SIZE = 16384 + 256  // Standard TLS max record

// Memory limits
HTTP_STREAM_ARENA_SIZE = 67108864     // 64MB per stream arena
HTTP_MAX_STREAMS_PER_CONNECTION = 128
```

## Code Location Summary

| Component | File | Lines |
|-----------|------|-------|
| EOF handler (bug) | `src/aio_uv.c` | 1117-1140 |
| SSL read function | `src/aio_ssl.c` | 223-297 |
| Early return guard | `src/aio_ssl.c` | 226-228 |
| reqres structure | `src/aio_uv.c` | 100-105 |
| Pointer arithmetic (bug) | `src/aio_uv.c` | 1645 |
| Box allocation | `src/aio_uv.c` | 2100-2114 |
| Response structure | `src/aio.h` | 54-74 |
| arc_box structure | `src/concurrency.h` | 102-113 |
| arc_box allocation | `src/concurrency.c` | 39-56 |
