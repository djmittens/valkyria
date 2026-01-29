# SSL Crash Fix Plan

## Issue Summary

**Symptom**: Segmentation fault in `BIO_read()` during SSL encryption when handling concurrent HTTP/2 requests with large (100MB) responses.

**Crash Location**: `src/aio_ssl.c:363` in `valk_aio_ssl_encrypt()`

**Backtrace**:
```
#0  libc.so.6
#1  libcrypto.so.3
#2-4  BIO_read()
#5  valk_aio_ssl_encrypt() at src/aio_ssl.c:363
#6  __http_tcp_read_cb() at src/aio_uv.c:1257
#7-11  libuv event loop
```

## Root Cause Analysis

### Primary Issue: Missing Connection State Management

The `valk_aio_http_conn` structure has a `state` field (`__aio_http_conn_e`) with values:
- `VALK_CONN_INIT`
- `VALK_CONN_ESTABLISHED`
- `VALK_CONN_CLOSING`
- `VALK_CONN_CLOSED`

**Problem**: This state is never set or checked. SSL operations continue even when a connection is in the process of closing.

### Secondary Issue: Use-After-Free Race Condition

**Sequence of events leading to crash**:

1. Connection A receives data, triggers `__http_tcp_read_cb`
2. Connection A starts processing, calls `valk_aio_ssl_encrypt`
3. Meanwhile, Connection B (or A itself) receives EOF/error
4. `uv_close()` is called, eventually triggering `__valk_aio_http2_on_disconnect`
5. `valk_aio_ssl_free()` is called:
   - `SSL_free(ssl->ssl)` frees the SSL object (which also frees associated BIOs)
   - `ssl->ssl = nullptr`
6. Connection A's `valk_aio_ssl_encrypt` continues, accessing freed `ssl->write_bio`
7. **CRASH**: `BIO_read(ssl->write_bio, ...)` accesses freed memory

### Tertiary Issue: Missing Null Checks

`valk_aio_ssl_encrypt()` at line 308 calls `SSL_is_init_finished(ssl->ssl)` without first verifying:
- `ssl` is not NULL
- `ssl->ssl` is not NULL
- `ssl->write_bio` is not NULL

## Fix Implementation Plan

### Phase 1: Add Connection State Management

#### 1.1 Set State on Connection Creation

**File**: `src/aio_uv.c`

Find where connections are allocated (likely in `__http_tcp_connection_cb` or similar) and set initial state:

```c
conn->state = VALK_CONN_INIT;
```

#### 1.2 Set State on SSL Handshake Completion

After successful handshake, set:

```c
conn->state = VALK_CONN_ESTABLISHED;
```

#### 1.3 Set State Before Closing

**File**: `src/aio_uv.c`

Before calling `uv_close()` on a connection (multiple locations):

```c
conn->state = VALK_CONN_CLOSING;
```

Locations to modify:
- `__http_tcp_read_cb` line ~1226 (EOF/error path)
- `__http_tcp_unencrypted_read_cb` line ~1172 (nghttp2 error path)
- Any other location calling `uv_close()` on connection handles

#### 1.4 Check State Before SSL Operations

**File**: `src/aio_uv.c`

In `__http_tcp_read_cb`, before calling SSL functions:

```c
// Early exit if connection is closing
if (conn->state == VALK_CONN_CLOSING || conn->state == VALK_CONN_CLOSED) {
    valk_slab_release_ptr(tcp_buffer_slab, slabItem);
    valk_slab_release_ptr(tcp_buffer_slab, In.items);
    return;
}
```

### Phase 2: Add Null Safety to SSL Functions

#### 2.1 Update `valk_aio_ssl_encrypt`

**File**: `src/aio_ssl.c`, lines 305-310

```c
valk_err_e valk_aio_ssl_encrypt(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out) {
    // Null safety checks
    if (!ssl || !ssl->ssl || !ssl->write_bio) {
        return VALK_ERR_SSL_INVALID;
    }

    if (!SSL_is_init_finished(ssl->ssl)) {
        return VALK_ERR_SUCCESS;
    }
    // ... rest of function
}
```

#### 2.2 Update `valk_aio_ssl_on_read`

**File**: `src/aio_ssl.c`, line 223

```c
valk_err_e valk_aio_ssl_on_read(valk_aio_ssl_t *ssl, valk_buffer_t *In,
                                valk_buffer_t *Out, void *arg,
                                void(onRead)(void *, const valk_buffer_t *)) {
    // Null safety checks
    if (!ssl || !ssl->ssl || !ssl->read_bio || !ssl->write_bio) {
        return VALK_ERR_SSL_INVALID;
    }
    // ... rest of function
}
```

#### 2.3 Add New Error Code (if needed)

**File**: `src/common.h` (or wherever `valk_err_e` is defined)

```c
VALK_ERR_SSL_INVALID,  // SSL context is NULL or freed
```

### Phase 3: Add Reference Counting for Pending Operations

#### 3.1 Add Pending Operation Counter

**File**: `src/aio_uv.c`, in `valk_aio_http_conn` struct

```c
typedef struct valk_aio_http_conn {
    __aio_http_conn_e state;
    // ... existing fields ...
    atomic_int pending_ops;  // Count of in-flight operations
} valk_aio_http_conn;
```

#### 3.2 Increment Before Async Operations

Before `uv_write()` calls:

```c
atomic_fetch_add(&conn->pending_ops, 1);
```

#### 3.3 Decrement in Callbacks

In `__http_tcp_on_write_cb`:

```c
atomic_fetch_sub(&conn->pending_ops, 1);
```

#### 3.4 Wait for Pending Ops Before Free

In `__valk_aio_http2_on_disconnect`:

```c
// Only free when no operations are pending
// Note: In libuv's single-threaded model, this may need different handling
if (atomic_load(&conn->pending_ops) > 0) {
    // Schedule cleanup for later or use uv_idle
    return;
}
```

### Phase 4: Clear BIO Pointers on Free

#### 4.1 Update `valk_aio_ssl_free`

**File**: `src/aio_ssl.c`, line 175

```c
void valk_aio_ssl_free(valk_aio_ssl_t *ssl) {
    if (!ssl || !ssl->ssl) {
        return;  // Already freed or never initialized
    }

    SSL_free_buffers(ssl->ssl);
    SSL_free(ssl->ssl);

    // Clear all pointers to prevent use-after-free
    ssl->ssl = nullptr;
    ssl->read_bio = nullptr;   // Freed by SSL_free
    ssl->write_bio = nullptr;  // Freed by SSL_free
}
```

## Testing Plan

### Unit Tests

1. **Test SSL encrypt with NULL ssl**: Verify `VALK_ERR_SSL_INVALID` returned
2. **Test SSL encrypt with NULL ssl->ssl**: Verify `VALK_ERR_SSL_INVALID` returned
3. **Test double-free protection**: Call `valk_aio_ssl_free` twice, verify no crash

### Integration Tests

1. **Concurrent connection stress test**:
   ```bash
   hey -n 1000 -c 50 https://localhost:8443/stress/100mb
   ```

2. **Rapid connect/disconnect test**:
   ```bash
   for i in {1..100}; do
       curl -k https://localhost:8443/ &
   done
   wait
   ```

3. **Mixed workload test**: Combine small and large requests with connection drops

### ASAN Testing

Run all tests with AddressSanitizer enabled:
```bash
ASAN_OPTIONS=detect_leaks=1 make test
```

## Implementation Order

1. **Phase 2** (Null safety) - Immediate crash prevention
2. **Phase 4** (Clear pointers) - Prevent stale pointer access
3. **Phase 1** (State management) - Proper lifecycle control
4. **Phase 3** (Reference counting) - If needed after Phase 1

## Risk Assessment

| Change | Risk | Mitigation |
|--------|------|------------|
| Null checks | Low | Simple guards, no behavior change |
| Pointer clearing | Low | Defensive, no behavior change |
| State management | Medium | Requires careful placement of state transitions |
| Reference counting | High | Complex synchronization, may introduce deadlocks |

## Rollback Plan

Each phase can be reverted independently. If issues arise:
1. Revert the specific phase's changes
2. The null checks (Phase 2) should remain as they're purely defensive

## Open Questions

1. Should we use `atomic_int` for `pending_ops` or rely on libuv's single-threaded model?
2. Should state transitions be logged for debugging?
3. Is there a need for a connection pool to reuse connections instead of frequent alloc/free?
