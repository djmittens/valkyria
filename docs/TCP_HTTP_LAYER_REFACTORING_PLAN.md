# TCP/HTTP Layer Refactoring Plan

## Overview

This plan addresses the triple duplication in AIO buffer management code and establishes clean separation between the TCP layer (`aio_conn_io`) and HTTP layer (`aio_http2_conn`).

## Current State Analysis

### Problem: Triple Duplication

| Function | `aio_conn_io.c` | `aio_http2_conn.c` | `aio_uv.c` |
|----------|-----------------|--------------------| -----------|
| write_buf_acquire | `valk_conn_io_write_buf_acquire` | `valk_http2_conn_write_buf_acquire` (wrapper) | `__conn_write_buf_acquire` (static) |
| write_buf_data | `valk_conn_io_write_buf_data` | `valk_http2_conn_write_buf_data` (wrapper) | `__conn_write_buf_data` (static) |
| write_buf_available | `valk_conn_io_write_buf_available` | `valk_http2_conn_write_buf_available` (wrapper) | `__conn_write_buf_available` (static) |
| write_buf_flush | `valk_conn_io_flush` (dead) | `valk_http2_conn_write_buf_flush` | `__conn_write_buf_flush` (static) |
| alloc_callback | N/A | `valk_http2_conn_alloc_callback` | `__alloc_callback` (static) |
| backpressure_add | N/A | `valk_http2_backpressure_list_add` (dead wrapper) | `__backpressure_list_add` (static) |

### Why This Happened

The refactoring started (`aio_conn_io.c` created) but:
1. `aio_uv.c` still has its own static versions
2. `aio_http2_conn.c` delegates to `aio_conn_io.c` but `aio_uv.c` uses its own statics
3. Both `aio_http2_conn.c` and `aio_uv.c` are compiled and linked

### Design Goal

Support multiple protocols (HTTP/2, future RPC) over the same TCP buffer management layer:

```
┌─────────────────────────────────────────────────────┐
│                   Protocol Layer                     │
│  ┌─────────────────┐  ┌─────────────────┐           │
│  │ aio_http2_conn  │  │  future: rpc    │           │
│  │ aio_http2_server│  │                 │           │
│  │ aio_http2_client│  │                 │           │
│  └────────┬────────┘  └────────┬────────┘           │
│           │                    │                     │
│           ▼                    ▼                     │
│  ┌─────────────────────────────────────────┐        │
│  │           TCP Buffer Layer               │        │
│  │           (aio_conn_io)                  │        │
│  │  - Read/write buffer management          │        │
│  │  - Flush with callback                   │        │
│  │  - SSL/TLS integration                   │        │
│  └─────────────────────────────────────────┘        │
│                        │                             │
│                        ▼                             │
│  ┌─────────────────────────────────────────┐        │
│  │           libuv / OS Layer               │        │
│  └─────────────────────────────────────────┘        │
└─────────────────────────────────────────────────────┘
```

---

## Phase 1: Establish Single Source of Truth for TCP Buffer Operations

### Step 1.1: Remove static duplicates from `aio_uv.c`

**Goal**: All TCP buffer operations go through `valk_conn_io_*` functions.

**Delete from `aio_uv.c`**:
- [ ] `__conn_write_buf_acquire` (lines ~46-60)
- [ ] `__conn_write_buf_data` (lines ~114-117)
- [ ] `__conn_write_buf_available` (lines ~119-122)
- [ ] `__conn_write_buf_flush` (lines ~128-163)
- [ ] `__conn_write_buf_on_flush_complete` (lines ~169-203)
- [ ] `__alloc_callback` (lines ~63-110) - consolidate with `valk_http2_conn_alloc_callback`

**Replace usages with**:
- `valk_http2_conn_write_buf_acquire(conn)`
- `valk_http2_conn_write_buf_data(conn)`
- `valk_http2_conn_write_buf_available(conn)`
- `valk_http2_conn_write_buf_flush(conn)`
- `valk_http2_conn_alloc_callback`

**Validation**:
```bash
# No static buffer functions should remain in aio_uv.c
grep -n "__conn_write_buf\|__conn_read_buf" src/aio/aio_uv.c
# Expected: 0 matches

# All buffer operations go through conn_io or http2_conn
grep -c "valk_conn_io_\|valk_http2_conn_" src/aio/aio_uv.c
# Expected: multiple matches
```

### Step 1.2: Wire up the flush callback properly

**Problem**: `valk_conn_io_flush()` has a hardcoded callback that doesn't do backpressure handling.

**Current signature** (broken):
```c
typedef void (*valk_conn_io_flush_cb)(valk_aio_handle_t *conn, int status);
int valk_conn_io_flush(valk_conn_io_t *io, uv_stream_t *stream, 
                       valk_conn_io_flush_cb on_complete);
```

**New signature** (protocol-agnostic):
```c
typedef void (*valk_conn_io_flush_cb)(void *ctx, int status);
int valk_conn_io_flush(valk_conn_io_t *io, uv_stream_t *stream, 
                       valk_conn_io_flush_cb cb, void *ctx);
```

**Changes needed**:
- [ ] Update `aio_conn_io.h` with new callback signature
- [ ] Update `aio_conn_io.c` to store and invoke callback with context
- [ ] Update `aio_http2_conn.c` to provide HTTP-specific flush callback

**Validation**:
```bash
# The flush function should be called from http2_conn
grep -n "valk_conn_io_flush" src/aio/*.c
# Expected: definition in aio_conn_io.c, calls from aio_http2_conn.c
```

---

## Phase 2: HTTP Wrapper Strategy

Keep thin HTTP wrappers that add protocol-specific context:

```c
// aio_http2_conn.c - HTTP-specific buffer operations
// These extract slab from conn->sys->tcpBufferSlab

bool valk_http2_conn_write_buf_acquire(valk_aio_handle_t *conn) {
  if (!conn->sys || !conn->sys->tcpBufferSlab) return false;
  return valk_conn_io_write_buf_acquire(&conn->http.io, conn->sys->tcpBufferSlab);
}
```

This maintains clean layering:
- TCP layer (`valk_conn_io_*`) takes explicit `slab` parameter
- HTTP layer (`valk_http2_conn_*`) knows where to get the slab

**No changes needed** - this is already the pattern in `aio_http2_conn.c`.

---

## Phase 3: Remove Dead Code

### Step 3.1: Remove unused functions from `aio_conn_io.c`

**Delete**:
- [ ] `valk_conn_io_read_buf_release()` (lines 35-40) - never called
- [ ] `valk_conn_io_write_buf_release()` (lines 68-74) - never called
- [ ] `valk_conn_io_on_flush_complete()` (lines 161-164) - never called
- [ ] `__conn_io_flush_cb()` (lines 110-126) - internal, used by dead flush

**Update `aio_conn_io.h`** to remove declarations:
- [ ] Remove `valk_conn_io_read_buf_release` declaration
- [ ] Remove `valk_conn_io_write_buf_release` declaration
- [ ] Remove `valk_conn_io_on_flush_complete` declaration

### Step 3.2: Remove unused public wrappers from `aio_http2_conn.c`

**Delete**:
- [ ] `valk_http2_backpressure_list_add()` (lines 18-20) - only internal `__backpressure_list_add` is used
- [ ] `valk_http2_backpressure_list_remove()` (lines 22-24) - only internal version used

**Update `aio_http2_conn.h`** to remove declarations:
- [ ] Remove `valk_http2_backpressure_list_add` declaration
- [ ] Remove `valk_http2_backpressure_list_remove` declaration

**Validation**:
```bash
# These functions should not exist
grep -n "valk_conn_io_read_buf_release\|valk_conn_io_write_buf_release\|valk_conn_io_on_flush_complete" src/aio/aio_conn_io.c
# Expected: 0 matches

grep -n "^bool valk_http2_backpressure_list_add\|^void valk_http2_backpressure_list_remove" src/aio/aio_http2_conn.c
# Expected: 0 matches
```

---

## Phase 4: Consolidate Alloc Callbacks

### Problem

Two alloc callbacks exist:
- `__alloc_callback` in `aio_uv.c` (lines 63-110)
- `valk_http2_conn_alloc_callback` in `aio_http2_conn.c` (lines 41-81)

They do nearly identical things.

### Solution

- [ ] Delete `__alloc_callback` from `aio_uv.c`
- [ ] Use `valk_http2_conn_alloc_callback` everywhere HTTP connections are read
- [ ] Update all `uv_read_start` calls to use `valk_http2_conn_alloc_callback`

**Validation**:
```bash
# Only one alloc callback for HTTP connections
grep -rn "uv_read_start.*__alloc" src/aio/*.c
# Expected: 0 matches

grep -rn "uv_read_start.*valk_http2_conn_alloc" src/aio/*.c
# Expected: matches in aio_http2_server.c, aio_http2_client.c, aio_http2_conn.c
```

---

## Phase 5: Remove HTTP-specific Constants from TCP Layer

### Problem

`aio_conn_io.c` uses HTTP-specific types:
- `HTTP_SLAB_ITEM_SIZE` (defined in `aio_internal.h`)
- `__tcp_buffer_slab_item_t` (HTTP-specific buffer layout)

### Solution

**Option A: Pass buffer size at init** (Recommended)

```c
// aio_conn_io.h
typedef struct valk_conn_io {
  valk_slab_item_t *read_buf;
  valk_slab_item_t *write_buf;
  size_t write_pos;
  size_t buf_size;              // NEW: size passed at init
  bool write_flush_pending;
  uv_write_t write_req;
  uv_buf_t write_uv_buf;
  valk_aio_ssl_t ssl;
} valk_conn_io_t;

void valk_conn_io_init(valk_conn_io_t *io, size_t buf_size);
size_t valk_conn_io_buf_size(const valk_conn_io_t *io);
```

**Changes needed**:
- [ ] Add `buf_size` field to `valk_conn_io_t`
- [ ] Update `valk_conn_io_init` to accept and store `buf_size`
- [ ] Replace `HTTP_SLAB_ITEM_SIZE` with `io->buf_size` in `aio_conn_io.c`
- [ ] Update callers to pass `HTTP_SLAB_ITEM_SIZE` at init time

**Option B: Keep using slab item size**

The slab already knows its item size, so we could query it. But this couples the TCP layer to slab internals.

**Validation**:
```bash
# No HTTP constants in conn_io
grep -n "HTTP_SLAB_ITEM_SIZE\|HTTP2_MAX" src/aio/aio_conn_io.c
# Expected: 0 matches

# No HTTP-specific includes
grep -n "#include.*http2\|#include.*nghttp" src/aio/aio_conn_io.c src/aio/aio_conn_io.h
# Expected: 0 matches
```

---

## Phase 6: Final Validation Checks

### Build Validation
```bash
make clean && make build
# Expected: Success with no warnings about unused functions
```

### Test Validation
```bash
make test
# Expected: All tests pass
```

### Dead Code Validation
```bash
# Check for orphaned declarations in headers
for func in valk_conn_io_read_buf_release valk_conn_io_write_buf_release valk_conn_io_on_flush_complete valk_http2_backpressure_list_add valk_http2_backpressure_list_remove; do
  echo "=== Checking $func ==="
  count=$(grep -rn "$func" src/aio/ | wc -l)
  echo "Found $count occurrences"
  if [ "$count" -gt 0 ]; then
    echo "ERROR: $func should be removed"
    grep -rn "$func" src/aio/
  fi
done
# Expected: 0 occurrences for each function
```

### Duplication Validation
```bash
# Count implementations of buffer operations per file
echo "=== Buffer operation counts ==="
for file in src/aio/aio_uv.c src/aio/aio_http2_conn.c src/aio/aio_conn_io.c; do
  count=$(grep -c "write_buf_acquire\|write_buf_data\|write_buf_available\|write_buf_flush" "$file" 2>/dev/null || echo 0)
  echo "$file: $count"
done
# Expected: 
#   aio_conn_io.c: ~4 (the implementations)
#   aio_http2_conn.c: ~8 (thin wrappers calling conn_io + their own flush)
#   aio_uv.c: ~4 (calls to http2_conn functions, not implementations)
```

### Layer Separation Validation
```bash
# TCP layer (conn_io) should not include HTTP-specific headers
echo "=== Checking TCP layer isolation ==="
grep -n "#include.*http2\|#include.*nghttp" src/aio/aio_conn_io.c src/aio/aio_conn_io.h
# Expected: 0 matches

# TCP layer should not use HTTP constants directly
grep -n "HTTP_\|HTTP2_\|nghttp2" src/aio/aio_conn_io.c
# Expected: 0 matches (after Phase 5)
```

### Comprehensive grep check
```bash
# Run all validations
echo "=== VALIDATION SUITE ==="

echo ""
echo "1. No static buffer functions in aio_uv.c:"
grep -c "__conn_write_buf\|__conn_read_buf" src/aio/aio_uv.c && echo "FAIL" || echo "PASS"

echo ""
echo "2. No dead functions in aio_conn_io.c:"
grep -c "valk_conn_io_read_buf_release\|valk_conn_io_write_buf_release\|valk_conn_io_on_flush_complete" src/aio/aio_conn_io.c && echo "FAIL" || echo "PASS"

echo ""
echo "3. No dead wrappers in aio_http2_conn.c:"
grep -c "^bool valk_http2_backpressure_list_add\|^void valk_http2_backpressure_list_remove" src/aio/aio_http2_conn.c && echo "FAIL" || echo "PASS"

echo ""
echo "4. No __alloc_callback in aio_uv.c:"
grep -c "__alloc_callback" src/aio/aio_uv.c && echo "FAIL" || echo "PASS"

echo ""
echo "5. HTTP constants not in TCP layer:"
grep -c "HTTP_SLAB_ITEM_SIZE" src/aio/aio_conn_io.c && echo "FAIL" || echo "PASS"

echo ""
echo "6. Build succeeds:"
make build >/dev/null 2>&1 && echo "PASS" || echo "FAIL"

echo ""
echo "7. Tests pass:"
make test >/dev/null 2>&1 && echo "PASS" || echo "FAIL"
```

---

## Execution Order

1. **Phase 1.1**: Delete static duplicates from `aio_uv.c`, replace with calls to `aio_http2_conn`
2. **Phase 4**: Consolidate alloc callbacks (part of Phase 1.1)
3. **Phase 1.2**: Fix `valk_conn_io_flush` callback signature  
4. **Phase 3**: Delete dead code from `aio_conn_io.c` and `aio_http2_conn.c`
5. **Phase 5**: Remove HTTP constants from TCP layer
6. **Phase 6**: Run all validations

---

## Files Modified

| File | Changes |
|------|---------|
| `src/aio/aio_conn_io.h` | Remove dead declarations, update flush signature, add buf_size |
| `src/aio/aio_conn_io.c` | Remove dead functions, update flush impl, use buf_size |
| `src/aio/aio_http2_conn.h` | Remove dead declarations |
| `src/aio/aio_http2_conn.c` | Remove dead wrappers, update flush to use new signature |
| `src/aio/aio_uv.c` | Remove all static buffer functions, use http2_conn functions |
| `src/aio/aio_internal.h` | No changes (HTTP constants stay here for HTTP layer) |

---

## Rollback Plan

If issues arise:
```bash
git stash  # or git checkout -- src/aio/
```

All changes are in `src/aio/` directory and can be reverted atomically.
