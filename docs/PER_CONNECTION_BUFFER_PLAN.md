# Per-Connection Buffer Redesign

## Implementation Status

**Phase 1 (Read Path): COMPLETE**
- Per-connection `read_buf` field added to `valk_aio_handle_t`
- `__alloc_callback` reuses existing read buffer instead of acquiring new one each time
- Read buffer held until connection close (released in `__uv_handle_closed_cb`)
- Slab sizing updated to `2 * max_connections`
- All tests updated and passing

**Phase 2 (Write Path): COMPLETE**
- Per-connection `write_buf`, `write_pos`, `write_flush_pending`, `write_req`, `write_uv_buf` fields added
- New functions: `__conn_write_buf_acquire()`, `__conn_write_buf_flush()`, `__conn_write_buf_on_flush_complete()`
- Server read callback (`__http_tcp_read_cb`) uses per-connection write buffer for SSL output
- Client SSL handshake (`__uv_http2_connect_cb`) uses per-connection write buffer
- Removed obsolete `__http_tcp_on_write_cb` (old per-write slab acquire/release model)
- Write buffer released back to slab on connection close (`__uv_handle_closed_cb`)
- All tests passing

**Phase 4 (SSL Integration): COMPLETE**
- SSL read path already using per-connection write buffer (in `__http_tcp_read_cb`)
- SSL write path uses per-connection buffer for encrypted output
- Client handshake (`__uv_http2_connect_cb`) uses per-connection write buffer
- All SSL operations correctly track activity for timeout purposes

**Phase 5 (Configuration): COMPLETE**
- Added `max_connections_per_client` field to `valk_aio_system_config_t` (default: 2)
- Updated slab sizing formula: `(max_servers * max_connections + max_clients * max_connections_per_client) * 4`
- Added timeout configuration fields:
  - `pending_stream_timeout_ms` (default: 10000ms = 10s)
  - `connection_idle_timeout_ms` (default: 60000ms = 60s)
  - `maintenance_interval_ms` (default: 1000ms = 1s)
- Updated tests to match new formula

**Phase 6 (Timeouts): COMPLETE**
- Added `maintenance_timer` to `valk_aio_system_t` for periodic timeout checks
- Added `last_activity_ms` field to connection handle for idle tracking
- Implemented `__maintenance_timer_cb()` which checks:
  - Connection idle timeouts: closes connections that haven't had activity in `connection_idle_timeout_ms`
  - Pending stream timeouts: sends RST_STREAM and removes streams waiting longer than `pending_stream_timeout_ms`
  - Backpressure timeouts: closes connections in backpressure longer than `backpressure_timeout_ms`
- Activity timestamp updated on read and successful write flush
- Timer properly stopped and closed during shutdown

**Phase 7 (Simplification): DEFERRED**
- The backpressure list is still needed for managing connections under memory pressure
- Future work could simplify this once timeout enforcement is proven stable in production

### Key Behavioral Changes from Phase 1 & 2

1. **Buffer retention**: Read buffers are now held for the lifetime of the connection instead of being released after each read operation.

2. **Write buffer model**: Write buffer acquired on first write, data accumulated until flush, then released on write completion callback. Buffer positions reset for reuse.

3. **Pool sizing**: The default `tcp_buffer_pool_size` is now `4 × total_connections` where:
   - `total_connections = (max_servers × max_connections) + (max_clients × max_connections_per_client)`
   - This accounts for read + write + temp frame buffers with headroom

4. **Test configuration**: Tests that stress the buffer pool now need larger pool sizes since buffers aren't recycled as quickly. Tests were updated to use adequate pool sizes.

5. **Timeout enforcement**: A maintenance timer now periodically checks for:
   - Idle connections (no activity for `connection_idle_timeout_ms`)
   - Stalled pending streams (waiting for arena longer than `pending_stream_timeout_ms`)
   - Stuck backpressure (in backpressure list longer than `backpressure_timeout_ms`)

### Remaining Work

All planned phases are complete. Optional future improvements:
1. **Idle buffer reclamation**: Release read buffers from idle connections after timeout
2. **Request timeout**: Add per-request timeout for long-running handlers
3. **Stream idle timeout**: Add per-stream timeout separate from connection timeout

## Executive Summary

The current TCP buffer slab design causes test hangs and potential production issues under load. This document outlines a redesign to use per-connection buffers (both read and write) allocated from a shared slab, where each connection holds **at most one** buffer of each type at a time.

## Problem Statement

### Current Architecture

```
Global TCP Buffer Slab (N items, ~32KB each)
    ├── Connection A grabs buffer → uv_write → holds until callback
    ├── Connection A grabs another buffer → uv_write → holds
    ├── Connection B grabs buffer → uv_write → holds until callback
    ├── Connection C tries to grab → EXHAUSTED
    └── Reads and writes compete for same pool
```

### Failure Modes

1. **Write starvation**: Connection A has slow client, holds multiple buffers waiting for `uv_write` callbacks. Other connections can't acquire.

2. **Read/Write interference**: Writes hold buffers across async boundaries (long-lived), reads need buffers synchronously (short-lived). Slow writes starve reads.

3. **Unpredictable capacity**: With N buffers and M connections, if any connection can grab multiple buffers, worst case is N/M buffers per connection - but one greedy connection can take all N.

### Root Cause

The fundamental issue is **unbounded buffer acquisition per connection**. A single slow connection can hold multiple write buffers simultaneously, exhausting the pool for everyone else.

## Proposed Solution: One Buffer Per Connection

### Key Insight

Each connection needs **at most one** read buffer and **at most one** write buffer at any time:

- **Writes**: Fill buffer → `uv_write` → wait for callback → release → repeat
- **Reads**: `uv_read` callback → process → release (or hold for next read)

By enforcing this invariant, slab size = `2 × total_connections` guarantees no starvation.

**Note**: An AIO system can host multiple servers and clients. Total connections = sum of all server connections + all client connections.

### New Architecture

```
TCP Buffer Slab (2 × max_connections items)
    ├── Connection A: [read_buf] [write_buf]  ← at most 1 each
    ├── Connection B: [read_buf] [write_buf]
    ├── Connection C: [read_buf] [NULL]       ← no pending write
    └── Connection D: [NULL]     [write_buf]  ← idle, has pending write
```

### Buffer Lifecycle

**Write Buffer:**
```
Connection state: write_buf = NULL

1. Need to send data:
   - If write_buf == NULL: acquire from slab, attach to connection
   - Append data to write_buf

2. Buffer ready to flush:
   - Call uv_write with write_buf
   - Mark flush_pending = true

3. uv_write callback fires:
   - Release write_buf back to slab
   - Set write_buf = NULL
   - If more data pending: acquire new buffer, repeat
```

**Read Buffer:**
```
Connection state: read_buf = NULL

1. uv_read alloc callback:
   - If read_buf == NULL: acquire from slab, attach to connection
   - Return read_buf to libuv

2. uv_read data callback:
   - Process data (SSL decrypt, feed to nghttp2)
   - Keep read_buf attached (will reuse for next read)

3. Connection closes:
   - Release read_buf back to slab
```

### Why This Works

1. **Guaranteed capacity**: With `2 × max_connections` buffers, every connection can have both a read and write buffer simultaneously.

2. **No starvation**: One slow connection holds at most 1 write buffer. Its slowness only affects itself (buffer fills up → stop pulling from nghttp2 → HTTP/2 flow control kicks in).

3. **Simple mental model**: Each connection owns 0-2 buffers. No complex backpressure lists needed.

4. **Memory efficient**: Idle connections release buffers. Active connections reuse theirs.

## Implementation Plan

### Phase 1: Data Structure Changes - COMPLETE

**What was implemented:**

1. Added per-connection buffer fields to `valk_aio_handle_t` in `src/aio_uv.c` (lines ~238-244):
```c
valk_slab_item_t *read_buf;      // Acquired on first read, held until close
valk_slab_item_t *write_buf;     // Acquired on write, released after uv_write
size_t write_pos;                // Current fill position in write buffer
bool write_flush_pending;        // uv_write in flight
uv_write_t write_req;            // Reusable write request
uv_buf_t write_uv_buf;           // Reusable uv buffer descriptor
```

2. Updated `tcp_buffer_pool_size` auto-calculation (lines ~4021-4024):
   - Changed from `max_connections * (2 + max_concurrent_streams/8)` to `max_connections * 2`

3. Updated `__alloc_callback` (lines ~274-311):
   - Now checks if connection already has a read buffer and reuses it
   - Only acquires from slab if `conn->http.read_buf` is NULL

4. Updated `__http_tcp_read_cb` (lines ~2603-2707):
   - Removed code that released read buffer after each read
   - Read buffer stays attached until connection close

5. Updated `__uv_handle_closed_cb` (lines ~1361-1383):
   - Releases both `read_buf` and `write_buf` when connection closes

6. Updated tests in:
   - `test/test_aio_config.c` - Fixed expected pool size calculations
   - `test/test_aio_load_shedding.c` - Adjusted test parameters for new model
   - `test/test_aio_uv_coverage.c` - Increased buffer pools for backpressure tests
   - `test/test_backpressure.valk` - Increased pool sizes
   - `test/test_pending_streams.valk` - Added explicit buffer config

#### 1.1 Connection Buffer Pointers - COMPLETE

```c
// In valk_aio_handle_t.http:
struct {
    // ... existing fields ...
    
    // Per-connection buffer management
    valk_slab_item_t *read_buf;      // Acquired on first read, held until close
    valk_slab_item_t *write_buf;     // Acquired on write, released after uv_write
    
    // Write buffer state
    size_t write_pos;                // Current fill position
    size_t write_capacity;           // Buffer capacity
    bool write_flush_pending;        // uv_write in flight
    uv_write_t write_req;            // Reusable write request
    uv_buf_t write_uv_buf;           // Reusable uv buffer descriptor
} http;
```

#### 1.2 Slab Sizing - COMPLETE (Simplified)

```c
// Actual implementation in valk_aio_system_config_resolve():
// Simplified formula: 2 buffers per connection (1 read + 1 write)
if (cfg->tcp_buffer_pool_size == 0) {
  cfg->tcp_buffer_pool_size = cfg->max_connections * 2;
}
```

**Note**: The original plan called for `(servers * conns) + (clients * conns_per_client)` but the current implementation uses the simpler `max_connections * 2`. This works because the system shares a single connection pool.

#### 1.3 Buffer Item Structure

```c
// Simplified - no longer need uv_write_t embedded in slab item
typedef struct valk_tcp_buffer_item {
    uint8_t data[TCP_BUFFER_SIZE];  // 64KB default
} valk_tcp_buffer_item_t;
```

### Phase 2: Write Path Changes - COMPLETE

#### 2.1 Acquire-On-Demand Write Buffer

```c
static valk_slab_item_t* __conn_acquire_write_buf(valk_aio_handle_t *conn) {
    if (conn->http.write_buf) {
        return conn->http.write_buf;  // Already have one
    }
    
    valk_slab_item_t *item = valk_slab_aquire(tcp_buffer_slab);
    if (!item) {
        // Slab exhausted - should not happen if sized correctly
        VALK_ERROR("Write buffer slab exhausted (bug: check slab sizing)");
        return NULL;
    }
    
    conn->http.write_buf = item;
    conn->http.write_pos = 0;
    conn->http.write_capacity = TCP_BUFFER_SIZE;
    return item;
}
```

#### 2.2 Flush and Release

```c
static void __conn_flush_write_buf(valk_aio_handle_t *conn) {
    if (!conn->http.write_buf || conn->http.write_flush_pending) {
        return;
    }
    if (conn->http.write_pos == 0) {
        return;  // Nothing to flush
    }
    
    valk_tcp_buffer_item_t *buf = (void*)conn->http.write_buf->data;
    
    conn->http.write_uv_buf.base = (char*)buf->data;
    conn->http.write_uv_buf.len = conn->http.write_pos;
    conn->http.write_flush_pending = true;
    conn->http.write_req.data = conn;
    
    uv_write(&conn->http.write_req, (uv_stream_t*)&conn->uv.tcp,
             &conn->http.write_uv_buf, 1, __conn_write_cb);
}

static void __conn_write_cb(uv_write_t *req, int status) {
    valk_aio_handle_t *conn = req->data;
    
    // Release write buffer back to slab
    if (conn->http.write_buf) {
        valk_slab_release(tcp_buffer_slab, conn->http.write_buf);
        conn->http.write_buf = NULL;
    }
    conn->http.write_flush_pending = false;
    conn->http.write_pos = 0;
    
    if (status != 0) {
        // Handle write error - close connection
        return;
    }
    
    // If more data pending, acquire new buffer and continue
    if (conn->http.pending_write) {
        __http2_flush_to_conn_buffer(conn);
        __conn_flush_write_buf(conn);
    }
}
```

#### 2.3 Append to Write Buffer

```c
static bool __conn_write_append(valk_aio_handle_t *conn, 
                                 const uint8_t *data, size_t len) {
    if (conn->http.write_flush_pending) {
        // Can't append while flush in progress
        // Caller should wait or queue
        return false;
    }
    
    valk_slab_item_t *item = __conn_acquire_write_buf(conn);
    if (!item) return false;
    
    valk_tcp_buffer_item_t *buf = (void*)item->data;
    size_t space = conn->http.write_capacity - conn->http.write_pos;
    
    if (len > space) {
        // Buffer full - need to flush first
        return false;
    }
    
    memcpy(buf->data + conn->http.write_pos, data, len);
    conn->http.write_pos += len;
    return true;
}
```

#### 2.4 Handling Buffer Full / Flush Pending

When `__conn_write_append` returns `false`, the caller (nghttp2 send callback) must handle backpressure:

```c
// In nghttp2 send callback:
static ssize_t __nghttp2_send_callback(nghttp2_session *session,
                                        const uint8_t *data, size_t length,
                                        int flags, void *user_data) {
    valk_aio_handle_t *conn = user_data;
    
    // Case 1: Flush in progress - tell nghttp2 to retry later
    if (conn->http.write_flush_pending) {
        return NGHTTP2_ERR_WOULDBLOCK;
    }
    
    // Case 2: Try to append
    if (!__conn_write_append(conn, data, length)) {
        // Buffer full - flush what we have, then tell nghttp2 to retry
        __conn_flush_write_buf(conn);
        return NGHTTP2_ERR_WOULDBLOCK;
    }
    
    return (ssize_t)length;
}
```

**Flow when buffer fills:**

```
1. nghttp2 generates frames → calls send_callback
2. __conn_write_append fills buffer
3. Buffer full → __conn_write_append returns false
4. __conn_flush_write_buf initiates uv_write, sets flush_pending=true
5. send_callback returns NGHTTP2_ERR_WOULDBLOCK
6. nghttp2 stops generating frames, sets session.pending_write=true
7. ... uv_write completes asynchronously ...
8. __conn_write_cb fires, releases buffer, flush_pending=false
9. Check pending_write → call nghttp2_session_send() to resume
10. nghttp2 retries, send_callback succeeds, cycle continues
```

This provides natural backpressure: slow kernel send buffer → slow uv_write → buffer stays full → nghttp2 blocks → HTTP/2 flow control kicks in → client stops sending.

### Phase 3: Read Path Changes - COMPLETE

#### 3.1 Acquire-On-Demand Read Buffer - COMPLETE

```c
void __alloc_callback(uv_handle_t *handle, size_t suggested_size,
                      uv_buf_t *buf) {
    UNUSED(suggested_size);
    valk_aio_handle_t *conn = handle->data;
    
    // Reuse existing read buffer if we have one
    if (conn->http.read_buf) {
        valk_tcp_buffer_item_t *item = (void*)conn->http.read_buf->data;
        buf->base = (char*)item->data;
        buf->len = TCP_BUFFER_SIZE;
        return;
    }
    
    // Acquire new read buffer
    valk_slab_item_t *item = valk_slab_aquire(tcp_buffer_slab);
    if (!item) {
        // Slab exhausted - return empty buffer, libuv will handle
        buf->base = NULL;
        buf->len = 0;
        VALK_WARN("Read buffer slab exhausted");
        return;
    }
    
    conn->http.read_buf = item;
    valk_tcp_buffer_item_t *data = (void*)item->data;
    buf->base = (char*)data->data;
    buf->len = TCP_BUFFER_SIZE;
}
```

#### 3.2 Read Callback (No Release) - COMPLETE

```c
static void __http_tcp_read_cb(uv_stream_t *stream, ssize_t nread,
                               const uv_buf_t *buf) {
    valk_aio_handle_t *conn = stream->data;
    
    // Handle errors
    if (nread < 0) {
        // Connection closed or error - release read buffer
        if (conn->http.read_buf) {
            valk_slab_release(tcp_buffer_slab, conn->http.read_buf);
            conn->http.read_buf = NULL;
        }
        // Close connection...
        return;
    }
    
    if (nread == 0) {
        return;  // EAGAIN, keep buffer for next read
    }
    
    // Process data (SSL, nghttp2, etc.)
    // ...
    
    // Keep read_buf attached - will reuse for next uv_read
}
```

#### 3.3 Release on Connection Close - COMPLETE

```c
static void __uv_handle_closed_cb(uv_handle_t *handle) {
    valk_aio_handle_t *conn = handle->data;
    
    // Release any held buffers
    if (conn->http.read_buf) {
        valk_slab_release(tcp_buffer_slab, conn->http.read_buf);
        conn->http.read_buf = NULL;
    }
    if (conn->http.write_buf) {
        valk_slab_release(tcp_buffer_slab, conn->http.write_buf);
        conn->http.write_buf = NULL;
    }
    
    // ... rest of cleanup
}
```

### Phase 4: SSL/TLS Integration - NOT STARTED

#### 4.1 SSL Read Path

The SSL layer needs buffers for decryption. Use the existing `valk_conn_read_buf_t` structure:

```c
// Already exists in aio_conn_buffer.h
typedef struct valk_conn_read_buf {
    uint8_t encrypted[32KB];    // Raw TLS data from socket
    uint8_t decrypted[32KB];    // Decrypted plaintext for nghttp2
    // ... length/consumed tracking
} valk_conn_read_buf_t;
```

**Read flow:**
1. `uv_read` fills slab buffer with encrypted data
2. Copy to `conn->ssl.read_buf.encrypted` 
3. SSL decrypts to `conn->ssl.read_buf.decrypted`
4. Feed decrypted data to nghttp2
5. Slab buffer stays attached for next `uv_read`

#### 4.2 SSL Write Path

For writes, we need to encrypt plaintext from nghttp2 before sending:

**Option A: Two-phase buffer (recommended)**

```c
// Write buffer layout:
// [plaintext region: 0..capacity/2] [ciphertext region: capacity/2..capacity]

static bool __conn_ssl_write_append(valk_aio_handle_t *conn,
                                     const uint8_t *plaintext, size_t len) {
    valk_slab_item_t *item = __conn_acquire_write_buf(conn);
    if (!item) return false;
    
    valk_tcp_buffer_item_t *buf = (void*)item->data;
    size_t half = conn->http.write_capacity / 2;
    
    // Append plaintext to first half
    if (conn->http.write_pos + len > half) {
        return false;  // Plaintext region full
    }
    memcpy(buf->data + conn->http.write_pos, plaintext, len);
    conn->http.write_pos += len;
    return true;
}

static void __conn_ssl_flush(valk_aio_handle_t *conn) {
    valk_tcp_buffer_item_t *buf = (void*)conn->http.write_buf->data;
    size_t half = conn->http.write_capacity / 2;
    
    // Encrypt plaintext (first half) into ciphertext (second half)
    size_t cipher_len = 0;
    int rc = SSL_write_to_buffer(conn->ssl.ctx,
                                  buf->data, conn->http.write_pos,        // plaintext in
                                  buf->data + half, half, &cipher_len);   // ciphertext out
    
    // Send ciphertext
    conn->http.write_uv_buf.base = (char*)(buf->data + half);
    conn->http.write_uv_buf.len = cipher_len;
    conn->http.write_flush_pending = true;
    
    uv_write(&conn->http.write_req, ...);
}
```

**Option B: Separate slab acquisition for ciphertext**

Acquire a second buffer for ciphertext output. More memory usage but simpler buffer management. Not recommended since it breaks the "1 write buffer per connection" invariant.

#### 4.3 Non-SSL Path

For plaintext connections, the write buffer is used directly:

```c
static void __conn_plaintext_flush(valk_aio_handle_t *conn) {
    valk_tcp_buffer_item_t *buf = (void*)conn->http.write_buf->data;
    
    conn->http.write_uv_buf.base = (char*)buf->data;
    conn->http.write_uv_buf.len = conn->http.write_pos;
    conn->http.write_flush_pending = true;
    
    uv_write(&conn->http.write_req, ...);
}

### Phase 5: Configuration Changes - PARTIAL

#### 5.1 Simplified Configuration

```c
typedef struct valk_aio_system_config {
    // ... existing fields ...
    
    // Buffer settings
    size_t conn_buffer_size;     // Per-buffer size (default: 64KB)
    // tcp_buffer_pool_size is now auto-calculated: 2 * max_connections
} valk_aio_system_config_t;
```

#### 5.2 Auto-Calculation

```c
int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg) {
    // Buffer size defaults
    if (cfg->conn_buffer_size == 0) {
        cfg->conn_buffer_size = 64 * 1024;  // 64KB default
    }
    
    // Total connections = server connections + client connections
    //
    // Server connections:
    //   max_servers * max_connections
    //   (each server can accept up to max_connections)
    //
    // Client connections:
    //   max_clients * max_connections_per_client
    //   
    //   For HTTP/2: typically 1 connection per client is sufficient due to
    //   stream multiplexing. Additional connections only needed when:
    //   - max_concurrent_streams limit is reached
    //   - max_requests_per_connection limit is reached  
    //   - GOAWAY received and draining
    //
    //   For HTTP/1.1: multiple connections required for concurrency
    //
    // Conservative approach: allocate for worst case (all at capacity)
    // This guarantees no buffer exhaustion under any load pattern.
    
    size_t server_conns = cfg->max_servers * cfg->max_connections;
    size_t client_conns = cfg->max_clients * cfg->max_connections_per_client;
    size_t total_conns = server_conns + client_conns;
    
    // Slab size = 2 buffers per connection (1 read + 1 write)
    if (cfg->tcp_buffer_pool_size == 0) {
        cfg->tcp_buffer_pool_size = 2 * total_conns;
    }
    
    // ... rest of config resolution
}
```

#### 5.3 Configuration Fields

```c
typedef struct valk_aio_system_config {
    // ... existing fields ...
    
    // Server limits
    uint32_t max_servers;                 // Max HTTP servers (default: 8)
    uint32_t max_connections;             // Max connections per server (default: 100)
    
    // Client limits  
    uint32_t max_clients;                 // Max HTTP/2 client instances (default: 8)
    uint32_t max_connections_per_client;  // Connections per client (default: 2)
                                          // = num_upstreams + headroom for failover/draining
                                          // HTTP/2: 1 per upstream (multiplexed)
                                          // HTTP/1.1: multiply by concurrency needs
    
    // Buffer pool (auto-calculated if 0)
    uint32_t tcp_buffer_pool_size;        // Total buffers in slab
    size_t conn_buffer_size;              // Size per buffer (default: 64KB)
} valk_aio_system_config_t;
```

#### 5.4 HTTP/2 Connection Pooling

Per Envoy's documentation, HTTP/2 connection pools work as follows:

> "The HTTP/2 connection pool multiplexes multiple requests over a single connection...
> The HTTP/2 connection pool establishes as many connections as are needed to serve requests.
> With no limits, this will be only a single connection."

**However**, `max_connections_per_client` represents total connections a client instance might hold across ALL its upstreams, not just one. A client may need multiple connections for:

1. **Multiple upstreams** - load balancing across N backends
2. **Failover** - connecting to backup while primary times out
3. **Draining** - old connection finishing requests after GOAWAY
4. **Stream limits** - exceeding `max_concurrent_streams` on one upstream
5. **Health checking** - separate connection for health probes

**Recommended formula:**
```
max_connections_per_client = num_upstreams + 1 (for failover/draining headroom)
```

**Implications for our runtime:**

1. **Default `max_connections_per_client = 2`** - handles single upstream + failover
2. For clients with multiple upstreams, increase accordingly
3. For HTTP/1.1 clients (future), multiply by concurrency needs

#### 5.5 Example Configurations

**Single server, no clients:**
```c
valk_aio_system_config_t cfg = {
    .max_servers = 1,
    .max_connections = 100,
    .max_clients = 0,
};
// Auto: (1 * 100) + 0 = 100 conns → 200 buffers
```

**Multi-server deployment:**
```c
valk_aio_system_config_t cfg = {
    .max_servers = 3,
    .max_connections = 100,
    .max_clients = 0,
};
// Auto: (3 * 100) + 0 = 300 conns → 600 buffers
```

**API gateway (servers + HTTP/2 clients):**
```c
valk_aio_system_config_t cfg = {
    .max_servers = 1,
    .max_connections = 1000,          // Frontend connections
    .max_clients = 10,                // 10 client instances
    .max_connections_per_client = 3,  // 2 upstreams + 1 failover headroom
};
// Auto: (1 * 1000) + (10 * 3) = 1030 conns → 2060 buffers
```

**Load balancer with failover:**
```c
// Client talks to 3 upstreams with failover capability
// Worst case: connected to all 3 + 1 draining after GOAWAY
valk_aio_system_config_t cfg = {
    .max_servers = 1,
    .max_connections = 500,
    .max_clients = 5,                 // 5 client instances
    .max_connections_per_client = 4,  // 3 upstreams + 1 failover/drain
};
// Auto: (1 * 500) + (5 * 4) = 520 conns → 1040 buffers
```

**High-throughput client (hitting stream limits):**
```c
// Each client talks to 1 upstream but needs 500 concurrent streams
// max_concurrent_streams=100, so need ceil(500/100) = 5 connections
valk_aio_system_config_t cfg = {
    .max_servers = 0,
    .max_clients = 4,                 // 4 client instances
    .max_connections_per_client = 6,  // 5 for streams + 1 draining
};
// Auto: 0 + (4 * 6) = 24 conns → 48 buffers
```

### Phase 6: Fix Timeout Enforcement - NOT STARTED

**Problem**: The current codebase has timeout configurations that are **never enforced**:

```c
// In valk_aio_system_config_t:
cfg->backpressure_timeout_ms = 30000;    // Configured but NEVER checked
cfg->pending_stream_timeout_ms = 10000;  // Configured but NEVER checked
```

The function `valk_pressure_evaluate()` in `aio_pressure.c` contains the timeout logic, but it's **only called from unit tests**, never from the event loop.

**Impact**:
- Connections stuck in backpressure never time out → resource leak
- Pending streams never time out → memory leak, stuck requests
- No way to recover from slow/dead clients

#### 6.1 Add Maintenance Timer

```c
// In __event_loop() or system init:
static uv_timer_t maintenance_timer;

static void __maintenance_timer_cb(uv_timer_t *timer) {
    valk_aio_system_t *sys = timer->data;
    uint64_t now = uv_now(sys->eventloop);
    
    // Check connection idle timeouts
    __check_connection_idle_timeouts(sys, now);
    
    // Check pending stream timeouts
    __check_pending_stream_timeouts(sys, now);
}

// Start timer during system init:
uv_timer_init(sys->eventloop, &maintenance_timer);
maintenance_timer.data = sys;
uv_timer_start(&maintenance_timer, __maintenance_timer_cb, 1000, 1000);  // Every 1s
```

#### 6.2 Connection Idle Timeout

Close connections that have been idle too long:

```c
static void __check_connection_idle_timeouts(valk_aio_system_t *sys, uint64_t now) {
    // Iterate active connections
    // For each connection:
    uint64_t idle_time = now - conn->http.last_activity_ms;
    
    if (idle_time > sys->config.connection_idle_timeout_ms) {
        VALK_INFO("Connection idle timeout after %lu ms", idle_time);
        __close_connection(conn, "idle timeout");
    }
}
```

**Requires**: Add `last_activity_ms` field to connection, update on read/write.

#### 6.3 Pending Stream Timeout

Close streams that have been waiting too long for a response:

```c
static void __check_pending_stream_timeouts(valk_aio_system_t *sys, uint64_t now) {
    // Iterate pending_stream_queue
    valk_pending_stream_t *ps = pending_stream_head;
    while (ps) {
        valk_pending_stream_t *next = ps->next;
        uint64_t age = now - ps->enqueued_at_ms;
        
        if (age > sys->config.pending_stream_timeout_ms) {
            VALK_WARN("Pending stream %d timeout after %lu ms", ps->stream_id, age);
            // Send 504 Gateway Timeout or RST_STREAM
            __pending_stream_timeout(ps);
            __pending_stream_remove(ps);
        }
        ps = next;
    }
}
```

**Requires**: Add `enqueued_at_ms` field to pending stream struct.

#### 6.4 Request Timeout (Optional)

Timeout individual requests that take too long to complete:

```c
// Per-stream timeout tracking
struct stream_state {
    uint64_t request_start_ms;
    // ...
};

// In maintenance timer:
if (now - stream->request_start_ms > sys->config.request_timeout_ms) {
    // Send RST_STREAM with CANCEL
    nghttp2_submit_rst_stream(session, NGHTTP2_FLAG_NONE, 
                               stream_id, NGHTTP2_CANCEL);
}
```

#### 6.5 Configuration Defaults

```c
// Recommended defaults (align with Envoy edge):
cfg->connection_idle_timeout_ms = 60000;     // 1 minute
cfg->pending_stream_timeout_ms = 10000;      // 10 seconds
cfg->request_timeout_ms = 300000;            // 5 minutes (0 = disabled)
```

### Phase 7: Remove Complex Backpressure - NOT STARTED

With per-connection buffers and proper timeouts, the backpressure system simplifies dramatically:

#### 7.1 Remove Global Backpressure List

```c
// DELETE these:
// static __thread valk_aio_handle_t *backpressure_list_head;
// static __thread size_t backpressure_list_size;
// static void __backpressure_list_add(...)
// static void __backpressure_list_remove(...)
// static void __backpressure_try_resume_one(...)
```

#### 7.2 Per-Connection Flow Control

Backpressure is now per-connection and automatic:

```c
// When write buffer is full:
static bool __conn_write_append(...) {
    // ...
    if (len > space) {
        // Buffer full - stop pulling from nghttp2
        // HTTP/2 flow control will propagate to client
        conn->http.write_buffer_full = true;
        return false;
    }
    // ...
}

// After flush completes:
static void __conn_write_cb(...) {
    // ...
    conn->http.write_buffer_full = false;
    // Resume pulling from nghttp2 if we have pending data
    if (conn->http.pending_write) {
        __http2_flush_to_conn_buffer(conn);
    }
}
```

## Memory Budget

### Single Server Deployment

| Configuration | Connections | Buffer Size | Buffers | Total Memory |
|---------------|-------------|-------------|---------|--------------|
| Default       | 100         | 64KB        | 200     | 12.8 MB      |
| High Scale    | 1000        | 64KB        | 2000    | 128 MB       |
| Extreme       | 10000       | 64KB        | 20000   | 1.28 GB      |

### Multi-Server + Client Deployment

| Servers | Conns/Srv | Clients | Conns/Client | Total Conns | Buffers | Memory  |
|---------|-----------|---------|--------------|-------------|---------|---------|
| 2       | 100       | 10      | 2            | 220         | 440     | 27.5 MB |
| 3       | 500       | 20      | 3            | 1560        | 3120    | 195 MB  |
| 5       | 1000      | 50      | 4            | 5200        | 10400   | 650 MB  |

Formula: 
- `Server Conns = Servers × Conns/Server`
- `Client Conns = Clients × Conns/Client`
- `Conns/Client = num_upstreams + 1` (for failover/draining headroom)
- `Total = Server Conns + Client Conns`
- `Memory = Total × 2 buffers × 64KB`

Note: This is **worst case** (all connections active with both buffers). In practice:
- Idle connections release their write buffer after flush
- Read buffers are held but reused (no churn)
- Failover connections only used during upstream issues
- Not all servers/clients run at max capacity simultaneously
- Actual usage will be significantly lower

## Migration Strategy

### Step 1: Add New Fields (Non-Breaking)

**Files to modify:**
- `src/aio_uv.c` - Add fields to `valk_aio_handle_t` struct

**Changes:**
```c
// In valk_aio_handle_t.http:
valk_slab_item_t *read_buf;
valk_slab_item_t *write_buf;
size_t write_pos;
bool write_flush_pending;
uv_write_t write_req;
uv_buf_t write_uv_buf;
```

### Step 2: Update Configuration

**Files to modify:**
- `src/aio_uv.c` - `valk_aio_system_config_t` struct and `valk_aio_system_config_resolve()`

**Changes:**
- Add `max_servers`, `max_connections_per_client` fields
- Update slab sizing formula in `valk_aio_system_config_resolve()`
- Update slab creation in `__event_loop()` or system init

### Step 3: Implement New Write Path

**Files to modify:**
- `src/aio_uv.c` - Write buffer management functions

**New functions:**
- `__conn_acquire_write_buf()` - Acquire buffer from slab
- `__conn_write_append()` - Append data to buffer  
- `__conn_flush_write_buf()` - Initiate uv_write
- `__conn_write_cb()` - Handle write completion, release buffer

**Functions to modify:**
- `__nghttp2_send_callback()` - Use new buffer append instead of direct slab
- `__http2_flush_frames()` - Replace with `__http2_flush_to_conn_buffer()`
- `__http_continue_pending_send()` - Use new flush mechanism

### Step 4: Implement New Read Path

**Files to modify:**
- `src/aio_uv.c` - Read buffer management

**Functions to modify:**
- `__alloc_callback()` - Reuse `conn->http.read_buf` if present
- `__http_tcp_read_cb()` - Don't release buffer after read
- `__uv_handle_closed_cb()` - Release both read and write buffers

### Step 5: Implement Timeout Enforcement

**Files to modify:**
- `src/aio_uv.c` - Add maintenance timer and timeout checks

**New functions:**
- `__maintenance_timer_cb()` - Periodic timeout checker
- `__check_connection_idle_timeouts()` - Close idle connections
- `__check_pending_stream_timeouts()` - Timeout pending streams

**Fields to add:**
- `conn->http.last_activity_ms` - Track last read/write time
- `pending_stream->enqueued_at_ms` - Track queue time

**Integration points:**
- Start timer in `__event_loop()` or system init
- Update `last_activity_ms` in read/write callbacks
- Set `enqueued_at_ms` when adding to pending queue

### Step 6: Remove Old Code

**Functions to remove:**
- `__backpressure_list_add()`
- `__backpressure_list_remove()`
- `__backpressure_try_resume_one()`

**Variables to remove:**
- `backpressure_list_head`
- `backpressure_list_size`

**Code to simplify:**
- Remove backpressure checks from `__http_tcp_read_cb()`
- Remove backpressure resume calls from `__http_tcp_on_write_cb()`

### Step 7: Update Tests

**Test files to update:**
- `test/unit/test_aio_backpressure.c` - Update for new model
- `test/test_aio_integration.c` - Verify slab sizing
- `test/test_aio_load_shedding.c` - Update backpressure tests

**New tests to add:**
- Per-connection buffer lifecycle tests
- Buffer exhaustion prevention tests (should never exhaust with correct sizing)
- Slow client isolation tests
- Connection idle timeout tests
- Pending stream timeout tests

## Testing Requirements

### Unit Tests

1. Single connection acquires/releases buffers correctly
2. Write buffer fills up → stops accepting data → flushes → resumes
3. Read buffer persists across multiple reads
4. Connection close releases both buffers
5. Slab sized to `2 * max_connections` never exhausts
6. Connection idle timeout fires after configured duration
7. Pending stream timeout fires and returns 504

### Integration Tests

1. `max_connections` simultaneous connections all active
2. Mix of fast and slow clients - no cross-connection interference
3. Rapid connect/disconnect cycles - no buffer leaks
4. Idle connections are closed after timeout
5. Slow handler triggers pending stream timeout

### Stress Tests

1. 1000 connections, each sending/receiving continuously
2. Memory usage stays bounded at expected level
3. No deadlocks or hangs under load
4. Idle connection cleanup under high connection churn

## Open Questions

1. **Buffer size tuning**: 64KB aligns with HTTP/2 default window size. Should we tie buffer size to `h2_initial_stream_window_size` for consistency?

2. **Idle buffer reclamation**: Should idle connections release their read buffer after a timeout? This would reduce memory for long-lived idle connections but add complexity.

3. **Metrics**: What buffer utilization metrics should we expose?
   - `tcp_buffers_in_use` gauge
   - `tcp_buffer_acquisitions_total` counter  
   - `tcp_buffer_wait_time_seconds` histogram (if we ever need to wait)

4. **Server vs Client buffer sizes**: Should client connections (outbound) have different buffer sizes than server connections (inbound)? Clients typically send small requests and receive large responses, servers do the opposite.

5. **HTTP/2 window size coordination**: Should we automatically configure nghttp2's `SETTINGS_INITIAL_WINDOW_SIZE` to match our buffer size? This would ensure HTTP/2 flow control and buffer backpressure are aligned.

6. **Edge vs Internal profiles**: Should we provide preset configurations for "edge" (untrusted clients, stricter limits) vs "internal" (trusted, higher throughput) deployments, similar to Envoy's recommendations?

7. **Accept rate limiting**: Envoy recommends `max_connections_to_accept_per_socket_event: 1` for better overload management. Should this be our default?

## Envoy Settings to Consider Adopting

Based on Envoy's edge proxy best practices, we should consider adding the following settings to `valk_aio_system_config_t` and `valk_http_server_config_t`:

### Connection Buffer Limits

| Setting | Envoy Default | Envoy Edge | Our Current | Recommended |
|---------|---------------|------------|-------------|-------------|
| `per_connection_buffer_limit_bytes` | 1 MB | 32 KB | 32 KB | 64 KB |

Envoy recommends 32KB for untrusted environments. Our 64KB aligns with HTTP/2 default window size.

### HTTP/2 Protocol Settings

| Setting | Envoy Default | Envoy Edge | Our Current | Recommended |
|---------|---------------|------------|-------------|-------------|
| `max_concurrent_streams` | 100 | 100 | 128 | 100 |
| `initial_stream_window_size` | 16 MB | 64 KB | 64 KB | 64 KB |
| `initial_connection_window_size` | 24 MB | 1 MB | N/A | 1 MB |

**Rationale**:
- `max_concurrent_streams`: 100 is safer for edge. Our 128 is fine for trusted environments.
- `initial_stream_window_size`: 64KB matches buffer size, provides natural backpressure.
- `initial_connection_window_size`: Envoy uses 1MB for edge. We should add this setting.

### Timeout Settings

| Setting | Envoy Edge | Our Current | Recommended |
|---------|------------|-------------|-------------|
| `idle_timeout` | 1 hour | None | 60s (edge), 1h (internal) |
| `stream_idle_timeout` | 5 min | None | 300s |
| `request_timeout` | 5 min | None | 300s |
| `max_connection_duration` | None | None | Optional |

**Rationale**: Timeouts prevent resource leaks from abandoned connections. Critical for edge deployments.

### Overload Management

| Setting | Envoy | Our Current | Recommended |
|---------|-------|-------------|-------------|
| `global_downstream_max_connections` | 50000 | `max_connections` per server | Add system-wide limit |
| `max_connections_to_accept_per_socket_event` | 1 | Unlimited | Add (1 recommended) |
| `tcp_backlog_size` | OS default | OS default | Configurable |

**Rationale**: 
- `max_connections_to_accept_per_socket_event`: Limits accept burst, improves overload behavior.
- Global connection limit prevents runaway resource usage across all servers.

### Security Settings (Future)

| Setting | Envoy | Notes |
|---------|-------|-------|
| `headers_with_underscores_action` | REJECT_REQUEST | Prevents header smuggling |
| `max_headers_count` | 100 | Limits header parsing DoS |
| `max_request_headers_kb` | 60 KB | Limits header memory |

### Proposed Config Additions

```c
typedef struct valk_aio_system_config {
    // ... existing ...
    
    // NEW: Global limits
    uint32_t global_max_connections;              // 0 = no global limit
    uint32_t max_accepts_per_event;               // Default: 1
    
    // NEW: HTTP/2 flow control
    uint32_t h2_initial_stream_window_size;       // Default: 64KB
    uint32_t h2_initial_connection_window_size;   // Default: 1MB
    
    // NEW: Timeouts (0 = disabled)
    uint32_t connection_idle_timeout_ms;          // Default: 60000 (1 min)
    uint32_t stream_idle_timeout_ms;              // Default: 300000 (5 min)
    uint32_t request_timeout_ms;                  // Default: 300000 (5 min)
} valk_aio_system_config_t;
```

### Implementation Priority

1. **High**: `connection_idle_timeout_ms` - Prevents connection leaks
2. **High**: `max_accepts_per_event` - Improves overload behavior  
3. **Medium**: `h2_initial_connection_window_size` - Better flow control
4. **Medium**: `global_max_connections` - System-wide protection
5. **Low**: `stream_idle_timeout_ms`, `request_timeout_ms` - Nice to have

## References

- Envoy `per_connection_buffer_limit_bytes`: 32KB default, 32KB for edge
- Envoy `max_concurrent_streams`: 100 for edge
- Envoy `initial_stream_window_size`: 64KB for edge (16MB default)
- Envoy `initial_connection_window_size`: 1MB for edge (24MB default)
- NGINX `proxy_buffer_size`: 4KB-8KB typical
- HTTP/2 default `INITIAL_WINDOW_SIZE`: 64KB (RFC 7540)
- TLS record max size: ~16KB
