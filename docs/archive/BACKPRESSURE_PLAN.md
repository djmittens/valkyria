# Backpressure & Connection Admission Control Implementation Plan

## Problem Statement

Under high load (e.g., `hey -n 5000000 -c 500 -h2`), the server initially handles ~400 Mbps throughput, but eventually:
1. TCP buffer slab exhausts
2. Backpressure is applied to all connections
3. Throughput collapses to kbits due to thrashing between pause/resume states

**Root Cause**: The server accepts unlimited connections despite `max_connections` being configured. The metric `connections_active` is tracked but never enforced.

---

## Research Summary

### Envoy Proxy
- **Connection limits**: Hard limit at listener level, reject with RST when exceeded
- **Circuit breakers**: `max_connections`, `max_pending_requests`, `max_requests`
- **Buffer watermarks**: High/low watermarks with gradual backpressure
- **Overload manager**: Staged degradation (92% heap → disable keep-alive, 95% → stop accepting)

### Nginx
- **`limit_conn`**: Hard connection limits per-IP and server-wide
- **`backlog=N`**: Kernel-level rejection queue on listen socket
- **Per-connection buffer quotas**: `proxy_buffers`, `proxy_busy_buffers_size`
- **Rate limiting**: Leaky bucket algorithm with burst handling

---

## Implementation Phases

### Phase 0: Connection Slab Allocator (P0 - Foundation)

**Goal**: Replace `malloc()`/`free()` for connection structs with a slab allocator. This provides O(1) allocation, implicit connection limit enforcement, and eliminates fragmentation.

#### 0.1 Why Slab for Connections?

| Aspect | malloc() | Slab |
|--------|----------|------|
| **Allocation time** | O(log n) typical | O(1) guaranteed |
| **Fragmentation** | Yes (variable sizes mixed) | None (fixed size) |
| **Cache locality** | Poor (scattered) | Excellent (contiguous) |
| **Limit enforcement** | Separate counter needed | Implicit (slab size = limit) |
| **Exhaustion handling** | malloc returns NULL (rare) | Normal rejection path |
| **Memory predictability** | Unknown | `max_connections × sizeof(conn)` |

**Key insight**: With a slab, connection admission becomes a single atomic operation. No separate counter check needed - if `valk_slab_aquire()` returns NULL, we're at capacity.

#### 0.2 Add Connection Slab to System

**File**: `src/aio_uv.c` (near line 98, with other thread-local slabs)

```c
static __thread valk_slab_t *tcp_buffer_slab;
static __thread valk_slab_t *conn_slab;  // NEW: Connection slab
```

#### 0.3 Initialize Connection Slab

**File**: `src/aio_uv.c` (in `valk_aio_start_with_config`, near line 454 where tcp_buffer_slab is created)

```c
// Existing: TCP buffer slab
tcp_buffer_slab = valk_slab_new(sizeof(__tcp_buffer_slab_item_t),
                                 sys->config.tcp_buffer_pool_size);

// NEW: Connection slab - sized exactly to max_connections
conn_slab = valk_slab_new(sizeof(valk_aio_http_conn),
                           sys->config.max_connections);
if (!conn_slab) {
  VALK_ERROR("Failed to allocate connection slab for %u connections",
             sys->config.max_connections);
  return NULL;
}

VALK_INFO("Connection slab: %u slots × %zu bytes = %zu KB",
          sys->config.max_connections,
          sizeof(valk_aio_http_conn),
          (sys->config.max_connections * valk_slab_item_stride(sizeof(valk_aio_http_conn))) / 1024);
```

#### 0.4 Replace malloc() with Slab Acquire

**File**: `src/aio_uv.c:1608` (in `__on_new_connection`)

**Before**:
```c
struct valk_aio_http_conn *conn = malloc(sizeof(struct valk_aio_http_conn));
if (!conn) {
  VALK_ERROR("Failed to allocate connection");
  return;
}
memset(conn, 0, sizeof(struct valk_aio_http_conn));
```

**After**:
```c
// Acquire connection from slab - implicitly enforces max_connections
valk_slab_item_t *conn_item = valk_slab_aquire(conn_slab);
if (!conn_item) {
  // At connection limit - reject immediately
  uv_tcp_t reject_handle;
  uv_tcp_init(stream->loop, &reject_handle);
  if (uv_accept(stream, (uv_stream_t *)&reject_handle) == 0) {
    uv_close((uv_handle_t *)&reject_handle, NULL);
  }

  #ifdef VALK_METRICS_ENABLED
  atomic_fetch_add(&srv->sys->metrics.connections_rejected, 1);
  #endif

  VALK_WARN("Connection rejected: slab exhausted (max_connections=%u)",
            srv->sys->config.max_connections);
  return;
}

struct valk_aio_http_conn *conn = (struct valk_aio_http_conn *)conn_item->data;
memset(conn, 0, sizeof(struct valk_aio_http_conn));
conn->slab_item = conn_item;  // Store for release
```

#### 0.5 Add Slab Item Reference to Connection Struct

**File**: `src/aio_uv.c:197` (in `valk_aio_http_conn` struct)

```c
typedef struct valk_aio_http_conn {
  __aio_http_conn_e state;
  struct valk_aio_http_conn *prev, *next;

  valk_slab_item_t *slab_item;  // NEW: Reference for slab release

  valk_aio_ssl_t ssl;
  nghttp2_session *session;
  // ... rest unchanged
} valk_aio_http_conn;
```

#### 0.6 Replace free() with Slab Release

**File**: `src/aio_uv.c:525` (in connection cleanup)

**Before**:
```c
free(conn);
```

**After**:
```c
valk_slab_release(conn_slab, conn->slab_item);
```

**File**: `src/aio_uv.c:1716` (in error path cleanup)

**Before**:
```c
free(conn);
```

**After**:
```c
valk_slab_release(conn_slab, conn->slab_item);
```

#### 0.7 Add Slab Cleanup on System Shutdown

**File**: `src/aio_uv.c` (in `valk_aio_stop` or cleanup function)

```c
// Free connection slab
if (conn_slab) {
  // Verify all connections released (debugging)
  size_t leaked = conn_slab->numItems - valk_slab_available(conn_slab);
  if (leaked > 0) {
    VALK_WARN("Connection slab leak: %zu connections not released", leaked);
  }
  valk_slab_free(conn_slab);
  conn_slab = NULL;
}
```

#### 0.8 Update Metrics to Use Slab Stats

**File**: `src/aio_uv.c` (metrics collection)

```c
// Connection metrics from slab (more accurate than atomic counter)
#ifdef VALK_METRICS_ENABLED
static inline uint64_t __get_active_connections(void) {
  if (!conn_slab) return 0;
  return conn_slab->numItems - valk_slab_available(conn_slab);
}

static inline uint64_t __get_available_connections(void) {
  if (!conn_slab) return 0;
  return valk_slab_available(conn_slab);
}
#endif
```

#### 0.9 Test Cases

**File**: `test/test_connection_slab.c` (new file)

```c
#include "testing.h"
#include "aio.h"
#include "memory.h"

// Test slab allocation for connections
void test_conn_slab_basic(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Create a small slab
  valk_slab_t *slab = valk_slab_new(sizeof(valk_aio_http_conn), 10);
  VALK_TEST_ASSERT(slab != NULL, "Slab should be created");
  VALK_TEST_ASSERT(valk_slab_available(slab) == 10, "Should have 10 slots");

  // Acquire all slots
  valk_slab_item_t *items[10];
  for (int i = 0; i < 10; i++) {
    items[i] = valk_slab_aquire(slab);
    VALK_TEST_ASSERT(items[i] != NULL, "Should acquire slot %d", i);
  }

  VALK_TEST_ASSERT(valk_slab_available(slab) == 0, "Should be exhausted");

  // Try to acquire one more - should fail
  valk_slab_item_t *extra = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(extra == NULL, "Should fail when exhausted");

  // Release one and try again
  valk_slab_release(slab, items[0]);
  VALK_TEST_ASSERT(valk_slab_available(slab) == 1, "Should have 1 slot");

  valk_slab_item_t *reacquired = valk_slab_aquire(slab);
  VALK_TEST_ASSERT(reacquired != NULL, "Should acquire after release");

  // Cleanup
  valk_slab_release(slab, reacquired);
  for (int i = 1; i < 10; i++) {
    valk_slab_release(slab, items[i]);
  }
  valk_slab_free(slab);

  VALK_PASS();
}

// Test connection limit via slab exhaustion
void test_conn_slab_limit_enforcement(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 3;  // Very low limit for testing
  valk_aio_system_config_resolve(&cfg);

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  VALK_TEST_ASSERT(sys != NULL, "System should start");

  // Start server
  valk_http2_handler_t handler = {0};
  valk_future *fserv = valk_aio_http2_listen(
      sys, "127.0.0.1", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server_box = valk_future_await(fserv);
  VALK_TEST_ASSERT(server_box->type == VALK_SUC, "Server should start");

  valk_aio_http_server *server = server_box->item;
  int port = server->port;

  // Connect 3 clients (should succeed)
  valk_arc_box *clients[3];
  for (int i = 0; i < 3; i++) {
    valk_future *f = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clients[i] = valk_future_await(f);
    VALK_TEST_ASSERT(clients[i]->type == VALK_SUC, "Client %d should connect", i);
    valk_arc_release(f);
  }

  // Try 4th connection (should be rejected)
  valk_future *f4 = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *client4 = valk_future_await(f4);

  // Should fail or be rejected
  #ifdef VALK_METRICS_ENABLED
  uint64_t rejected = atomic_load(&sys->metrics.connections_rejected);
  VALK_TEST_ASSERT(rejected >= 1, "4th connection should be rejected");
  #endif

  // Cleanup
  valk_arc_release(f4);
  if (client4) valk_arc_release(client4);
  for (int i = 0; i < 3; i++) {
    valk_arc_release(clients[i]);
  }
  valk_arc_release(server_box);
  valk_arc_release(fserv);
  valk_aio_stop(sys);

  VALK_PASS();
}

// Test that closing a connection frees the slab slot
void test_conn_slab_release_on_close(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 2;
  valk_aio_system_config_resolve(&cfg);

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);

  // ... setup server ...

  // Connect 2 clients (at limit)
  // Close 1 client
  // Connect new client (should succeed - slot was freed)

  // Verify slab accounting is correct
  // available should equal (max_connections - active)

  valk_aio_stop(sys);
  VALK_PASS();
}

// Test memory footprint calculation
void test_conn_slab_memory_footprint(VALK_TEST_ARGS()) {
  VALK_TEST();

  size_t conn_size = sizeof(valk_aio_http_conn);
  size_t stride = valk_slab_item_stride(conn_size);
  size_t slab_size = valk_slab_size(conn_size, 1000);

  VALK_TEST_ASSERT(stride >= conn_size, "Stride must fit connection");
  VALK_TEST_ASSERT(stride <= conn_size + 64, "Stride overhead reasonable");

  // For 1000 connections, memory should be predictable
  size_t expected_min = 1000 * conn_size;
  size_t expected_max = 1000 * (conn_size + 64) + 4096;  // +headers

  VALK_TEST_ASSERT(slab_size >= expected_min, "Slab size >= minimum");
  VALK_TEST_ASSERT(slab_size <= expected_max, "Slab size <= maximum");

  printf("Connection slab for 1000 conns: %zu KB\n", slab_size / 1024);
  printf("  Per-connection: %zu bytes (struct) + %zu bytes (overhead) = %zu bytes\n",
         conn_size, stride - conn_size, stride);

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_conn_slab_basic", test_conn_slab_basic);
  valk_testsuite_add_test(suite, "test_conn_slab_limit_enforcement",
                          test_conn_slab_limit_enforcement);
  valk_testsuite_add_test(suite, "test_conn_slab_release_on_close",
                          test_conn_slab_release_on_close);
  valk_testsuite_add_test(suite, "test_conn_slab_memory_footprint",
                          test_conn_slab_memory_footprint);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
```

#### 0.10 Memory Calculation

For `max_connections = 100` (default):

```
sizeof(valk_aio_http_conn) ≈ 150 bytes
valk_slab_item_stride(150)  ≈ 168 bytes (aligned + header)
Total slab size             ≈ 100 × 168 = 16.8 KB

For max_connections = 10,000:
Total slab size             ≈ 10,000 × 168 = 1.68 MB
```

This is negligible compared to the TCP buffer slab (1400 × 32KB = 44.8 MB) and arena pool.

---

### Phase 1: Connection Rejection Metrics (P0 - Critical)

**Goal**: Add metrics to track rejected connections. The actual limit enforcement is handled by Phase 0's slab exhaustion.

> **Note**: With Phase 0 implemented, this phase is simplified. The slab allocator implicitly enforces `max_connections`. This phase just adds the metrics instrumentation.

#### 1.1 Add Connection Rejection Metrics

**File**: `src/aio_metrics.h` (after line 30)

```c
// Add to valk_aio_metrics_t struct
_Atomic uint64_t connections_rejected;       // Rejected due to connection limit (slab exhausted)
_Atomic uint64_t connections_rejected_load;  // Rejected due to buffer exhaustion (Phase 2)
```

**File**: `src/aio_metrics.c` (in `valk_aio_metrics_init`)

```c
atomic_store(&m->connections_rejected, 0);
atomic_store(&m->connections_rejected_load, 0);
```

**File**: `src/aio_metrics.c` (in JSON/Prometheus export functions)

```c
// Add to JSON output
"connections_rejected": %lu,
"connections_rejected_load": %lu,

// Add to Prometheus output
"# HELP valk_aio_connections_rejected Total connections rejected due to limit\n"
"# TYPE valk_aio_connections_rejected counter\n"
"valk_aio_connections_rejected %lu\n"
"# HELP valk_aio_connections_rejected_load Total connections rejected due to buffer exhaustion\n"
"# TYPE valk_aio_connections_rejected_load counter\n"
"valk_aio_connections_rejected_load %lu\n"
```

#### 1.2 Test Cases

**File**: `test/test_connection_limit.c` (new file)

```c
#include "testing.h"
#include "aio.h"
#include "common.h"
#include <pthread.h>
#include <unistd.h>

// Test that connection limit is enforced
void test_connection_limit_enforced(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Configure system with low connection limit
  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 5;
  valk_aio_system_config_resolve(&cfg);

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  VALK_TEST_ASSERT(sys != NULL, "System should start");

  // Start server
  valk_http2_handler_t handler = {0};
  valk_future *fserv = valk_aio_http2_listen(
      sys, "127.0.0.1", 0, "build/server.key", "build/server.crt", &handler, NULL);
  valk_arc_box *server_box = valk_future_await(fserv);
  VALK_TEST_ASSERT(server_box->type == VALK_SUC, "Server should start");

  valk_aio_http_server *server = server_box->item;
  int port = server->port;

  // Create max_connections clients (should all succeed)
  valk_arc_box *clients[5];
  for (int i = 0; i < 5; i++) {
    valk_future *fclient = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    clients[i] = valk_future_await(fclient);
    VALK_TEST_ASSERT(clients[i]->type == VALK_SUC,
                     "Client %d should connect", i);
    valk_arc_release(fclient);
  }

  // Try to create one more (should fail or be rejected)
  valk_future *fextra = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
  valk_arc_box *extra = valk_future_await(fextra);

  // The connection should either fail or be immediately closed
  // Check metrics to verify rejection
  #ifdef VALK_METRICS_ENABLED
  uint64_t rejected = atomic_load(&sys->metrics.connections_rejected);
  VALK_TEST_ASSERT(rejected >= 1,
                   "At least one connection should be rejected, got %lu", rejected);
  #endif

  // Cleanup
  valk_arc_release(fextra);
  for (int i = 0; i < 5; i++) {
    valk_arc_release(clients[i]);
  }
  valk_arc_release(server_box);
  valk_arc_release(fserv);
  valk_aio_stop(sys);

  VALK_PASS();
}

// Test that rejected connections don't affect active connections
void test_rejection_doesnt_affect_active(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 2;
  valk_aio_system_config_resolve(&cfg);

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);

  // ... setup server ...

  // Create 2 clients at limit
  // Verify they can still send/receive requests
  // Try to create 10 more clients (all rejected)
  // Verify original 2 clients still work

  // Check that active connections didn't increase beyond limit
  #ifdef VALK_METRICS_ENABLED
  uint64_t active = atomic_load(&sys->metrics.connections_active);
  VALK_TEST_ASSERT(active <= 2,
                   "Active connections should not exceed limit, got %lu", active);
  #endif

  valk_aio_stop(sys);
  VALK_PASS();
}

// Test metrics are correctly updated on rejection
void test_rejection_metrics(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 1;
  valk_aio_system_config_resolve(&cfg);

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);

  // ... setup server, create 1 client at limit ...

  // Try to create 100 more connections rapidly
  for (int i = 0; i < 100; i++) {
    valk_future *f = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_arc_box *box = valk_future_await(f);
    valk_arc_release(f);
    if (box) valk_arc_release(box);
  }

  #ifdef VALK_METRICS_ENABLED
  uint64_t rejected = atomic_load(&sys->metrics.connections_rejected);
  VALK_TEST_ASSERT(rejected >= 95,
                   "Should reject most connections, got %lu rejections", rejected);
  #endif

  valk_aio_stop(sys);
  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_connection_limit_enforced",
                          test_connection_limit_enforced);
  valk_testsuite_add_test(suite, "test_rejection_doesnt_affect_active",
                          test_rejection_doesnt_affect_active);
  valk_testsuite_add_test(suite, "test_rejection_metrics",
                          test_rejection_metrics);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
```

---

### Phase 2: Buffer Availability Pre-Check (P1 - Important)

**Goal**: Reject new connections when buffer pool is nearly exhausted, preventing thrashing.

#### 2.1 Add Buffer Watermark Configuration

**File**: `src/aio.h` (add to `valk_aio_system_config_t` after line 123)

```c
typedef struct valk_aio_system_config {
  // PRIMARY TUNING PARAMETERS
  uint32_t max_connections;          // Default: 100
  uint32_t max_concurrent_streams;   // Default: 100

  // DERIVED SETTINGS (set to 0 for auto-calculation)
  uint32_t tcp_buffer_pool_size;     // Auto: max_connections × (2 + streams/8)
  uint32_t arena_pool_size;          // Auto: max_connections × 2
  uint32_t queue_capacity;           // Auto: max_connections × 2

  // MEMORY SIZING
  size_t   arena_size;               // Default: 64MB per arena
  size_t   max_request_body_size;    // Default: 8MB

  // BACKPRESSURE SETTINGS (new)
  float    buffer_high_watermark;    // Default: 0.85 (85%) - start load shedding
  float    buffer_critical_watermark; // Default: 0.95 (95%) - reject all new conns
  uint32_t min_buffers_per_conn;     // Default: 4 (BUFFERS_PER_CONNECTION)
} valk_aio_system_config_t;
```

#### 2.2 Implement Buffer Check in Accept Path

**File**: `src/aio_uv.c:1608` (add after connection limit check)

```c
  // Check 1: Hard connection limit (from Phase 1)
  // ...

  // Check 2: Buffer availability (load shedding)
  size_t available_buffers = valk_slab_available(tcp_buffer_slab);
  size_t total_buffers = tcp_buffer_slab->numItems;
  float buffer_usage = 1.0f - ((float)available_buffers / total_buffers);

  if (buffer_usage >= srv->sys->config.buffer_critical_watermark) {
    // Critical: reject immediately
    uv_tcp_t reject_handle;
    uv_tcp_init(stream->loop, &reject_handle);
    if (uv_accept(stream, (uv_stream_t *)&reject_handle) == 0) {
      uv_close((uv_handle_t *)&reject_handle, NULL);
    }

    #ifdef VALK_METRICS_ENABLED
    atomic_fetch_add(&srv->sys->metrics.connections_rejected_load, 1);
    #endif

    VALK_WARN("Connection rejected: buffer critical (%.1f%% used, %zu available)",
              buffer_usage * 100, available_buffers);
    return;
  }

  if (buffer_usage >= srv->sys->config.buffer_high_watermark) {
    // High watermark: check if we have minimum buffers for new connection
    if (available_buffers < srv->sys->config.min_buffers_per_conn * 2) {
      uv_tcp_t reject_handle;
      uv_tcp_init(stream->loop, &reject_handle);
      if (uv_accept(stream, (uv_stream_t *)&reject_handle) == 0) {
        uv_close((uv_handle_t *)&reject_handle, NULL);
      }

      #ifdef VALK_METRICS_ENABLED
      atomic_fetch_add(&srv->sys->metrics.connections_rejected_load, 1);
      #endif

      VALK_WARN("Connection rejected: insufficient buffers (%zu < %u required)",
                available_buffers, srv->sys->config.min_buffers_per_conn * 2);
      return;
    }
  }
```

#### 2.3 Update Config Resolution

**File**: `src/aio_uv.c:2669` (in `valk_aio_system_config_resolve`)

```c
int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg) {
  // ... existing resolution code ...

  // Backpressure defaults (add at end before validation)
  if (cfg->buffer_high_watermark == 0.0f)
    cfg->buffer_high_watermark = 0.85f;

  if (cfg->buffer_critical_watermark == 0.0f)
    cfg->buffer_critical_watermark = 0.95f;

  if (cfg->min_buffers_per_conn == 0)
    cfg->min_buffers_per_conn = BUFFERS_PER_CONNECTION;

  // Validate watermarks
  if (cfg->buffer_high_watermark >= cfg->buffer_critical_watermark) {
    fprintf(stderr, "AIO config error: buffer_high_watermark must be < buffer_critical_watermark\n");
    return -1;
  }

  // ... existing validation ...
}
```

#### 2.4 Test Cases

**File**: `test/test_buffer_backpressure.c` (new file)

```c
#include "testing.h"
#include "aio.h"
#include "memory.h"

// Test that connections are rejected when buffers are exhausted
void test_buffer_exhaustion_rejection(VALK_TEST_ARGS()) {
  VALK_TEST();

  // Configure with very small buffer pool to trigger exhaustion quickly
  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 20;  // Tiny pool, will exhaust fast
  cfg.buffer_critical_watermark = 0.95f;
  valk_aio_system_config_resolve(&cfg);

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  // ... setup server ...

  // Create connections until rejection
  int connected = 0;
  int rejected = 0;

  for (int i = 0; i < 50; i++) {
    valk_future *f = valk_aio_http2_connect(sys, "127.0.0.1", port, "");
    valk_arc_box *box = valk_future_await(f);
    if (box && box->type == VALK_SUC) {
      connected++;
    } else {
      rejected++;
    }
    valk_arc_release(f);
    if (box) valk_arc_release(box);
  }

  VALK_TEST_ASSERT(rejected > 0,
                   "Should reject some connections due to buffer exhaustion");
  VALK_TEST_ASSERT(connected < 50,
                   "Should not accept all connections, only accepted %d", connected);

  #ifdef VALK_METRICS_ENABLED
  uint64_t load_rejected = atomic_load(&sys->metrics.connections_rejected_load);
  VALK_TEST_ASSERT(load_rejected > 0,
                   "Should have load-based rejections, got %lu", load_rejected);
  #endif

  valk_aio_stop(sys);
  VALK_PASS();
}

// Test watermark configuration
void test_watermark_config(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.buffer_high_watermark = 0.70f;
  cfg.buffer_critical_watermark = 0.90f;

  int result = valk_aio_system_config_resolve(&cfg);
  VALK_TEST_ASSERT(result == 0, "Valid watermarks should be accepted");
  VALK_TEST_ASSERT(cfg.buffer_high_watermark == 0.70f, "High watermark preserved");
  VALK_TEST_ASSERT(cfg.buffer_critical_watermark == 0.90f, "Critical watermark preserved");

  // Test invalid config (high >= critical)
  valk_aio_system_config_t bad_cfg = {0};
  bad_cfg.buffer_high_watermark = 0.95f;
  bad_cfg.buffer_critical_watermark = 0.90f;

  result = valk_aio_system_config_resolve(&bad_cfg);
  VALK_TEST_ASSERT(result != 0, "Invalid watermarks should be rejected");

  VALK_PASS();
}

// Test that existing connections continue working under load shedding
void test_load_shedding_preserves_active(VALK_TEST_ARGS()) {
  VALK_TEST();

  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 10;
  cfg.tcp_buffer_pool_size = 50;
  valk_aio_system_config_resolve(&cfg);

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  // ... setup server ...

  // Create 5 clients
  valk_arc_box *clients[5];
  for (int i = 0; i < 5; i++) {
    // ... create client ...
  }

  // Send requests on all 5 clients (this will consume buffers)
  for (int i = 0; i < 5; i++) {
    // ... send request, consume buffers ...
  }

  // Try to create 20 more clients (should mostly be rejected)
  int new_connected = 0;
  for (int i = 0; i < 20; i++) {
    // ... try to connect ...
  }

  // Verify original 5 clients can still complete their requests
  for (int i = 0; i < 5; i++) {
    // ... await response, verify success ...
  }

  VALK_PASS();
}

int main(int argc, const char **argv) {
  UNUSED(argc);
  UNUSED(argv);

  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  valk_testsuite_add_test(suite, "test_buffer_exhaustion_rejection",
                          test_buffer_exhaustion_rejection);
  valk_testsuite_add_test(suite, "test_watermark_config",
                          test_watermark_config);
  valk_testsuite_add_test(suite, "test_load_shedding_preserves_active",
                          test_load_shedding_preserves_active);

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);

  return res;
}
```

---

### Phase 3: Graceful Overload Response (P1 - Important)

**Goal**: Instead of just closing connections, send HTTP/2 GOAWAY or 503 response.

#### 3.1 Add Pre-rendered 503 Response

**File**: `src/aio.h` (already has `error_503_body` in `valk_http_server_config_t`)

The config already supports this:
```c
typedef struct valk_http_server_config {
  size_t      max_response_body_size;
  const char* error_503_body;          // Pre-rendered overload response
  size_t      error_503_body_len;
} valk_http_server_config_t;
```

#### 3.2 Implement Graceful Rejection

**File**: `src/aio_uv.c` (new helper function, add before `__on_new_connection`)

```c
// Send HTTP/2 GOAWAY and close connection gracefully
// Used when rejecting connections due to overload
static void __reject_connection_graceful(uv_stream_t *server_stream,
                                          valk_aio_http_server *srv,
                                          const char *reason) {
  uv_tcp_t *reject_tcp = malloc(sizeof(uv_tcp_t));
  if (!reject_tcp) return;

  uv_tcp_init(server_stream->loop, reject_tcp);
  if (uv_accept(server_stream, (uv_stream_t *)reject_tcp) != 0) {
    free(reject_tcp);
    return;
  }

  // For now, just close immediately
  // TODO(networking): Implement full TLS handshake + GOAWAY frame
  // This requires completing TLS negotiation first, which is expensive.
  // For true graceful rejection, we'd need:
  // 1. Complete TLS handshake
  // 2. Send HTTP/2 connection preface
  // 3. Send GOAWAY frame with ENHANCE_YOUR_CALM or similar
  // 4. Close connection
  //
  // For performance, we just RST the connection instead.

  uv_close((uv_handle_t *)reject_tcp, (uv_close_cb)free);

  VALK_INFO("Connection rejected gracefully: %s", reason);
}
```

#### 3.3 Add GOAWAY on Existing Connections (Future Enhancement)

For connections that are already established when we hit high watermark:

**File**: `src/aio_uv.c` (add helper)

```c
// Send GOAWAY to existing connection, allowing it to drain
static void __connection_send_goaway(valk_aio_http_conn *conn,
                                      uint32_t error_code,
                                      const char *debug_data) {
  if (!conn || !conn->session) return;

  int rv = nghttp2_submit_goaway(conn->session,
                                  NGHTTP2_FLAG_NONE,
                                  nghttp2_session_get_last_proc_stream_id(conn->session),
                                  error_code,
                                  (const uint8_t *)debug_data,
                                  debug_data ? strlen(debug_data) : 0);
  if (rv == 0) {
    nghttp2_session_send(conn->session);
  }
}
```

---

### Phase 4: Improved Resume Strategy (P2 - Enhancement)

**Goal**: Reduce thrashing by improving how backpressured connections are resumed.

#### 4.1 Add Connection Priority Score

**File**: `src/aio_uv.c` (modify backpressure list to be a priority queue)

```c
// Priority score for backpressure queue
// Higher score = higher priority to resume
static inline uint32_t __backpressure_priority(valk_aio_http_conn *conn) {
  uint32_t score = 0;

  // Prefer connections with pending responses (they're almost done)
  if (conn->pending_responses > 0) {
    score += 1000;
  }

  // Prefer connections with more bytes already transferred
  // (connection is making progress, worth continuing)
  score += (conn->bytes_sent / 1024);  // 1 point per KB sent

  // Slight preference for older connections (fairness)
  // Use connection age in seconds, capped at 100
  uint64_t age_sec = (uv_now(conn->handle->sys->uv) - conn->connect_time_ms) / 1000;
  if (age_sec > 100) age_sec = 100;
  score += age_sec;

  return score;
}
```

#### 4.2 Replace FIFO with Priority Queue

**File**: `src/aio_uv.c:256-294` (replace `__backpressure_try_resume_one`)

```c
// Backpressure list as min-heap based on priority
// For simplicity, we keep the linked list but sort on insert

static void __backpressure_list_add_sorted(valk_aio_http_conn *conn) {
  conn->backpressure = true;
  conn->backpressure_priority = __backpressure_priority(conn);

  // Insert in sorted order (highest priority first)
  if (!backpressure_list_head ||
      conn->backpressure_priority > backpressure_list_head->backpressure_priority) {
    conn->backpressure_next = backpressure_list_head;
    backpressure_list_head = conn;
    return;
  }

  valk_aio_http_conn *prev = backpressure_list_head;
  while (prev->backpressure_next &&
         prev->backpressure_next->backpressure_priority >= conn->backpressure_priority) {
    prev = prev->backpressure_next;
  }

  conn->backpressure_next = prev->backpressure_next;
  prev->backpressure_next = conn;
}

// Updated resume function with adaptive threshold
static void __backpressure_try_resume_adaptive(void) {
  if (!backpressure_list_head) return;

  size_t available = valk_slab_available(tcp_buffer_slab);
  size_t total = tcp_buffer_slab->numItems;
  float usage = 1.0f - ((float)available / total);

  // Adaptive resume threshold based on current pressure
  uint32_t min_buffers;
  if (usage < 0.5f) {
    // Low pressure: resume aggressively
    min_buffers = 2;
  } else if (usage < 0.75f) {
    // Medium pressure: normal threshold
    min_buffers = BUFFERS_PER_CONNECTION;
  } else {
    // High pressure: conservative threshold
    min_buffers = BUFFERS_PER_CONNECTION * 2;
  }

  if (available < min_buffers) return;

  // Resume highest priority connection
  valk_aio_http_conn *conn = backpressure_list_head;
  backpressure_list_head = conn->backpressure_next;
  conn->backpressure_next = NULL;
  conn->backpressure = false;

  if (conn->state == VALK_CONN_ESTABLISHED) {
    uv_read_start((uv_stream_t *)&conn->handle->uv.tcp,
                  __alloc_callback, __http_tcp_read_cb);

    VALK_DEBUG("Resumed connection (priority=%u, available=%zu, usage=%.1f%%)",
               conn->backpressure_priority, available, usage * 100);
  }
}
```

#### 4.3 Add Connection Fields

**File**: `src/aio_uv.c` (in `valk_aio_http_conn` struct definition)

```c
typedef struct valk_aio_http_conn {
  // ... existing fields ...

  // Backpressure tracking
  bool backpressure;
  uint32_t backpressure_priority;
  struct valk_aio_http_conn *backpressure_next;

  // Statistics for priority calculation
  uint64_t connect_time_ms;
  uint64_t bytes_sent;
  uint64_t bytes_recv;
  uint32_t pending_responses;
} valk_aio_http_conn;
```

---

### Phase 5: Backpressure List Size Limit (P2 - Enhancement)

**Goal**: Prevent unbounded growth of backpressure list.

#### 5.1 Add List Size Tracking

**File**: `src/aio_uv.c`

```c
static __thread size_t backpressure_list_size = 0;
#define BACKPRESSURE_LIST_MAX_SIZE 1000

static void __backpressure_list_add(valk_aio_http_conn *conn) {
  // Check if list is at capacity
  if (backpressure_list_size >= BACKPRESSURE_LIST_MAX_SIZE) {
    // Evict oldest (tail) connection by closing it
    valk_aio_http_conn *prev = NULL;
    valk_aio_http_conn *curr = backpressure_list_head;
    while (curr && curr->backpressure_next) {
      prev = curr;
      curr = curr->backpressure_next;
    }

    if (curr && prev) {
      prev->backpressure_next = NULL;
      backpressure_list_size--;

      // Close the evicted connection
      VALK_WARN("Evicting oldest backpressured connection to make room");
      __connection_send_goaway(curr, NGHTTP2_ENHANCE_YOUR_CALM, "server overloaded");
      valk_aio_http_close(curr);
    }
  }

  // Add new connection
  conn->backpressure = true;
  conn->backpressure_next = backpressure_list_head;
  backpressure_list_head = conn;
  backpressure_list_size++;
}

static void __backpressure_list_remove(valk_aio_http_conn *conn) {
  if (!conn->backpressure) return;

  if (backpressure_list_head == conn) {
    backpressure_list_head = conn->backpressure_next;
  } else {
    valk_aio_http_conn *prev = backpressure_list_head;
    while (prev && prev->backpressure_next != conn) {
      prev = prev->backpressure_next;
    }
    if (prev) {
      prev->backpressure_next = conn->backpressure_next;
    }
  }

  conn->backpressure = false;
  conn->backpressure_next = NULL;
  backpressure_list_size--;
}
```

---

## Summary: Files to Modify

| File | Changes | Phase |
|------|---------|-------|
| `src/aio_uv.c:98` | Add `conn_slab` thread-local | P0 |
| `src/aio_uv.c:197` | Add `slab_item` field to connection struct | P0 |
| `src/aio_uv.c:454` | Initialize connection slab | P0 |
| `src/aio_uv.c:525,1716` | Replace `free(conn)` with slab release | P0 |
| `src/aio_uv.c:1608` | Replace `malloc()` with slab acquire + rejection | P0 |
| `src/aio_metrics.h:29-30` | Add rejection counters | P1 |
| `src/aio_metrics.c` | Initialize/instrument rejection metrics | P1 |
| `src/aio.h:111-124` | Add watermark config fields | P2 |
| `src/aio_uv.c:1608` | Buffer availability check (after slab) | P2 |
| `src/aio_uv.c:2669-2700` | Config resolution for watermarks | P2 |
| `src/aio_uv.c:256-294` | Improved resume strategy | P4 |
| `test/test_connection_slab.c` | New test file | P0 |
| `test/test_connection_limit.c` | New test file | P1 |
| `test/test_buffer_backpressure.c` | New test file | P2 |

---

## Expected Outcomes

### Before Implementation

```
Load: hey -n 5000000 -c 500 -h2 https://localhost:8443/

T+0s:  ~400 Mbps throughput
T+5s:  Buffer exhaustion warnings begin
T+10s: Throughput drops to ~5 Mbps
T+30s: Throughput at ~50 Kbps (thrashing)
```

### After Phase 1 (Connection Limit)

```
Load: hey -n 5000000 -c 500 -h2 https://localhost:8443/
Config: max_connections=100

T+0s:  100 connections accepted, 400 rejected immediately
T+5s:  ~400 Mbps sustained
T+30s: ~400 Mbps sustained (no degradation)

Metrics:
  connections_active: 100 (constant)
  connections_rejected: 400+
```

### After Phase 2 (Buffer Watermarks)

```
Load: hey -n 5000000 -c 500 -h2 https://localhost:8443/
Config: max_connections=200, buffer_critical_watermark=0.95

T+0s:  200 connections accepted initially
T+2s:  Buffer usage hits 85%, load shedding begins
T+5s:  Only 150 connections active, rest rejected
T+30s: ~350 Mbps sustained (graceful degradation)

Metrics:
  connections_active: 150 (varies with load)
  connections_rejected: 50
  connections_rejected_load: 200+
```

---

## Testing Plan

### Unit Tests
1. `test_connection_limit_enforced` - Verify hard limit works
2. `test_rejection_doesnt_affect_active` - Active connections unaffected
3. `test_rejection_metrics` - Metrics correctly updated
4. `test_buffer_exhaustion_rejection` - Buffer-based rejection
5. `test_watermark_config` - Config validation
6. `test_load_shedding_preserves_active` - Graceful degradation

### Integration Tests
```bash
# Test 1: Connection limit
./build/valk examples/webserver_demo.valk &
hey -n 10000 -c 200 https://localhost:8443/
# Expect: ~100 connections active, rest rejected, stable throughput

# Test 2: Sustained load
./build/valk examples/webserver_demo.valk &
hey -n 5000000 -c 500 -h2 https://localhost:8443/debug/metrics
# Expect: Stable throughput throughout, no collapse

# Test 3: Burst handling
./build/valk examples/webserver_demo.valk &
for i in {1..10}; do
  hey -n 10000 -c 100 -h2 https://localhost:8443/ &
done
wait
# Expect: Spikes handled gracefully, recovery between bursts
```

### Metrics to Monitor
```bash
# Watch buffer usage during test
watch -n 0.5 'curl -k https://localhost:8443/debug/metrics 2>/dev/null | jq ".tcp_buffers_used, .tcp_buffers_total"'

# Watch connection metrics
watch -n 0.5 'curl -k https://localhost:8443/debug/metrics 2>/dev/null | jq ".connections_active, .connections_rejected"'
```

---

## Rollout Plan

1. **Phase 0** (Connection Slab): Foundation refactoring
   - Add `conn_slab` thread-local variable
   - Add `slab_item` field to connection struct
   - Initialize slab in `valk_aio_start_with_config`
   - Replace `malloc()` with slab acquire + rejection logic
   - Replace `free()` with slab release
   - Add cleanup in `valk_aio_stop`
   - **Result**: Connection limit implicitly enforced by slab size

2. **Phase 1** (Rejection Metrics): Observability
   - Add `connections_rejected` counter to metrics
   - Add `connections_rejected_load` counter (for Phase 2)
   - Export in JSON/Prometheus formats
   - **Result**: Visibility into rejection behavior

3. **Phase 2** (Buffer Watermarks): Load shedding
   - Add watermark config fields (use `== 0.0f` for float default checks)
   - Implement buffer availability check after slab acquire
   - Tune thresholds based on testing
   - **Result**: Graceful degradation before buffer exhaustion

4. **Phase 3** (Graceful Response): Client experience *(Optional/Future)*
   - Implement GOAWAY sending on rejection
   - Only if RST causes client issues
   - **Note**: True graceful rejection requires TLS handshake + HTTP/2 preface + GOAWAY, which is expensive. RST is sufficient for load shedding.
   - **Result**: Clients get clear "overloaded" signal

5. **Phase 4** (Improved Resume): Optimization *(Optional/Future)*
   - Profile current resume behavior
   - Add priority scoring for connections
   - Implement if thrashing still observed
   - **Result**: Better completion rate under load

6. **Phase 5** (List Limit): Safety net *(Optional/Future)*
   - Add if unbounded growth observed
   - Implement connection eviction (LIFO)
   - **Note**: Must also update existing `__backpressure_list_add()` and `__backpressure_list_remove()` functions to maintain the size counter
   - **Result**: Bounded memory for backpressure list

---

## Build System Updates

New test files require registration in the build system:

### CMakeLists.txt

Add the following executables:

```cmake
# Phase 0 test
add_executable(test_connection_slab
  test/test_connection_slab.c
  test/testing.c
)
target_link_libraries(test_connection_slab valk_core)

# Phase 1 test
add_executable(test_connection_limit
  test/test_connection_limit.c
  test/testing.c
)
target_link_libraries(test_connection_limit valk_core)

# Phase 2 test
add_executable(test_buffer_backpressure
  test/test_buffer_backpressure.c
  test/testing.c
)
target_link_libraries(test_buffer_backpressure valk_core)
```

### Makefile

Add to the `test` target (around line 100):

```makefile
# Backpressure tests
test: build/test_connection_slab build/test_connection_limit build/test_buffer_backpressure
	./build/test_connection_slab
	./build/test_connection_limit
	./build/test_buffer_backpressure
```

---

## Additional Recommendations

### Hysteresis for Watermark Logic (Phase 2.5)

If oscillation is observed during testing, consider adding hysteresis to prevent rapid state transitions:

```c
// Instead of simple threshold check, add hysteresis band
static __thread bool in_critical_state = false;

// Enter critical state at 95%
if (buffer_usage >= cfg->buffer_critical_watermark) {
  in_critical_state = true;
}
// Exit critical state at 90% (5% hysteresis band)
if (in_critical_state && buffer_usage < (cfg->buffer_critical_watermark - 0.05f)) {
  in_critical_state = false;
}

if (in_critical_state) {
  // Reject connection
}
```

### Slab Overflow Tracking

The existing slab has `overflowCount` that's incremented on failed acquire. This can be used for debugging alongside the new `connections_rejected` metric:

```c
// In metrics collection, both are available:
uint64_t rejected = atomic_load(&sys->metrics.connections_rejected);       // Operational metric
uint64_t overflow = atomic_load(&conn_slab->overflowCount);                // Debug metric
```

---

## Implementation Checklist

| Phase | Task | Files | Risk | Status |
|-------|------|-------|------|--------|
| **0.1** | Add `conn_slab` thread-local | `aio_uv.c:98` | Low | ☐ |
| **0.2** | Add `slab_item` to conn struct | `aio_uv.c:197` | Low | ☐ |
| **0.3** | Initialize conn_slab | `aio_uv.c:454` | Low | ☐ |
| **0.4** | Replace malloc with slab acquire | `aio_uv.c:1608` | Medium | ☐ |
| **0.5** | Replace free with slab release | `aio_uv.c:525,1716` | Medium | ☐ |
| **0.6** | Add cleanup in shutdown | `aio_uv.c` (new) | Low | ☐ |
| **1.1** | Add rejection metrics | `aio_metrics.h:32` | Low | ☐ |
| **1.2** | Initialize metrics | `aio_metrics.c:34` | Low | ☐ |
| **1.3** | Instrument rejection | `aio_uv.c:1608` | Low | ☐ |
| **1.4** | Export metrics (JSON/Prometheus) | `aio_metrics.c` | Low | ☐ |
| **2.1** | Add watermark config | `aio.h:123` | Low | ☐ |
| **2.2** | Resolve watermark defaults | `aio_uv.c:2680` | Low | ☐ |
| **2.3** | Implement buffer check | `aio_uv.c:1620` | Medium | ☐ |
| **Test** | Add test files | `test/test_*.c` | Low | ☐ |
| **Build** | Update CMakeLists/Makefile | Build files | Low | ☐ |
| **6.1** | Add rejection rows to Connections card | `debug/script.js:246` | Low | ☐ |
| **6.2** | Add utilization to Memory Pools card | `debug/script.js:203` | Low | ☐ |
| **6.3** | Add new Backpressure card | `debug/script.js:224` | Low | ☐ |
| **6.4** | Export backpressure stats in JSON | `aio_metrics.c` | Low | ☐ |

---

## Phase 6: Debug Dashboard Updates (P1 - Observability)

**Goal**: Display the new connection metrics in the debug dashboard UI for real-time monitoring during load testing.

### 6.1 Dashboard Architecture Overview

The debug dashboard is assembled from modular files in `src/modules/aio/debug/`:

| File | Purpose | Size |
|------|---------|------|
| `head.html` | HTML header, doctype | 101 bytes |
| `style.css` | Dark theme styling (GitHub colors) | 3,717 bytes |
| `body.html` | HTML structure, status indicator | 307 bytes |
| `script.js` | Metrics fetching, rendering logic | 11,516 bytes |
| `footer.html` | HTML closing tags | 29 bytes |
| `debug.valk` | Lisp module that assembles and serves dashboard | 69 lines |

**Data Flow**:
1. Browser polls `/debug/metrics` every 1000ms
2. Lisp handler merges three JSON sources: `aio_metrics`, `modular_metrics`, `vm_metrics`
3. JavaScript parses JSON and renders hierarchical tree view

### 6.2 Current Metrics Display (Assessment)

**Current Dashboard Structure**:
```
Valkyria VM (uptime)
├── Async I/O
│   ├── Resources: Servers, Clients, Handles
│   ├── Memory Pools: Stream Arenas, TCP Buffers (used/total)
│   ├── Event Loop: Iterations, Events, Idle Time
│   └── Queue Status: Queue Depth, Pending Reqs, Pending Resp
├── Garbage Collector
│   ├── GC Cycles: Total, Pause times
│   └── Heap Memory: Used, Total, Utilization
├── Interpreter
│   ├── Evaluations: Total, Function/Builtin Calls
│   └── Stack & Closures: Max Depth, Closures, Lookups
└── HTTP Server (per server:port)
    ├── Connections: Active, Total, Failed
    ├── Streams: Active, Total
    ├── HTTP Requests: Total, 2xx, 4xx, 5xx
    ├── Traffic: Sent, Received, Send/Recv Rate
    └── Latency: Avg Response, Request Count, Total Time
```

**Assessment of Current Dashboard**:

| Aspect | Current State | Improvement Needed |
|--------|--------------|-------------------|
| **Layout** | Well-organized hierarchical tree | Good as-is |
| **Polling** | 1000ms interval | Good for debugging |
| **Formatting** | Consistent (bytes, uptime, rates) | Good as-is |
| **Color Coding** | Green/Red/Yellow/Blue semantic | Good as-is |
| **Connection Metrics** | Shows Active/Total/Failed | Missing: Rejected, Rejected (Load) |
| **Buffer Metrics** | Shows used/total | Missing: Utilization %, Overflow count |
| **Backpressure** | Not shown | Missing: Backpressure list size, Watermark status |

### 6.3 New Metrics to Add

After implementing Phase 0-2, the following metrics will be available and should be displayed:

**Connection Admission (in Connections card)**:
- `connections_rejected` - Hard limit rejections (slab exhausted)
- `connections_rejected_load` - Load shedding rejections (buffer watermark)

**Buffer Pool Health (in Memory Pools card)**:
- `tcp_buffer_utilization_pct` - Current buffer usage percentage
- `tcp_buffer_overflow` - Cumulative buffer acquire failures
- `conn_slab_available` - Available connection slots (NEW - from Phase 0)

**Backpressure Status (NEW card in Async I/O)**:
- `backpressure_list_size` - Connections currently paused
- `buffer_watermark_state` - "normal" / "high" / "critical"

### 6.4 Metrics Export Changes

**File**: `src/aio_metrics.h` - Add to `valk_aio_metrics_t` (after line 30):

```c
// Connection admission control (Phase 1)
_Atomic uint64_t connections_rejected;       // Rejected at max_connections limit
_Atomic uint64_t connections_rejected_load;  // Rejected due to buffer pressure
```

**File**: `src/aio_metrics.c` - Update `valk_aio_combined_to_json()` to include:

```c
// In the "connections" section:
"\"rejected\": %lu,\n"
"\"rejected_load\": %lu,\n"

// In the "system" section (add buffer utilization):
"\"tcp_buffer_utilization_pct\": %.1f,\n"
"\"tcp_buffer_overflow\": %lu,\n"
```

### 6.5 JavaScript Updates

**File**: `src/modules/aio/debug/script.js`

**Update Connections card** (around line 246-252):

```javascript
// Current:
html += '<div class="sub-card">';
html += '<h3>Connections</h3>';
html += row('Active', c.active || 0, c.active > 0 ? 'grn' : '');
html += row('Total', c.total || 0);
html += row('Failed', c.failed || 0, c.failed > 0 ? 'red' : '');
html += '</div>';

// After (add rejection metrics):
html += '<div class="sub-card">';
html += '<h3>Connections</h3>';
html += row('Active', c.active || 0, c.active > 0 ? 'grn' : '');
html += row('Total', c.total || 0);
html += row('Failed', c.failed || 0, c.failed > 0 ? 'red' : '');
html += row('Rejected (Limit)', c.rejected || 0, c.rejected > 0 ? 'ylw' : '');
html += row('Rejected (Load)', c.rejected_load || 0, c.rejected_load > 0 ? 'ylw' : '');
html += '</div>';
```

**Update Memory Pools card** (around line 203-208):

```javascript
// Current:
html += '<div class="sub-card">';
html += '<h3>Memory Pools</h3>';
html += row('Stream Arenas', (sys.arenas_used || 0) + '/' + (sys.arenas_total || 0));
html += row('TCP Buffers', (sys.tcp_buffers_used || 0) + '/' + (sys.tcp_buffers_total || 0));
html += '</div>';

// After (add utilization and overflow):
var bufUtil = sys.tcp_buffers_total > 0
  ? ((sys.tcp_buffers_used / sys.tcp_buffers_total) * 100).toFixed(1)
  : 0;
var bufClass = bufUtil > 95 ? 'red' : bufUtil > 85 ? 'ylw' : bufUtil > 50 ? 'blu' : '';

html += '<div class="sub-card">';
html += '<h3>Memory Pools</h3>';
html += row('Stream Arenas', (sys.arenas_used || 0) + '/' + (sys.arenas_total || 0));
html += row('TCP Buffers', (sys.tcp_buffers_used || 0) + '/' + (sys.tcp_buffers_total || 0));
html += row('Buffer Util', bufUtil + '%', bufClass);
html += row('Buffer Overflow', sys.tcp_buffer_overflow || 0, (sys.tcp_buffer_overflow || 0) > 0 ? 'red' : '');
html += '</div>';
```

**Add new Backpressure Status card** (after Queue Status, around line 224):

```javascript
// NEW: Backpressure Status card
html += '<div class="sub-card">';
html += '<h3>Backpressure</h3>';
var bpSize = sys.backpressure_list_size || 0;
var bpState = sys.watermark_state || 'normal';
var stateClass = bpState === 'critical' ? 'red' : bpState === 'high' ? 'ylw' : 'grn';
html += row('Paused Conns', bpSize, bpSize > 0 ? 'ylw' : '');
html += row('Watermark', bpState, stateClass);
html += row('Conn Slots', (sys.conn_slab_available || 0) + '/' + (sys.conn_slab_total || 0));
html += '</div>';
```

### 6.6 CSS Updates (Optional)

**File**: `src/modules/aio/debug/style.css`

No changes required - existing color classes (`.grn`, `.red`, `.ylw`, `.blu`) cover all new metrics.

### 6.7 Lisp Export Updates

**File**: `src/modules/aio/debug.valk`

No changes required - the Lisp layer just passes through JSON from the C export functions. The changes in `valk_aio_combined_to_json()` will automatically appear in the dashboard.

### 6.8 Example Dashboard After Implementation

```
Valkyria VM (2h 34m 12s)
├── Async I/O (2 srv, 1.2M iters)
│   ├── Resources
│   │   ├── Servers: 2 ✓
│   │   ├── Clients: 0
│   │   └── Handles: 156
│   ├── Memory Pools
│   │   ├── Stream Arenas: 45/200
│   │   ├── TCP Buffers: 892/1450
│   │   ├── Buffer Util: 61.5% (blue)
│   │   └── Buffer Overflow: 0
│   ├── Event Loop
│   │   ├── Iterations: 1,234,567
│   │   ├── Events: 8,901,234
│   │   └── Idle Time: 45.2s
│   ├── Queue Status
│   │   ├── Queue Depth: 12
│   │   ├── Pending Reqs: 8
│   │   └── Pending Resp: 4
│   └── Backpressure (NEW)
│       ├── Paused Conns: 0
│       ├── Watermark: normal ✓
│       └── Conn Slots: 95/100
├── Garbage Collector (...)
├── Interpreter (...)
└── HTTP Server :8443
    ├── Connections
    │   ├── Active: 95 ✓
    │   ├── Total: 12,456
    │   ├── Failed: 3 ✗
    │   ├── Rejected (Limit): 1,234 ⚠  (NEW)
    │   └── Rejected (Load): 567 ⚠     (NEW)
    ├── Streams (...)
    ├── HTTP Requests (...)
    ├── Traffic (...)
    └── Latency (...)
```

### 6.9 Dashboard UX Recommendations

Based on holistic review of the current dashboard:

**Strengths**:
1. **Hierarchical organization** - Logical grouping by subsystem
2. **Dark theme** - Reduces eye strain during long debugging sessions
3. **Color semantics** - Green=good, Red=error, Yellow=warning is intuitive
4. **Compact layout** - Shows many metrics without scrolling
5. **Auto-refresh** - 1s polling keeps data fresh

**Areas for Improvement** (Future Enhancements):

| Issue | Recommendation | Priority |
|-------|---------------|----------|
| No historical trends | Add sparkline charts for key metrics | P2 |
| No alerting thresholds | Highlight when metrics cross configurable thresholds | P2 |
| No export capability | Add "Copy as JSON" button | P3 |
| Fixed polling interval | Make interval configurable (1s/5s/10s) | P3 |
| No pause/resume | Add button to pause polling during analysis | P3 |

**For This Implementation**: Focus only on adding the new backpressure metrics. UI enhancements can be done separately.

### 6.10 Testing the Dashboard

After implementing the metrics export changes, verify the dashboard displays correctly:

```bash
# Start server with debug handler
./build/valk examples/debug_server.valk &

# Open dashboard in browser
open https://localhost:8443/debug/

# Generate load to see rejection metrics
hey -n 100000 -c 200 -h2 https://localhost:8443/

# Watch dashboard update with:
# - Rejected (Limit) increasing when at max_connections
# - Rejected (Load) increasing when buffer utilization > 95%
# - Buffer Util % changing with load
# - Paused Conns showing backpressure queue size
```

### 6.11 Files to Modify Summary

| File | Changes | Phase |
|------|---------|-------|
| `src/aio_metrics.h:30` | Add `connections_rejected`, `connections_rejected_load` | P1 |
| `src/aio_metrics.c` | Update JSON export with new fields | P1 |
| `src/modules/aio/debug/script.js:246` | Add rejection rows to Connections card | P6 |
| `src/modules/aio/debug/script.js:203` | Add utilization to Memory Pools card | P6 |
| `src/modules/aio/debug/script.js:224` | Add new Backpressure card | P6 |
