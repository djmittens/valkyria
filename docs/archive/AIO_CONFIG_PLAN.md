# AIO System Configuration Plan

## Problem Statement

The AIO (Async I/O) system has hardcoded constants that don't scale well:

- `HTTP_MAX_IO_REQUESTS = 1024` - only 1024 TCP buffer slab items
- Each slab item is ~32KB (`SSL3_RT_MAX_PACKET_SIZE * 2`)
- With 500 concurrent connections, each needing 2+ buffers (read + write), the system immediately hits limits
- HTTP/2 multiplexing compounds the problem with multiple streams per connection
- Backpressure kicks in immediately, starving most connections

**Current state**: Configuration structs exist in `aio.h` (`valk_aio_system_config_t`, `valk_http_server_config_t`) but are **not used** - all values come from hardcoded enums in `aio_uv.c`.

## Design Philosophy

### Two Primary Tuning Parameters

Most settings are **codependent**. Instead of exposing 10+ knobs, we expose **two primary tuning parameters** and derive the rest:

```
max_connections         = Primary input (how many TCP connections)
max_concurrent_streams  = Primary input (HTTP/2 streams per connection)

tcp_buffer_pool_size    = max_connections × (2 + max_concurrent_streams / 8)
arena_pool_size         = max_connections × 2
queue_capacity          = max_connections × 2
```

Users can override any derived value if needed.

### Simplified Configuration

Based on deep investigation of the codebase, several settings from the original plan have been **removed or hidden**:

| Original Setting | Decision | Rationale |
|------------------|----------|-----------|
| `tcp_buffer_size` | **Hidden constant** | Must be 32KB for TLS. Changing causes data loss (see bug fixes). |
| `connection_heap_size` | **Removed** | Defined but never used. Neither OpenSSL nor nghttp2 uses per-connection allocators. |
| `max_response_body_size` | **Moved to server config** | Response streaming works in C runtime; limit is Lisp API concern. |

---

## Configuration API

### System Configuration Structure

```c
typedef struct valk_aio_system_config {
  // ═══════════════════════════════════════════════════════════════════
  // PRIMARY TUNING PARAMETERS
  // Set these values; others are derived automatically if left at 0
  // ═══════════════════════════════════════════════════════════════════
  uint32_t max_connections;          // Default: 100
  uint32_t max_concurrent_streams;   // Default: 100 (per connection, sent via SETTINGS)

  // ═══════════════════════════════════════════════════════════════════
  // DERIVED SETTINGS (set to 0 for auto-calculation)
  // ═══════════════════════════════════════════════════════════════════
  uint32_t tcp_buffer_pool_size;     // Auto: max_connections × (2 + streams/8)
  uint32_t arena_pool_size;          // Auto: max_connections × 2
  uint32_t queue_capacity;           // Auto: max_connections × 2

  // ═══════════════════════════════════════════════════════════════════
  // MEMORY SIZING
  // ═══════════════════════════════════════════════════════════════════
  size_t   arena_size;               // Default: 64MB per arena
  size_t   max_request_body_size;    // Default: 8MB (required - requests are buffered)
} valk_aio_system_config_t;
```

### Server Configuration (per-server)

```c
typedef struct valk_http_server_config {
  // Moved from system config - these are per-server policies
  size_t      max_response_body_size;  // Default: 64MB (Lisp API limit, not C runtime)
  const char* error_503_body;          // Pre-rendered overload response
  size_t      error_503_body_len;
} valk_http_server_config_t;
```

### Hidden Constants (not configurable)

```c
// TCP buffer size MUST be 2 × SSL3_RT_MAX_PACKET_SIZE (32 KB minimum)
// to hold encrypted output from two TLS records. This accommodates:
// - TLS record max = 16,384 bytes plaintext + ~256 bytes cipher overhead
// - Frame boundary alignment during encryption
// - Multiple small records before flush
//
// DO NOT REDUCE: Will cause data loss. See: 16KB_DATA_LOSS_FIX_PLAN.md
#define HTTP_SLAB_ITEM_SIZE (SSL3_RT_MAX_PACKET_SIZE * 2)  // ~32 KB, fixed
```

---

## Research Findings

### Why `connection_heap_size` Was Removed

Investigation found that `HTTP_MAX_CONNECTION_HEAP` (1MB) is **defined but never referenced** in the codebase.

**Actual per-connection memory usage** (via malloc, not a dedicated heap):
| Component | Memory |
|-----------|--------|
| nghttp2 session base | 50-76 KB |
| HPACK tables (encoder + decoder) | 8 KB |
| Frame buffers | 32-48 KB |
| Per-stream state (×100 streams) | 30-40 KB |
| **Total nghttp2** | **~130-170 KB** |

Neither OpenSSL nor nghttp2 uses custom allocators in this codebase - both use `malloc()` directly. A `connection_heap_size` setting would give users false sense of memory control.

**Future option**: Implement real enforcement via custom `nghttp2_mem` callbacks and OpenSSL memory hooks, then re-add this setting.

### Why `tcp_buffer_size` Is Hidden

Two past bug fixes prove 32KB is mandatory for HTTP/2 over TLS:
- `16KB_DATA_LOSS_FIX_PLAN.md` - continuation send dropped final TLS record with smaller buffer
- `LARGE_RESPONSE_FIX_PLAN.md` - pending SSL data lost on close

The size is tied to TLS record layer constraints (`SSL3_RT_MAX_PACKET_SIZE = 16,640 bytes`). Exposing this would let users break TLS.

### Why `tcp_buffer_pool_size` Formula Changed

The original `× 2` formula ignores HTTP/2 multiplexing:

**Buffer lifecycle:**
1. Acquired on TCP read
2. Held through SSL encryption (can spawn 2-3 buffers for large responses)
3. Held until OS TCP layer completes write
4. Released in write callback

**Problem:** A single connection with 100 concurrent streams can exhaust 200 buffers.

**New formula:** `max_connections × (2 + max_concurrent_streams / 8)`

| Connections | Streams | Old Formula | New Formula |
|-------------|---------|-------------|-------------|
| 100 | 100 | 200 | 1,450 |
| 500 | 100 | 1,000 | 7,250 |
| 100 | 50 | 200 | 825 |

### Why `arena_pool_size` Formula Changed

Original: `(max_connections × max_streams) / 16` = 6% of max streams

**Problem:** The 6% figure was arbitrary. Arenas are held for **entire stream lifetime**:
1. Header frame arrives → arena acquired
2. Handler evaluates (synchronously, blocks event loop)
3. Response sent
4. Stream closes → arena released

With synchronous handlers, many streams wait on I/O while holding arenas.

**New formula:** `max_connections × 2` (assumes 2 active streams per connection on average)

**Future enhancement:** Auto-growing pool with malloc fallback instead of immediate 503.

### Request vs Response Body Handling

**Verified in codebase:**

| Direction | Streaming? | Where | Limit Required? |
|-----------|------------|-------|-----------------|
| **Request body (server)** | NO | No `on_data_chunk_recv_callback` registered for server | YES - memory safety |
| **Response body (server)** | YES | `nghttp2_data_provider2` + `__http_byte_body_cb` | Policy only |
| **Response body (client)** | NO | Buffered into `reqres->res->body` | YES - memory safety |

**Key insight:** The C runtime DOES stream responses via `nghttp2_data_provider2`, but the Lisp API requires the full `:body` string upfront. This is a Lisp API limitation, not C runtime.

**Conclusion:**
- `max_request_body_size` (8MB): Required in system config - requests are fully buffered before handler sees them
- `max_response_body_size` (64MB): Move to server config - policy limit for Lisp API, not C runtime constraint

---

## Default Values

| Setting | Default | Derivation Formula | Rationale |
|---------|---------|-------------------|-----------|
| `max_connections` | 100 | Primary input | Good for dev, easy to scale |
| `max_concurrent_streams` | 100 | Primary input | HTTP/2 default, sent via SETTINGS |
| `tcp_buffer_pool_size` | 1,450 | `max_conn × (2 + streams/8)` | Accounts for multiplexing + TLS chunking |
| `arena_pool_size` | 200 | `max_connections × 2` | 2 active streams per connection average |
| `arena_size` | 64 MB | Fixed | Generous for Lisp handler evaluation |
| `max_request_body_size` | 8 MB | Fixed | Standard HTTP limit, required (no streaming) |
| `queue_capacity` | 200 | `max_connections × 2` | Request/response queue depth |

### Memory Footprint Examples

| max_connections | streams | TCP Buffers | Buffer Memory | Arena Memory (max) | Total (max) |
|-----------------|---------|-------------|---------------|-------------------|-------------|
| 100 | 100 | 1,450 × 32KB | 46 MB | 200 × 64MB = 12.8 GB | ~13 GB |
| 500 | 100 | 7,250 × 32KB | 232 MB | 1,000 × 64MB = 64 GB | ~64 GB |
| 100 | 50 | 825 × 32KB | 26 MB | 200 × 64MB = 12.8 GB | ~13 GB |

> **Note**: Arena memory is the maximum if all arenas are used simultaneously. In practice, arenas are pooled and reused. Typical usage is 10-20% of max.

---

## API Changes

### New Function

```c
/// @brief Start AIO system with custom configuration
/// @param config System configuration (NULL for defaults)
/// @return AIO system handle
valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config);
```

### Existing Function (unchanged signature)

```c
/// @brief Start AIO system with default configuration
/// Equivalent to valk_aio_start_with_config(NULL)
valk_aio_system_t *valk_aio_start(void);
```

### Configuration Helpers

```c
/// @brief Get default configuration
static inline valk_aio_system_config_t valk_aio_system_config_default(void);

/// @brief Resolve derived values (called automatically by valk_aio_start_with_config)
/// Fills in any 0-valued fields with derived/default values
/// Returns 0 on success, -1 on validation failure
int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg);

/// @brief Validate configuration
/// Returns NULL on success, or error message on failure
const char *valk_aio_system_config_validate(const valk_aio_system_config_t *cfg);
```

---

## Validation Rules

### Hard Limits

| Setting | Min | Max | Reason |
|---------|-----|-----|--------|
| `max_connections` | 1 | 100,000 | Sanity bounds |
| `max_concurrent_streams` | 1 | 1,000 | HTTP/2 practical limits |
| `tcp_buffer_pool_size` | 16 | 1,000,000 | Memory limits |
| `arena_pool_size` | 1 | 10,000 | Memory limits |
| `arena_size` | 1 MB | 256 MB | Reasonable range |
| `max_request_body_size` | 1 KB | 1 GB | Prevent abuse |
| `queue_capacity` | 16 | 100,000 | Memory limits |

### Relationship Validations

```c
// TCP buffers must be >= max_connections (at least 1 buffer per connection)
if (cfg->tcp_buffer_pool_size < cfg->max_connections) {
  return "tcp_buffer_pool_size must be >= max_connections";
}

// Warn if TCP buffers seem low for stream count
uint32_t recommended = cfg->max_connections * (2 + cfg->max_concurrent_streams / 8);
if (cfg->tcp_buffer_pool_size < recommended * 0.7) {
  WARN("tcp_buffer_pool_size (%u) may be insufficient for %u streams/conn; "
       "recommend >= %u", cfg->tcp_buffer_pool_size,
       cfg->max_concurrent_streams, recommended);
}

// Arena pool should support concurrent handler evaluation
if (cfg->arena_pool_size < cfg->max_connections) {
  WARN("arena_pool_size < max_connections may cause frequent 503 responses");
}
```

### Validation Implementation

```c
const char *valk_aio_system_config_validate(const valk_aio_system_config_t *cfg) {
  // Hard limits
  if (cfg->max_connections < 1 || cfg->max_connections > 100000)
    return "max_connections must be between 1 and 100,000";

  if (cfg->max_concurrent_streams < 1 || cfg->max_concurrent_streams > 1000)
    return "max_concurrent_streams must be between 1 and 1,000";

  if (cfg->tcp_buffer_pool_size < 16 || cfg->tcp_buffer_pool_size > 1000000)
    return "tcp_buffer_pool_size must be between 16 and 1,000,000";

  if (cfg->arena_pool_size < 1 || cfg->arena_pool_size > 10000)
    return "arena_pool_size must be between 1 and 10,000";

  if (cfg->arena_size < (1 << 20) || cfg->arena_size > (256 << 20))
    return "arena_size must be between 1MB and 256MB";

  if (cfg->max_request_body_size < (1 << 10) || cfg->max_request_body_size > (1ULL << 30))
    return "max_request_body_size must be between 1KB and 1GB";

  if (cfg->queue_capacity < 16 || cfg->queue_capacity > 100000)
    return "queue_capacity must be between 16 and 100,000";

  // Relationship validations
  if (cfg->tcp_buffer_pool_size < cfg->max_connections)
    return "tcp_buffer_pool_size must be >= max_connections";

  if (cfg->arena_pool_size < cfg->max_connections / 10)
    return "arena_pool_size must be >= max_connections / 10";

  return NULL; // Valid
}
```

---

## Implementation Changes

### Files to Modify

| File | Changes |
|------|---------|
| `src/aio.h` | Update `valk_aio_system_config_t`, add new API declarations |
| `src/aio_uv.c` | Replace hardcoded enums, implement `valk_aio_start_with_config()` |
| `src/parser.c` | Expose config to Lisp via `(aio-start {:max-connections 500})` |

### Step 1: Update `src/aio.h`

1. Update `valk_aio_system_config_t` with simplified fields
2. Move `max_concurrent_streams` from server config to system config
3. Add `valk_aio_start_with_config()` declaration
4. Add validation function declarations

### Step 2: Update `src/aio_uv.c`

1. Add resolved config storage to `valk_aio_system_t`:
   ```c
   struct valk_aio_system {
     valk_aio_system_config_t config;  // Resolved configuration
     // ... existing fields
   };
   ```

2. Implement `valk_aio_system_config_resolve()`:
   ```c
   int valk_aio_system_config_resolve(valk_aio_system_config_t *cfg) {
     // Set defaults for primary parameters
     if (cfg->max_connections == 0) cfg->max_connections = 100;
     if (cfg->max_concurrent_streams == 0) cfg->max_concurrent_streams = 100;

     // Derive dependent values (new formulas based on research)
     if (cfg->tcp_buffer_pool_size == 0) {
       uint32_t stream_overhead = cfg->max_concurrent_streams / 8;
       cfg->tcp_buffer_pool_size = cfg->max_connections * (2 + stream_overhead);
     }

     if (cfg->arena_pool_size == 0)
       cfg->arena_pool_size = cfg->max_connections * 2;

     if (cfg->arena_size == 0)
       cfg->arena_size = 64 * 1024 * 1024;

     if (cfg->max_request_body_size == 0)
       cfg->max_request_body_size = 8 * 1024 * 1024;

     if (cfg->queue_capacity == 0)
       cfg->queue_capacity = cfg->max_connections * 2;

     // Validate
     const char *err = valk_aio_system_config_validate(cfg);
     if (err) {
       fprintf(stderr, "AIO config error: %s\n", err);
       return -1;
     }

     return 0;
   }
   ```

3. Implement `valk_aio_start_with_config()`:
   ```c
   valk_aio_system_t *valk_aio_start_with_config(valk_aio_system_config_t *config) {
     valk_aio_system_config_t resolved;

     if (config) {
       resolved = *config;
     } else {
       resolved = valk_aio_system_config_default();
     }

     if (valk_aio_system_config_resolve(&resolved) != 0) {
       return NULL;
     }

     // Allocate system
     valk_aio_system_t *sys = malloc(sizeof(valk_aio_system_t));
     sys->config = resolved;

     // Initialize slabs using resolved config...
     // (rest of existing initialization, but using sys->config.* instead of constants)
   }
   ```

4. Update `valk_aio_start()` to call new function:
   ```c
   valk_aio_system_t *valk_aio_start(void) {
     return valk_aio_start_with_config(NULL);
   }
   ```

5. Replace enum constant usages with `sys->config.*`:
   - `HTTP_MAX_IO_REQUESTS` → `sys->config.tcp_buffer_pool_size`
   - `HTTP_MAX_CONNECTIONS` → `sys->config.max_connections`
   - `HTTP_MAX_STREAMS_PER_CONNECTION` → `sys->config.max_concurrent_streams`
   - `HTTP_MAX_REQUEST_SIZE_BYTES` → `sys->config.max_request_body_size`
   - `HTTP_STREAM_ARENA_SIZE` → `sys->config.arena_size`
   - `HTTP_STREAM_ARENA_POOL_SIZE` → `sys->config.arena_pool_size`
   - `HTTP_QUEUE_CAPACITY` → `sys->config.queue_capacity`

6. Keep `HTTP_SLAB_ITEM_SIZE` as hidden constant (32KB, TLS requirement)

### Step 3: Update Lisp Interface (src/parser.c)

Add configuration parsing for `aio-start`:

```c
// (aio-start) - use defaults
// (aio-start {:max-connections 500}) - custom config

if (argc >= 1 && LVAL_TYPE(valk_lval_list_nth(a, 0)) == LVAL_QEXPR) {
  valk_lval_t *config_map = valk_lval_list_nth(a, 0);
  valk_aio_system_config_t config = valk_aio_system_config_default();

  valk_lval_t *val;
  if ((val = valk_plist_get(config_map, ":max-connections")) && LVAL_TYPE(val) == LVAL_NUM)
    config.max_connections = (uint32_t)val->num;
  if ((val = valk_plist_get(config_map, ":max-concurrent-streams")) && LVAL_TYPE(val) == LVAL_NUM)
    config.max_concurrent_streams = (uint32_t)val->num;
  if ((val = valk_plist_get(config_map, ":tcp-buffer-pool-size")) && LVAL_TYPE(val) == LVAL_NUM)
    config.tcp_buffer_pool_size = (uint32_t)val->num;
  if ((val = valk_plist_get(config_map, ":arena-pool-size")) && LVAL_TYPE(val) == LVAL_NUM)
    config.arena_pool_size = (uint32_t)val->num;
  if ((val = valk_plist_get(config_map, ":arena-size")) && LVAL_TYPE(val) == LVAL_NUM)
    config.arena_size = (size_t)val->num;
  if ((val = valk_plist_get(config_map, ":max-request-body-size")) && LVAL_TYPE(val) == LVAL_NUM)
    config.max_request_body_size = (size_t)val->num;

  sys = valk_aio_start_with_config(&config);
}
```

---

## Test Plan

### Unit Tests (C)

Add to `test/test_aio_config.c`:

#### T1: Default Configuration

```c
void test_config_defaults(void) {
  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  valk_aio_system_config_resolve(&cfg);

  TEST_ASSERT_EQUAL(100, cfg.max_connections);
  TEST_ASSERT_EQUAL(100, cfg.max_concurrent_streams);
  // New formula: 100 × (2 + 100/8) = 100 × 14.5 = 1450
  TEST_ASSERT_EQUAL(1450, cfg.tcp_buffer_pool_size);
  // New formula: 100 × 2 = 200
  TEST_ASSERT_EQUAL(200, cfg.arena_pool_size);
  TEST_ASSERT_EQUAL(64 * 1024 * 1024, cfg.arena_size);
}
```

#### T2: Auto-Derivation with Custom Streams

```c
void test_config_derivation_streams(void) {
  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 500;
  cfg.max_concurrent_streams = 50;  // Lower stream count
  valk_aio_system_config_resolve(&cfg);

  // 500 × (2 + 50/8) = 500 × 8.25 = 4125
  TEST_ASSERT_EQUAL(4125, cfg.tcp_buffer_pool_size);
  // 500 × 2 = 1000
  TEST_ASSERT_EQUAL(1000, cfg.arena_pool_size);
}
```

#### T3: Override Derived Values

```c
void test_config_override(void) {
  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 500;  // Override auto-derivation
  valk_aio_system_config_resolve(&cfg);

  TEST_ASSERT_EQUAL(500, cfg.tcp_buffer_pool_size);  // Kept override
}
```

#### T4: Validation - Hard Limits

```c
void test_config_validation_limits(void) {
  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  valk_aio_system_config_resolve(&cfg);

  // Test max_connections bounds
  cfg.max_connections = 0;
  TEST_ASSERT_NOT_NULL(valk_aio_system_config_validate(&cfg));

  cfg.max_connections = 100001;
  TEST_ASSERT_NOT_NULL(valk_aio_system_config_validate(&cfg));

  cfg.max_connections = 100;
  TEST_ASSERT_NULL(valk_aio_system_config_validate(&cfg));  // Valid
}
```

#### T5: Validation - Relationships

```c
void test_config_validation_relationships(void) {
  valk_aio_system_config_t cfg = valk_aio_system_config_default();
  valk_aio_system_config_resolve(&cfg);

  // tcp_buffer_pool_size < max_connections should fail
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 50;
  TEST_ASSERT_NOT_NULL(valk_aio_system_config_validate(&cfg));

  // tcp_buffer_pool_size >= max_connections should pass
  cfg.tcp_buffer_pool_size = 100;
  TEST_ASSERT_NULL(valk_aio_system_config_validate(&cfg));
}
```

#### T6: System Start with Config

```c
void test_system_start_with_config(void) {
  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 50;
  cfg.max_concurrent_streams = 50;

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  TEST_ASSERT_NOT_NULL(sys);

  // Verify config was applied
  TEST_ASSERT_EQUAL(50, sys->config.max_connections);
  // 50 × (2 + 50/8) = 50 × 8.25 = 412
  TEST_ASSERT_EQUAL(412, sys->config.tcp_buffer_pool_size);

  valk_aio_stop(sys);
}
```

#### T7: Invalid Config Returns NULL

```c
void test_system_start_invalid_config(void) {
  valk_aio_system_config_t cfg = {0};
  cfg.max_connections = 100;
  cfg.tcp_buffer_pool_size = 10;  // Invalid: < max_connections

  valk_aio_system_t *sys = valk_aio_start_with_config(&cfg);
  TEST_ASSERT_NULL(sys);  // Should fail validation
}
```

### Integration Tests (Lisp)

Add to `test/test_aio_config.valk`:

#### T8: Lisp Config Parsing

```lisp
; Test default config
(def sys (aio-start))
(assert (not (nil? sys)) "aio-start with defaults should succeed")
(aio-stop sys)

; Test custom config
(def sys2 (aio-start {:max-connections 200 :max-concurrent-streams 50}))
(assert (not (nil? sys2)) "aio-start with config should succeed")
(aio-stop sys2)
```

#### T9: Invalid Lisp Config

```lisp
; Test invalid config (should return nil or error)
(def sys3 (aio-start {:max-connections 0}))
(assert (nil? sys3) "aio-start with invalid config should fail")
```

### Load Tests

#### T10: Verify Scaling Works

```bash
# Start server with 500 connection config
./build/valk -e '(aio-start {:max-connections 500})' &

# Run load test with 500 concurrent connections
wrk -t12 -c500 -d30s https://localhost:8443/

# Verify:
# - No "TCP buffer slab exhausted" errors
# - Backpressure only triggers under extreme load
# - All connections eventually serviced
```

#### T11: Memory Bounds

```bash
# Monitor memory usage
valgrind --tool=massif ./build/valk -e '
  (def sys (aio-start {:max-connections 100}))
  (http-listen sys 8443 "key.pem" "cert.pem" handler)
  (sleep 60000)
'

# Verify memory usage matches expected:
# ~46MB TCP buffers + arena pool (max 12.8GB, typical 1-2GB)
```

### Backwards Compatibility Tests

#### T12: Existing Code Still Works

```c
// Existing code without config should still work
valk_aio_system_t *sys = valk_aio_start();
TEST_ASSERT_NOT_NULL(sys);
valk_aio_stop(sys);
```

#### T13: Existing Lisp Code Still Works

```lisp
; Old-style aio-start without config
(def sys (aio-start))
(assert (not (nil? sys)))
(aio-stop sys)
```

---

## Usage Examples

### Development (Defaults)

```c
// Use defaults - good for local development
valk_aio_system_t *sys = valk_aio_start();
```

### Production (High Concurrency)

```c
valk_aio_system_config_t config = valk_aio_system_config_default();
config.max_connections = 1000;
config.max_concurrent_streams = 100;
// Derived: tcp_buffer_pool_size = 14,500, arena_pool_size = 2,000

valk_aio_system_t *sys = valk_aio_start_with_config(&config);
```

### Memory-Constrained Environment

```c
valk_aio_system_config_t config = valk_aio_system_config_default();
config.max_connections = 50;
config.max_concurrent_streams = 20;  // Fewer streams = fewer buffers
config.arena_size = 16 * 1024 * 1024;  // 16MB instead of 64MB
config.arena_pool_size = 50;           // Override: 1 per connection

valk_aio_system_t *sys = valk_aio_start_with_config(&config);
```

### Lisp Configuration

```lisp
; Simple - just set max connections
(def sys (aio-start {:max-connections 500}))

; Advanced - full control
(def sys (aio-start {
  :max-connections 500
  :max-concurrent-streams 50
  :tcp-buffer-pool-size 5000
  :arena-pool-size 500
  :arena-size 33554432  ; 32MB
}))
```

---

## Migration Guide

### For C Code

**Before:**
```c
valk_aio_system_t *sys = valk_aio_start();
// Limited to hardcoded 10 connections, 1024 buffers
```

**After:**
```c
// Option 1: Use defaults (100 connections, 100 streams)
valk_aio_system_t *sys = valk_aio_start();

// Option 2: Custom configuration
valk_aio_system_config_t config = valk_aio_system_config_default();
config.max_connections = 500;
config.max_concurrent_streams = 100;
valk_aio_system_t *sys = valk_aio_start_with_config(&config);
```

### For Lisp Code

**Before:**
```lisp
(def sys (aio-start))
```

**After:**
```lisp
; Same as before (uses defaults)
(def sys (aio-start))

; Or with config
(def sys (aio-start {:max-connections 500 :max-concurrent-streams 100}))
```

---

## Future Enhancements

### Auto-Growing Arena Pool

Current behavior: When arena pool exhausted, immediately return 503.

Proposed: Fallback to malloc when slab exhausted, track overflow metrics.

```c
valk_slab_item_t *arena_item = valk_slab_aquire(sys->httpStreamArenas);
if (!arena_item) {
  // Fallback to malloc instead of 503
  arena_item = malloc(sizeof(valk_mem_arena_t) + sys->config.arena_size);
  atomic_fetch_add(&sys->system_stats.arena_pool_malloc_fallback, 1);
  VALK_WARN("Arena pool exhausted, using malloc fallback");
}
```

### Request Body Streaming

Current: Requests are fully buffered before handler is called.

Proposed: Register `on_data_chunk_recv_callback` for server, allow handlers to receive body chunks incrementally.

### Per-Connection Memory Enforcement

Current: `connection_heap_size` is unused.

Proposed: Implement via custom `nghttp2_mem` callbacks:
```c
typedef struct {
  valk_mem_arena_t *conn_heap;
  size_t used;
  size_t max;
} nghttp2_mem_ctx_t;

static void *conn_malloc(size_t size, void *mem_user_data) {
  nghttp2_mem_ctx_t *ctx = mem_user_data;
  if (ctx->used + size > ctx->max) return NULL;  // Enforce limit
  ctx->used += size;
  return valk_arena_allocate(ctx->conn_heap, size);
}
```

---

## Open Questions

1. **Should we log resolved configuration at startup?**
   - Pro: Helps debugging
   - Con: Noisy for simple use cases
   - Recommendation: Log at DEBUG level

2. **Should validation produce warnings for suboptimal configs?**
   - Example: `tcp_buffer_pool_size` below recommended for stream count
   - Recommendation: Yes, log warnings but don't fail

3. **Should we support runtime reconfiguration?**
   - Not planned for initial implementation
   - Would require careful handling of in-flight connections
