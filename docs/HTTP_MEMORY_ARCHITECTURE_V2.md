# HTTP Memory Architecture v2

## Executive Summary

This document describes a redesigned HTTP memory architecture that:
1. Eliminates TCP read slab contention by using per-connection buffers
2. Provides views into connection buffers for zero-copy handler data flow
3. Extracts pressure evaluation into a pure, testable function
4. Reduces copies from 4 to 2 in the common path
5. Enables streaming handlers without TCP layer changes

## Current Architecture Problems

### Copy Chain (4 copies)
```
Kernel TCP Buffer
    │ (1) uv_read
    ▼
TCP Slab Buffer (32KB, contended)
    │ (2) BIO_write
    ▼
OpenSSL read_bio
    │ (3) SSL_read
    ▼
TCP Slab Buffer (reused for decrypted)
    │ (4) arena allocation + memcpy
    ▼
Stream Arena (headers, body)
```

### Contention Points
1. **TCP Read Slab**: All connections compete for read buffers
2. **Stream Arena Slab**: All streams compete for arenas
3. **Backpressure List**: Single linked list, O(n) removal

### Attack Surface
- Slow TLS handshakes hold TCP buffers
- Partial HTTP/2 frames hold TCP buffers
- Malformed requests consume arena slots

---

## New Architecture

### Design Philosophy: Network Layer as Protection Boundary

The network layer is the **gate** protecting the rest of the system from unbounded
internet traffic. Every resource must be bounded with hard limits:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                            INTERNET                                      │
│                       (unbounded, adversarial)                           │
└─────────────────────────────────────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    NETWORK LAYER (all resources bounded)                 │
│                                                                          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌─────────────┐  │
│  │  Connection  │  │  Write Slab  │  │  Arena Slab  │  │  Pending    │  │
│  │  Handle Slab │  │  (N buffers) │  │  (M arenas)  │  │  Stream Q   │  │
│  │  (C handles) │  │              │  │              │  │  (P slots)  │  │
│  └──────────────┘  └──────────────┘  └──────────────┘  └─────────────┘  │
│                                                                          │
│  INVARIANTS:                                                             │
│  - At most C concurrent connections                                      │
│  - At most N in-flight write operations                                  │
│  - At most M concurrent requests being processed                         │
│  - At most P streams queued waiting for arenas                           │
│  - Memory usage: O(C + N + M + P), all compile-time constants            │
│                                                                          │
│  GUARANTEES TO INNER LAYERS:                                             │
│  - Bounded concurrency (never more than M handler invocations)           │
│  - Bounded memory pressure (each handler gets arena of known max size)   │
│  - GC heap pressure bounded by M × arena_size                            │
│  - Cannot be DoS'd by network traffic (only by application bugs)         │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                         HANDLER / APPLICATION                            │
│                                                                          │
│  Can safely assume:                                                      │
│  - Bounded concurrent requests                                           │
│  - Bounded memory per request                                            │
│  - Network layer absorbs all DoS pressure                                │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Why Write Slab is a Protection Mechanism (Not Just Optimization)

The write slab bounds total in-flight output data. This is **intentional backpressure**:

```
Handler wants to send 100MB response
    │
    ▼
Write slab has 32 × 32KB = 1MB capacity
    │
    ├─ First 1MB: acquired from slab, queued to kernel
    │
    ├─ Slab exhausted: handler blocks (or returns deferred)
    │      │
    │      └─ This is GOOD - prevents memory explosion
    │
    ├─ Kernel sends data, write callbacks fire
    │
    ├─ Slab items released back to pool
    │
    └─ Handler continues sending next 1MB
```

Without bounded writes (e.g., using malloc):
- Handler could queue 100MB instantly
- malloc "succeeds" (OS overcommits memory)
- System thrashes swap or OOM killer arrives
- Other connections starve

**Write slab exhaustion is not a bug - it's the system protecting itself.**

### Memory Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         CONNECTION HANDLE                                │
│  (allocated from handle slab, one per connection)                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │  read_buf (embedded, per-connection)                            │    │
│  │  ┌─────────────────────┬─────────────────────────────────────┐  │    │
│  │  │ encrypted[32KB]     │ decrypted[32KB]                     │  │    │
│  │  │ ← uv_read writes    │ ← SSL_read outputs                  │  │    │
│  │  │                     │ ← nghttp2 parses directly           │  │    │
│  │  │                     │ ← handlers receive views            │  │    │
│  │  └─────────────────────┴─────────────────────────────────────┘  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  ssl_ctx, nghttp2_session, active_streams, etc.                         │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
           │
           │ Handler receives view into decrypted region
           ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                      HANDLER DECISION POINT                              │
│                                                                          │
│  Option A: Buffering Handler                                             │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │  Acquires stream arena (from bounded arena slab)                │    │
│  │  Copies headers + body chunks from view                         │    │
│  │  Processes complete request                                     │    │
│  │  Releases arena on response complete                            │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
│  Option B: Streaming Handler                                             │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │  Processes view directly (no arena needed)                      │    │
│  │  Writes to file/socket/etc immediately                          │    │
│  │  Returns before view is invalidated                             │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
           │
           │ Response via TCP Write Slab
           ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                   TCP WRITE SLAB (Protection Mechanism)                  │
│                                                                          │
│  Purpose: Bound total in-flight output data across all connections       │
│                                                                          │
│  Why slab, not malloc:                                                   │
│  - Bounded memory: exactly (pool_size × buffer_size) bytes maximum       │
│  - Backpressure: exhaustion blocks new writes, doesn't crash             │
│  - Server-controlled: we decide send rate, not attacker                  │
│  - Predictable: memory ceiling known at startup                          │
│                                                                          │
│  Flow:                                                                   │
│  - nghttp2_session_mem_send2 produces HTTP/2 frames                      │
│  - Acquire buffer from slab (block if exhausted)                         │
│  - SSL_write encrypts into buffer                                        │
│  - uv_write sends async                                                  │
│  - Release buffer in write callback                                      │
│                                                                          │
│  If slab exhausted:                                                      │
│  - Don't call nghttp2_session_mem_send2 until space available            │
│  - This is intentional backpressure, not a bug                           │
│  - Protects system from memory exhaustion                                │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Bounded Resource Summary

| Resource | Config Field | Bound | Protects Against |
|----------|--------------|-------|------------------|
| Connection handles | `max_connections` | C handles | Connection flood |
| Per-conn read buffer | (embedded) | 64KB × C | Read amplification |
| Write slab | `tcp_write_buffer_pool_size` | N × 32KB | Write amplification / memory exhaustion |
| Stream arenas | `arena_pool_size` | M × `arena_size` | Request body flood |
| Pending stream queue | `pending_stream_pool_size` | P slots | Stream flood during arena exhaustion |
| Backpressure queue | `backpressure_list_max` | Q entries | Slow client accumulation |

**Total memory ceiling (compile-time constant):**
```
max_memory = (C × 64KB)              # per-connection read buffers
           + (N × 32KB)              # write slab
           + (M × arena_size)        # stream arenas
           + (handle_slab_overhead)  # connection state
           + (fixed_overhead)        # SSL contexts, nghttp2, etc.
```

Attacker cannot push memory usage past this ceiling.

### Copy Chain (2 copies)
```
Kernel TCP Buffer
    │ (1) uv_read → conn->read_buf.encrypted
    ▼
Connection encrypted region
    │ SSL_read (in-place to decrypted region)
    ▼
Connection decrypted region
    │ nghttp2 parses in-place
    │ handler receives VIEW (no copy)
    │ (2) handler copies to arena IF buffering
    ▼
Stream Arena (only if handler buffers)
```

### Why Reads Use Per-Connection Buffer, Writes Use Slab

**Reads are serialized by the OS:**
```
uv_read callback fires
    │
    ├─ Process data (SSL decrypt, HTTP parse)
    │
    └─ Return from callback
        │
        └─ Only NOW can next read callback fire
```
- Only one read callback active at a time per connection
- We fully process data before returning
- One buffer per connection is sufficient
- No contention between connections (each has own buffer)

**Writes are pipelined:**
```
Handler produces response
    │
    ├─ uv_write(chunk1) → returns immediately
    ├─ uv_write(chunk2) → returns immediately  
    ├─ uv_write(chunk3) → returns immediately
    │
    │   ... kernel sending in background ...
    │
    ├─ write_callback(chunk1) → release buffer
    ├─ write_callback(chunk2) → release buffer
    └─ write_callback(chunk3) → release buffer
```
- Multiple writes in flight simultaneously per connection
- Can't embed N buffers in connection (N is unbounded for large responses)
- Slab provides bounded pool shared across all connections
- Exhaustion = backpressure (intentional, not failure)

**Contention characteristics:**

| Property | Read (old slab) | Write (keep slab) |
|----------|-----------------|-------------------|
| Contention source | Attacker-controlled (slow TLS, partial frames) | Server-controlled (we decide when to send) |
| Duration held | SSL handshake + HTTP parsing (slow, variable) | uv_write to callback (fast, kernel-limited) |
| Count per connection | 1 at a time | Many concurrent (chunked responses) |
| Exhaustion impact | Blocks victim connections | Blocks our own output (backpressure) |

Read slab was an attack surface. Write slab is a protection mechanism.

---

## Core Data Structures

### Connection Read Buffer

```c
// src/aio_conn_buffer.h

#define VALK_CONN_ENCRYPTED_SIZE (32 * 1024)  // 32KB
#define VALK_CONN_DECRYPTED_SIZE (32 * 1024)  // 32KB
#define VALK_CONN_BUFFER_SIZE (VALK_CONN_ENCRYPTED_SIZE + VALK_CONN_DECRYPTED_SIZE)

typedef struct valk_conn_read_buf {
  // Encrypted region - uv_read writes here
  uint8_t encrypted[VALK_CONN_ENCRYPTED_SIZE];
  size_t encrypted_len;       // Bytes of encrypted data present
  size_t encrypted_consumed;  // Bytes fed to SSL

  // Decrypted region - SSL_read outputs here
  uint8_t decrypted[VALK_CONN_DECRYPTED_SIZE];
  size_t decrypted_len;       // Bytes of decrypted data present
  size_t decrypted_consumed;  // Bytes consumed by nghttp2
} valk_conn_read_buf_t;

// Initialize read buffer (zeroes counters)
void valk_conn_read_buf_init(valk_conn_read_buf_t *buf);

// Get pointer for uv_read to write into
// Returns NULL if buffer full (backpressure needed)
uint8_t *valk_conn_read_buf_get_encrypted_ptr(valk_conn_read_buf_t *buf, size_t *available);

// Record bytes written by uv_read
void valk_conn_read_buf_commit_encrypted(valk_conn_read_buf_t *buf, size_t len);

// Get encrypted data for SSL
const uint8_t *valk_conn_read_buf_get_encrypted(valk_conn_read_buf_t *buf, size_t *len);

// Mark encrypted bytes as consumed by SSL
void valk_conn_read_buf_consume_encrypted(valk_conn_read_buf_t *buf, size_t len);

// Get pointer for SSL_read to write decrypted data into
uint8_t *valk_conn_read_buf_get_decrypted_ptr(valk_conn_read_buf_t *buf, size_t *available);

// Record bytes written by SSL_read
void valk_conn_read_buf_commit_decrypted(valk_conn_read_buf_t *buf, size_t len);

// Get decrypted data for nghttp2/handler
const uint8_t *valk_conn_read_buf_get_decrypted(valk_conn_read_buf_t *buf, size_t *len);

// Mark decrypted bytes as consumed by nghttp2
void valk_conn_read_buf_consume_decrypted(valk_conn_read_buf_t *buf, size_t len);

// Compact buffers (move unconsumed data to start)
void valk_conn_read_buf_compact(valk_conn_read_buf_t *buf);
```

### Body View (Zero-Copy Interface)

```c
// src/aio_body_view.h

typedef enum {
  VALK_BODY_CONTINUE,   // More data expected
  VALK_BODY_COMPLETE,   // END_STREAM was set, this is the last chunk
} valk_body_status_e;

typedef struct valk_body_chunk {
  const uint8_t *data;      // Points into conn->read_buf.decrypted (NOT OWNED)
  size_t len;               // Length of this chunk
  valk_body_status_e status;
} valk_body_chunk_t;

// Header view (for on_header callback)
typedef struct valk_header_view {
  const uint8_t *name;      // Points into conn->read_buf.decrypted (NOT OWNED)
  size_t name_len;
  const uint8_t *value;     // Points into conn->read_buf.decrypted (NOT OWNED)
  size_t value_len;
} valk_header_view_t;

// Request metadata view (set after headers complete)
typedef struct valk_request_meta {
  const char *method;       // Points into conn->read_buf.decrypted
  size_t method_len;
  const char *scheme;
  size_t scheme_len;
  const char *authority;
  size_t authority_len;
  const char *path;
  size_t path_len;
} valk_request_meta_t;
```

### Pressure Evaluation (Pure Function)

```c
// src/aio_pressure.h

typedef struct valk_pressure_state {
  // Resource usage (0.0 to 1.0)
  float tcp_write_slab_usage;
  float arena_slab_usage;
  float pending_stream_usage;
  float handle_slab_usage;

  // Absolute counts
  uint32_t active_connections;
  uint32_t backpressure_queue_len;
  uint32_t pending_stream_count;

  // Timing
  uint64_t oldest_backpressure_age_ms;
  uint64_t oldest_pending_stream_age_ms;
} valk_pressure_state_t;

typedef struct valk_pressure_config {
  float high_watermark;           // Default: 0.85
  float critical_watermark;       // Default: 0.95

  uint32_t backpressure_max;      // Default: 1000
  uint32_t backpressure_timeout_ms; // Default: 30000

  uint32_t pending_stream_max;    // Default: 64
  uint32_t pending_stream_timeout_ms; // Default: 10000
} valk_pressure_config_t;

typedef enum {
  VALK_PRESSURE_NORMAL,     // Accept all
  VALK_PRESSURE_ELEVATED,   // Slow accept, prioritize completing in-flight
  VALK_PRESSURE_HIGH,       // No new connections, 503 for new streams
  VALK_PRESSURE_CRITICAL,   // Drop oldest queued, aggressive timeouts
} valk_pressure_level_e;

typedef struct valk_pressure_decision {
  valk_pressure_level_e level;

  // Connection-level decisions
  bool accept_connection;
  float connection_shed_probability;  // 0.0 to 1.0

  // Stream-level decisions
  bool accept_stream;
  bool use_pending_queue;

  // Cleanup actions
  bool drop_oldest_backpressure;
  bool drop_oldest_pending_stream;
  uint32_t connections_to_timeout;
} valk_pressure_decision_t;

// Pure function - no side effects, easy to test
valk_pressure_decision_t valk_pressure_evaluate(
    const valk_pressure_state_t *state,
    const valk_pressure_config_t *config
);

// Collect current pressure state from system
valk_pressure_state_t valk_pressure_collect(valk_aio_system_t *sys);

// Default configuration
valk_pressure_config_t valk_pressure_config_default(void);
```

### Body Buffer Helper (For Buffering Handlers)

```c
// src/aio_body_buffer.h

typedef struct valk_body_buffer {
  valk_mem_arena_t *arena;  // Arena to allocate from
  uint8_t *data;            // Current buffer
  size_t len;               // Bytes written
  size_t capacity;          // Allocated capacity
} valk_body_buffer_t;

// Initialize body buffer with arena
void valk_body_buffer_init(valk_body_buffer_t *bb, valk_mem_arena_t *arena);

// Append chunk to buffer (grows as needed)
// Returns false if allocation fails (arena exhausted)
bool valk_body_buffer_append(valk_body_buffer_t *bb, const valk_body_chunk_t *chunk);

// Get final contiguous buffer
// Returns NULL if no data
const uint8_t *valk_body_buffer_get(const valk_body_buffer_t *bb, size_t *len);

// Reset buffer (keeps arena, resets len to 0)
void valk_body_buffer_reset(valk_body_buffer_t *bb);
```

---

## Handler Interface

### C Handler Callbacks

```c
// src/aio_handler.h

// Forward declarations
typedef struct valk_http_stream valk_http_stream_t;

// Handler callback types
typedef void (*valk_on_headers_fn)(
    valk_http_stream_t *stream,
    const valk_request_meta_t *meta,
    void *user_data
);

typedef void (*valk_on_header_fn)(
    valk_http_stream_t *stream,
    const valk_header_view_t *header,
    void *user_data
);

typedef void (*valk_on_body_fn)(
    valk_http_stream_t *stream,
    const valk_body_chunk_t *chunk,
    void *user_data
);

typedef void (*valk_on_complete_fn)(
    valk_http_stream_t *stream,
    void *user_data
);

typedef struct valk_http_handler {
  void *user_data;
  valk_on_headers_fn on_headers;    // Called when all pseudo-headers received
  valk_on_header_fn on_header;      // Called for each regular header
  valk_on_body_fn on_body;          // Called for each body chunk (VIEW!)
  valk_on_complete_fn on_complete;  // Called when request fully received
} valk_http_handler_t;

// Stream API for handlers
typedef struct valk_http_stream {
  int32_t stream_id;
  valk_aio_handle_t *conn;

  // Handler can store state here (NOT managed by TCP layer)
  void *handler_ctx;

  // Arena acquisition (lazy - only if handler needs it)
  valk_mem_arena_t *arena;          // NULL until acquired
  valk_slab_item_t *arena_item;     // For release
} valk_http_stream_t;

// Acquire arena for this stream (lazy allocation)
// Returns NULL if no arenas available (handler should send 503)
valk_mem_arena_t *valk_http_stream_acquire_arena(valk_http_stream_t *stream);

// Send response (takes ownership of nothing - copies as needed)
int valk_http_stream_send_response(
    valk_http_stream_t *stream,
    int status,
    const valk_http2_header_t *headers,
    size_t header_count,
    const uint8_t *body,
    size_t body_len
);

// Send 503 overload response (no arena needed)
int valk_http_stream_send_503(valk_http_stream_t *stream);
```

### Buffering Handler Example

```c
// Example: JSON API handler that needs complete body

typedef struct {
  valk_body_buffer_t body_buf;
  valk_request_meta_t meta;
  bool headers_done;
} api_handler_ctx_t;

void api_on_headers(valk_http_stream_t *stream, const valk_request_meta_t *meta, void *ud) {
  // Acquire arena for this request
  valk_mem_arena_t *arena = valk_http_stream_acquire_arena(stream);
  if (!arena) {
    valk_http_stream_send_503(stream);
    return;
  }

  // Allocate handler context in arena
  api_handler_ctx_t *ctx;
  VALK_WITH_ALLOC((valk_mem_allocator_t *)arena) {
    ctx = valk_mem_alloc(sizeof(api_handler_ctx_t));
    valk_body_buffer_init(&ctx->body_buf, arena);

    // Copy meta strings to arena (they're views into conn buffer)
    ctx->meta.method = valk_arena_strdup(arena, meta->method, meta->method_len);
    ctx->meta.path = valk_arena_strdup(arena, meta->path, meta->path_len);
    // ... etc
  }

  stream->handler_ctx = ctx;
}

void api_on_body(valk_http_stream_t *stream, const valk_body_chunk_t *chunk, void *ud) {
  api_handler_ctx_t *ctx = stream->handler_ctx;

  // Append chunk to body buffer (copies from view to arena)
  if (!valk_body_buffer_append(&ctx->body_buf, chunk)) {
    // Arena exhausted
    valk_http_stream_send_503(stream);
    return;
  }
}

void api_on_complete(valk_http_stream_t *stream, void *ud) {
  api_handler_ctx_t *ctx = stream->handler_ctx;

  // Now we have complete body in arena
  size_t body_len;
  const uint8_t *body = valk_body_buffer_get(&ctx->body_buf, &body_len);

  // Parse JSON, process, send response...
  json_t *json = json_parse(body, body_len);
  // ...

  valk_http_stream_send_response(stream, 200, headers, header_count, response_body, response_len);
  // Arena released automatically when stream closes
}
```

### Streaming Handler Example

```c
// Example: File upload handler that streams to disk

typedef struct {
  FILE *file;
  size_t bytes_written;
} upload_ctx_t;

void upload_on_headers(valk_http_stream_t *stream, const valk_request_meta_t *meta, void *ud) {
  // NO arena needed for streaming!
  upload_ctx_t *ctx = malloc(sizeof(upload_ctx_t));  // Small fixed allocation
  ctx->file = fopen("/tmp/upload.bin", "wb");
  ctx->bytes_written = 0;
  stream->handler_ctx = ctx;
}

void upload_on_body(valk_http_stream_t *stream, const valk_body_chunk_t *chunk, void *ud) {
  upload_ctx_t *ctx = stream->handler_ctx;

  // Write directly from view - NO COPY to arena
  fwrite(chunk->data, 1, chunk->len, ctx->file);
  ctx->bytes_written += chunk->len;

  // MUST return before next uv_read - view becomes invalid
}

void upload_on_complete(valk_http_stream_t *stream, void *ud) {
  upload_ctx_t *ctx = stream->handler_ctx;

  fclose(ctx->file);

  char response[64];
  snprintf(response, sizeof(response), "Uploaded %zu bytes", ctx->bytes_written);

  valk_http_stream_send_response(stream, 200, NULL, 0, (uint8_t *)response, strlen(response));

  free(ctx);
}
```

---

## Pressure Evaluation Algorithm

```c
valk_pressure_decision_t valk_pressure_evaluate(
    const valk_pressure_state_t *state,
    const valk_pressure_config_t *config
) {
  valk_pressure_decision_t decision = {0};

  // Determine overall pressure level
  float max_usage = fmaxf(
    fmaxf(state->tcp_write_slab_usage, state->arena_slab_usage),
    fmaxf(state->pending_stream_usage, state->handle_slab_usage)
  );

  if (max_usage >= config->critical_watermark) {
    decision.level = VALK_PRESSURE_CRITICAL;
  } else if (max_usage >= config->high_watermark) {
    decision.level = VALK_PRESSURE_HIGH;
  } else if (max_usage >= config->high_watermark * 0.7f) {
    decision.level = VALK_PRESSURE_ELEVATED;
  } else {
    decision.level = VALK_PRESSURE_NORMAL;
  }

  // Connection acceptance
  switch (decision.level) {
    case VALK_PRESSURE_NORMAL:
      decision.accept_connection = true;
      decision.connection_shed_probability = 0.0f;
      break;

    case VALK_PRESSURE_ELEVATED:
      decision.accept_connection = true;
      // Gradual slowdown
      decision.connection_shed_probability =
        (max_usage - config->high_watermark * 0.7f) /
        (config->high_watermark * 0.3f) * 0.3f;
      break;

    case VALK_PRESSURE_HIGH:
      decision.accept_connection = false;
      decision.connection_shed_probability = 1.0f;
      break;

    case VALK_PRESSURE_CRITICAL:
      decision.accept_connection = false;
      decision.connection_shed_probability = 1.0f;
      decision.drop_oldest_backpressure = true;
      break;
  }

  // Stream acceptance
  if (state->arena_slab_usage >= config->critical_watermark) {
    decision.accept_stream = false;
    decision.use_pending_queue = false;
  } else if (state->arena_slab_usage >= config->high_watermark) {
    decision.accept_stream = false;
    decision.use_pending_queue =
      state->pending_stream_usage < config->high_watermark;
  } else {
    decision.accept_stream = true;
    decision.use_pending_queue = false;
  }

  // Timeout expired entries
  if (state->oldest_backpressure_age_ms > config->backpressure_timeout_ms) {
    decision.drop_oldest_backpressure = true;
  }
  if (state->oldest_pending_stream_age_ms > config->pending_stream_timeout_ms) {
    decision.drop_oldest_pending_stream = true;
  }

  return decision;
}
```

---

## Implementation Phases

### Phase 1: Connection Read Buffer
1. Add `valk_conn_read_buf_t` to connection handle
2. Modify `__alloc_callback` to return pointer into conn buffer
3. Modify `__http_tcp_read_cb` to use conn buffer
4. Keep TCP slab for writes only
5. Tests: Connection lifecycle, buffer management

### Phase 2: Pressure Module Extraction
1. Create `aio_pressure.h` and `aio_pressure.c`
2. Extract pressure evaluation into pure function
3. Replace inline pressure checks with module calls
4. Tests: Unit tests for all pressure levels and transitions

### Phase 3: Body View Interface
1. Create `aio_body_view.h`
2. Modify nghttp2 callbacks to create views
3. Add handler callback interface
4. Tests: View lifecycle, handler callbacks

### Phase 4: Lazy Arena Acquisition
1. Move arena acquisition from `on_begin_headers` to `on_body` (if handler requests)
2. Implement `valk_http_stream_acquire_arena()`
3. Implement `valk_http_stream_send_503()` (no arena needed)
4. Tests: Buffering handlers, streaming handlers

### Phase 5: Body Buffer Helper
1. Create `aio_body_buffer.h` and `aio_body_buffer.c`
2. Implement grow-on-demand buffer for arenas
3. Tests: Buffer growth, arena exhaustion

---

## Test Plan

### Unit Tests (90% coverage target)

#### `test/unit/test_conn_read_buf.c`

| Test | Description | Coverage |
|------|-------------|----------|
| `test_init_zeroes_counters` | Verify init sets all counters to 0 | Basic init |
| `test_encrypted_ptr_returns_buffer_start` | First call returns buffer start | get_encrypted_ptr |
| `test_encrypted_ptr_advances_after_commit` | Pointer advances after commit | commit_encrypted |
| `test_encrypted_ptr_null_when_full` | Returns NULL when buffer full | Backpressure |
| `test_commit_updates_len` | Commit updates encrypted_len | commit_encrypted |
| `test_get_encrypted_returns_correct_slice` | get_encrypted returns committed data | get_encrypted |
| `test_consume_encrypted_advances_consumed` | Consume advances consumed counter | consume_encrypted |
| `test_decrypted_ptr_returns_buffer_start` | First call returns decrypted buffer start | get_decrypted_ptr |
| `test_decrypted_commit_updates_len` | Commit updates decrypted_len | commit_decrypted |
| `test_get_decrypted_returns_correct_slice` | get_decrypted returns committed data | get_decrypted |
| `test_consume_decrypted_advances_consumed` | Consume advances consumed counter | consume_decrypted |
| `test_compact_moves_unconsumed_to_start` | Compact moves remaining data to start | compact |
| `test_compact_resets_counters` | Compact resets consumed counters | compact |
| `test_full_cycle_encrypt_decrypt` | Complete encrypt/decrypt cycle | Integration |
| `test_partial_consume_then_more_data` | Consume partial, add more, consume rest | Edge case |

#### `test/unit/test_pressure.c`

| Test | Description | Coverage |
|------|-------------|----------|
| `test_normal_accepts_all` | Below 70% high watermark accepts everything | NORMAL level |
| `test_elevated_gradual_shedding` | 70-85% range has gradual shedding | ELEVATED level |
| `test_high_rejects_connections` | 85-95% rejects new connections | HIGH level |
| `test_critical_drops_queued` | Above 95% drops oldest queued | CRITICAL level |
| `test_arena_pressure_blocks_streams` | High arena usage blocks new streams | Arena pressure |
| `test_pending_queue_used_when_available` | Use pending queue when arenas exhausted | Pending queue |
| `test_timeout_triggers_drop` | Old backpressure entries get dropped | Timeout logic |
| `test_multiple_resources_max_wins` | Max of all resources determines level | Multiple resources |
| `test_config_defaults` | Default config has valid values | Config |
| `test_config_validation` | Invalid configs are rejected | Validation |
| `test_shed_probability_in_range` | Shed probability is 0.0-1.0 | Probability |
| `test_collect_state_from_system` | Collect gathers correct values | Integration |

#### `test/unit/test_body_view.c`

| Test | Description | Coverage |
|------|-------------|----------|
| `test_chunk_view_points_to_buffer` | Chunk data points into conn buffer | Basic view |
| `test_chunk_status_continue` | CONTINUE status for non-final chunk | Status |
| `test_chunk_status_complete` | COMPLETE status for END_STREAM | Status |
| `test_header_view_name_value` | Header view has correct name/value | Header view |
| `test_meta_view_pseudo_headers` | Meta contains pseudo-headers | Meta view |
| `test_view_invalid_after_compact` | View becomes invalid after buffer compact | Lifetime |

#### `test/unit/test_body_buffer.c`

| Test | Description | Coverage |
|------|-------------|----------|
| `test_init_sets_arena` | Init stores arena pointer | Init |
| `test_append_single_chunk` | Append single chunk works | Basic append |
| `test_append_multiple_chunks` | Append multiple chunks concatenates | Multiple appends |
| `test_append_grows_buffer` | Buffer grows when needed | Growth |
| `test_append_fails_arena_exhausted` | Returns false when arena full | Error handling |
| `test_get_returns_contiguous` | Get returns contiguous buffer | Get |
| `test_get_empty_returns_null` | Get on empty returns NULL | Edge case |
| `test_reset_keeps_arena` | Reset keeps arena, zeroes len | Reset |
| `test_large_append_multiple_grows` | Large appends cause multiple grows | Stress |

### Integration Tests

#### `test/test_http_views.c`

| Test | Description | Coverage |
|------|-------------|----------|
| `test_simple_get_request` | GET request with view-based headers | Basic flow |
| `test_post_body_single_chunk` | POST with body in single chunk | Body handling |
| `test_post_body_multiple_chunks` | POST with body split across chunks | Chunked body |
| `test_buffering_handler_receives_complete_body` | Handler buffers and gets full body | Buffering |
| `test_streaming_handler_zero_copy` | Streaming handler uses views directly | Streaming |
| `test_handler_arena_lazy_acquisition` | Arena acquired only when needed | Lazy arena |
| `test_handler_no_arena_for_streaming` | Streaming handler needs no arena | Resource usage |
| `test_concurrent_streams_independent_views` | Multiple streams have independent views | Concurrency |

#### `test/test_pressure_integration.c`

| Test | Description | Coverage |
|------|-------------|----------|
| `test_normal_operation` | System under normal load | NORMAL |
| `test_connection_rejection_under_pressure` | High load rejects connections | HIGH |
| `test_stream_503_under_arena_pressure` | Arena exhaustion sends 503 | 503 response |
| `test_pending_queue_drains_on_arena_free` | Pending streams processed when arena freed | Pending queue |
| `test_backpressure_timeout_drops_connection` | Old backpressure entries dropped | Timeout |
| `test_recovery_after_pressure` | System recovers when load decreases | Recovery |
| `test_metrics_updated_correctly` | Pressure metrics accurate | Metrics |

#### `test/test_no_tcp_read_slab.c`

| Test | Description | Coverage |
|------|-------------|----------|
| `test_reads_work_without_slab` | Connections work with conn buffers only | Core |
| `test_many_concurrent_reads` | Many connections reading simultaneously | Concurrency |
| `test_large_request_body` | Large body handled correctly | Large data |
| `test_slow_client_doesnt_block_others` | Slow client isolated to its buffer | Isolation |
| `test_conn_buffer_backpressure` | Full conn buffer triggers backpressure | Backpressure |

### Stress Tests

#### `test/stress/test_http_memory_stress.c`

| Test | Description | Duration |
|------|-------------|----------|
| `test_sustained_load_no_leaks` | 60s sustained load, verify no leaks | 60s |
| `test_burst_load_recovery` | Burst to critical, verify recovery | 30s |
| `test_slow_clients_mixed_fast` | Mix of slow/fast clients | 30s |
| `test_large_body_stress` | Many large body requests | 30s |
| `test_connection_churn` | Rapid connect/disconnect | 30s |

---

## Coverage Analysis

### Files and Expected Coverage

| File | Lines | Covered | % |
|------|-------|---------|---|
| `aio_conn_buffer.c` | ~120 | 115 | 96% |
| `aio_pressure.c` | ~150 | 140 | 93% |
| `aio_body_view.c` | ~80 | 75 | 94% |
| `aio_body_buffer.c` | ~100 | 92 | 92% |
| `aio_uv.c` (modified) | ~3000 | 2700 | 90% |
| **Total New Code** | **~450** | **~420** | **93%** |

### Hard-to-Test Paths

1. **SSL read errors during handshake** - Requires mock SSL
2. **nghttp2 internal errors** - Requires mock nghttp2
3. **uv_write failures** - Requires mock libuv
4. **Race conditions in backpressure list** - Requires thread sanitizer

### Test Categories by Type

```
Unit Tests:        ~50 tests,  90% of new code coverage
Integration Tests: ~20 tests,  covers interactions
Stress Tests:      ~5 tests,   long-running stability
Total:             ~75 tests
```

---

## Migration Path

### Backward Compatibility

1. Existing `valk_http2_handler_t` callbacks continue to work
2. Lisp handlers receive same request Q-expr format
3. SSE handlers unchanged (already use views internally)

### Deprecation

1. `tcp_buffer_pool_size` config - ignored for reads, used for writes
2. Internal slab acquisition in `__alloc_callback` - replaced by conn buffer

### Configuration Changes

```c
typedef struct valk_aio_system_config {
  // ... existing fields ...

  // NEW: Connection buffer sizes
  size_t conn_encrypted_buf_size;  // Default: 32KB
  size_t conn_decrypted_buf_size;  // Default: 32KB

  // CHANGED: Only for writes now
  uint32_t tcp_write_buffer_pool_size;  // Renamed from tcp_buffer_pool_size
} valk_aio_system_config_t;
```

---

## Appendix A: Pressure Level Matrix

| Level | TCP Write | Arena | Accept Conn | Accept Stream | Actions |
|-------|-----------|-------|-------------|---------------|---------|
| NORMAL | <60% | <60% | Yes | Yes | None |
| ELEVATED | 60-85% | 60-85% | Probabilistic | Yes | Monitor |
| HIGH | 85-95% | 85-95% | No | Via queue | Queue new streams |
| CRITICAL | >95% | >95% | No | No | Drop oldest, 503 |

---

## Appendix B: Write Slab Exhaustion Behavior

When the write slab is exhausted, the system applies backpressure to response output:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    WRITE SLAB EXHAUSTION FLOW                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  1. Handler calls send_response()                                        │
│         │                                                                │
│         ▼                                                                │
│  2. Try to acquire write buffer from slab                                │
│         │                                                                │
│         ├─── Buffer available ──► Continue normally                     │
│         │                                                                │
│         └─── Slab exhausted ──► Set conn->pending_write = true          │
│                                      │                                   │
│                                      ▼                                   │
│  3. Return from handler (response queued but not sent)                   │
│         │                                                                │
│         ▼                                                                │
│  4. Other connections complete writes, release buffers                   │
│         │                                                                │
│         ▼                                                                │
│  5. In write callback: check for connections with pending_write          │
│         │                                                                │
│         ▼                                                                │
│  6. Resume sending for those connections                                 │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

**Key behaviors:**
- No malloc fallback (would defeat the purpose)
- No connection drops (just delays output)
- Fair scheduling: round-robin resume among waiting connections
- Metrics: track `write_slab_exhaustion_count`, `pending_write_queue_len`

**Tuning the write slab:**
```c
// Conservative: low memory, may delay large responses
.tcp_write_buffer_pool_size = 32,   // 32 × 32KB = 1MB total

// Balanced: good for most workloads
.tcp_write_buffer_pool_size = 128,  // 128 × 32KB = 4MB total

// High throughput: large responses, many concurrent streams
.tcp_write_buffer_pool_size = 512,  // 512 × 32KB = 16MB total
```

Rule of thumb: `pool_size >= max_connections × 2` for typical workloads.

---

## Appendix C: Memory Budget Calculator

Given configuration:
```c
valk_aio_system_config_t cfg = {
  .max_connections = 100,
  .tcp_write_buffer_pool_size = 256,
  .arena_pool_size = 200,
  .arena_size = 4 * 1024 * 1024,  // 4MB
  .pending_stream_pool_size = 64,
  .backpressure_list_max = 500,
};
```

Memory budget:
```
Per-connection read buffers:  100 × 64KB   =    6.4 MB
Write slab:                   256 × 32KB   =    8.0 MB
Stream arenas:                200 × 4MB    =  800.0 MB
Pending stream queue:         64 × ~1KB   =    0.1 MB
Connection handles:           100 × ~2KB  =    0.2 MB
Backpressure list:            500 × ~32B  =    0.0 MB
                                          ─────────────
Total bounded memory:                     ≈  815 MB
```

This is the **maximum** memory the network layer can consume, regardless of traffic.
The application layer (handlers, GC heap) uses additional memory, but is protected
by the bounded concurrency guarantees (at most 200 concurrent handlers).
