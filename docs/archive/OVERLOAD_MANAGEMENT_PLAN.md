# Overload Management Plan

This document describes the implementation plan for proper HTTP/2 server overload management in Valkyria.

## Problem Statement

During stress testing with `hey -n 5000000 -c 500 -h2 https://localhost:8443/debug/metrics`, the server exhibits resource exhaustion:

```
[ERROR] aio_uv.c:548:__http_on_begin_headers_callback | Stream arena pool exhausted for stream 66511
[ERROR] aio_uv.c:1229:__http_tcp_read_cb | TCP buffer slab exhausted in EOF handling
```

**Current behavior**: When arena pool is exhausted, the server returns `NGHTTP2_ERR_TEMPORAL_CALLBACK_FAILURE` which causes nghttp2 to send `RST_STREAM` with `INTERNAL_ERROR`. Clients see cryptic errors like:

```
stream error: stream ID 66511; INTERNAL_ERROR
```

**Desired behavior**: Return HTTP 503 with proper headers and a configurable error page, matching industry standards (Envoy, nginx).

## Root Cause Analysis

### Current Pool Sizes (src/aio_uv.c:65-80)

```c
enum {
  HTTP_MAX_IO_REQUESTS = (1024),              // TCP buffer slab size
  HTTP_STREAM_ARENA_SIZE = (67108864),        // 64MB per stream arena
  HTTP_STREAM_ARENA_POOL_SIZE = (64),         // Total arenas in pool
};
```

### The Math Problem

- Pool size: 64 arenas
- Per-connection stream limit: 100 (sent via SETTINGS at line 1358)
- Connections from `hey -c 500`: 500
- Theoretical max concurrent streams: 50,000
- Available arenas: 64

The current design cannot handle high concurrency.

### Current Failure Path (src/aio_uv.c:545-551)

```c
valk_slab_item_t *arena_item = valk_slab_aquire(conn->server->sys->httpStreamArenas);
if (!arena_item) {
  VALK_ERROR("Stream arena pool exhausted for stream %d", frame->hd.stream_id);
  // Return error to reject the stream
  return NGHTTP2_ERR_TEMPORAL_CALLBACK_FAILURE;  // <-- Causes RST_STREAM
}
```

## Design

### 1. Configuration API

Configuration is split between **system-level** (pool sizing) and **server-level** (behavior):

#### System Configuration (`aio/new`)

Pool resources are system-wide, so pool sizing is configured when creating the AIO system:

```lisp
; Current API
(def aio (aio/new))

; New API with optional config
(def aio (aio/new {:arena-pool-size 256        ; total stream arenas (default: 256)
                   :arena-size (* 4 1024 1024) ; 4MB per arena (default: 4MB)
                   :tcp-buffer-pool-size 2048})) ; TCP I/O buffers (default: 2048)
```

#### Server Configuration (`http2/server-listen`)

Per-server behavior settings:

```lisp
; Current API (src/parser.c:3621-3656)
(http2/server-listen aio port handler)

; New API with optional config
(http2/server-listen aio port handler {
  :max-concurrent-streams 100    ; per-connection limit (SETTINGS frame)
  :error-handler error-fn        ; optional custom error handler
})

; Error handler signature:
; (lambda {status-code request} ...) -> string
; - status-code: 503, 502, 500, etc.
; - request: request map or nil if error before parsing
; - returns: HTML string for response body
```

### 2. Configuration Structs

**File: src/aio.h** - system config (new struct)

```c
typedef struct valk_aio_system_config {
  // Pool sizing (system-wide resources)
  uint32_t arena_pool_size;        // Total stream arenas (default: 256)
  size_t   arena_size;             // Bytes per arena (default: 4MB)
  uint32_t tcp_buffer_pool_size;   // TCP I/O buffers (default: 2048)
} valk_aio_system_config_t;

// Default system configuration
static inline valk_aio_system_config_t valk_aio_system_config_default(void) {
  return (valk_aio_system_config_t){
    .arena_pool_size = 256,
    .arena_size = 4 * 1024 * 1024,  // 4MB
    .tcp_buffer_pool_size = 2048,
  };
}
```

**File: src/aio.h** - server config (new struct)

```c
typedef struct valk_http_server_config {
  // Connection limits
  uint32_t max_concurrent_streams;   // Per-connection, sent via SETTINGS (default: 100)

  // Error handling - pre-rendered at server startup
  const char* error_503_body;        // Pre-rendered 503 body (NULL = use default)
  size_t      error_503_body_len;    // Length of pre-rendered body
} valk_http_server_config_t;

// Default server configuration
static inline valk_http_server_config_t valk_http_server_config_default(void) {
  return (valk_http_server_config_t){
    .max_concurrent_streams = 100,
    .error_503_body = NULL,
    .error_503_body_len = 0,
  };
}
```

**Pre-rendering approach**: The error handler is called **once at server startup** and the result is cached. This avoids memory allocation during overload conditions.

```lisp
; Error handler is evaluated once at startup, result is cached
(http2/server-listen aio 8443 handler {
  :error-handler (lambda {status-code}
    (str "<html><body>"
         "<h1>" status-code " - Service Unavailable</h1>"
         "<p>Server: MyApp v1.2.3</p>"
         "</body></html>"))
})
```

**Handler signature**: `(lambda {status-code} ...) -> string`
- `status-code`: 503 (passed at startup for rendering)
- Returns: HTML/text body string (cached for all future 503 responses)

**Note**: Since the handler is pre-rendered, it cannot include per-request information. The `request` parameter from the original design is removed.

### 3. Metrics

Using the existing metrics system (`src/metrics.h`), add the following.

**Note**: Metric names use `http_*` prefix (not `valk_http_*`) to match existing conventions.

**Gauges** (current state):

| Metric | Description |
|--------|-------------|
| `http_arena_pool_total` | Pool capacity (system-wide) |
| `http_arena_pool_in_use` | Currently acquired arenas (system-wide) |
| `http_tcp_buffer_pool_total` | TCP buffer pool capacity |
| `http_tcp_buffer_pool_in_use` | Currently acquired buffers |
| `http_active_streams{port="..."}` | Active HTTP/2 streams (per-server) |
| `http_connections_active{port="..."}` | Active TCP connections (per-server, exists) |

**Counters** (cumulative):

| Metric | Description |
|--------|-------------|
| `http_arena_pool_overflow_total` | Arena acquire failures (system-wide) |
| `http_tcp_buffer_overflow_total` | TCP buffer acquire failures |
| `http_overload_responses_total{port="..."}` | 503 responses sent (per-server) |

**File: src/aio_uv.c** - add to `valk_server_metrics_t` (around line 51):

```c
typedef struct {
  // Existing metrics...
  valk_counter_t* requests_total;
  valk_counter_t* requests_success;
  // ...

  // New overload metrics (per-server)
  valk_counter_t* overload_responses;
} valk_server_metrics_t;
```

**File: src/aio_metrics.h** - add to `valk_aio_system_stats_t` (around line 42):

```c
typedef struct {
  // Existing fields...
  _Atomic uint64_t arenas_used;
  uint64_t arenas_total;

  // New overflow tracking (system-wide)
  valk_counter_t* arena_pool_overflow;
  valk_counter_t* tcp_buffer_overflow;
} valk_aio_system_stats_t;
```

### 4. Slab Instrumentation

**File: src/memory.h** - add overflow tracking to slab (around line 206):

```c
typedef struct {
  valk_mem_allocator_e type;
  size_t itemSize;
  size_t numItems;
  size_t numFree;
  uint64_t overflowCount;  // NEW: track failures (use __atomic_fetch_add)
  uint64_t head;
  uint8_t heap[];
} valk_slab_t;
```

**Note**: `numAcquired` is omitted as it's redundant (`numItems - numFree`).

**File: src/memory.c** - update `valk_slab_aquire` (around line 268):

```c
valk_slab_item_t *valk_slab_aquire(valk_slab_t *self) {
  // Phase 1: Reserve a slot atomically
  size_t expected, desired;
  do {
    expected = __atomic_load_n(&self->numFree, __ATOMIC_ACQUIRE);
    if (expected == 0) {
      __atomic_fetch_add(&self->overflowCount, 1, __ATOMIC_RELAXED);  // NEW
      return NULL;
    }
    desired = expected - 1;
  } while (!__atomic_compare_exchange_n(&self->numFree, &expected, desired,
                                        false, __ATOMIC_ACQ_REL,
                                        __ATOMIC_RELAXED));

  // Phase 2: Pop from Treiber stack (existing logic)
  // ...
}
```

**File: src/memory.c** - update `valk_slab_init` (around line 210):

```c
void valk_slab_init(valk_slab_t *self, size_t itemSize, size_t numItems) {
  // ... existing code ...
  __atomic_store_n(&self->numFree, numItems, __ATOMIC_RELAXED);
  __atomic_store_n(&self->overflowCount, 0, __ATOMIC_RELAXED);  // NEW
}
```

### 5. Overload Response Path

**File: src/aio_uv.c** - replace RST_STREAM with HTTP 503 (around line 545):

```c
static int __http_on_begin_headers_callback(nghttp2_session *session,
                                            const nghttp2_frame *frame,
                                            void *user_data) {
  valk_aio_http_conn *conn = (valk_aio_http_conn *)user_data;

  if (frame->hd.type == NGHTTP2_HEADERS &&
      frame->headers.cat == NGHTTP2_HCAT_REQUEST) {

    conn->active_streams++;

    // Acquire per-stream arena from slab
    valk_slab_item_t *arena_item = valk_slab_aquire(conn->server->sys->httpStreamArenas);
    if (!arena_item) {
      // NEW: Send 503 instead of RST_STREAM
      conn->active_streams--;

#ifdef VALK_METRICS_ENABLED
      valk_counter_inc(conn->server->sys->system_stats.arena_pool_overflow);
      valk_counter_inc(conn->server->metrics.overload_responses);
#endif

      __http_send_overload_response(session, frame->hd.stream_id, conn);
      return 0;  // Success - we handled it with 503
    }

    // ... rest of existing code ...
  }
  return 0;
}
```

**New function to send 503 response** (thread-local static for body source):

```c
// Thread-local body source (safe - event loop is single-threaded)
static _Thread_local http_body_source_t __overload_body_src;

// Send HTTP 503 response for overload conditions
static void __http_send_overload_response(nghttp2_session *session,
                                          int32_t stream_id,
                                          valk_aio_http_conn *conn) {
  const char* body;
  size_t body_len;

  // Use pre-rendered custom body if available, otherwise default
  if (conn->server->config.error_503_body) {
    body = conn->server->config.error_503_body;
    body_len = conn->server->config.error_503_body_len;
  } else {
    body = valk_http_default_503_html;
    body_len = valk_http_default_503_html_len;
  }

  // Setup thread-local body source
  __overload_body_src.body = body;
  __overload_body_src.body_len = body_len;
  __overload_body_src.offset = 0;

  // Build response headers (stack allocation OK - nghttp2 copies them)
  // Note: content-length omitted (optional in HTTP/2)
  nghttp2_nv headers[] = {
    MAKE_NV2(":status", "503"),
    MAKE_NV2("content-type", "text/html; charset=utf-8"),
    MAKE_NV2("retry-after", "1"),
  };

  // Submit response using nghttp2_data_provider2 (modern API)
  nghttp2_data_provider2 data_prd = {
    .source.ptr = &__overload_body_src,
    .read_callback = __http_byte_body_cb,
  };

  nghttp2_submit_response2(session, stream_id, headers,
                           sizeof(headers) / sizeof(headers[0]), &data_prd);
}
```

### 6. Default Error HTML

**File: src/aio_uv.c** - embedded HTML template:

```c
static const char valk_http_default_503_html[] =
  "<!DOCTYPE html>\n"
  "<html>\n"
  "<head>\n"
  "  <title>503 Service Unavailable</title>\n"
  "  <style>\n"
  "    body {\n"
  "      font-family: system-ui, -apple-system, sans-serif;\n"
  "      max-width: 600px;\n"
  "      margin: 100px auto;\n"
  "      padding: 20px;\n"
  "      text-align: center;\n"
  "      color: #333;\n"
  "    }\n"
  "    h1 {\n"
  "      font-size: 72px;\n"
  "      margin: 0;\n"
  "      color: #e53935;\n"
  "    }\n"
  "    p {\n"
  "      font-size: 18px;\n"
  "      color: #666;\n"
  "      margin-top: 20px;\n"
  "    }\n"
  "  </style>\n"
</head>\n"
  "<body>\n"
  "  <h1>503</h1>\n"
  "  <p>Server is temporarily at capacity.<br>Please try again shortly.</p>\n"
  "</body>\n"
  "</html>\n";

static const size_t valk_http_default_503_html_len = sizeof(valk_http_default_503_html) - 1;
```

### 7. Update Server Struct

**File: src/aio_uv.c:303-316** - add config field:

```c
typedef struct valk_aio_http_server {
  __aio_http_srv_e state;
  valk_aio_system_t *sys;
  SSL_CTX *ssl_ctx;
  valk_aio_handle_t *listener;
  char interface[200];
  int port;
  valk_http2_handler_t handler;
  valk_lval_t* lisp_handler_fn;
  valk_lenv_t* sandbox_env;
  valk_http_server_config_t config;  // NEW
#ifdef VALK_METRICS_ENABLED
  valk_server_metrics_t metrics;
#endif
} valk_aio_http_server;
```

### 8. Helper Function for Plist Parsing

**File: src/parser.c** - add helper (needed because `valk_map_get()` doesn't exist):

```c
// Get value from property list (plist) by key symbol
// Plist format: {:key1 val1 :key2 val2 ...}
static valk_lval_t* valk_plist_get(valk_lval_t* plist, const char* key_str) {
  if (!plist || LVAL_TYPE(plist) != LVAL_QEXPR) return NULL;

  valk_lval_t* curr = plist;
  while (curr && LVAL_TYPE(curr) == LVAL_CONS) {
    if (valk_lval_list_is_empty(curr)) break;

    valk_lval_t* key = curr->cons.head;
    valk_lval_t* rest = curr->cons.tail;

    if (!rest || valk_lval_list_is_empty(rest)) break;

    valk_lval_t* val = rest->cons.head;

    if (LVAL_TYPE(key) == LVAL_SYM && strcmp(key->str, key_str) == 0) {
      return val;
    }

    curr = rest->cons.tail;  // Skip key and value
  }
  return NULL;
}
```

### 9. Update Lisp Builtins

**File: src/parser.c** - update `aio/new` to accept config:

```c
static valk_lval_t* valk_builtin_aio_new(valk_lenv_t* e, valk_lval_t* a) {
  UNUSED(e);

  // Accept 0 or 1 arguments
  size_t argc = valk_lval_list_count(a);
  LVAL_ASSERT(a, argc <= 1, "aio/new expects 0 or 1 arguments, got %zu", argc);

  // Start with defaults
  valk_aio_system_config_t config = valk_aio_system_config_default();

  // Parse optional config map
  if (argc == 1) {
    valk_lval_t* config_qexpr = valk_lval_list_nth(a, 0);
    LVAL_ASSERT_TYPE(a, config_qexpr, LVAL_QEXPR);

    valk_lval_t* val;

    val = valk_plist_get(config_qexpr, ":arena-pool-size");
    if (val && LVAL_TYPE(val) == LVAL_NUM) {
      config.arena_pool_size = (uint32_t)val->num;
    }

    val = valk_plist_get(config_qexpr, ":arena-size");
    if (val && LVAL_TYPE(val) == LVAL_NUM) {
      config.arena_size = (size_t)val->num;
    }

    val = valk_plist_get(config_qexpr, ":tcp-buffer-pool-size");
    if (val && LVAL_TYPE(val) == LVAL_NUM) {
      config.tcp_buffer_pool_size = (uint32_t)val->num;
    }
  }

  // Create system with config
  valk_aio_system_t* sys = valk_aio_system_new_with_config(&config);
  // ... rest of function ...
}
```

**File: src/parser.c** - update `http2/server-listen` to accept config:

```c
static valk_lval_t* valk_builtin_http2_server_listen(valk_lenv_t* e,
                                                     valk_lval_t* a) {
  // Accept 3 or 4 arguments
  size_t argc = valk_lval_list_count(a);
  LVAL_ASSERT(a, argc >= 3 && argc <= 4,
              "http2/server-listen expects 3 or 4 arguments, got %zu", argc);

  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_REF);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 1), LVAL_NUM);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 2), LVAL_FUN);

  valk_aio_system_t* sys = valk_lval_list_nth(a, 0)->ref.ptr;
  int port = (int)valk_lval_list_nth(a, 1)->num;
  valk_lval_t* handler_fn = valk_lval_list_nth(a, 2);

  // Start with defaults
  valk_http_server_config_t config = valk_http_server_config_default();

  // Parse optional config map
  if (argc == 4) {
    valk_lval_t* config_qexpr = valk_lval_list_nth(a, 3);
    LVAL_ASSERT_TYPE(a, config_qexpr, LVAL_QEXPR);

    valk_lval_t* val;

    val = valk_plist_get(config_qexpr, ":max-concurrent-streams");
    if (val && LVAL_TYPE(val) == LVAL_NUM) {
      config.max_concurrent_streams = (uint32_t)val->num;
    }

    // Pre-render error handler at startup
    val = valk_plist_get(config_qexpr, ":error-handler");
    if (val && LVAL_TYPE(val) == LVAL_FUN) {
      // Call (error-handler 503) once at startup to get the body string
      valk_lval_t* args = valk_lval_qexpr();
      args = valk_lval_list_append(args, valk_lval_num(503));

      valk_lval_t* result = valk_lval_call(e, val, args);

      if (LVAL_TYPE(result) == LVAL_STR) {
        // Copy rendered body to GC heap for persistence
        VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
          size_t len = strlen(result->str);
          char* body_copy = valk_mem_alloc(len + 1);
          memcpy(body_copy, result->str, len + 1);
          config.error_503_body = body_copy;
          config.error_503_body_len = len;
        }
      } else if (LVAL_TYPE(result) == LVAL_ERR) {
        VALK_WARN("Error handler returned error: %s, using default 503 page",
                  result->str);
      } else {
        VALK_WARN("Error handler must return string, got %s, using default 503 page",
                  valk_ltype_name(LVAL_TYPE(result)));
      }
    }
  }

  // Copy handler to GC heap
  valk_lval_t* heap_handler;
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    heap_handler = valk_lval_copy(handler_fn);
  }

  // ... rest of function using config ...
}
```

## Test Cases

### Test 1: Basic 503 Response on Overload

**File: test/test_overload.valk**

```lisp
(load "src/prelude.valk")

; Create system with tiny arena pool to force overload
(def aio (aio/new {:arena-pool-size 2
                   :arena-size 4096}))

(def handler (lambda {req respond}
  (respond 200 {"content-type" "text/plain"} "OK")))

(http2/server-listen aio 8443 handler {:max-concurrent-streams 10})

; Server running - test with external client
(print "Server running on :8443 with arena-pool-size=2")
(print "Test with: curl -k https://localhost:8443/ & curl -k https://localhost:8443/ & curl -k https://localhost:8443/")
(aio/run aio)
```

### Test 2: Custom Error Handler

**File: test/test_custom_error_handler.valk**

```lisp
(load "src/prelude.valk")

; Error handler is called once at startup with status-code=503
; The returned string is cached and used for all future 503 responses
(def my-error-handler (lambda {status-code}
  (str "<html><body>"
       "<h1>Custom " status-code "</h1>"
       "<p>Server: MyApp v1.0</p>"
       "<p>Please try again in a few seconds.</p>"
       "</body></html>")))

(def aio (aio/new {:arena-pool-size 2}))

(def handler (lambda {req respond}
  (respond 200 {"content-type" "text/plain"} "OK")))

(http2/server-listen aio 8443 handler {:error-handler my-error-handler})
(print "Custom 503 page pre-rendered at startup")
(aio/run aio)
```

### Test 3: Metrics Verification

**File: test/test_overload_metrics.valk**

```lisp
(load "src/prelude.valk")

(def aio (aio/new {:arena-pool-size 4}))

(def handler (lambda {req respond}
  (if (= (plist/get req :path) "/metrics")
    ; Return prometheus metrics
    (respond 200 {"content-type" "text/plain"} (metrics/prometheus))
    (respond 200 {"content-type" "text/plain"} "OK"))))

(http2/server-listen aio 8443 handler)
(print "Check metrics at https://localhost:8443/metrics")
(print "Look for: http_arena_pool_overflow_total")
(aio/run aio)
```

### Test 4: C Unit Test for Slab Overflow Counter

**File: test/test_slab_overflow.c**

```c
#include "testing.h"
#include "memory.h"

void test_slab_overflow_counter(void) {
  // Create tiny slab with 2 items
  valk_slab_t* slab = valk_slab_new(64, 2);

  // Verify initial state
  TEST_ASSERT(slab->overflowCount == 0, "overflowCount should start at 0");

  // Acquire all items
  valk_slab_item_t* item1 = valk_slab_aquire(slab);
  valk_slab_item_t* item2 = valk_slab_aquire(slab);

  TEST_ASSERT(item1 != NULL, "First acquire should succeed");
  TEST_ASSERT(item2 != NULL, "Second acquire should succeed");

  // This should fail and increment overflow counter
  valk_slab_item_t* item3 = valk_slab_aquire(slab);
  TEST_ASSERT(item3 == NULL, "Third acquire should fail");
  TEST_ASSERT(slab->overflowCount == 1, "overflowCount should be 1");

  // Try again - should increment again
  valk_slab_item_t* item4 = valk_slab_aquire(slab);
  TEST_ASSERT(item4 == NULL, "Fourth acquire should also fail");
  TEST_ASSERT(slab->overflowCount == 2, "overflowCount should be 2");

  // Release one and try again
  valk_slab_release(slab, item1);

  valk_slab_item_t* item5 = valk_slab_aquire(slab);
  TEST_ASSERT(item5 != NULL, "Fifth acquire should succeed after release");
  TEST_ASSERT(slab->overflowCount == 2, "overflowCount should still be 2");

  valk_slab_free(slab);
}

int main(void) {
  TEST_RUN(test_slab_overflow_counter);
  return test_summary();
}
```

### Test 5: Integration Test with hey

**File: test/stress/test_overload_503.sh**

```bash
#!/bin/bash
set -e

# Start server in background
./build/valk test/test_overload.valk &
SERVER_PID=$!
sleep 2

# Run stress test
hey -n 1000 -c 100 -h2 https://localhost:8443/ 2>&1 | tee /tmp/hey_output.txt

# Check results
SUCCESSFUL=$(grep -oP '\[200\]\s+\K\d+' /tmp/hey_output.txt || echo 0)
OVERLOADED=$(grep -oP '\[503\]\s+\K\d+' /tmp/hey_output.txt || echo 0)
STREAM_ERRORS=$(grep -c 'INTERNAL_ERROR' /tmp/hey_output.txt || echo 0)

echo "Results:"
echo "  200 OK: $SUCCESSFUL"
echo "  503 Overloaded: $OVERLOADED"
echo "  Stream errors: $STREAM_ERRORS"

# Cleanup
kill $SERVER_PID 2>/dev/null || true

# Assert no stream errors (should all be 200 or 503)
if [ "$STREAM_ERRORS" -gt 0 ]; then
  echo "FAIL: Got $STREAM_ERRORS stream errors (should be 0)"
  exit 1
fi

echo "PASS: All overload cases returned proper 503"
```

## Implementation Order

1. **Slab instrumentation** (`src/memory.c`, `src/memory.h`)
   - Add `overflowCount` field (skip `numAcquired` - redundant)
   - Update `valk_slab_init` and `valk_slab_aquire`
   - Use `__atomic_fetch_add` for consistency with existing code

2. **Add plist helper** (`src/parser.c`)
   - Implement `valk_plist_get()` for config parsing

3. **Add config structs** (`src/aio.h`)
   - Define `valk_aio_system_config_t`
   - Define `valk_http_server_config_t`

4. **Embed default 503 HTML** (`src/aio_uv.c`)
   - Add static HTML string

5. **Implement 503 response path** (`src/aio_uv.c`)
   - Add thread-local `__overload_body_src`
   - Add `__http_send_overload_response()` using `nghttp2_data_provider2`
   - Modify `__http_on_begin_headers_callback()` to call it

6. **Add metrics** (`src/aio_uv.c`, `src/aio_metrics.h`)
   - Add `overload_responses` to `valk_server_metrics_t`
   - Add `arena_pool_overflow` to `valk_aio_system_stats_t`
   - Register in `server_metrics_init()`

7. **Update Lisp APIs** (`src/parser.c`)
   - Extend `aio/new` to accept config map
   - Extend `http2/server-listen` to accept config map
   - Wire config through to C layer

8. **Update server/system structs** (`src/aio_uv.c`)
   - Add config to `valk_aio_http_server`
   - Pass system config to pool initialization

9. **Tests**
   - Add all test files listed above
   - Verify with `make test`

## Key Corrections from Review

The following issues were identified and corrected during review:

1. **Split configuration API**: Pool sizing moved to `aio/new` (system-wide), server behavior stays on `http2/server-listen`

2. **`valk_map_get()` doesn't exist**: Added `valk_plist_get()` helper for property list parsing

3. **Wrong nghttp2 API**: Changed from deprecated `nghttp2_data_provider`/`nghttp2_submit_response` to `nghttp2_data_provider2`/`nghttp2_submit_response2`

4. **Header lifetime issue**: Removed `content-length` header (optional in HTTP/2) to avoid stack buffer lifetime issues

5. **Metric naming**: Changed `valk_http_*` to `http_*` to match existing conventions

6. **Atomic syntax**: Changed `_Atomic` to `__atomic_*` intrinsics for consistency

7. **Thread-local body source**: Use `_Thread_local` static for 503 body source (event loop is single-threaded)

8. **Removed redundant `numAcquired`**: It equals `numItems - numFree`, so only `overflowCount` is added

9. **Pre-rendered error handler**: Error handler is called once at startup (not during overload) to avoid memory allocation when arenas are exhausted. Handler signature simplified to `(lambda {status-code} ...)` - no request parameter since it's pre-rendered

## References

- [Envoy Circuit Breaking](https://www.envoyproxy.io/docs/envoy/latest/intro/arch_overview/upstream/circuit_breaking)
- [nginx backlog tuning](https://www.getpagespeed.com/server-setup/nginx/maximizing-nginx-performance-a-comprehensive-guide-to-tuning-the-backlog-and-net-core-somaxconn-parameters)
- Current implementation: `src/aio_uv.c:545-551`
