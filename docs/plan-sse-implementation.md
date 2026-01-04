# SSE Implementation Plan: Exposing Server-Sent Events to Lisp

## Executive Summary

This document outlines a plan to properly implement Server-Sent Events (SSE) throughout the Valkyria stack, from the C async I/O layer through to Lisp builtins. The current implementation is specialized for memory diagnostics and lacks a general-purpose API. This plan addresses that limitation.

---

## Current State Analysis

### Existing Architecture

The current SSE implementation (`src/aio_sse_diagnostics.c:1-1829`) is tightly coupled to memory diagnostics:

```
┌─────────────────────────────────────────────────────────────────┐
│                    Current SSE Architecture                      │
├─────────────────────────────────────────────────────────────────┤
│  Lisp Layer (debug.valk:60)                                     │
│    └─ Returns: {:body-type :sse-stream :sse-handler :memory-diagnostics}
│                                                                 │
│  Response Handler (aio_uv.c:1190-1235)                         │
│    └─ Hardcoded check for :body-type :sse-stream               │
│    └─ Creates valk_sse_diag_conn_t via valk_sse_diag_init_http2│
│                                                                 │
│  Timer Loop (aio_sse_diagnostics.c:1526-1562)                  │
│    └─ 100ms interval, pushes memory snapshots                   │
│    └─ Uses valk_diag_snapshot_to_sse() for full events         │
│    └─ Uses valk_diag_delta_to_sse() for incremental updates    │
│                                                                 │
│  nghttp2 Data Provider (aio_sse_diagnostics.c:1565-1598)       │
│    └─ Callback reads from pending_data buffer                   │
│    └─ Returns NGHTTP2_ERR_DEFERRED when no data available      │
└─────────────────────────────────────────────────────────────────┘
```

### Limitations

1. **No Lisp API**: Cannot create SSE streams from Lisp code
2. **Hardcoded Content**: Only supports memory diagnostics data
3. **Fixed Timer**: 100ms interval, not configurable per-stream
4. **No Custom Events**: Cannot send arbitrary event types/data
5. **No Backpressure API**: Cannot detect when client is slow

---

## Proposed Architecture

### Layer 1: Core SSE Stream Abstraction (C)

Create a general-purpose SSE stream type that separates the transport from the content:

**File**: `src/aio_sse.h` (NEW)

```c
// Line 1-80 (new file)
#ifndef VALK_AIO_SSE_H
#define VALK_AIO_SSE_H

#include "aio.h"
#include <nghttp2/nghttp2.h>
#include <stdbool.h>
#include <stdint.h>

// Forward declarations
typedef struct valk_sse_stream valk_sse_stream_t;
typedef struct valk_sse_event valk_sse_event_t;

// SSE stream state
typedef enum {
  VALK_SSE_INIT,
  VALK_SSE_OPEN,
  VALK_SSE_CLOSING,
  VALK_SSE_CLOSED,
} valk_sse_state_e;

// SSE event structure (for queueing)
struct valk_sse_event {
  valk_sse_event_t *next;
  char *event_type;       // NULL for default "message" event
  char *data;             // Event data (JSON, text, etc.)
  size_t data_len;
  uint64_t id;            // Optional event ID for resumption
  uint32_t retry_ms;      // Optional retry hint (0 = not set)
};

// SSE stream context
struct valk_sse_stream {
  // Identity
  uint64_t id;
  valk_sse_state_e state;

  // HTTP/2 context
  valk_aio_handle_t *conn;
  nghttp2_session *session;
  int32_t stream_id;

  // Event queue (producer-consumer)
  valk_sse_event_t *queue_head;
  valk_sse_event_t *queue_tail;
  size_t queue_len;
  size_t queue_max;           // Backpressure threshold

  // Pending write buffer
  char *pending_data;
  size_t pending_len;
  size_t pending_offset;
  size_t pending_capacity;

  // State tracking
  bool data_deferred;
  uint64_t last_event_id;
  uint64_t events_sent;
  uint64_t bytes_sent;

  // Callbacks (optional, for C-level hooks)
  void (*on_drain)(valk_sse_stream_t *stream, void *user_data);
  void (*on_close)(valk_sse_stream_t *stream, void *user_data);
  void *user_data;

  // Lisp callbacks (stored as heap-allocated lvals)
  struct valk_lval_t *lisp_on_drain;
  struct valk_lval_t *lisp_on_close;
  struct valk_lenv_t *callback_env;
};

// Stream lifecycle
valk_sse_stream_t *valk_sse_stream_new(
    valk_aio_handle_t *conn,
    nghttp2_session *session,
    int32_t stream_id,
    nghttp2_data_provider2 *data_prd_out);

void valk_sse_stream_close(valk_sse_stream_t *stream);

// Event sending
int valk_sse_send(valk_sse_stream_t *stream, const char *data, size_t len);
int valk_sse_send_event(valk_sse_stream_t *stream, const char *event_type,
                        const char *data, size_t len, uint64_t id);
int valk_sse_send_retry(valk_sse_stream_t *stream, uint32_t retry_ms);

// Backpressure
bool valk_sse_is_writable(valk_sse_stream_t *stream);
size_t valk_sse_queue_len(valk_sse_stream_t *stream);

#endif // VALK_AIO_SSE_H
```

### Layer 2: SSE Stream Implementation (C)

**File**: `src/aio_sse.c` (NEW)

```c
// Key functions with line numbers

// valk_sse_stream_new (lines 50-120)
// Creates stream context, sets up nghttp2 data provider
valk_sse_stream_t *valk_sse_stream_new(
    valk_aio_handle_t *conn,
    nghttp2_session *session,
    int32_t stream_id,
    nghttp2_data_provider2 *data_prd_out) {

  valk_sse_stream_t *stream = malloc(sizeof(valk_sse_stream_t));
  if (!stream) return NULL;

  memset(stream, 0, sizeof(*stream));
  stream->id = __atomic_fetch_add(&g_sse_stream_id, 1, __ATOMIC_RELAXED);
  stream->state = VALK_SSE_OPEN;
  stream->conn = conn;
  stream->session = session;
  stream->stream_id = stream_id;
  stream->queue_max = 1000;  // Default backpressure threshold
  stream->pending_capacity = 65536;  // 64KB initial buffer
  stream->pending_data = malloc(stream->pending_capacity);
  stream->data_deferred = true;  // Start deferred

  // Set up nghttp2 data provider
  data_prd_out->source.ptr = stream;
  data_prd_out->read_callback = __sse_data_read_callback;

  return stream;
}

// valk_sse_send_event (lines 150-220)
// Formats and queues an SSE event
int valk_sse_send_event(valk_sse_stream_t *stream, const char *event_type,
                        const char *data, size_t len, uint64_t id) {
  if (!stream || stream->state != VALK_SSE_OPEN) {
    return -1;
  }

  // Check backpressure
  if (stream->queue_len >= stream->queue_max) {
    return -2;  // EAGAIN - queue full
  }

  // Calculate event size
  size_t event_size = 0;
  if (id > 0) event_size += snprintf(NULL, 0, "id: %lu\n", id);
  if (event_type) event_size += snprintf(NULL, 0, "event: %s\n", event_type);
  event_size += 6;  // "data: "
  event_size += len;
  event_size += 2;  // "\n\n"

  // Allocate event
  valk_sse_event_t *event = malloc(sizeof(valk_sse_event_t) + event_size + 1);
  if (!event) return -3;

  // Format event into buffer
  char *buf = (char *)(event + 1);
  char *p = buf;
  if (id > 0) p += sprintf(p, "id: %lu\n", id);
  if (event_type) p += sprintf(p, "event: %s\n", event_type);
  p += sprintf(p, "data: ");
  memcpy(p, data, len);
  p += len;
  *p++ = '\n';
  *p++ = '\n';
  *p = '\0';

  event->data = buf;
  event->data_len = p - buf;
  event->next = NULL;

  // Enqueue
  if (stream->queue_tail) {
    stream->queue_tail->next = event;
  } else {
    stream->queue_head = event;
  }
  stream->queue_tail = event;
  stream->queue_len++;

  // Resume if deferred
  if (stream->data_deferred) {
    stream->data_deferred = false;
    nghttp2_session_resume_data(stream->session, stream->stream_id);
    valk_http2_flush_pending(stream->conn);
  }

  return 0;
}

// __sse_data_read_callback (lines 250-300)
// nghttp2 data provider callback
static nghttp2_ssize __sse_data_read_callback(
    nghttp2_session *session, int32_t stream_id,
    uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data) {

  valk_sse_stream_t *stream = source->ptr;

  if (!stream || stream->state == VALK_SSE_CLOSED) {
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  // Flush pending buffer first
  if (stream->pending_offset < stream->pending_len) {
    size_t remaining = stream->pending_len - stream->pending_offset;
    size_t to_send = remaining < length ? remaining : length;
    memcpy(buf, stream->pending_data + stream->pending_offset, to_send);
    stream->pending_offset += to_send;
    return (nghttp2_ssize)to_send;
  }

  // Check queue for next event
  if (!stream->queue_head) {
    stream->data_deferred = true;
    return NGHTTP2_ERR_DEFERRED;
  }

  // Dequeue and copy to pending buffer
  valk_sse_event_t *event = stream->queue_head;
  stream->queue_head = event->next;
  if (!stream->queue_head) stream->queue_tail = NULL;
  stream->queue_len--;

  // Ensure buffer capacity
  if (event->data_len > stream->pending_capacity) {
    stream->pending_data = realloc(stream->pending_data, event->data_len);
    stream->pending_capacity = event->data_len;
  }

  memcpy(stream->pending_data, event->data, event->data_len);
  stream->pending_len = event->data_len;
  stream->pending_offset = 0;
  stream->events_sent++;
  stream->bytes_sent += event->data_len;

  free(event);

  // Send from pending buffer
  size_t to_send = stream->pending_len < length ? stream->pending_len : length;
  memcpy(buf, stream->pending_data, to_send);
  stream->pending_offset = to_send;

  // Call drain callback if queue was full
  if (stream->queue_len < stream->queue_max / 2 && stream->on_drain) {
    stream->on_drain(stream, stream->user_data);
  }

  return (nghttp2_ssize)to_send;
}
```

### Layer 3: Lisp Builtins (C)

**File**: `src/aio_sse_builtins.c` (NEW)

```c
// Line 1-50: Includes and helpers
#include "aio_sse.h"
#include "parser.h"
#include "aio_uv.c"  // For current_request_ctx

// Helper: Extract SSE stream from LVAL_REF
static valk_sse_stream_t *get_sse_stream(valk_lval_t *ref) {
  if (LVAL_TYPE(ref) != LVAL_REF) return NULL;
  if (strcmp(ref->ref.type, "sse_stream") != 0) return NULL;
  return (valk_sse_stream_t *)ref->ref.ptr;
}

// Cleanup function for ref
static void sse_stream_cleanup(void *ptr) {
  valk_sse_stream_t *stream = ptr;
  valk_sse_stream_close(stream);
}

// ===== BUILTIN: sse/open (lines 60-130) =====
// Usage: (sse/open) -> stream-handle
// Must be called within HTTP request handler context
static valk_lval_t *valk_builtin_sse_open(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  // Validate no arguments
  if (valk_lval_list_count(a) != 0) {
    return valk_lval_err("sse/open expects no arguments");
  }

  // Must be in HTTP request context
  if (!current_request_ctx) {
    return valk_lval_err("sse/open must be called within HTTP request handler");
  }

  nghttp2_session *session = current_request_ctx->session;
  int32_t stream_id = current_request_ctx->stream_id;
  valk_aio_handle_t *conn = current_request_ctx->conn;

  // Create SSE stream
  nghttp2_data_provider2 data_prd;
  valk_sse_stream_t *stream = valk_sse_stream_new(conn, session, stream_id, &data_prd);
  if (!stream) {
    return valk_lval_err("Failed to create SSE stream");
  }

  // Submit HTTP/2 response headers
  nghttp2_nv headers[] = {
    MAKE_NV2(":status", "200"),
    MAKE_NV2("content-type", "text/event-stream"),
    MAKE_NV2("cache-control", "no-cache"),
    MAKE_NV2("connection", "keep-alive"),
  };

  int rv = nghttp2_submit_response2(session, stream_id, headers, 4, &data_prd);
  if (rv != 0) {
    valk_sse_stream_close(stream);
    return valk_lval_err("Failed to submit SSE response: %s", nghttp2_strerror(rv));
  }

  // Return handle as LVAL_REF
  return valk_lval_ref("sse_stream", stream, sse_stream_cleanup);
}

// ===== BUILTIN: sse/send (lines 140-190) =====
// Usage: (sse/send stream data) -> bytes-sent or error
// Usage: (sse/send stream event-type data) -> bytes-sent or error
static valk_lval_t *valk_builtin_sse_send(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  size_t argc = valk_lval_list_count(a);
  if (argc < 2 || argc > 3) {
    return valk_lval_err("sse/send expects 2-3 arguments (stream data) or (stream event-type data)");
  }

  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/send: first argument must be SSE stream handle");
  }

  const char *event_type = NULL;
  const char *data;
  size_t data_len;

  if (argc == 3) {
    // (sse/send stream event-type data)
    valk_lval_t *event_arg = valk_lval_list_nth(a, 1);
    valk_lval_t *data_arg = valk_lval_list_nth(a, 2);
    LVAL_ASSERT_TYPE(a, event_arg, LVAL_STR);
    LVAL_ASSERT_TYPE(a, data_arg, LVAL_STR);
    event_type = event_arg->str;
    data = data_arg->str;
    data_len = strlen(data);
  } else {
    // (sse/send stream data)
    valk_lval_t *data_arg = valk_lval_list_nth(a, 1);
    LVAL_ASSERT_TYPE(a, data_arg, LVAL_STR);
    data = data_arg->str;
    data_len = strlen(data);
  }

  int rv = valk_sse_send_event(stream, event_type, data, data_len, 0);
  if (rv == -2) {
    return valk_lval_err("sse/send: queue full (backpressure)");
  } else if (rv < 0) {
    return valk_lval_err("sse/send: failed with code %d", rv);
  }

  return valk_lval_num((long)data_len);
}

// ===== BUILTIN: sse/close (lines 200-230) =====
// Usage: (sse/close stream) -> nil
static valk_lval_t *valk_builtin_sse_close(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  valk_sse_stream_t *stream = get_sse_stream(stream_ref);

  if (!stream) {
    return valk_lval_err("sse/close: argument must be SSE stream handle");
  }

  valk_sse_stream_close(stream);
  return valk_lval_nil();
}

// ===== BUILTIN: sse/writable? (lines 240-260) =====
// Usage: (sse/writable? stream) -> true/false
static valk_lval_t *valk_builtin_sse_writable(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  valk_sse_stream_t *stream = get_sse_stream(stream_ref);

  if (!stream) {
    return valk_lval_err("sse/writable?: argument must be SSE stream handle");
  }

  return valk_sse_is_writable(stream) ? valk_lval_sym("true") : valk_lval_sym("false");
}

// ===== BUILTIN: sse/on-drain (lines 270-310) =====
// Usage: (sse/on-drain stream callback) -> stream
// Callback called when queue drains below threshold
static valk_lval_t *valk_builtin_sse_on_drain(valk_lenv_t *e, valk_lval_t *a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t *stream_ref = valk_lval_list_nth(a, 0);
  valk_lval_t *callback = valk_lval_list_nth(a, 1);

  valk_sse_stream_t *stream = get_sse_stream(stream_ref);
  if (!stream) {
    return valk_lval_err("sse/on-drain: first argument must be SSE stream handle");
  }
  LVAL_ASSERT_TYPE(a, callback, LVAL_FUN);

  // Copy callback to heap for persistence
  VALK_WITH_ALLOC((valk_mem_allocator_t*)valk_thread_ctx.heap) {
    stream->lisp_on_drain = valk_lval_copy(callback);
  }
  stream->callback_env = e;

  return stream_ref;
}

// ===== Registration (lines 320-340) =====
void valk_register_sse_builtins(valk_lenv_t *env) {
  valk_lenv_put_builtin(env, "sse/open", valk_builtin_sse_open);
  valk_lenv_put_builtin(env, "sse/send", valk_builtin_sse_send);
  valk_lenv_put_builtin(env, "sse/close", valk_builtin_sse_close);
  valk_lenv_put_builtin(env, "sse/writable?", valk_builtin_sse_writable);
  valk_lenv_put_builtin(env, "sse/on-drain", valk_builtin_sse_on_drain);
  valk_lenv_put_builtin(env, "sse/on-close", valk_builtin_sse_on_close);
}
```

### Layer 4: Lisp Module

**File**: `src/modules/aio/sse.valk` (NEW)

```lisp
; SSE Module - High-level SSE stream utilities
; Line 1-80

; Create an SSE stream and return it
; Usage: (sse/create) within HTTP handler
(def {sse/create} sse/open)

; Send a message event (default event type)
; Usage: (sse/message stream "hello world")
(fun {sse/message stream data}
  {sse/send stream data})

; Send a named event
; Usage: (sse/event stream "update" "{\"count\": 42}")
(fun {sse/event stream event-type data}
  {sse/send stream event-type data})

; Send JSON data as a message
; Usage: (sse/json stream {:count 42})
(fun {sse/json stream data}
  {sse/send stream (json/encode data)})

; Send JSON data with event type
; Usage: (sse/json-event stream "update" {:count 42})
(fun {sse/json-event stream event-type data}
  {sse/send stream event-type (json/encode data)})

; Create an SSE endpoint handler
; Usage: (def {handler} (sse/handler (fn {stream req} ...)))
(fun {sse/handler body-fn}
  {fn {req}
    {
      (= {stream} (sse/open))
      (body-fn stream req)
      ; Return deferred - stream stays open
      :deferred
    }})

; Periodic SSE sender with interval
; Usage: (sse/interval stream 1000 (fn {} "tick"))
(fun {sse/interval stream interval-ms data-fn}
  {
    (= {send-tick} (fn {}
      {if (sse/writable? stream)
        {sse/send stream (data-fn)}}))
    ; Use aio/delay for timing
    (aio/loop interval-ms send-tick)
  })
```

---

## Task Breakdown

### Phase 1: Core Infrastructure (3 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 1.1 | Create `valk_sse_stream_t` structure and header | `src/aio_sse.h` | ~80 |
| 1.2 | Implement stream lifecycle (new, close) | `src/aio_sse.c` | ~150 |
| 1.3 | Implement event queue and data provider | `src/aio_sse.c` | ~200 |

### Phase 2: Lisp Bindings (4 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 2.1 | Implement `sse/open` builtin | `src/aio_sse_builtins.c` | ~70 |
| 2.2 | Implement `sse/send` builtin | `src/aio_sse_builtins.c` | ~60 |
| 2.3 | Implement `sse/close`, `sse/writable?` | `src/aio_sse_builtins.c` | ~50 |
| 2.4 | Register builtins in `valk_lenv_builtins()` | `src/parser.c:4182` | ~10 |

### Phase 3: Lisp Module (2 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 3.1 | Create high-level Lisp wrappers | `src/modules/aio/sse.valk` | ~80 |
| 3.2 | Add `sse/handler` macro for endpoint creation | `src/modules/aio/sse.valk` | ~20 |

### Phase 4: Integration (3 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 4.1 | Modify response handler for SSE streams | `src/aio_uv.c:1190-1235` | ~30 |
| 4.2 | Add SSE stream tracking to connection cleanup | `src/aio_uv.c:750-757` | ~20 |
| 4.3 | Integrate with existing diagnostics (optional) | `src/aio_sse_diagnostics.c` | ~50 |

### Phase 5: Testing (2 tasks)

| # | Task | Files | Lines |
|---|------|-------|-------|
| 5.1 | Unit tests for C layer | `test/test_sse.c` | ~200 |
| 5.2 | Integration tests for Lisp | `test/test_sse.valk` | ~100 |

---

## Migration Path for Existing Code

The existing diagnostics SSE (`aio_sse_diagnostics.c`) can be refactored to use the new generic SSE layer:

**Before** (current, `aio_sse_diagnostics.c:1416-1522`):
```c
static bool sse_push_to_stream(valk_sse_diag_conn_t *stream, ...) {
  // Custom formatting logic
  len = valk_diag_snapshot_to_sse(snapshot, ...);
  // Custom buffer management
  stream->pending_data = ...;
  // Custom resume logic
  nghttp2_session_resume_data(...);
}
```

**After** (using new abstraction):
```c
static bool sse_push_to_stream(valk_sse_stream_t *stream, ...) {
  // Format data
  char buf[SSE_BUFFER_SIZE];
  int len = valk_diag_snapshot_to_sse(snapshot, buf, sizeof(buf), event_id);

  // Use generic SSE API
  valk_sse_send_event(stream, "diagnostics", buf, len, event_id);
}
```

---

## Example Usage

### Basic SSE Endpoint

```lisp
; HTTP handler that streams events
(fun {my-sse-handler req}
  {
    (= {stream} (sse/open))

    ; Send initial message
    (sse/send stream "connected")

    ; Send periodic updates
    (sse/interval stream 1000 (fn {}
      (json/encode {:time (time/now) :data "tick"})))

    ; Return deferred to keep stream open
    :deferred
  })

; Register route
(http2/server-listen sys 8080 (fn {req}
  {match (get req :path)
    "/events" (my-sse-handler req)
    _ {:status "404" :body "Not Found"}}))
```

### With Backpressure Handling

```lisp
(fun {high-volume-sse req}
  {
    (= {stream} (sse/open))

    ; Set up drain callback for slow clients
    (sse/on-drain stream (fn {}
      (println "Client caught up, resuming")))

    ; Producer loop
    (= {send-data} (fn {}
      {if (sse/writable? stream)
        {sse/json-event stream "data" {:seq (random 1000)}}
        {println "Backpressure - waiting for drain"}}))

    (aio/loop 10 send-data)  ; Try to send every 10ms
    :deferred
  })
```

---

## Memory Management Considerations

1. **Stream Lifetime**: SSE streams live as long as the HTTP/2 stream is open
2. **Event Queue**: Events are heap-allocated and freed after transmission
3. **Lisp Callbacks**: Copied to GC heap for persistence, freed on stream close
4. **Buffer Growth**: Pending buffer grows dynamically, freed on close

---

## Metrics to Add

Extend `valk_aio_metrics_t` (`src/aio_metrics.h:18-44`):

```c
// SSE-specific metrics
_Atomic uint64_t sse_streams_total;
_Atomic uint64_t sse_streams_active;
_Atomic uint64_t sse_events_sent;
_Atomic uint64_t sse_bytes_sent;
_Atomic uint64_t sse_backpressure_events;  // Times queue hit limit
```

---

## Dependencies

- **nghttp2**: Already integrated (`src/aio_uv.c:10`)
- **libuv**: Already integrated (`src/aio_uv.c:23`)
- **Memory allocator**: Use existing slab/arena patterns

---

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Memory leak on stream close | Use cleanup function in LVAL_REF |
| Race condition on callback | Run callbacks in event loop thread |
| Buffer overflow | Dynamic buffer with capacity tracking |
| Slow client DoS | Backpressure threshold + timeout |

---

## Success Criteria

1. Can create SSE stream from Lisp: `(sse/open)`
2. Can send events: `(sse/send stream "data")`
3. Backpressure works: queue full returns error
4. Clean shutdown: stream closes when HTTP stream ends
5. Diagnostics migrated: existing dashboard uses new API
