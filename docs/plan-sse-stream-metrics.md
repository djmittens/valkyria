# Implementation Plan: SSE Stream Tracking with Global Timer and Fresh State Endpoint

## Overview

This plan implements a refactored SSE architecture with:
1. **Per-stream tracking** (not per-connection) for SSE metrics updates
2. **Global timer per event loop** that iterates over a subscription list of streams
3. **New `/debug/metrics/state` endpoint** for fresh initial state before SSE updates

## Current Architecture Analysis

### Existing SSE Diagnostics (`aio_sse_diagnostics.c`)
- **Per-connection timer**: Each HTTP connection with SSE streams gets its own timer (`valk_sse_diag_state_t.timer_handle`)
- **Stream linked list**: Multiple streams per connection via `valk_sse_diag_conn_t *streams`
- **Timer fires at 100ms**: Collects snapshot once, pushes to all streams on that connection
- **Delta tracking**: Per-stream baseline for metrics (`valk_metrics_baseline_t`)

### Problem with Current Approach
- Timer is per-connection, not global
- If multiple browser tabs connect, each gets its own timer (wasteful)
- No central registry of all SSE streams across all connections
- No way to get fresh state without opening SSE connection

---

## Implementation Plan

### Phase 1: Global SSE Stream Registry

**File: `src/aio_sse_stream_registry.h` (NEW)**

```c
#ifndef VALK_AIO_SSE_STREAM_REGISTRY_H
#define VALK_AIO_SSE_STREAM_REGISTRY_H

#include "aio.h"
#include "aio_sse_diagnostics.h"
#include <stdint.h>
#include <stdbool.h>

// Forward declarations
typedef struct valk_sse_stream_entry valk_sse_stream_entry_t;
typedef struct valk_sse_stream_registry valk_sse_stream_registry_t;

// Stream subscription types
typedef enum {
  VALK_SSE_SUB_DIAGNOSTICS,    // Memory + metrics combined
  VALK_SSE_SUB_METRICS_ONLY,   // Metrics only (modular)
  VALK_SSE_SUB_MEMORY_ONLY,    // Memory snapshots only
} valk_sse_subscription_type_e;

// Registry entry for a single SSE stream
struct valk_sse_stream_entry {
  valk_sse_stream_entry_t *next;      // Linked list
  valk_sse_stream_entry_t *prev;      // Doubly-linked for O(1) removal

  // Stream identity
  uint64_t stream_id;                 // Unique ID within registry
  valk_sse_subscription_type_e type;  // What to push

  // HTTP/2 context
  valk_aio_handle_t *handle;          // Connection handle
  nghttp2_session *session;           // HTTP/2 session
  int32_t http2_stream_id;            // HTTP/2 stream ID

  // State tracking
  bool active;                        // Stream still open
  bool first_event_sent;              // Full state sent?
  uint64_t last_event_id;             // For resumption

  // Delta tracking (per-stream baseline)
  valk_mem_snapshot_t prev_snapshot;  // Memory snapshot for delta
  valk_metrics_baseline_t *metrics_baseline;  // Metrics baseline

  // Pending write buffer
  char *pending_data;
  size_t pending_len;
  size_t pending_offset;
  bool data_deferred;

  // Previous AIO metrics for delta
  struct {
    uint64_t bytes_sent;
    uint64_t bytes_recv;
    uint64_t requests_total;
    uint64_t connections_total;
  } prev_aio_metrics;
};

// Global registry for all SSE streams
struct valk_sse_stream_registry {
  valk_sse_stream_entry_t *streams;   // Doubly-linked list head
  size_t stream_count;                // Number of active streams

  // Global timer (one per event loop)
  valk_aio_handle_t *timer_handle;
  bool timer_running;
  uint64_t timer_interval_ms;         // Default: 100ms

  // Shared state (collected once per tick)
  valk_mem_snapshot_t current_snapshot;
  valk_delta_snapshot_t modular_delta;
  bool modular_delta_initialized;
  valk_metrics_baseline_t global_baseline;  // For modular metrics

  // Back-reference to AIO system
  valk_aio_system_t *aio_system;

  // Statistics
  uint64_t events_pushed_total;
  uint64_t bytes_pushed_total;
};

// ============================================================================
// Registry Lifecycle
// ============================================================================

// Initialize global registry (called once at AIO system startup)
void valk_sse_registry_init(valk_sse_stream_registry_t *registry,
                            valk_aio_system_t *aio);

// Shutdown registry (stops timer, closes all streams)
void valk_sse_registry_shutdown(valk_sse_stream_registry_t *registry);

// ============================================================================
// Stream Management
// ============================================================================

// Subscribe a new SSE stream to updates
// Returns stream entry (owned by registry) or NULL on failure
valk_sse_stream_entry_t* valk_sse_registry_subscribe(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    nghttp2_session *session,
    int32_t stream_id,
    valk_sse_subscription_type_e type,
    nghttp2_data_provider2 *data_prd_out);

// Unsubscribe a stream (called on stream close)
void valk_sse_registry_unsubscribe(valk_sse_stream_registry_t *registry,
                                    valk_sse_stream_entry_t *entry);

// Unsubscribe all streams on a connection (called on connection close)
void valk_sse_registry_unsubscribe_connection(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle);

// ============================================================================
// Timer Control
// ============================================================================

// Start global timer (idempotent - only starts if not running)
void valk_sse_registry_timer_start(valk_sse_stream_registry_t *registry);

// Stop global timer (stops if no streams remain)
void valk_sse_registry_timer_stop(valk_sse_stream_registry_t *registry);

// ============================================================================
// Query API
// ============================================================================

// Get current stream count
size_t valk_sse_registry_stream_count(valk_sse_stream_registry_t *registry);

// Get registry statistics as JSON
size_t valk_sse_registry_stats_json(valk_sse_stream_registry_t *registry,
                                     char *buf, size_t buf_size);

#endif // VALK_AIO_SSE_STREAM_REGISTRY_H
```

**Line count estimate: ~100 lines**

---

### Phase 2: Registry Implementation

**File: `src/aio_sse_stream_registry.c` (NEW)**

Key functions to implement:

```c
// Line ~20-60: Registry initialization
void valk_sse_registry_init(valk_sse_stream_registry_t *registry,
                            valk_aio_system_t *aio) {
  memset(registry, 0, sizeof(*registry));
  registry->aio_system = aio;
  registry->timer_interval_ms = 100;  // 100ms = 10 Hz

  // Allocate timer handle from slab
  registry->timer_handle = valk_aio_timer_alloc(aio);
  if (registry->timer_handle) {
    valk_aio_timer_init(registry->timer_handle);
    valk_aio_timer_set_data(registry->timer_handle, registry);
  }

  // Initialize modular delta snapshot
  valk_delta_snapshot_init(&registry->modular_delta);
  registry->modular_delta_initialized = true;
  valk_metrics_baseline_init(&registry->global_baseline);
}

// Line ~62-150: Global timer callback
static void sse_registry_timer_cb(uv_timer_t *timer) {
  valk_sse_stream_registry_t *registry = timer->data;

  if (!registry || !registry->streams) {
    // No streams, stop timer
    valk_sse_registry_timer_stop(registry);
    return;
  }

  // 1. Collect memory snapshot ONCE
  valk_mem_snapshot_collect(&registry->current_snapshot, registry->aio_system);

  // 2. Collect modular metrics delta ONCE
  size_t modular_changes = valk_delta_snapshot_collect_stateless(
      &registry->modular_delta, &g_metrics, &registry->global_baseline);

  // 3. Iterate all streams and push updates
  valk_sse_stream_entry_t *entry = registry->streams;
  while (entry) {
    valk_sse_stream_entry_t *next = entry->next;  // Save next before potential removal

    if (!entry->active) {
      // Stream closed, remove from list
      valk_sse_registry_unsubscribe(registry, entry);
    } else {
      // Push update to this stream
      sse_push_to_stream_entry(registry, entry, modular_changes > 0);
    }

    entry = next;
  }

  // 4. Free snapshot allocations
  valk_mem_snapshot_free(&registry->current_snapshot);
}

// Line ~152-280: Subscribe new stream
valk_sse_stream_entry_t* valk_sse_registry_subscribe(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle,
    nghttp2_session *session,
    int32_t stream_id,
    valk_sse_subscription_type_e type,
    nghttp2_data_provider2 *data_prd_out) {

  // Allocate entry
  valk_sse_stream_entry_t *entry = calloc(1, sizeof(valk_sse_stream_entry_t));
  if (!entry) return NULL;

  // Initialize
  static uint64_t next_id = 0;
  entry->stream_id = __atomic_fetch_add(&next_id, 1, __ATOMIC_RELAXED);
  entry->type = type;
  entry->handle = handle;
  entry->session = session;
  entry->http2_stream_id = stream_id;
  entry->active = true;
  entry->first_event_sent = false;
  entry->data_deferred = true;  // Start deferred

  // Allocate metrics baseline if needed
  if (type == VALK_SSE_SUB_DIAGNOSTICS || type == VALK_SSE_SUB_METRICS_ONLY) {
    entry->metrics_baseline = malloc(sizeof(valk_metrics_baseline_t));
    if (entry->metrics_baseline) {
      valk_metrics_baseline_init(entry->metrics_baseline);
    }
  }

  // Add to doubly-linked list (prepend)
  entry->prev = NULL;
  entry->next = registry->streams;
  if (registry->streams) {
    registry->streams->prev = entry;
  }
  registry->streams = entry;
  registry->stream_count++;

  // Set up nghttp2 data provider
  data_prd_out->source.ptr = entry;
  data_prd_out->read_callback = sse_registry_data_read_callback;

  // Start timer if this is first stream
  if (registry->stream_count == 1) {
    valk_sse_registry_timer_start(registry);
  }

  VALK_INFO("SSE Registry: subscribed stream %lu (type=%d), total=%zu",
            entry->stream_id, type, registry->stream_count);

  return entry;
}

// Line ~282-340: Unsubscribe stream
void valk_sse_registry_unsubscribe(valk_sse_stream_registry_t *registry,
                                    valk_sse_stream_entry_t *entry) {
  if (!entry) return;

  // Remove from doubly-linked list
  if (entry->prev) {
    entry->prev->next = entry->next;
  } else {
    registry->streams = entry->next;
  }
  if (entry->next) {
    entry->next->prev = entry->prev;
  }
  registry->stream_count--;

  // Free resources
  free(entry->pending_data);
  free(entry->metrics_baseline);
  valk_mem_snapshot_free(&entry->prev_snapshot);
  free(entry);

  // Stop timer if no more streams
  if (registry->stream_count == 0) {
    valk_sse_registry_timer_stop(registry);
  }

  VALK_INFO("SSE Registry: unsubscribed stream, remaining=%zu",
            registry->stream_count);
}

// Line ~342-400: nghttp2 data provider callback
static nghttp2_ssize sse_registry_data_read_callback(
    nghttp2_session *session, int32_t stream_id, uint8_t *buf, size_t length,
    uint32_t *data_flags, nghttp2_data_source *source, void *user_data) {

  valk_sse_stream_entry_t *entry = source->ptr;

  if (!entry || !entry->active) {
    *data_flags |= NGHTTP2_DATA_FLAG_EOF;
    return 0;
  }

  // No data available - defer
  if (!entry->pending_data || entry->pending_offset >= entry->pending_len) {
    entry->data_deferred = true;
    return NGHTTP2_ERR_DEFERRED;
  }

  // Copy data to buffer
  size_t remaining = entry->pending_len - entry->pending_offset;
  size_t to_send = remaining < length ? remaining : length;
  memcpy(buf, entry->pending_data + entry->pending_offset, to_send);
  entry->pending_offset += to_send;

  return (nghttp2_ssize)to_send;
}
```

**Line count estimate: ~400 lines**

---

### Phase 3: Fresh State Endpoint

**File: `src/aio_sse_diagnostics.c` (MODIFY)**

Add new function for one-shot fresh state:

```c
// Line ~1920+ (NEW): Get fresh diagnostics state as JSON
// Called by /debug/metrics/state endpoint
int valk_diag_fresh_state_json(valk_aio_system_t *aio, char *buf, size_t buf_size) {
  char *p = buf;
  char *end = buf + buf_size;
  int n;

  // Start JSON object
  n = snprintf(p, end - p, "{");
  if (n < 0 || n >= end - p) return -1;
  p += n;

  // ===== Memory Section =====
  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, aio);

  n = snprintf(p, end - p, "\"memory\":{");
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // Slabs array (full state, not RLE for readability)
  n = snprintf(p, end - p, "\"slabs\":[");
  // ... encode each slab with full states ...

  // Arenas array
  // ... encode arenas ...

  // GC stats
  // ... encode gc ...

  // Owner map
  // ... encode owner_map ...

  n = snprintf(p, end - p, "},");  // Close memory
  if (n < 0 || n >= end - p) goto cleanup;
  p += n;

  // ===== Metrics Section =====
  // ... same as valk_diag_snapshot_to_sse but without SSE framing ...

  // ===== Timestamp =====
  uint64_t now_us = (uint64_t)(uv_hrtime() / 1000);
  n = snprintf(p, end - p, "\"timestamp_us\":%lu}", now_us);

cleanup:
  valk_mem_snapshot_free(&snapshot);
  return (p - buf);
}
```

**File: `src/modules/aio/debug.valk` (MODIFY)**

Add new endpoint route:

```lisp
; Line ~55 (ADD new route)
{(== path "/debug/metrics/state")
 ; Fresh state endpoint - returns current snapshot without SSE
 `{:status "200"
   :content-type "application/json"
   :cache-control "no-cache, no-store, must-revalidate"
   :body ,(aio/diagnostics-state-json sys)}}
```

---

### Phase 4: Integrate Registry into AIO System

**File: `src/aio_uv.c` (MODIFY)**

```c
// Line ~580 (ADD to valk_aio_system struct):
#ifdef VALK_METRICS_ENABLED
  valk_sse_stream_registry_t sse_registry;  // Global SSE stream registry
#endif

// Line ~3440 (ADD to valk_aio_start_with_config):
#ifdef VALK_METRICS_ENABLED
  valk_sse_registry_init(&sys->sse_registry, sys);
#endif

// Line ~3580 (ADD to cleanup path):
#ifdef VALK_METRICS_ENABLED
  valk_sse_registry_shutdown(&sys->sse_registry);
#endif
```

**File: `src/aio.h` (MODIFY)**

```c
// Line ~365 (ADD accessor):
#ifdef VALK_METRICS_ENABLED
valk_sse_stream_registry_t* valk_aio_get_sse_registry(valk_aio_system_t* sys);
#endif
```

---

### Phase 5: Update Dashboard JavaScript

**File: `src/modules/aio/debug/script.js` (MODIFY)**

```javascript
// Line ~1420 (MODIFY MemoryDiagnostics class):

class MemoryDiagnostics {
  constructor() {
    // ... existing ...
    this.freshStateUrl = '/debug/metrics/state';  // NEW
  }

  // NEW: Fetch fresh state before connecting SSE
  async fetchFreshState() {
    try {
      const response = await fetch(this.freshStateUrl);
      if (!response.ok) throw new Error(`HTTP ${response.status}`);

      const data = await response.json();
      console.log('[MemDiag] Fresh state fetched:', data);

      // Store as full state
      this.fullState = {
        memory: data.memory,
        metrics: data.metrics
      };

      // Expand and store slab states
      if (data.memory && data.memory.slabs) {
        data.memory.slabs.forEach(slab => {
          if (slab.states) {
            this.slabStates[slab.name] = decodeRLE(slab.states);
          }
        });
      }

      // Render initial state
      if (data.metrics) {
        this.handleMetricsUpdate(data.metrics);
      }
      if (data.memory) {
        this.handleMemoryUpdate(data.memory);
      }

      return true;
    } catch (error) {
      console.error('[MemDiag] Failed to fetch fresh state:', error);
      return false;
    }
  }

  // MODIFY: connect() to fetch fresh state first
  async connect() {
    // Fetch fresh state FIRST
    await this.fetchFreshState();

    // Then connect to SSE for updates
    if (this.eventSource) {
      this.eventSource.close();
    }

    this.eventSource = new EventSource(this.sseUrl);

    // Now SSE will only send deltas (skip first full event)
    this.eventSource.addEventListener('diagnostics-delta', (e) => {
      this.lastEventId = e.lastEventId;
      var delta = JSON.parse(e.data);
      this.applyDelta(delta);
    });

    // Handle full events as fallback (reconnection)
    this.eventSource.addEventListener('diagnostics', (e) => {
      // ... existing full event handling ...
    });

    // ... rest of existing connect() ...
  }
}
```

---

### Phase 6: Update Lisp Builtins

**File: `src/metrics_builtins.c` (MODIFY)**

Add new builtin for fresh state JSON:

```c
// Line ~480 (ADD):
// (aio/diagnostics-state-json sys) -> json-string
// Returns fresh diagnostics state as JSON (for /debug/metrics/state endpoint)
static valk_lval_t *valk_builtin_aio_diagnostics_state_json(valk_lenv_t *e, valk_lval_t *a) {
  UNUSED(e);

  // Get AIO system from argument or global
  valk_aio_system_t *sys = valk_aio_active_system;
  if (valk_lval_list_count(a) >= 1) {
    valk_lval_t *sys_arg = valk_lval_list_nth(a, 0);
    if (LVAL_TYPE(sys_arg) == LVAL_REF &&
        strcmp(sys_arg->ref.type, "aio_system") == 0) {
      sys = (valk_aio_system_t *)sys_arg->ref.ptr;
    }
  }

  if (!sys) {
    return valk_lval_err("aio/diagnostics-state-json: no AIO system available");
  }

  // Allocate buffer (256KB for full state)
  char *buf = malloc(262144);
  if (!buf) {
    return valk_lval_err("aio/diagnostics-state-json: allocation failed");
  }

  int len = valk_diag_fresh_state_json(sys, buf, 262144);
  if (len < 0) {
    free(buf);
    return valk_lval_err("aio/diagnostics-state-json: encoding failed");
  }

  valk_lval_t *result = valk_lval_str_n(buf, len);
  free(buf);

  return result;
}

// Line ~530 (ADD to registration):
valk_lenv_put_builtin(env, "aio/diagnostics-state-json",
                      valk_builtin_aio_diagnostics_state_json);
```

---

## File Summary

| File | Action | Lines Changed |
|------|--------|---------------|
| `src/aio_sse_stream_registry.h` | NEW | ~100 |
| `src/aio_sse_stream_registry.c` | NEW | ~400 |
| `src/aio_sse_diagnostics.c` | MODIFY | ~100 |
| `src/aio_sse_diagnostics.h` | MODIFY | ~20 |
| `src/aio_uv.c` | MODIFY | ~30 |
| `src/aio.h` | MODIFY | ~10 |
| `src/metrics_builtins.c` | MODIFY | ~60 |
| `src/modules/aio/debug.valk` | MODIFY | ~10 |
| `src/modules/aio/debug/script.js` | MODIFY | ~80 |
| `CMakeLists.txt` | MODIFY | ~5 |

**Total: ~815 lines**

---

## Test Plan

### Unit Tests

**File: `test/test_sse_registry.c` (NEW)**

```c
// Test 1: Registry initialization
void test_registry_init(void) {
  valk_sse_stream_registry_t registry;
  valk_sse_registry_init(&registry, test_aio_system);

  ASSERT_EQ(registry.stream_count, 0);
  ASSERT_NOT_NULL(registry.timer_handle);
  ASSERT_FALSE(registry.timer_running);
}

// Test 2: Subscribe/unsubscribe
void test_registry_subscribe(void) {
  // ... subscribe stream, verify count increases
  // ... unsubscribe, verify count decreases
  // ... verify timer starts on first subscribe
  // ... verify timer stops on last unsubscribe
}

// Test 3: Multiple streams
void test_registry_multiple_streams(void) {
  // Subscribe 3 streams
  // Verify all receive updates on timer tick
  // Unsubscribe middle stream
  // Verify remaining streams still work
}

// Test 4: Connection cleanup
void test_registry_connection_cleanup(void) {
  // Subscribe 2 streams on same connection
  // Call unsubscribe_connection()
  // Verify both removed
}
```

**File: `test/test_metrics_state.valk` (NEW)**

```lisp
; Test fresh state endpoint
(def {test-fresh-state}
  (\\ {}
    (let {state (aio/diagnostics-state-json aio)}
      ; Verify JSON structure
      (assert (str-contains state "\"memory\""))
      (assert (str-contains state "\"metrics\""))
      (assert (str-contains state "\"timestamp_us\""))
      (assert (str-contains state "\"slabs\""))
    )))
```

### Integration Tests

**File: `test/test_sse_integration.c` (NEW)**

```c
// Test: Dashboard flow simulation
void test_dashboard_flow(void) {
  // 1. Start server
  // 2. Fetch /debug/metrics/state
  // 3. Verify JSON response
  // 4. Connect to /debug/diagnostics/memory SSE
  // 5. Verify delta events received
  // 6. Change some metrics
  // 7. Verify deltas reflect changes
}

// Test: Multiple browser tabs
void test_multiple_sse_clients(void) {
  // Connect 3 SSE clients
  // Verify single timer running
  // Verify all clients receive updates
  // Disconnect 2 clients
  // Verify remaining client still works
  // Disconnect last client
  // Verify timer stops
}
```

### Manual Validation

1. **Browser Test**:
   ```bash
   make build && ./build/valk src/modules/aio/debug-server.valk
   # Open http://localhost:8443/debug/ in 3 browser tabs
   # Verify single timer in server logs
   # Verify all tabs update in sync
   ```

2. **Fresh State Test**:
   ```bash
   curl -k https://localhost:8443/debug/metrics/state | jq .
   # Verify complete JSON with memory + metrics
   ```

3. **SSE Stream Test**:
   ```bash
   curl -k -N https://localhost:8443/debug/diagnostics/memory
   # Verify delta events after first full event
   ```

---

## Migration Strategy

1. **Backward Compatibility**: Keep existing `valk_sse_diag_init_http2()` working during transition
2. **Feature Flag**: Use `#ifdef VALK_SSE_REGISTRY_ENABLED` to toggle new code
3. **Gradual Rollout**:
   - Phase 1-2: Implement registry (disabled by default)
   - Phase 3-4: Add fresh state endpoint (works independently)
   - Phase 5: Update dashboard to use new flow
   - Phase 6: Enable registry, deprecate old per-connection timer

---

## Lifetime Management and Resource Safety

### Lifetime Hierarchy

```
┌─────────────────────────────────────────────────────────────────┐
│  AIO System (longest lifetime)                                  │
│  - Owns: global SSE registry                                    │
│  - Cleanup: valk_aio_stop() → valk_sse_registry_shutdown()      │
├─────────────────────────────────────────────────────────────────┤
│  HTTP Connection (valk_aio_handle_t)                            │
│  - Owns: reference to registry entries for its streams          │
│  - Cleanup: __uv_handle_closed_cb() → unsubscribe_connection()  │
│  - HAZARD: Connection can close while timer callback is running │
├─────────────────────────────────────────────────────────────────┤
│  HTTP/2 Session (nghttp2_session)                               │
│  - Owns: stream state in nghttp2                                │
│  - Cleanup: session_del callback, then handle close             │
│  - HAZARD: Session freed before our stream entry removed        │
├─────────────────────────────────────────────────────────────────┤
│  SSE Stream Entry (valk_sse_stream_entry_t)                     │
│  - Owns: pending buffer, metrics baseline, prev_snapshot        │
│  - Cleanup: unsubscribe() frees all owned resources             │
│  - HAZARD: Entry accessed after connection closed               │
├─────────────────────────────────────────────────────────────────┤
│  Global Timer (single uv_timer_t)                               │
│  - Owns: nothing (just schedules callbacks)                     │
│  - Cleanup: stop when stream_count==0, close on shutdown        │
│  - HAZARD: Timer callback races with connection cleanup         │
└─────────────────────────────────────────────────────────────────┘
```

### Critical Invariants

1. **Registry outlives all streams**: Registry is freed only in `valk_aio_stop()`
2. **Entry removal is synchronous**: `unsubscribe()` removes from list before freeing
3. **Session validity checked before use**: Always call `valk_aio_http_session_valid()`
4. **Stream validity checked before resume**: Check `nghttp2_session_get_stream_user_data()`
5. **Double-free guard**: Set pointers to NULL after free, check before free

### Cleanup Scenarios

#### Scenario 1: Normal stream close (client closes browser tab gracefully)

```
1. nghttp2 calls on_stream_close callback
2. on_stream_close finds our stream entry via stream_user_data
3. Calls valk_sse_registry_unsubscribe(entry)
4. Entry removed from doubly-linked list (O(1))
5. Entry resources freed (pending_data, baseline, prev_snapshot)
6. Entry freed
7. If stream_count==0, timer stopped (but not closed yet)
```

#### Scenario 2: Abrupt disconnect (browser refresh, network drop)

```
1. TCP connection dies, uv_read_cb gets error
2. Connection state set to VALK_CONN_CLOSING
3. uv_close() called on TCP handle
4. __uv_handle_closed_cb() fires:
   a. Calls valk_sse_registry_unsubscribe_connection(handle)
   b. Iterates all registry entries, removes those with matching handle
   c. Each entry's resources freed
5. Connection handle freed
```

#### Scenario 3: Timer callback races with connection close

```
Timer fires:
1. Lock registry (or use atomic flag)
2. Iterate streams:
   for each entry:
     a. Check entry->active (atomic read)
     b. Check valk_aio_http_session_valid(entry->handle, entry->session)
     c. Check nghttp2_session_get_stream_user_data(session, stream_id)
     d. If any check fails: mark entry inactive, continue
     e. Push data to stream
3. After iteration: remove inactive entries

Connection close races:
1. Sets entry->active = false (atomic write)
2. Timer sees this in step 2a, skips the entry
3. Connection cleanup proceeds safely
```

### Implementation: Safe Stream Entry Structure

```c
struct valk_sse_stream_entry {
  // === Linkage (protected by registry iteration) ===
  valk_sse_stream_entry_t *next;
  valk_sse_stream_entry_t *prev;

  // === Identity (immutable after creation) ===
  uint64_t stream_id;
  valk_sse_subscription_type_e type;

  // === HTTP/2 context (READ-ONLY after creation, may become stale) ===
  valk_aio_handle_t *handle;        // Back-pointer to connection
  nghttp2_session *session;          // DANGER: may be freed by nghttp2
  int32_t http2_stream_id;           // HTTP/2 stream ID

  // === Lifecycle state (atomic for safe cross-thread access) ===
  _Atomic bool active;               // Set false before any cleanup
  _Atomic bool being_removed;        // Guard against double-remove

  // === Per-stream state (owned, freed in unsubscribe) ===
  bool first_event_sent;
  uint64_t last_event_id;
  valk_mem_snapshot_t prev_snapshot; // Deep-copied, must free bitmaps
  valk_metrics_baseline_t *metrics_baseline;  // malloc'd, NULL if not needed

  // === Pending write buffer (owned) ===
  char *pending_data;                // malloc'd buffer
  size_t pending_len;
  size_t pending_offset;
  size_t pending_capacity;
  bool data_deferred;

  // === AIO metrics baseline (inline, no separate alloc) ===
  struct {
    uint64_t bytes_sent;
    uint64_t bytes_recv;
    uint64_t requests_total;
    uint64_t connections_total;
  } prev_aio_metrics;
};
```

### Implementation: Safe Unsubscribe

```c
void valk_sse_registry_unsubscribe(valk_sse_stream_registry_t *registry,
                                    valk_sse_stream_entry_t *entry) {
  if (!entry) return;

  // Guard: check if already being removed (race with timer cleanup)
  bool expected = false;
  if (!atomic_compare_exchange_strong(&entry->being_removed, &expected, true)) {
    VALK_DEBUG("SSE Registry: entry already being removed, skipping");
    return;
  }

  // Mark inactive FIRST (timer will see this)
  atomic_store(&entry->active, false);

  // Remove from list
  if (entry->prev) {
    entry->prev->next = entry->next;
  } else {
    registry->streams = entry->next;
  }
  if (entry->next) {
    entry->next->prev = entry->prev;
  }
  registry->stream_count--;

  VALK_INFO("SSE Registry: unsubscribed stream %lu, remaining=%zu",
            entry->stream_id, registry->stream_count);

  // === Free owned resources ===

  // 1. Pending buffer
  if (entry->pending_data) {
    free(entry->pending_data);
    entry->pending_data = NULL;
  }

  // 2. Metrics baseline (if allocated)
  if (entry->metrics_baseline) {
    free(entry->metrics_baseline);
    entry->metrics_baseline = NULL;
  }

  // 3. Previous snapshot (has internal allocations)
  valk_mem_snapshot_free(&entry->prev_snapshot);

  // 4. Entry itself
  free(entry);

  // Stop timer if no more streams
  if (registry->stream_count == 0 && registry->timer_running) {
    valk_sse_registry_timer_stop(registry);
  }
}
```

### Implementation: Safe Connection Cleanup

```c
void valk_sse_registry_unsubscribe_connection(
    valk_sse_stream_registry_t *registry,
    valk_aio_handle_t *handle) {

  if (!registry || !handle) return;

  VALK_INFO("SSE Registry: cleaning up streams for connection %p", (void*)handle);

  // Build removal list first (don't modify list while iterating)
  valk_sse_stream_entry_t *to_remove[64];
  size_t remove_count = 0;

  for (valk_sse_stream_entry_t *entry = registry->streams;
       entry && remove_count < 64;
       entry = entry->next) {
    if (entry->handle == handle) {
      to_remove[remove_count++] = entry;
    }
  }

  // Now remove each entry
  for (size_t i = 0; i < remove_count; i++) {
    valk_sse_registry_unsubscribe(registry, to_remove[i]);
  }

  if (remove_count > 0) {
    VALK_INFO("SSE Registry: removed %zu streams for connection", remove_count);
  }
}
```

### Implementation: Safe Timer Callback

```c
static void sse_registry_timer_cb(uv_timer_t *timer) {
  valk_sse_stream_registry_t *registry = timer->data;

  if (!registry) return;

  // Early exit if no streams (race: last stream just unsubscribed)
  if (!registry->streams) {
    valk_sse_registry_timer_stop(registry);
    return;
  }

  // 1. Collect snapshots ONCE
  valk_mem_snapshot_t snapshot = {0};
  valk_mem_snapshot_collect(&snapshot, registry->aio_system);

  valk_delta_snapshot_t *modular_delta = NULL;
#ifdef VALK_METRICS_ENABLED
  size_t modular_changes = valk_delta_snapshot_collect_stateless(
      &registry->modular_delta, &g_metrics, &registry->global_baseline);
  if (modular_changes > 0) {
    modular_delta = &registry->modular_delta;
  }
#endif

  // 2. Track entries to remove (don't remove during iteration)
  valk_sse_stream_entry_t *inactive[32];
  size_t inactive_count = 0;

  // 3. Push to each active stream
  for (valk_sse_stream_entry_t *entry = registry->streams;
       entry;
       entry = entry->next) {

    // Check 1: Is entry still active?
    if (!atomic_load(&entry->active)) {
      if (inactive_count < 32) inactive[inactive_count++] = entry;
      continue;
    }

    // Check 2: Is session still valid?
    if (!valk_aio_http_session_valid(entry->handle, entry->session)) {
      VALK_INFO("SSE Registry: session invalidated for stream %lu", entry->stream_id);
      atomic_store(&entry->active, false);
      if (inactive_count < 32) inactive[inactive_count++] = entry;
      continue;
    }

    // Check 3: Is HTTP/2 stream still open?
    if (nghttp2_session_get_stream_user_data(entry->session, entry->http2_stream_id) == NULL) {
      VALK_INFO("SSE Registry: HTTP/2 stream %d closed", entry->http2_stream_id);
      atomic_store(&entry->active, false);
      if (inactive_count < 32) inactive[inactive_count++] = entry;
      continue;
    }

    // All checks passed - push data
    sse_push_to_entry(registry, entry, &snapshot, modular_delta);
  }

  // 4. Remove inactive entries (after iteration)
  for (size_t i = 0; i < inactive_count; i++) {
    valk_sse_registry_unsubscribe(registry, inactive[i]);
  }

  // 5. Cleanup snapshot
  valk_mem_snapshot_free(&snapshot);
}
```

### Integration Points in aio_uv.c

```c
// In __uv_handle_closed_cb() (around line 773):
static void __uv_handle_closed_cb(uv_handle_t *handle) {
  valk_aio_handle_t *aio_handle = container_of(handle, ...);

  // ... existing cleanup ...

  // Clean up SSE registry entries for this connection
#ifdef VALK_METRICS_ENABLED
  valk_sse_stream_registry_t *registry =
      valk_aio_get_sse_registry(aio_handle->sys);
  if (registry) {
    valk_sse_registry_unsubscribe_connection(registry, aio_handle);
  }
#endif

  // Also clean up legacy sse_state if present
  if (aio_handle->http.sse_state) {
    valk_sse_diag_stop_all(aio_handle->http.sse_state);
  }

  // ... rest of cleanup ...
}
```

---

## Performance Considerations

1. **Single Timer Overhead**: One timer tick serves all clients (~100 streams max)
2. **Snapshot Collection**: Collected once per tick, shared by all streams
3. **Delta Encoding**: Reduces bandwidth by 90%+ vs full snapshots
4. **Doubly-Linked List**: O(1) insert and remove for stream management
5. **Memory**: ~1KB per stream entry, 256KB shared buffer for JSON encoding
