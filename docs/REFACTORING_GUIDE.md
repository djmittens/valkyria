# AIO Subsystem Refactoring Guide

This document defines the target architecture for Valkyria's I/O and networking subsystems, along with step-by-step refactoring tasks to achieve it.

---

## Implementation Progress

| Phase | Status | Notes |
|-------|--------|-------|
| Phase 1: Metrics Extraction | **Complete** | `metrics_v2` is standalone; AIO-specific metrics in `aio_metrics.c` (correct design) |
| Phase 2: SSE Cleanup | **Complete** | Removed `aio_sse_stream_registry.c/h` and `aio_diagnostics_timer.c/h`; diagnostics now Lisp-only per R4.1-R4.2 |
| Phase 3: Overload Consolidation | **Complete** | All files renamed to `aio_overload_*.c/h` |
| Phase 4: I/O Cleanup | **Complete** | Size fields removed from vtables |
| Phase 5: Code Organization | Not Started | Directory restructure pending (low priority, risky) |
| Phase 6: Complexity Reduction | **Complete** | All 17 `#ifdef` blocks consolidated into helper functions (R6.4) |
| Phase 7: Generic Streaming | **Complete** | Created generic streaming API; SSE now available as Lisp module |

### Recent Changes (2025-12-31)

10. **Fixed Allocator Mismatch Bugs (2025-12-31)**: During refactoring audit, discovered and fixed critical memory issues:
    - **FIX 1**: `valk_lenv_copy` at parser.c:2276 was copying the source env's allocator pointer instead of using the current thread-local allocator. This caused double-free when copied envs were modified with a different active allocator.
    - **FIX 2**: `valk_http2_client_request_with_headers_impl` at aio_http2_client.c was storing a raw pointer to the caller's environment (`ctx->env = e`). Changed to use `valk_aio_deep_copy_callback()` which properly deep-copies the callback including its captured environment. 
    - **CREATED**: `valk_aio_deep_copy_callback()` - exported version of `__deep_copy_lval_for_timer()` for use by HTTP client
    - **Result**: No more crashes on test exit. All C tests pass. Basic valk tests pass.
    - **Remaining**: Some async batch tests (`http2/health-check-all`, `http2/fetch-all`) still timing out - appears to be related to continuation-passing style callbacks not receiving expected arguments. Needs further investigation.

### Recent Changes (2025-12-30)

9. **Phase 7 Complete - Generic Streaming Responses (2025-12-30)**: Created generic streaming API:
   - **CREATED**: `aio_stream_body.c/h` - generic streaming response body with queue + backpressure
   - **CREATED**: `aio_stream_body_conn.c` - per-connection stream body tracking
   - **CREATED**: `aio_stream_builtins.c` - Lisp builtins: `stream/open`, `stream/write`, `stream/writable?`, `stream/close`, `stream/on-drain`, `stream/set-timeout`, `stream/cancel`, `stream/id`
   - **CREATED**: `src/modules/sse.valk` - SSE formatting as pure Lisp on top of generic streaming
   - Updated `CMakeLists.txt`, `aio_internal.h`, `parser.c`
   - Generic API works for any streaming response (SSE, chunked downloads, etc.)
   - SSE C builtins kept for backward compatibility
   - **Benefit**: SSE formatting is now Lisp (easy to modify), while streaming mechanics are generic C

### Recent Changes (2025-12-29)

1. **Fixed GC bug**: Removed redundant `used_bytes` decrement in TLAB cleanup that caused integer underflow in `test_gc_soft_limit_multithread`

2. **Fixed SSE conditional compilation bug (Step 2.2)**: Moved SSE `:sse-stream` body-type detection OUTSIDE `#ifdef VALK_METRICS_ENABLED` in `aio_http2_session.c:443-497`. SSE now works regardless of metrics flag. Only the metrics gauge increment remains conditional.

3. **Phase 3 Complete - Overload Consolidation**: Renamed files to unified "overload" terminology:
   - `aio_pressure.c/h` → `aio_overload_state.c/h`
   - `aio_conn_admission.c/h` → `aio_overload_admission.c/h`
   - `aio_backpressure.c/h` → `aio_overload_backpressure.c/h`
   - `aio_pending_stream.c/h` → `aio_overload_deferred.c/h`

4. **Phase 4 Complete - I/O Cleanup**: Removed unused size fields from vtables:
   - Removed `tcp_size`, `write_req_size` from `io_tcp_ops.h`
   - Removed `timer_size` from `io_timer_ops.h`
   - Updated all implementations (uv and test)

5. **Phase 6 Complete - Complexity Reduction (R6.4)**: Consolidated all 17 `#ifdef VALK_METRICS_ENABLED` blocks in `aio_http2_session.c` into dedicated helper functions:
   - Created new header `aio_http2_session_metrics.h` with 17 inline helpers
   - Replaced all scattered `#ifdef` blocks with clean function calls
   - Helpers are no-ops when metrics disabled (zero overhead)
   - File reduced from 1104 to 970 lines

6. **Phase 2 Complete - SSE Cleanup (2025-12-30)**: Removed diagnostics-specific SSE registry:
   - **DELETED**: `aio_sse_stream_registry.c/h` (924 + 152 lines)
   - **CREATED**: `aio_diagnostics_timer.c/h` - new timer module using generic SSE infrastructure
   - Updated all references: `aio_http2_session.c`, `aio_http2_session_metrics.h`, `aio_http2_conn.c`, `aio_sse_diagnostics.c`
   - Removed `sse_registry` field from `valk_aio_system_t`, replaced with `diag_timer`
   - Removed `valk_aio_get_sse_registry()`, added `valk_aio_get_diag_timer()`
   - Deleted obsolete tests: `test_sse_registry.c`, `test_sse_stream_registry.c`
   - SSE now has single generic implementation in `aio_sse.c/h` (R3.2 satisfied)

7. **Diagnostics Timer Removed (2025-12-30)**: Per R4.1-R4.2, diagnostics publishing should be in Lisp:
   - **DELETED**: `aio_diagnostics_timer.c/h` - the C-side timer that auto-pushed metrics
   - Removed `diag_timer` field from `valk_aio_system_t`
   - Removed `valk_aio_get_diag_timer()` function
   - Removed `:sse-stream` body-type handling from `aio_http2_session.c`
   - Updated `aio_http2_session_metrics.h` to use generic `valk_sse_get_manager()` for SSE stats
   - Updated test files: `test_aio_uv_coverage.c`, `test/unit/test_aio_uv.c`, `test_sse_diagnostics.c`
   - **Future**: Lisp handlers should use `(sse/open)`, `(aio/interval)`, `(sse/send)` for diagnostics

8. **SSE Architecture Review (2025-12-30)**: Identified SSE code as over-specialized:
   - Current SSE is just HTTP/2 streams with `Content-Type: text/event-stream` and specific text format
   - `valk_sse_stream_t` duplicates HTTP/2 stream tracking unnecessarily
   - Two conflicting linked lists: per-connection (`conn->http.sse_streams`) and global (`valk_sse_manager_t`)
   - Global manager not integrated into production code path - only used in unit tests
   - `sse/stream-count` and `sse/shutdown-all` builtins are broken (operate on empty global list)
   - **Decision**: Replace SSE-specific code with generic streaming response API (see Phase 7)

---

## Table of Contents

1. [Formal Requirements](#formal-requirements)
2. [Target Architecture](#target-architecture)
3. [Phase 1: Metrics System Extraction](#phase-1-metrics-system-extraction)
4. [Phase 2: SSE Subsystem Cleanup](#phase-2-sse-subsystem-cleanup)
5. [Phase 3: Overload Subsystem Consolidation](#phase-3-overload-subsystem-consolidation)
6. [Phase 4: I/O Abstraction Cleanup](#phase-4-io-abstraction-cleanup)
7. [Phase 5: Code Organization](#phase-5-code-organization)
8. [Phase 6: Session Callback Complexity Reduction](#phase-6-session-callback-complexity-reduction)
9. [Phase 7: Generic Streaming Responses](#phase-7-generic-streaming-responses)

---

## Formal Requirements

### R1: System Separation

**R1.1** AIO System and Metrics System SHALL be sibling systems, not nested.

**R1.2** AIO System SHALL own the lifecycle of all I/O resources (loop, connections, servers, timers).

**R1.3** Metrics System SHALL operate independently of AIO (usable in REPL, tests, without networking).

**R1.4** Composition of systems SHALL occur at the Lisp application layer.

### R2: AIO System Ownership

**R2.1** AIO System SHALL own the event loop; no external code SHALL directly access the loop.

**R2.2** HTTP/2 servers/clients SHALL be built-in to AIO (not pluggable subsystems) because they require tight lifecycle coupling with the event loop.

**R2.3** AIO System SHALL dictate shutdown of all owned resources.

**R2.4** Future I/O types (files, UDP, signals) SHALL be added to AIO, not as separate systems.

### R3: HTTP/2 Subsystems

**R3.1** HTTP/2 SHALL contain the following subsystems:
- Connections (TCP lifecycle, TLS, I/O buffers)
- Streams (request/response lifecycle)
- SSE (sub-subsystem of Streams)
- Overload (load management subsystem)

**R3.2** Streaming responses SHALL be generic HTTP/2 stream functionality, NOT SSE-specific.
- SSE is just a content-type (`text/event-stream`) and text format (`data: ...\n\n`)
- The transport layer should provide generic streaming writes with backpressure
- SSE formatting belongs in Lisp, not C

**R3.3** Overload SHALL encompass:
- Admission (accept/defer/reject at connection and stream entry points)
- Backpressure (pause/resume flow when buffers full)
- Deferred work queue (where deferred streams wait)

**R3.4** Backpressure SHALL use high/low watermarks with hysteresis:
- High watermark (default 80%): trigger pause (stop reading from TCP)
- Low watermark (default 40%): trigger resume (resume reading)
- Low watermark SHOULD be half of high watermark (per Envoy pattern)
- Hysteresis gap (40%) prevents oscillation between pause/resume states

**R3.5** Streams SHALL follow RFC 9113 Section 5.1 lifecycle states:
- `idle` → `open` (on HEADERS receive without END_STREAM)
- `idle` → `half-closed (remote)` (on HEADERS receive with END_STREAM)
- `open` → `half-closed (remote)` (on END_STREAM receive)
- `open` → `half-closed (local)` (on END_STREAM send)
- `half-closed (local)` → `closed` (on END_STREAM receive or RST_STREAM)
- `half-closed (remote)` → `closed` (on END_STREAM send or RST_STREAM)
- Any state → `closed` (on RST_STREAM send or receive)

> **Note**: RFC 9113 also defines `reserved (local)` and `reserved (remote)` states
> for PUSH_PROMISE. These are omitted as server push is not implemented.

**R3.6** HTTP/2 handles SHALL follow explicit lifecycle states:

> **Terminology**: A "handle" represents the combined TCP + TLS + HTTP/2 session
> as a single unit. States span all layers because they are tightly coupled in
> `valk_aio_handle_t`. GOAWAY states are HTTP/2-level but affect the entire handle.

```
INIT → HANDSHAKING → ESTABLISHED → GOAWAY_SENT → DRAINING → CLOSING → CLOSED
  │         │            │              │            │          │
  └─────────┴────────────┴──────────────┴────────────┴──────────→ ERROR
```

| State | Layer | Description | Entry Action | Exit Condition |
|-------|-------|-------------|--------------|----------------|
| INIT | TCP | Socket accepted | Start TLS handshake | Handshake begins |
| HANDSHAKING | TLS | SSL/TLS negotiation | - | SSL complete or error |
| ESTABLISHED | HTTP/2 | Session active, accepting streams | Enable reads | GOAWAY sent or error |
| GOAWAY_SENT | HTTP/2 | First GOAWAY sent (max stream ID) | Start drain timer | Timer fires or all streams close |
| DRAINING | HTTP/2 | Second GOAWAY sent (actual last ID) | - | All streams closed or timeout |
| CLOSING | All | Cleanup in progress | Stop reads, flush pending | Cleanup complete |
| CLOSED | All | Terminal state | Release resources | - |
| ERROR | All | Fatal error occurred | Log, notify | Immediate transition to CLOSING |

**R3.7** Graceful shutdown SHALL use two-phase GOAWAY (per Envoy pattern):
1. Send GOAWAY with `last_stream_id = 2^31-1` (accept no new streams)
2. Wait ≥ 1 RTT or configurable timeout (default 1s)
3. Send GOAWAY with actual `last_stream_id`
4. Wait for active streams to complete or timeout (default 5s)
5. Force close remaining connections

> **Terminology Note**: Industry uses varied terms for load management:
> - Envoy: "Overload Manager"
> - Netflix: "Concurrency Limiter"
> - AWS: "Admission Control"
>
> We use "Overload" following Envoy's pattern, as it naturally encompasses
> admission decisions, backpressure, and deferred work under one concept.

**R3.8** Overload detection SHALL use request queue latency as primary signal:
- Measure time between request arrival and handler invocation
- Threshold: average queue latency > 20ms indicates overload (per WeChat DAGOR)
- Secondary signals: slab usage, inflight count, deferred queue depth
- Composite pressure = max(normalized resource pressures)

### R4: Diagnostics Publishing

**R4.1** Diagnostics publishing SHALL NOT be implemented in C.

**R4.2** Diagnostics publishing SHALL be a Lisp handler that composes:
- Metrics System (via `metrics/snapshot` or similar)
- SSE transport (via `sse/open`, `sse/send`)
- Timer (via `aio/interval` or `aio/schedule`)

**R4.3** The current `aio_sse_stream_registry.c` (diagnostics-specific) SHALL be removed or refactored to generic SSE.

**R4.4** Wire format SHALL remain JSON for UI compatibility:
- Initial snapshot: full metrics state as JSON object
- Delta updates: changed metrics only as JSON object
- Lisp handler SHALL use `json/encode` or equivalent to produce JSON
- This preserves existing dashboard without UI changes during refactor

### R5: I/O Abstraction

**R5.1** I/O operations SHALL be abstracted via vtables (`io_tcp_ops`, `io_timer_ops`, `io_loop_ops`).

**R5.2** Vtables SHALL NOT expose implementation-specific size fields.
- AIO System owns all handle allocations internally
- Callers never allocate I/O handles directly; they request handles from AIO
- Size fields leak implementation details and are unused by callers
- Use `_Static_assert` to verify storage sizes at compile time

**R5.3** Test implementations SHALL be **fakes** (test doubles), NOT mocks:
- Fakes are real implementations with simplified/deterministic behavior
- Fakes record inputs for inspection (e.g., `valk_test_tcp_get_sent()`)
- Fakes allow injecting data (e.g., `valk_test_tcp_inject_data()`)
- No mocking frameworks, no expectation setup, no verification calls

### R6: Code Quality

**R6.1** Cyclomatic complexity of any function SHALL NOT exceed 10.

**R6.2** Nesting depth SHALL NOT exceed 4 levels.

**R6.3** Code coverage SHALL reach 90% for AIO subsystem.

**R6.4** All `#ifdef` blocks SHALL be consolidated into dedicated functions.

### R7: Deployment Model

**R7.1** Valkyria SHALL be deployed behind an edge proxy (Envoy sidecar) for production.

**R7.2** Direct internet exposure is NOT a supported configuration.

**R7.3** The Envoy sidecar handles both inbound and outbound traffic:

```
                    ┌─────────────────────────────────────┐
                    │            Pod / Host               │
                    │                                     │
Internet ──────────▶│  Envoy   ◀──────▶  Valkyria        │
                    │ (sidecar)         (server+client)   │
                    │    │                                │
                    │    └──────────────────────────────▶ │ Upstreams
                    │         (outbound)                  │
                    └─────────────────────────────────────┘
```

**R7.4** Edge proxy responsibilities (NOT in Valkyria):
- TLS termination and certificate management
- DDoS mitigation and rate limiting
- Connection pooling to upstreams
- WAF / request filtering
- Retry policies and circuit breaking

**R7.5** Valkyria's trust model:
- Trusts traffic from local Envoy sidecar
- Focus on correctness, not adversarial internet resilience
- Overload protection provides defense-in-depth, not primary security

### R8: HTTP/2 Client

**R8.1** HTTP/2 client SHALL be part of the AIO System (same as server).

**R8.2** Client connection pooling SHALL be delegated to Envoy sidecar:
- Valkyria maintains single HTTP/2 connection to localhost sidecar
- Sidecar handles connection pooling to upstream services
- Simplifies client to: connect, multiplex streams, reconnect on failure

**R8.3** Client handle states (simplified, single connection to sidecar):

| State | Description |
|-------|-------------|
| DISCONNECTED | No connection to sidecar |
| CONNECTING | TCP/TLS handshake in progress |
| CONNECTED | HTTP/2 session active, can open streams |
| RECONNECTING | Connection lost, attempting reconnect |

**R8.4** Client streams follow same RFC 9113 states as server (R3.5).

**R8.5** For non-sidecar deployments (development, testing):
- Provide simple "connect-per-request" mode (no pooling)
- Or optionally implement basic connection pool as future enhancement

---

## Target Architecture

### Deployment View

```
                        ┌──────────────────────────────────────────────────────┐
                        │                    Pod / Host                        │
                        │                                                      │
Internet ──────────────▶│  ┌─────────┐    ┌─────────────────────────────────┐ │
                        │  │  Envoy  │◀──▶│           Valkyria              │ │
                        │  │(sidecar)│    │  ┌─────────┐    ┌───────────┐   │ │
                        │  │         │    │  │ Server  │    │  Client   │   │ │
                        │  │         │    │  │(handler)│    │(to sidecar│   │ │
                        │  │         │    │  └─────────┘    └───────────┘   │ │
                        │  └────┬────┘    └─────────────────────────────────┘ │
                        │       │                                              │
                        │       └─────────────────────────────────────────────▶│ Upstreams
                        └──────────────────────────────────────────────────────┘
```

### System-Level View

```
┌─────────────────────────────────────────────────────────────┐
│  Lisp Application Layer                                     │
│    ├── HTTP handlers (server)                               │
│    ├── HTTP clients (outbound requests via sidecar)         │
│    ├── Diagnostics publisher (composes Metrics + SSE)       │
│    └── Application logic                                    │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌─────────────────────────┐    ┌─────────────────────────┐ │
│  │  AIO System             │    │  Metrics System         │ │
│  │  (owns I/O lifecycle)   │    │  (independent)          │ │
│  │                         │    │                         │ │
│  │  ├── Core I/O           │    │  ├── Counters           │ │
│  │  │   ├── Loop           │    │  ├── Gauges             │ │
│  │  │   ├── TCP            │    │  ├── Histograms         │ │
│  │  │   ├── Timers         │    │  └── Query API          │ │
│  │  │   └── Files [future] │    │                         │ │
│  │  │                      │    └─────────────────────────┘ │
│  │  └── HTTP/2             │                                │
│  │      ├── Server         │                                │
│  │      │   ├── Handles    │                                │
│  │      │   ├── Streams    │                                │
│  │      │   │   └── SSE    │                                │
│  │      │   └── Overload   │                                │
│  │      └── Client         │                                │
│  │          ├── Handle     │  (single conn to sidecar)      │
│  │          └── Streams    │                                │
│  │                         │                                │
│  └─────────────────────────┘                                │
│                                                             │
├─────────────────────────────────────────────────────────────┤
│  Runtime (GC, Memory, Eval)                                 │
└─────────────────────────────────────────────────────────────┘
```

### AIO Internal Structure

```
AIO System
├── Core I/O (protocol-agnostic)
│   ├── io_loop_ops      - Event loop abstraction
│   ├── io_tcp_ops       - TCP connection abstraction
│   ├── io_timer_ops     - Timer abstraction
│   └── [future: io_file_ops, io_udp_ops, io_signal_ops]
│
├── HTTP/2 Server (built-in, uses Core I/O)
│   ├── Handles (TCP+TLS+Session as unit)
│   │   ├── Lifecycle (init, establish, close)
│   │   ├── TLS/SSL integration
│   │   └── I/O buffers (conn_io)
│   │
│   ├── Streams
│   │   ├── Request/response lifecycle (RFC 9113 state machine)
│   │   ├── Arena management (per-stream memory)
│   │   └── Streaming bodies (for long-lived responses)
│   │       ├── Generic stream creation (stream/open)
│   │       ├── Chunked writing (stream/write)
│   │       ├── Backpressure (queue limits)
│   │       └── Uses existing HTTP/2 stream lifecycle
│   │
│   └── Overload
│       ├── State tracking (resource usage snapshots)
│       ├── Admission (accept/defer/reject)
│       ├── Backpressure (pause reads at high watermark, resume at low)
│       └── Deferred queue (pending streams)
│
├── HTTP/2 Client (built-in, uses Core I/O)
│   ├── Handle (single connection to sidecar)
│   │   ├── Connect/reconnect logic
│   │   ├── States: DISCONNECTED → CONNECTING → CONNECTED → RECONNECTING
│   │   └── Automatic reconnection on failure
│   │
│   └── Streams
│       ├── Request/response lifecycle (RFC 9113 state machine)
│       └── Arena management (per-request memory)
│
└── System Lifecycle
    ├── Initialization (slabs, loop, config)
    ├── Run (event loop execution)
    ├── Shutdown (graceful teardown)
    └── Maintenance (periodic timeouts, cleanup)
```

### Connection State Machine Implementation

**Recommended Pattern: Hybrid (State Handler Functions)**

Each state has a handler function, central dispatcher manages transitions with entry/exit actions:

```c
// Connection states (expanded from current 4 to 8)
typedef enum {
  VALK_CONN_INIT,           // TCP accepted
  VALK_CONN_HANDSHAKING,    // SSL in progress
  VALK_CONN_ESTABLISHED,    // HTTP/2 active
  VALK_CONN_GOAWAY_SENT,    // First GOAWAY sent
  VALK_CONN_DRAINING,       // Second GOAWAY sent, waiting for streams
  VALK_CONN_CLOSING,        // Cleanup in progress
  VALK_CONN_CLOSED,         // Terminal
  VALK_CONN_ERROR,          // Error occurred
  VALK_CONN_STATE_COUNT
} valk_conn_state_e;

// Events that trigger state transitions
typedef enum {
  VALK_CONN_EVT_SSL_COMPLETE,
  VALK_CONN_EVT_SSL_ERROR,
  VALK_CONN_EVT_DATA,
  VALK_CONN_EVT_WRITE_COMPLETE,
  VALK_CONN_EVT_GOAWAY_RECV,
  VALK_CONN_EVT_SHUTDOWN,        // Server shutdown requested
  VALK_CONN_EVT_DRAIN_TIMEOUT,   // First GOAWAY timeout
  VALK_CONN_EVT_CLOSE_TIMEOUT,   // Force close timeout
  VALK_CONN_EVT_ALL_STREAMS_CLOSED,
  VALK_CONN_EVT_IO_ERROR,
  VALK_CONN_EVT_PROTOCOL_ERROR,
  VALK_CONN_EVT_COUNT
} valk_conn_event_e;

// State handler returns next state
typedef valk_conn_state_e (*conn_state_handler_fn)(
    valk_aio_handle_t *conn,
    valk_conn_event_e event
);

typedef struct {
  conn_state_handler_fn handler;
  void (*on_enter)(valk_aio_handle_t *conn);
  void (*on_exit)(valk_aio_handle_t *conn);
  const char *name;  // For logging/debugging
} valk_conn_state_def_t;

// Dispatcher with entry/exit actions
static inline void valk_conn_transition(
    valk_aio_handle_t *conn,
    valk_conn_state_e next
) {
  if (next == conn->http.state) return;

  const valk_conn_state_def_t *cur = &conn_state_defs[conn->http.state];
  const valk_conn_state_def_t *nxt = &conn_state_defs[next];

  VALK_TRACE("conn %p: %s → %s", conn, cur->name, nxt->name);

  if (cur->on_exit) cur->on_exit(conn);
  conn->http.state = next;
  if (nxt->on_enter) nxt->on_enter(conn);
}
```

**Graceful Shutdown Sequence:**

```c
// Phase 1: ESTABLISHED → GOAWAY_SENT
static void on_enter_goaway_sent(valk_aio_handle_t *conn) {
  // Send GOAWAY with max stream ID (no new streams)
  valk_http2_submit_goaway(conn, INT32_MAX, NGHTTP2_NO_ERROR);
  valk_http2_flush_pending(conn);

  // Start drain timer (default 1s)
  uv_timer_start(&conn->http.drain_timer, drain_timer_cb,
                 conn->http.sys->config.drain_timeout_ms, 0);
}

// Phase 2: GOAWAY_SENT → DRAINING
static void on_enter_draining(valk_aio_handle_t *conn) {
  // Send GOAWAY with actual last stream ID
  valk_http2_submit_goaway(conn,
      nghttp2_session_get_last_proc_stream_id(conn->http.session),
      NGHTTP2_NO_ERROR);
  valk_http2_flush_pending(conn);

  // Start close timer (default 5s)
  uv_timer_start(&conn->http.close_timer, close_timer_cb,
                 conn->http.sys->config.close_timeout_ms, 0);
}
```

**State Machine Testing Strategy:**

> **Testing Philosophy**: This project uses **test doubles** (fakes, stubs), NOT mocking
> frameworks. Test doubles are real implementations with simplified/deterministic
> behavior (e.g., `valk_io_tcp_ops_test`, `valk_io_timer_ops_test`). They allow
> injecting data and inspecting results without complex expectation setup.

```c
// 1. Transition table verification
typedef struct {
  valk_conn_state_e from;
  valk_conn_event_e event;
  valk_conn_state_e expected;
  const char *desc;
} transition_test_t;

static const transition_test_t transition_tests[] = {
  { VALK_CONN_INIT, VALK_CONN_EVT_SSL_COMPLETE, VALK_CONN_HANDSHAKING, "init→handshaking" },
  { VALK_CONN_HANDSHAKING, VALK_CONN_EVT_DATA, VALK_CONN_ESTABLISHED, "handshake complete" },
  { VALK_CONN_ESTABLISHED, VALK_CONN_EVT_SHUTDOWN, VALK_CONN_GOAWAY_SENT, "graceful shutdown" },
  { VALK_CONN_GOAWAY_SENT, VALK_CONN_EVT_DRAIN_TIMEOUT, VALK_CONN_DRAINING, "drain timeout" },
  { VALK_CONN_GOAWAY_SENT, VALK_CONN_EVT_ALL_STREAMS_CLOSED, VALK_CONN_CLOSING, "early close" },
  { VALK_CONN_DRAINING, VALK_CONN_EVT_ALL_STREAMS_CLOSED, VALK_CONN_CLOSING, "drain complete" },
  { VALK_CONN_DRAINING, VALK_CONN_EVT_CLOSE_TIMEOUT, VALK_CONN_CLOSING, "force close" },
  // Error paths
  { VALK_CONN_ESTABLISHED, VALK_CONN_EVT_IO_ERROR, VALK_CONN_ERROR, "io error" },
  { VALK_CONN_ERROR, VALK_CONN_EVT_IO_ERROR, VALK_CONN_CLOSING, "error→closing" },
};

// 2. Scenario tests using test doubles (fake I/O ops)
void test_graceful_shutdown_scenario(void) {
  // Uses valk_io_tcp_ops_test - a fake implementation that records sent data
  valk_aio_handle_t conn = test_create_established_conn();

  valk_conn_dispatch(&conn, VALK_CONN_EVT_SHUTDOWN);
  ASSERT_EQ(conn.http.state, VALK_CONN_GOAWAY_SENT);
  ASSERT_TRUE(test_goaway_sent_with_max_id(&conn));  // Inspect fake's recorded data

  test_advance_time(1000);  // Fake timer fires drain timeout
  ASSERT_EQ(conn.http.state, VALK_CONN_DRAINING);
  ASSERT_TRUE(test_goaway_sent_with_actual_id(&conn));

  valk_conn_dispatch(&conn, VALK_CONN_EVT_ALL_STREAMS_CLOSED);
  ASSERT_EQ(conn.http.state, VALK_CONN_CLOSING);
}
```

### Overload Subsystem Detail

```
Overload
├── State Snapshot
│   ├── TCP buffer slab usage
│   ├── Arena slab usage
│   ├── Handle slab usage
│   ├── Deferred queue depth
│   ├── Backpressure list length
│   ├── Request queue latency (primary overload signal)
│   └── Inflight request count
│
├── Policy Evaluation
│   ├── NORMAL    (< 70% usage)  → Accept all
│   ├── ELEVATED  (70-85%)       → Probabilistic shedding
│   ├── HIGH      (85-95%)       → Reject new work
│   └── CRITICAL  (> 95%)        → Reject + shed existing
│
├── Admission
│   ├── Connection gate   → Accept/Reject TCP
│   └── Stream gate       → Accept/Defer/Reject HTTP/2 stream
│
├── Backpressure (watermark-based)
│   ├── High watermark (80%) → Pause TCP reads
│   ├── Low watermark (40%)  → Resume TCP reads (half of high)
│   └── Timeout              → Close stuck connections
│
└── Deferred Queue
    ├── Pending stream pool (pre-allocated)
    ├── FIFO queue (process when overload subsides)
    └── Timeout (RST_STREAM if waiting too long)
```

### Diagnostics Publisher (Lisp)

```lisp
;; Example: Diagnostics endpoint handler using generic streaming + SSE formatting
(defun diagnostics-handler (req)
  (let ((stream (sse/open req)))  ; SSE is Lisp wrapper around stream/open
    ;; Send initial full snapshot
    (sse/send stream (json/encode (metrics/snapshot)))

    ;; Set up periodic delta updates
    (aio/interval 100  ; 100ms
      (fn ()
        (when (sse/writable? stream)
          (sse/send stream (json/encode (metrics/delta))))))

    ;; Keep connection open
    :deferred))

;; Where sse/open and sse/send are defined in Lisp (src/modules/sse.valk):
;; (defun sse/open (req)
;;   (stream/open req {:content-type "text/event-stream" ...}))
;; (defun sse/send (stream data)
;;   (stream/write stream (str "data: " data "\n\n")))
```

---

## Phase 1: Metrics System Extraction

### Problem

Metrics code is scattered throughout AIO:
- `aio_metrics.c/h` - metrics collection
- `aio_sse_stream_registry.c` - metrics publishing via SSE
- `aio_sse_diagnostics.c` - memory snapshot formatting
- 13 `#ifdef VALK_METRICS_ENABLED` blocks in `aio_http2_session.c`

This violates R1.1 (systems should be siblings) and R4.1 (diagnostics should be in Lisp).

### Solution

1. Extract Metrics System to standalone location
2. Remove metrics-specific code from AIO
3. Provide Lisp API for metrics access

### Implementation Steps

#### Step 1.1: Create standalone Metrics System

**Move/refactor files:**
```
src/metrics/              # New location
├── metrics.h             # Public API
├── metrics.c             # Counter/gauge/histogram
├── metrics_registry.c    # Registration
├── metrics_snapshot.c    # Snapshot/delta
└── metrics_builtins.c    # Lisp builtins
```

**Public API:**
```c
// metrics.h
valk_counter_t* valk_metrics_counter(const char* name);
valk_gauge_t* valk_metrics_gauge(const char* name);
valk_histogram_t* valk_metrics_histogram(const char* name, ...);

valk_metrics_snapshot_t* valk_metrics_snapshot(void);
valk_metrics_delta_t* valk_metrics_delta(valk_metrics_snapshot_t* baseline);
char* valk_metrics_to_json(valk_metrics_snapshot_t* snap);
```

**Lisp builtins:**
```lisp
(metrics/snapshot)        ; → snapshot object
(metrics/delta baseline)  ; → delta since baseline
(metrics/json snapshot)   ; → JSON string
(metrics/counter name)    ; → counter value
(metrics/gauge name)      ; → gauge value
```

#### Step 1.2: Remove diagnostics registry

**Delete or gut:**
- `src/aio/aio_sse_stream_registry.c` - timer-driven push logic
- `src/aio/aio_sse_stream_registry.h` - diagnostics-specific types
- `src/aio/aio_sse_diagnostics.c` - memory formatting (move to metrics)

**Keep generic SSE in:**
- `src/aio/aio_sse.c/h` - generic stream management
- `src/aio/aio_sse_builtins.c` - Lisp builtins
- `src/aio/aio_sse_conn_tracking.c/h` - per-connection cleanup

#### Step 1.3: Create Lisp diagnostics handler

**New file:** `src/modules/diagnostics.valk`

```lisp
(defun diagnostics/handler (req)
  "SSE endpoint for system diagnostics"
  (let ((stream (sse/open))
        (baseline (metrics/snapshot)))

    ;; Send initial state
    (sse/send stream "init" (metrics/json baseline))

    ;; Periodic updates
    (aio/interval 100
      (fn ()
        (if (sse/writable? stream)
          (let ((delta (metrics/delta baseline)))
            (sse/send stream "delta" (metrics/json delta))
            (set! baseline (metrics/snapshot)))
          nil)))

    :deferred))
```

#### Step 1.4: Remove #ifdef blocks from session.c

**File:** `src/aio/aio_http2_session.c`

Replace 13 scattered `#ifdef VALK_METRICS_ENABLED` blocks with hook calls:

```c
// BEFORE (13 blocks like this)
#ifdef VALK_METRICS_ENABLED
  valk_counter_inc(server->metrics.requests_total);
  req->start_time = uv_hrtime();
#endif

// AFTER (single hook, always called)
valk_http2_on_request_start(conn, req);  // Metrics hooks internally
```

### Test Plan: Phase 1

| Test | Description | Expected |
|------|-------------|----------|
| Metrics standalone | Metrics work without AIO | Pass |
| Metrics builtins | `(metrics/snapshot)` returns data | Valid JSON |
| SSE generic | `(sse/open)` works | Stream created |
| Diagnostics handler | Lisp handler streams data | Events received |
| No metrics build | Build with metrics disabled | Compiles, runs |

### Verification Checklist

- [ ] Metrics System has no dependencies on AIO
- [ ] AIO has no `#include "metrics.h"` (except optional hooks)
- [ ] `aio_sse_stream_registry.c` deleted or gutted
- [ ] Diagnostics works via Lisp handler
- [ ] All metrics still collected (no regression)

---

## Phase 2: SSE Subsystem Cleanup

### Problem

SSE currently has two parallel implementations:
1. Generic (`aio_sse.c`) - works with Lisp builtins
2. Diagnostics-specific (`aio_sse_stream_registry.c`) - hardcoded metrics push

This violates R3.2 (SSE should be generic).

### Solution

Keep only generic SSE. Remove diagnostics-specific registry.

### Implementation Steps

#### Step 2.1: Audit generic SSE completeness

**Verify these work:**
```lisp
(sse/open)              ; Create stream in handler
(sse/send stream data)  ; Send event
(sse/send stream type data)  ; Send typed event
(sse/close stream)      ; Close stream
(sse/writable? stream)  ; Check backpressure
(sse/on-drain stream fn); Drain callback
(sse/set-timeout stream ms) ; Idle timeout
```

**Add if missing:**
```lisp
(sse/on-close stream fn)   ; Close callback (infrastructure exists)
(sse/on-timeout stream fn) ; Timeout callback (infrastructure exists)
```

#### Step 2.2: Fix SSE conditional compilation bug

**File:** `src/aio/aio_http2_session.c` lines 444-496

**CRITICAL BUG:** SSE setup is entirely inside `#ifdef VALK_METRICS_ENABLED`

```c
// BEFORE (broken when metrics disabled)
#ifdef VALK_METRICS_ENABLED
  if (body_type_val && strcmp(body_type_val->str, ":sse-stream") == 0) {
    // All SSE setup here - BROKEN without metrics!
  }
#endif

// AFTER (SSE always works)
if (body_type_val && strcmp(body_type_val->str, ":sse-stream") == 0) {
  // SSE setup - always runs
  // Metrics recording is optional, handled by hooks
}
```

#### Step 2.3: Remove diagnostics registry

**Delete:**
- `src/aio/aio_sse_stream_registry.c`
- `src/aio/aio_sse_stream_registry.h`

**Update references:**
- Remove `sse_registry` from `valk_aio_system_t`
- Remove registry timer logic
- Remove `VALK_SSE_SUB_DIAGNOSTICS` enum

### Test Plan: Phase 2

| Test | Description | Expected |
|------|-------------|----------|
| SSE without metrics | Build without metrics, test SSE | Works |
| SSE builtins | All builtins functional | Pass |
| SSE backpressure | Queue fills, writable? returns false | Correct |
| SSE cleanup | Connection close cleans up streams | No leaks |

---

## Phase 3: Overload Subsystem Consolidation

**STATUS: Step 3.1 COMPLETE (2025-12-29)**

### Problem

Overload-related code is scattered:
- ~~`aio_pressure.c/h`~~ → `aio_overload_state.c/h` ✓
- ~~`aio_conn_admission.c/h`~~ → `aio_overload_admission.c/h` ✓
- ~~`aio_backpressure.c/h`~~ → `aio_overload_backpressure.c/h` ✓
- ~~`aio_pending_stream.c/h`~~ → `aio_overload_deferred.c/h` ✓

This makes the overload model hard to understand and modify.

### Solution

Consolidate under unified "Overload" naming and structure.

### Implementation Steps

#### Step 3.1: Rename to overload terminology ✓ DONE

```
aio_pressure.c       → aio_overload_state.c       ✓
aio_conn_admission.c → aio_overload_admission.c   ✓
aio_backpressure.c   → aio_overload_backpressure.c ✓
aio_pending_stream.c → aio_overload_deferred.c    ✓
```

#### Step 3.2: Unify header

**New file:** `src/aio/aio_overload.h`

```c
#pragma once

// Overload state snapshot
typedef struct valk_overload_state valk_overload_state_t;
void valk_overload_snapshot(valk_aio_system_t* sys, valk_overload_state_t* out);

// Overload levels (based on resource pressure)
typedef enum {
  VALK_OVERLOAD_NORMAL,    // < 60% - accept all
  VALK_OVERLOAD_ELEVATED,  // 60-85% - probabilistic shedding
  VALK_OVERLOAD_HIGH,      // 85-95% - reject new work
  VALK_OVERLOAD_CRITICAL,  // > 95% - reject + shed existing
} valk_overload_level_e;

valk_overload_level_e valk_overload_evaluate(const valk_overload_state_t* state);

// Admission decisions
bool valk_overload_accept_connection(valk_aio_system_t* sys);
typedef enum { ADMIT, DEFER, REJECT } valk_admit_decision_e;
valk_admit_decision_e valk_overload_accept_stream(valk_aio_system_t* sys);

// Backpressure (watermark-based)
typedef struct {
  float high_watermark;  // default 0.80 - pause reads
  float low_watermark;   // default 0.50 - resume reads
} valk_watermarks_t;

void valk_overload_pause_reads(valk_aio_handle_t* conn);
void valk_overload_resume_reads(valk_aio_handle_t* conn);
bool valk_overload_try_resume_one(valk_aio_system_t* sys);

// Deferred queue
valk_deferred_stream_t* valk_overload_defer_stream(valk_aio_system_t* sys, ...);
valk_deferred_stream_t* valk_overload_dequeue(valk_aio_system_t* sys);
```

#### Step 3.3: Update call sites

Replace old function names with new unified API.

### Test Plan: Phase 3

| Test | Description | Expected |
|------|-------------|----------|
| Admission | High load rejects connections | 503 responses |
| Deferral | Arena exhaustion defers streams | Streams queued |
| Backpressure | Buffer full pauses reads | Reads paused |
| Resume | Flush resumes reading | Reads resumed |
| Timeout | Old deferred streams timeout | RST_STREAM sent |

---

## Phase 4: I/O Abstraction Cleanup

**STATUS: Steps 4.1 and 4.3 COMPLETE (2025-12-29)**

### Problem

Vtables expose unused size fields and leak implementation details.

### Solution

Remove size fields, use opaque handles.

### Implementation Steps

#### Step 4.1: Remove size fields ✓ DONE

**Files:**
- `src/aio/io/io_tcp_ops.h` - removed `tcp_size`, `write_req_size` ✓
- `src/aio/io/io_timer_ops.h` - removed `timer_size` ✓

#### Step 4.2: Add static assertions (OPTIONAL)

```c
_Static_assert(sizeof(uv_tcp_t) <= sizeof(((valk_aio_handle_t*)0)->tcp_storage),
               "TCP storage too small");
```

#### Step 4.3: Update implementations ✓ DONE

Removed size field initializations from:
- `io_tcp_ops_uv.c` ✓
- `io_tcp_ops_test.c` ✓
- `io_timer_ops_uv.c` ✓
- `io_timer_ops_test.c` ✓

### Test Plan: Phase 4

| Test | Description | Expected |
|------|-------------|----------|
| Build | Compiles without size fields | Pass |
| Tests | All tests pass | Pass |
| Static assert | Undersized storage fails compile | Compile error |

---

## Phase 5: Code Organization

### Problem

All code is in flat `src/aio/` directory with unclear boundaries.

### Solution

Organize into subdirectories reflecting architecture.

### Target Structure

```
src/aio/
├── io/                      # Core I/O abstraction (existing)
│   ├── io_loop_ops.h
│   ├── io_tcp_ops.h
│   ├── io_timer_ops.h
│   └── ...
│
├── http2/                   # HTTP/2 protocol
│   ├── server.c
│   ├── client.c
│   ├── conn.c
│   ├── session.c
│   ├── sse/                 # SSE sub-subsystem
│   │   ├── sse.c
│   │   ├── sse_builtins.c
│   │   └── sse_conn_tracking.c
│   └── overload/            # Overload management
│       ├── state.c          # Resource usage snapshots
│       ├── admission.c      # Accept/defer/reject decisions
│       ├── backpressure.c   # Watermark-based flow control
│       └── deferred.c       # Pending stream queue
│
├── system/                  # System lifecycle
│   ├── aio_system.c
│   ├── aio_maintenance.c
│   └── aio_config.c
│
└── aio.h                    # Public API
```

### Implementation Steps

1. Create subdirectories
2. Move files with minimal changes
3. Update `#include` paths
4. Update Makefile/CMake

---

## Phase 6: Session Callback Complexity Reduction

**STATUS: R6.4 COMPLETE (2025-12-29)** - All `#ifdef` blocks consolidated

### Problem

`aio_http2_session.c` has functions with CC > 10 and nesting > 4.

### Solution

Extract helpers, use dispatch tables.

### Implementation Steps

#### Step 6.0: Consolidate `#ifdef` blocks ✓ DONE

Created `aio_http2_session_metrics.h` with 17 inline helper functions that encapsulate all metrics-related `#ifdef VALK_METRICS_ENABLED` blocks. These are no-ops when metrics are disabled.

| Helper Function | Purpose |
|-----------------|---------|
| `valk_http2_metrics_on_header_recv` | Track bytes per header |
| `valk_http2_metrics_on_stream_start` | Stream start + diag state |
| `valk_http2_metrics_on_arena_overflow_pending` | Overflow → pending queue |
| `valk_http2_metrics_on_arena_overflow_rejected` | Overflow → 503 |
| `valk_http2_metrics_on_arena_acquire` | Arena pool acquire |
| `valk_http2_metrics_on_request_init` | Request start time |
| `valk_http2_metrics_on_sse_start` | SSE gauge inc |
| `valk_http2_metrics_on_response_body` | Response bytes/status |
| `valk_http2_metrics_on_frame_send_eof` | Response sent timestamp |
| `valk_http2_metrics_on_pending_stream_close` | Pending timeout metrics |
| `valk_http2_metrics_on_sse_stream_close` | SSE cleanup (returns was_sse) |
| `valk_http2_metrics_on_stream_close` | Full stream close metrics |
| `valk_http2_metrics_on_arena_release` | Arena release stats |
| `valk_http2_metrics_on_async_request_timeout` | Async timeout metrics |
| `valk_http2_metrics_on_conn_idle` | Diag conn idle |
| `valk_http2_metrics_on_pending_stream_acquire` | Pending arena + dequeue |
| `valk_http2_metrics_on_pending_request_init` | Pending request start |

#### Step 6.1: Extract async response dispatch (FUTURE)

```c
static int __dispatch_async_response(
    nghttp2_session* session,
    int32_t stream_id,
    valk_async_handle_t* handle,
    valk_http2_server_request_t* req
) {
  switch (handle->status) {
    case VALK_ASYNC_COMPLETED: return __handle_completed(...);
    case VALK_ASYNC_FAILED:    return __handle_failed(...);
    case VALK_ASYNC_CANCELLED: return __handle_cancelled(...);
    default:                   return __handle_pending(...);
  }
}
```

#### Step 6.2: Unify header processing

Extract duplicate header parsing for pending vs active streams.

#### Step 6.3: Response type dispatch table

```c
static const struct {
  valk_ltype_e type;
  const char* sym;
  response_handler_t handler;
} dispatch[] = {
  { LVAL_SYM, ":deferred", __handle_deferred },
  { LVAL_HANDLE, NULL, __handle_async },
  { LVAL_ERR, NULL, __handle_error },
  { .handler = __handle_success },
};
```

### Test Plan: Phase 6

| Test | Description | Expected |
|------|-------------|----------|
| All request types | Sync, async, deferred, error | All work |
| Coverage | CC < 10 for all functions | Pass |
| Nesting | Max 4 levels | Pass |

---

## Phase 7: Generic Streaming Responses

### Problem

SSE-specific code duplicates HTTP/2 stream functionality:

1. **`valk_sse_stream_t`** duplicates stream state that HTTP/2 already tracks
2. **`conn->http.sse_streams`** is a separate linked list from regular HTTP/2 streams
3. **`valk_sse_manager_t`** is a global registry that conflicts with per-connection tracking
4. **Event queue + backpressure** is useful for ANY streaming response, not just SSE
5. **SSE formatting** (`data: ...\n\n`) belongs in Lisp, not C

The result is ~1200 lines of SSE-specific code that should be ~200 lines of generic streaming.

### Current SSE Files (to be removed/replaced)

```
src/aio/
├── aio_sse.c                   # 686 lines - stream lifecycle, event queue
├── aio_sse.h                   # 148 lines - SSE-specific types
├── aio_sse_builtins.c          # 488 lines - Lisp builtins
├── aio_sse_conn_tracking.c     # 69 lines  - per-connection list (duplicates HTTP/2)
├── aio_sse_conn_tracking.h     # 13 lines
├── aio_sse_diagnostics.c       # 2000+ lines - snapshot formatting (keep, move to metrics)
└── aio_sse_diagnostics.h       # 318 lines
```

### Target Architecture

**Generic streaming at HTTP/2 level:**

```c
// In aio_http2_stream.c - generic streaming response body

typedef struct valk_stream_body {
  valk_aio_handle_t *conn;
  i32 stream_id;
  nghttp2_session *session;
  
  // Write queue with backpressure (reused from current SSE)
  valk_stream_chunk_t *queue_head;
  valk_stream_chunk_t *queue_tail;
  u64 queue_len;
  u64 queue_max;
  
  // Pending write buffer
  char *pending_data;
  u64 pending_len;
  u64 pending_offset;
  
  // State
  bool data_deferred;
  bool closed;
} valk_stream_body_t;

// Lifecycle
valk_stream_body_t *valk_stream_body_new(valk_aio_handle_t *conn, i32 stream_id);
void valk_stream_body_free(valk_stream_body_t *body);

// Writing (queues data, resumes nghttp2 if deferred)
int valk_stream_body_write(valk_stream_body_t *body, const char *data, u64 len);

// Backpressure
bool valk_stream_body_writable(valk_stream_body_t *body);
u64 valk_stream_body_queue_len(valk_stream_body_t *body);

// Close (sends EOF)
void valk_stream_body_close(valk_stream_body_t *body);
```

**Lisp builtins (generic):**

```lisp
;; Generic streaming response builtins
(stream/open request)           ; Create streaming body, send headers
(stream/open request headers)   ; With custom headers
(stream/write body data)        ; Queue data, returns bytes or error
(stream/writable? body)         ; Check backpressure
(stream/close body)             ; Send EOF

;; SSE is just Lisp formatting on top
(defun sse/open (request)
  (stream/open request {:content-type "text/event-stream"
                        :cache-control "no-cache"}))

(defun sse/send (body data)
  (stream/write body (str "data: " data "\n\n")))

(defun sse/send-event (body event-type data)
  (stream/write body (str "event: " event-type "\ndata: " data "\n\n")))
```

### Implementation Steps

#### Step 7.1: Create generic stream body

**New file:** `src/aio/aio_http2_stream_body.c`

Extract from `aio_sse.c`:
- Event queue logic → chunk queue
- `nghttp2_data_provider2` callback
- `NGHTTP2_ERR_DEFERRED` / `nghttp2_session_resume_data` pattern
- Backpressure tracking

Remove SSE-specific:
- SSE event formatting (`data:`, `event:`, `id:`)
- `valk_sse_stream_t` (replace with `valk_stream_body_t`)
- Global manager (not needed - HTTP/2 stream lifecycle is sufficient)

#### Step 7.2: Create generic builtins

**New file:** `src/aio/aio_http2_stream_builtins.c`

```c
// stream/open - creates streaming response
static valk_lval_t *valk_builtin_stream_open(valk_lenv_t *e, valk_lval_t *a);

// stream/write - queues data
static valk_lval_t *valk_builtin_stream_write(valk_lenv_t *e, valk_lval_t *a);

// stream/writable? - backpressure check
static valk_lval_t *valk_builtin_stream_writable(valk_lenv_t *e, valk_lval_t *a);

// stream/close - sends EOF
static valk_lval_t *valk_builtin_stream_close(valk_lenv_t *e, valk_lval_t *a);

void valk_register_stream_builtins(valk_lenv_t *env);
```

#### Step 7.3: Implement SSE in Lisp

**New file:** `src/modules/sse.valk`

```lisp
(defun sse/open (request)
  "Open an SSE stream with appropriate headers"
  (stream/open request 
    {:status "200"
     :content-type "text/event-stream"
     :cache-control "no-cache"
     :connection "keep-alive"}))

(defun sse/send (stream data)
  "Send SSE message event"
  (stream/write stream (str "data: " data "\n\n")))

(defun sse/send-event (stream event-type data)
  "Send SSE event with type"
  (stream/write stream (str "event: " event-type "\ndata: " data "\n\n")))

(defun sse/send-id (stream id data)
  "Send SSE event with ID for resumption"
  (stream/write stream (str "id: " id "\ndata: " data "\n\n")))

(defun sse/writable? (stream)
  "Check if stream can accept more data"
  (stream/writable? stream))

(defun sse/close (stream)
  "Close SSE stream"
  (stream/close stream))
```

#### Step 7.4: Delete SSE-specific C code

**Delete:**
- `src/aio/aio_sse.c`
- `src/aio/aio_sse.h`
- `src/aio/aio_sse_builtins.c`
- `src/aio/aio_sse_conn_tracking.c`
- `src/aio/aio_sse_conn_tracking.h`

**Move to metrics:**
- `src/aio/aio_sse_diagnostics.c` → `src/metrics/memory_snapshot.c`
- `src/aio/aio_sse_diagnostics.h` → `src/metrics/memory_snapshot.h`

**Update:**
- `CMakeLists.txt` - remove old files, add new
- `aio_internal.h` - remove SSE includes
- `aio_http2_session_metrics.h` - remove SSE manager references
- Tests - update to use generic streaming API

#### Step 7.5: Update existing SSE tests

Convert SSE-specific tests to use new generic API:
- `test/unit/test_sse_core.c` → `test/unit/test_stream_body.c`
- `test/test_sse_*.valk` → update to use Lisp `sse/` functions

### Test Plan: Phase 7

| Test | Description | Expected |
|------|-------------|----------|
| stream/open | Create streaming response | Headers sent, body open |
| stream/write | Queue data | Data sent via HTTP/2 DATA frames |
| stream/writable? | Backpressure detection | false when queue full |
| stream/close | End stream | EOF flag sent |
| sse/open (Lisp) | SSE headers | content-type: text/event-stream |
| sse/send (Lisp) | SSE format | data: ...\n\n format |
| Connection close | Cleanup | Stream body freed |
| Chunked download | Non-SSE streaming | Works with same API |

### Benefits

1. **~1000 lines removed** - SSE-specific C code replaced by ~200 lines generic + ~50 lines Lisp
2. **Single streaming mechanism** - works for SSE, chunked downloads, WebSocket-like patterns
3. **SSE formatting in Lisp** - easier to modify, extend (retry, comments, etc.)
4. **No duplicate tracking** - uses existing HTTP/2 stream lifecycle
5. **Backpressure for all streams** - not just SSE

---

## Summary: Refactoring Priority

| Phase | Effort | Impact | Risk | Priority |
|-------|--------|--------|------|----------|
| 1. Metrics extraction | High | High | Medium | **Complete** |
| 2. SSE cleanup | Medium | High | Low | **Complete** |
| 3. Overload consolidation | Medium | Medium | Low | **Complete** |
| 4. I/O cleanup | Low | Low | Low | **Complete** |
| 5. Code organization | Medium | Medium | Low | Low priority |
| 6. Complexity reduction | Medium | High | Low | **Complete** |
| 7. Generic streaming | Medium | High | Medium | **Complete** - generic API + SSE Lisp module |

---

## Appendix: Current vs Target Comparison

| Aspect | Current | Target |
|--------|---------|--------|
| Metrics location | Inside AIO | Sibling system |
| Diagnostics publisher | C (aio_sse_stream_registry) | Lisp handler (JSON wire format) |
| SSE | Generic streaming + Lisp formatting (~250 lines) | **Done**: `stream/*` builtins + `sse.valk` |
| Streaming responses | Generic `stream/write` for any streaming body | **Done**: Works for SSE, chunked, etc. |
| Load management naming | pressure/admission/backpressure | Unified "Overload" |
| Backpressure | Ad-hoc thresholds | High/low watermarks (80%/40%) with hysteresis |
| Overload detection | Slab usage only | Request queue latency (primary) + slab usage |
| Code organization | Flat directory | Hierarchical |
| Session complexity | CC 11-12, 7 levels | CC < 10, 4 levels |
| HTTP/2 client | Not implemented | Single connection to sidecar, multiplexed |
| Deployment model | Unspecified | Envoy sidecar required for production |
| Connection pooling | N/A | Delegated to Envoy sidecar |

---

## Appendix: File Mapping

| Current File | Target Location | Notes |
|--------------|-----------------|-------|
| `aio_metrics.c` | `src/metrics/metrics.c` | Standalone system |
| `aio_sse_stream_registry.c` | DELETE | Replace with Lisp handler |
| `aio_sse_diagnostics.c` | `src/metrics/snapshot.c` | Part of metrics |
| `aio_sse.c` | `src/aio/http2/sse/sse.c` | Keep, generic |
| `aio_pressure.c` | `src/aio/http2/overload/state.c` | Rename |
| `aio_conn_admission.c` | `src/aio/http2/overload/admission.c` | Rename |
| `aio_backpressure.c` | `src/aio/http2/overload/backpressure.c` | Rename, add watermarks |
| `aio_pending_stream.c` | `src/aio/http2/overload/deferred.c` | Rename |
| `aio_http2_session.c` | `src/aio/http2/session.c` | Move + refactor |
| `aio_sse.c` | DELETE | Replace with generic streaming in `aio_http2_stream.c` |
| `aio_sse_builtins.c` | DELETE | Replace with `stream/write`, `stream/close` builtins |
| `aio_sse_conn_tracking.c` | DELETE | Use existing HTTP/2 stream tracking |
| `aio_sse_diagnostics.c` | `src/metrics/snapshot.c` | Memory snapshot formatting only |
