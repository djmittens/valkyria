# AIO Subsystem Refactoring Guide

This document defines the target architecture for Valkyria's I/O and networking subsystems, along with step-by-step refactoring tasks to achieve it.

---

## 🚨 RULES FOR AI AGENTS (MANDATORY)

**These rules exist because previous AI runs marked phases "complete" without doing the work.**

### Rule 1: No Phase May Be Marked Complete Without ALL Verifications Passing

Each phase has TWO types of verification:
1. **Negative verification**: Old pattern is gone (e.g., no direct `http.state =` assignments)
2. **Positive verification**: New pattern exists and is used (e.g., `valk_conn_transition` called 16+ times)

**BOTH must pass.** Just removing old code is not completion.

### Rule 2: No Cancelling or Descoping

You may NOT:
- Mark a phase as "cancelled" or "out of scope"
- Reduce the requirements (e.g., "only 4 states needed instead of 8")
- Claim the current implementation is "good enough"
- Skip verification steps

If a phase is too hard, say so and stop. Do not claim completion.

### Rule 3: Tests Must Pass

After any change:
```bash
make build && make test
```
If tests fail, fix them. Do not mark complete with failing tests.

### Rule 4: Verification Is Auditable

Every verification command is designed to be run by a human. If you claim a phase is complete, the human will run the verification commands. If they don't pass, you lied.

### Rule 5: The Functional Requirements Are Non-Negotiable

These requirements from the Formal Requirements section MUST be met:
- **R3.6**: 8 connection states with centralized FSM
- **R3.7**: Two-phase GOAWAY graceful shutdown  
- **R6.1**: Cyclomatic complexity < 10 for all functions
- **R6.2**: Nesting depth < 4 levels

"Partial" completion of these requirements means "not complete".

---

## ⚠️ CRITICAL: ROOT CAUSE ANALYSIS (2026-01-01)

**THIS SECTION MUST BE READ FIRST. DO NOT SKIP.**

Previous refactoring efforts completed organizational tasks (file moves, renames, `#ifdef` consolidation) but **DID NOT address the architectural root causes** of HTTP/2 connection, session, and request bugs. The bugs persist because:

### The Three Root Causes of HTTP/2 Bugs

#### Root Cause 1: No Centralized State Machine

**Current state:** 4 connection states (`INIT`, `ESTABLISHED`, `CLOSING`, `CLOSED`) with **16 scattered transition points** across 6 files:
- `aio_http2_conn.c` - 6 transitions
- `aio_http2_client.c` - 5 transitions  
- `aio_http2_server.c` - 2 transitions
- `aio_maintenance.c` - 2 transitions
- `aio_uv.c` - 1 transition

**Required state (per R3.6):** 8 states with centralized transition function:
```
INIT → HANDSHAKING → ESTABLISHED → GOAWAY_SENT → DRAINING → CLOSING → CLOSED
                                                                    ↑
ERROR ──────────────────────────────────────────────────────────────┘
```

**Why this causes bugs:** State transitions happen ad-hoc with repeated boilerplate. No single place validates transitions. Race conditions between cleanup paths. No graceful shutdown (two-phase GOAWAY per R3.7).

**Evidence:**
```bash
$ grep -rn "http.state = " src/aio --include="*.c" | wc -l
16  # Should be 1 (the transition function)
```

#### Root Cause 2: Implicit Arena Ownership via Nullable Pointers

**Current state:** Arena ownership transfers implicitly by setting pointers to `nullptr`:

| Location | What Happens |
|----------|--------------|
| `aio_http2_session.c:245` | Request gets arena: `req->arena_slab_item = arena_item` |
| `aio_http2_session.c:731` | Transfer to async ctx: `http_ctx->arena_slab_item = req->arena_slab_item` |
| `aio_http2_session.c:735` | Clear request's copy: `req->arena_slab_item = nullptr` |
| `aio_async.c:70` | Transfer back: `stream_req->arena_slab_item = http->arena_slab_item` |
| `aio_async.c:72` | Clear async ctx: `http->arena_slab_item = nullptr` |
| `aio_http2_conn.c:543` | Cleanup sets: `req->arena_slab_item = nullptr` |

**Why this causes bugs:** 
- 11 assignment sites with no type system enforcement
- Easy to forget to clear source after transfer → double-free
- Easy to use after clearing → use-after-free
- Defensive cleanup in `aio_http2_conn.c:519-559` exists because normal paths leak

**Evidence:** The disconnect handler has a "leaked arenas" loop that shouldn't exist if cleanup worked:
```c
// aio_http2_conn.c:519-559
u64 leaked_arenas = 0;
while (slot != UINT32_MAX) {
  // ... release each leaked arena
  leaked_arenas++;
}
if (leaked_arenas > 0) {
  VALK_WARN("Released %zu leaked stream arenas on disconnect", leaked_arenas);
}
```

#### Root Cause 3: Tagged Pointer Anti-Pattern for Stream User Data

**Current state:** nghttp2 stream user data uses pointer tagging to distinguish types:
```c
// aio_internal.h:420-428
static inline bool __is_pending_stream(void *user_data) {
  return user_data && ((uptr)user_data & (1ULL << 63));
}
```

Stream user data can be:
1. `nullptr` - no data
2. `valk_http2_server_request_t*` - normal request (high bit clear)
3. `valk_pending_stream_t*` - pending stream (high bit set)

**Why this causes bugs:**
- 8 call sites must check `__is_pending_stream()` before casting
- Forgetting the check → crash or memory corruption
- Platform-dependent (assumes 64-bit with unused high bit)
- No compiler help - it's just `void*`

**Evidence:**
```bash
$ grep -rn "__is_pending_stream\|__get_pending_stream" src/aio --include="*.c" | grep -v define | wc -l
8  # Each is a potential bug if check is forgotten
```

### What Previous Refactoring Actually Did (vs What Was Claimed)

| Phase | Claimed | Actually Done | Root Cause Addressed? |
|-------|---------|---------------|----------------------|
| 1. Metrics | ✅ Complete | ✅ Moved to `metrics_v2` | N/A |
| 2. SSE Cleanup | ✅ Complete | ✅ Deleted old registry | N/A |
| 3. Overload | ✅ Complete | ✅ Renamed files | N/A |
| 4. I/O Cleanup | ✅ Complete | ✅ Removed size fields | N/A |
| 5. Organization | ✅ Complete | ✅ Directory restructure | N/A |
| 6. Complexity | ✅ Complete | ⚠️ PARTIAL - only `#ifdef` consolidation | **NO** - CC still >20, nesting still >4 |
| 7. Streaming | ✅ Complete | ✅ Generic `stream/` API | N/A |

**Phase 6 was marked complete but only addressed R6.4 (`#ifdef` blocks). It did NOT address:**
- R6.1: Cyclomatic complexity < 10 (`on_frame_recv_callback` is CC ≈ 25)
- R6.2: Nesting depth < 4 (still 5-6 levels deep)
- R3.6: Connection state machine (not implemented)
- R3.7: Two-phase GOAWAY (not implemented)

### Dead Code Still Present

**`http2_ops_nghttp2.c`**: 297 lines of abstraction layer that is **never used** in the main code path.
```bash
$ grep -r "http2_ops" src/aio --include="*.c" | grep -v "http2_ops_nghttp2.c" | grep -v "http2_ops_test.c"
src/aio/aio_ops.c:  .http2 = &valk_http2_ops_nghttp2,  # Registered but never called
src/aio/aio_ops.c:  .http2 = &valk_http2_ops_test,
```

The main code calls nghttp2 directly (e.g., `nghttp2_session_mem_recv2` in `aio_http2_conn.c:289`).

---

## Mandatory Next Steps (DO NOT SKIP)

Before claiming any phase is "complete", the following MUST be done:

### Phase 8: State Machine Implementation (REQUIRED)

**Files to create:**
- `src/aio/http2/aio_http2_conn_fsm.c` - State machine implementation
- `src/aio/http2/aio_http2_conn_fsm.h` - State/event enums, transition function

**Implementation:**
1. Add states: `HANDSHAKING`, `GOAWAY_SENT`, `DRAINING`, `ERROR`
2. Create `valk_conn_transition(conn, event)` function
3. Replace ALL 16 `conn->http.state = X` with `valk_conn_transition(conn, EVENT_Y)`
4. Add `on_enter`/`on_exit` callbacks for cleanup actions

**Verification (ALL must pass):**
```bash
# NEGATIVE: No direct state assignments outside FSM (must return 0)
grep -rn "http\.state = " src/aio --include="*.c" | grep -v "conn_fsm.c" | wc -l

# POSITIVE: FSM files exist
test -f src/aio/http2/aio_http2_conn_fsm.c && echo "FSM impl exists"
test -f src/aio/http2/aio_http2_conn_fsm.h && echo "FSM header exists"

# POSITIVE: All 8 states defined (must return 8)
grep -c "VALK_CONN_" src/aio/http2/aio_http2_conn_fsm.h | grep -E "^8$"

# POSITIVE: Transition function exists and is called (must return >= 16)
grep -rn "valk_conn_transition" src/aio --include="*.c" | wc -l

# POSITIVE: Two-phase GOAWAY implemented (must find both)
grep -q "VALK_CONN_GOAWAY_SENT" src/aio/http2/aio_http2_conn_fsm.h && echo "GOAWAY_SENT state exists"
grep -q "VALK_CONN_DRAINING" src/aio/http2/aio_http2_conn_fsm.h && echo "DRAINING state exists"

# POSITIVE: on_enter callbacks for graceful shutdown
grep -q "on_enter_goaway_sent\|on_enter.*goaway" src/aio/http2/aio_http2_conn_fsm.c && echo "GOAWAY entry action exists"
grep -q "on_enter_draining\|on_enter.*drain" src/aio/http2/aio_http2_conn_fsm.c && echo "DRAINING entry action exists"

# FUNCTIONAL: Tests pass
make build && make test
```

### Phase 9: Arena Ownership Tokens (REQUIRED)

**Replace implicit transfers with explicit tokens:**

```c
// BEFORE (bug-prone)
http_ctx->arena_slab_item = req->arena_slab_item;
req->arena_slab_item = nullptr;

// AFTER (compiler-enforced)
valk_arena_token_t token = valk_arena_take(&req->arena);  // Clears source
valk_arena_give(&http_ctx->arena, token);                  // Sets destination
```

**Files to modify:**
- `aio_internal.h` - Add `valk_arena_token_t` type
- `aio_http2_session.c` - Use token transfers
- `aio_async.c` - Use token transfers

**Verification (ALL must pass):**
```bash
# NEGATIVE: No direct arena_slab_item assignments (must return 0)
grep -rn "arena_slab_item\s*=" src/aio --include="*.c" | wc -l

# POSITIVE: Arena token type exists
grep -q "typedef.*valk_arena_token_t\|struct valk_arena_token" src/aio/aio_internal.h && echo "Token type exists"

# POSITIVE: Arena ref type exists in request struct
grep -q "valk_arena_ref_t\s*arena" src/aio/aio_internal.h && echo "Arena ref in request"

# POSITIVE: Token API functions exist and are used
grep -c "valk_arena_take\|valk_arena_give\|valk_arena_release" src/aio/http2/aio_http2_session.c | grep -E "^[6-9]|^[0-9]{2}"

# POSITIVE: The "leaked arenas" defensive loop is REMOVED (we don't need it if ownership is correct)
grep -q "leaked_arenas\|leaked.*arena" src/aio/http2/aio_http2_conn.c && echo "FAIL: Leaked arena hack still exists" || echo "PASS: No leaked arena hack"

# FUNCTIONAL: Tests pass
make build && make test
```

### Phase 10: Stream User Data Type Safety (REQUIRED)

**Replace tagged pointers with discriminated union:**

```c
// BEFORE (crash-prone)
void *stream_data = nghttp2_session_get_stream_user_data(session, stream_id);
if (__is_pending_stream(stream_data)) {
  pending_stream_t *ps = __get_pending_stream(stream_data);
  // ...
}

// AFTER (type-safe)
valk_stream_data_t data = valk_stream_get_data(session, stream_id);
switch (data.type) {
  case STREAM_DATA_NONE: break;
  case STREAM_DATA_REQUEST: handle_request(data.request); break;
  case STREAM_DATA_PENDING: handle_pending(data.pending); break;
}
```

**Files to modify:**
- `aio_internal.h` - Add `valk_stream_data_t` union
- `aio_http2_session.c` - Replace all 8 tagged pointer sites

**Verification (ALL must pass):**
```bash
# NEGATIVE: No tagged pointer usage (must return 0)
grep -rn "__is_pending_stream\|__get_pending_stream" src/aio --include="*.c" | grep -v "define\|inline" | wc -l

# POSITIVE: Discriminated union type exists
grep -q "STREAM_DATA_NONE\|STREAM_DATA_REQUEST\|STREAM_DATA_PENDING" src/aio/aio_internal.h && echo "Stream data enum exists"
grep -q "valk_stream_data_t" src/aio/aio_internal.h && echo "Stream data type exists"

# POSITIVE: Type-safe accessor is used (must return >= 8)
grep -c "valk_stream_get_data" src/aio/http2/aio_http2_session.c | grep -E "^[8-9]|^[0-9]{2}"

# POSITIVE: Switch statements on stream data type exist
grep -c "case STREAM_DATA_" src/aio/http2/aio_http2_session.c | grep -E "^[0-9]+"

# FUNCTIONAL: Tests pass
make build && make test
```

### Phase 11: Complexity Reduction (REQUIRED)

**Extract from `valk_http2_on_frame_recv_callback` (currently ~175 lines → target <50 lines):**

```c
// Create these helper functions:
static int handle_goaway_frame(conn, frame);
static int handle_rst_stream_frame(conn, frame);
static int handle_pending_stream(conn, stream_id, pending);
static int invoke_handler_sync(conn, req, handler, env);
static int invoke_handler_async(conn, req, handle, http_ctx);
static int send_error_response(session, stream_id, status, message, arena);
```

**Verification (ALL must pass):**
```bash
# NEGATIVE: on_frame_recv_callback is small (must return number < 50)
# This counts lines from function start to next function
awk '/^int valk_http2_on_frame_recv_callback/,/^(int|static int|void|static void) [a-z_]+\(/' \
  src/aio/http2/aio_http2_session.c | head -n -1 | wc -l

# POSITIVE: Helper functions exist (must find all 4)
grep -q "static int handle_goaway_frame" src/aio/http2/aio_http2_session.c && echo "handle_goaway_frame exists"
grep -q "static int handle_rst_stream_frame" src/aio/http2/aio_http2_session.c && echo "handle_rst_stream_frame exists"
grep -q "static int handle_headers_frame\|static int handle_request_headers" src/aio/http2/aio_http2_session.c && echo "handle_headers_frame exists"
grep -q "static int.*send_error_response\|static void.*send_error_response" src/aio/http2/aio_http2_session.c && echo "send_error_response exists"

# POSITIVE: Helper functions are called from on_frame_recv_callback
grep -A50 "int valk_http2_on_frame_recv_callback" src/aio/http2/aio_http2_session.c | grep -q "handle_goaway_frame\|handle_rst_stream_frame\|handle_headers_frame"

# POSITIVE: No deep nesting in main callback (max 4 levels - count leading spaces)
awk '/^int valk_http2_on_frame_recv_callback/,/^(int|static|void) [a-z]/' src/aio/http2/aio_http2_session.c | \
  grep -E "^\s{16,}" | wc -l
# Must return 0 (no lines indented 16+ spaces = 4+ levels at 4-space indent, or 8+ at 2-space)

# FUNCTIONAL: Tests pass
make build && make test
```

### Phase 12: Dead Code Removal (REQUIRED)

**Delete unused `http2_ops` abstraction:**
- `src/aio/http2/http2_ops.h` - DELETE or migrate all calls to use it
- `src/aio/http2/http2_ops_nghttp2.c` - DELETE or migrate
- `src/aio/http2/http2_ops_test.c` - DELETE or migrate

**Decision required:** Either delete 297 lines of dead code, OR migrate all nghttp2 calls to use the abstraction (enables testing).

**Verification (ALL must pass):**
```bash
# Option A chosen: Files deleted
test ! -f src/aio/http2/http2_ops.h && echo "http2_ops.h deleted"
test ! -f src/aio/http2/http2_ops_nghttp2.c && echo "http2_ops_nghttp2.c deleted"  
test ! -f src/aio/http2/http2_ops_test.c && echo "http2_ops_test.c deleted"

# OR Option B chosen: Abstraction is actually used
# (must return >= 20 - every nghttp2 call goes through ops)
grep -rn "ops->http2->" src/aio --include="*.c" | wc -l

# No direct nghttp2 calls outside the ops implementation (must return 0)
grep -rn "nghttp2_session_\|nghttp2_submit_" src/aio --include="*.c" | grep -v "http2_ops_nghttp2.c" | wc -l

# FUNCTIONAL: Tests pass
make build && make test
```

---

## Master Verification Script

Run this script to verify all phases. **ALL checks must pass** before any phase can be marked complete.

```bash
#!/bin/bash
# Save as: scripts/verify_refactoring.sh
# Run from repo root: ./scripts/verify_refactoring.sh

set -e
FAIL=0

echo "=== Phase 8: State Machine ==="

echo -n "  [NEG] No direct state assignments: "
COUNT=$(grep -rn "http\.state = " src/aio --include="*.c" | grep -v "conn_fsm.c" | wc -l | tr -d ' ')
if [ "$COUNT" -eq 0 ]; then echo "PASS"; else echo "FAIL ($COUNT found)"; FAIL=1; fi

echo -n "  [POS] FSM implementation exists: "
if [ -f src/aio/http2/aio_http2_conn_fsm.c ]; then echo "PASS"; else echo "FAIL"; FAIL=1; fi

echo -n "  [POS] 8 states defined: "
COUNT=$(grep -c "VALK_CONN_[A-Z]" src/aio/http2/aio_http2_conn_fsm.h 2>/dev/null || echo 0)
if [ "$COUNT" -ge 8 ]; then echo "PASS ($COUNT states)"; else echo "FAIL ($COUNT states, need 8)"; FAIL=1; fi

echo -n "  [POS] Transition function called: "
COUNT=$(grep -rn "valk_conn_transition" src/aio --include="*.c" | wc -l | tr -d ' ')
if [ "$COUNT" -ge 16 ]; then echo "PASS ($COUNT calls)"; else echo "FAIL ($COUNT calls, need 16)"; FAIL=1; fi

echo -n "  [POS] GOAWAY_SENT state exists: "
grep -q "VALK_CONN_GOAWAY_SENT" src/aio/http2/aio_http2_conn_fsm.h 2>/dev/null && echo "PASS" || { echo "FAIL"; FAIL=1; }

echo -n "  [POS] DRAINING state exists: "
grep -q "VALK_CONN_DRAINING" src/aio/http2/aio_http2_conn_fsm.h 2>/dev/null && echo "PASS" || { echo "FAIL"; FAIL=1; }

echo ""
echo "=== Phase 9: Arena Ownership ==="

echo -n "  [NEG] No direct arena_slab_item assignments: "
COUNT=$(grep -rn "arena_slab_item\s*=" src/aio --include="*.c" | wc -l | tr -d ' ')
if [ "$COUNT" -eq 0 ]; then echo "PASS"; else echo "FAIL ($COUNT found)"; FAIL=1; fi

echo -n "  [POS] Arena token type exists: "
grep -q "valk_arena_token_t\|valk_arena_ref_t" src/aio/aio_internal.h && echo "PASS" || { echo "FAIL"; FAIL=1; }

echo -n "  [POS] Token API used: "
COUNT=$(grep -c "valk_arena_take\|valk_arena_give" src/aio/http2/aio_http2_session.c 2>/dev/null || echo 0)
if [ "$COUNT" -ge 6 ]; then echo "PASS ($COUNT uses)"; else echo "FAIL ($COUNT uses, need 6)"; FAIL=1; fi

echo -n "  [NEG] Leaked arena hack removed: "
grep -q "leaked_arenas" src/aio/http2/aio_http2_conn.c && { echo "FAIL (still exists)"; FAIL=1; } || echo "PASS"

echo ""
echo "=== Phase 10: Stream Data Type Safety ==="

echo -n "  [NEG] No tagged pointer usage: "
COUNT=$(grep -rn "__is_pending_stream\|__get_pending_stream" src/aio --include="*.c" | grep -v "define\|inline" | wc -l | tr -d ' ')
if [ "$COUNT" -eq 0 ]; then echo "PASS"; else echo "FAIL ($COUNT found)"; FAIL=1; fi

echo -n "  [POS] Stream data enum exists: "
grep -q "STREAM_DATA_NONE\|STREAM_DATA_REQUEST" src/aio/aio_internal.h && echo "PASS" || { echo "FAIL"; FAIL=1; }

echo -n "  [POS] Type-safe accessor used: "
COUNT=$(grep -c "valk_stream_get_data" src/aio/http2/aio_http2_session.c 2>/dev/null || echo 0)
if [ "$COUNT" -ge 8 ]; then echo "PASS ($COUNT uses)"; else echo "FAIL ($COUNT uses, need 8)"; FAIL=1; fi

echo ""
echo "=== Phase 11: Complexity Reduction ==="

echo -n "  [NEG] on_frame_recv_callback < 50 lines: "
COUNT=$(awk '/^int valk_http2_on_frame_recv_callback/,/^(int|static int|void|static void) [a-z_]+\(/' \
  src/aio/http2/aio_http2_session.c | head -n -1 | wc -l | tr -d ' ')
if [ "$COUNT" -lt 50 ]; then echo "PASS ($COUNT lines)"; else echo "FAIL ($COUNT lines)"; FAIL=1; fi

echo -n "  [POS] Helper functions exist: "
HELPERS=0
grep -q "static int handle_goaway_frame" src/aio/http2/aio_http2_session.c && HELPERS=$((HELPERS+1))
grep -q "static int handle_rst_stream" src/aio/http2/aio_http2_session.c && HELPERS=$((HELPERS+1))
grep -q "static int handle_headers_frame\|static int handle_request" src/aio/http2/aio_http2_session.c && HELPERS=$((HELPERS+1))
if [ "$HELPERS" -ge 3 ]; then echo "PASS ($HELPERS found)"; else echo "FAIL ($HELPERS found, need 3)"; FAIL=1; fi

echo ""
echo "=== Phase 12: Dead Code Removal ==="

echo -n "  [CHK] http2_ops files status: "
if [ ! -f src/aio/http2/http2_ops_nghttp2.c ]; then
  echo "DELETED (Option A)"
else
  COUNT=$(grep -rn "ops->http2->" src/aio --include="*.c" | wc -l | tr -d ' ')
  if [ "$COUNT" -ge 20 ]; then
    echo "USED (Option B, $COUNT calls)"
  else
    echo "FAIL (exists but unused)"
    FAIL=1
  fi
fi

echo ""
echo "=== Functional Tests ==="
echo -n "  Building and testing: "
if make build >/dev/null 2>&1 && make test >/dev/null 2>&1; then
  echo "PASS"
else
  echo "FAIL"
  FAIL=1
fi

echo ""
if [ "$FAIL" -eq 0 ]; then
  echo "✅ ALL VERIFICATIONS PASSED"
  exit 0
else
  echo "❌ SOME VERIFICATIONS FAILED"
  exit 1
fi
```

---

## Implementation Progress

| Phase | Status | Notes |
|-------|--------|-------|
| Phase 1: Metrics Extraction | **Complete** | `metrics_v2` is standalone |
| Phase 2: SSE Cleanup | **Complete** | Old registry deleted |
| Phase 3: Overload Consolidation | **Complete** | Files renamed to `aio_overload_*` |
| Phase 4: I/O Cleanup | **Complete** | Size fields removed from vtables |
| Phase 5: Code Organization | **Complete** | Directory restructure done |
| Phase 6: Complexity Reduction | **PARTIAL** | Only `#ifdef` consolidation done; CC/nesting NOT addressed |
| Phase 7: Generic Streaming | **Complete** | `stream/` API created |
| Phase 8: State Machine | **NOT STARTED** | 16 scattered transitions, no FSM |
| Phase 9: Arena Ownership | **NOT STARTED** | 11 implicit transfer sites |
| Phase 10: Stream Data Safety | **NOT STARTED** | 8 tagged pointer sites |
| Phase 11: Function Extraction | **NOT STARTED** | `on_frame_recv_callback` CC ≈ 25 |
| Phase 12: Dead Code Removal | **NOT STARTED** | 297 lines unused `http2_ops` |

### Recent Changes (2025-12-31)

13. **Phase 5 Complete - Directory Restructure (2025-12-31)**: Reorganized AIO subsystem into logical subdirectories:
    - **CREATED**: `src/aio/system/` - System lifecycle files (aio_system, aio_task, aio_maintenance, aio_chase_lev, aio_task_queue)
    - **CREATED**: `src/aio/http2/` - HTTP/2 protocol files (aio_http2_*, aio_ssl, aio_conn_io, aio_body_buffer)
    - **CREATED**: `src/aio/http2/overload/` - Overload management (aio_overload_state, aio_overload_admission, aio_overload_backpressure, aio_overload_deferred)
    - **CREATED**: `src/aio/http2/stream/` - Streaming responses (aio_stream_body, aio_stream_body_conn, aio_stream_builtins)
    - **UPDATED**: CMakeLists.txt with new paths and include directories
    - **UPDATED**: aio_internal.h with new include paths
    - **UPDATED**: Test files with corrected header paths
    - **Benefit**: Clear separation of concerns matching target architecture

12. **Moved AIO Diagnostics Builtins (2025-12-31)**: Cleaned up metrics_builtins.c by moving AIO-specific builtins to proper location:
    - **CREATED**: `aio_diagnostics_builtins.c/h` - new file for `aio/slab-buckets` and `aio/diagnostics-state-json` builtins
    - **REMOVED**: AIO builtins from `metrics_builtins.c` and its `#include "aio/aio.h"` dependency
    - **UPDATED**: `aio_internal.h` to include new header, `parser.c` to register new builtins
    - **Benefit**: Metrics system no longer depends on AIO headers

11. **GC Rooting for Async Callbacks (2025-12-31)**: Replaced deep-copy approach with GC rooting for async callback storage. This is the correct solution to the callback corruption bugs.
    - **REMOVED**: `valk_aio_deep_copy_callback()` - deep copying was fundamentally flawed due to race conditions with GC
    - **FIX**: `aio_combinators.c` - `aio/schedule` and `aio/interval` now use `valk_gc_add_global_root()` to protect callbacks
    - **FIX**: `aio_http2_client.c` - HTTP client requests now root callbacks and headers during async operations
    - **FIX**: `aio_stream_builtins.c` - `stream/on-drain` and new `stream/on-close` use GC roots
    - **FIX**: `aio_stream_body.c` - Properly invokes `lisp_on_drain` and `lisp_on_close` callbacks; cleans up roots on stream close
    - **FIX**: `parser.c` - Rewrote `valk_lenv_copy()` to single-pass dynamic array approach to avoid TOCTOU bugs
    - **Pattern**: Store original callback reference + `valk_gc_add_global_root(&ctx->callback)`, cleanup with `valk_gc_remove_global_root(&ctx->callback)` before freeing context
    - **Result**: All async callback tests pass; no more crashes from corrupted environments

10. **Fixed Allocator Mismatch Bugs (2025-12-31)** (SUPERSEDED by #11): Initial attempt using deep copying - later replaced with GC rooting as the correct solution.

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

- [x] Metrics System core (`metrics_v2.c/h`, `metrics_delta.c/h`) has no AIO dependencies
- [x] AIO has no `#include "metrics.h"` (uses `metrics_v2.h` for hooks in `aio_http2_session_metrics.h`)
- [x] `aio_sse_stream_registry.c` deleted
- [x] Diagnostics works via Lisp handler (`src/modules/aio/metrics-stream.valk`)
- [x] All metrics still collected (no regression)
- [x] `aio/slab-buckets` and `aio/diagnostics-state-json` moved from `metrics_builtins.c` to `aio_diagnostics_builtins.c`

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

**STATUS: COMPLETE (2025-12-31)**

### Problem

All code was in flat `src/aio/` directory with unclear boundaries.

### Solution

Organized into subdirectories reflecting architecture.

### Implemented Structure

```
src/aio/
├── io/                      # Core I/O abstraction (unchanged)
│   ├── io_loop_ops.h
│   ├── io_tcp_ops.h
│   ├── io_timer_ops.h
│   └── ...
│
├── http2/                   # HTTP/2 protocol ✓
│   ├── aio_http2_conn.c/h
│   ├── aio_http2_server.c/h
│   ├── aio_http2_client.c/h
│   ├── aio_http2_session.c/h
│   ├── aio_ssl.c/h
│   ├── aio_conn_io.c/h
│   ├── aio_body_buffer.c/h
│   ├── http2_ops_nghttp2.c
│   ├── http2_ops_test.c
│   ├── overload/            # Overload management ✓
│   │   ├── aio_overload_state.c/h
│   │   ├── aio_overload_admission.c/h
│   │   ├── aio_overload_backpressure.c/h
│   │   └── aio_overload_deferred.c/h
│   └── stream/              # Streaming responses ✓
│       ├── aio_stream_body.c/h
│       ├── aio_stream_body_conn.c
│       └── aio_stream_builtins.c
│
├── system/                  # System lifecycle ✓
│   ├── aio_system.c/h
│   ├── aio_maintenance.c/h
│   ├── aio_task.c/h
│   ├── aio_task_queue.c
│   └── aio_chase_lev.c/h
│
├── aio.h                    # Public API
├── aio_internal.h           # Internal types/includes
├── aio_alloc.c/h            # Memory allocation
├── aio_async.c/h            # Async handle management
├── aio_combinators.c        # Timer/interval builtins
├── aio_diagnostics_builtins.c/h  # AIO-specific builtins
├── aio_http_builtins.c      # HTTP builtins
├── aio_metrics.c/h          # AIO metrics (when VALK_METRICS enabled)
├── aio_ops.c/h              # Ops abstraction
├── aio_owner.c/h            # Owner tracking
├── aio_timer.c/h            # Timer utilities
├── aio_types.h              # Type definitions
└── aio_uv.c                 # libuv integration
```

### Implementation Steps ✓

1. Create subdirectories ✓
2. Move files with git mv to preserve history ✓
3. Update `#include` paths in aio_internal.h ✓
4. Update CMakeLists.txt with new source paths ✓
5. Add subdirectories to include path for tests ✓
6. Update test file includes ✓
7. Verify build and all tests pass ✓

### Test Plan: Phase 5 ✓

| Test | Description | Expected | Result |
|------|-------------|----------|--------|
| Build | All sources compile | Pass | ✓ |
| Tests | All C and Valk tests pass | Pass | ✓ |
| Lint | clang-tidy passes | Pass | ✓ |

---

## Phase 6: Session Callback Complexity Reduction

**STATUS: PARTIAL** - Only Step 6.0 (`#ifdef` consolidation) done. Steps 6.1-6.3 NOT DONE.

> ⚠️ **WARNING**: This phase was previously marked "Complete" but that was incorrect.
> Only the `#ifdef` consolidation was done. The actual complexity reduction (function
> extraction, dispatch tables) was marked "FUTURE" and never implemented.
>
> **Current state of `aio_http2_session.c`:**
> - 964 lines total
> - `valk_http2_on_frame_recv_callback`: ~175 lines, CC ≈ 25, nesting 5-6 levels
> - Requirements R6.1 (CC < 10) and R6.2 (nesting < 4): **NOT MET**

### Problem

`aio_http2_session.c` has functions with CC > 10 and nesting > 4.

### Solution

Extract helpers, use dispatch tables.

### Implementation Steps

#### Step 6.0: Consolidate `#ifdef` blocks ✅ DONE

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

#### Step 6.1: Extract async response dispatch ❌ NOT DONE

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

#### Step 6.2: Unify header processing ❌ NOT DONE

Extract duplicate header parsing for pending vs active streams.

#### Step 6.3: Response type dispatch table ❌ NOT DONE

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

| Phase | Effort | Impact | Risk | Status |
|-------|--------|--------|------|--------|
| 1. Metrics extraction | High | High | Medium | ✅ Complete |
| 2. SSE cleanup | Medium | High | Low | ✅ Complete |
| 3. Overload consolidation | Medium | Medium | Low | ✅ Complete |
| 4. I/O cleanup | Low | Low | Low | ✅ Complete |
| 5. Code organization | Medium | Medium | Low | ✅ Complete |
| 6. Complexity reduction | Medium | High | Low | ⚠️ PARTIAL - only `#ifdef` done |
| 7. Generic streaming | Medium | High | Medium | ✅ Complete |
| **8. State Machine** | **High** | **Critical** | **Medium** | ❌ NOT STARTED |
| **9. Arena Ownership** | **Medium** | **Critical** | **Medium** | ❌ NOT STARTED |
| **10. Stream Data Safety** | **Medium** | **High** | **Low** | ❌ NOT STARTED |
| **11. Function Extraction** | **Medium** | **High** | **Low** | ❌ NOT STARTED |
| **12. Dead Code Removal** | **Low** | **Medium** | **Low** | ❌ NOT STARTED |

---

## Phase 8: Connection State Machine (REQUIRED - ROOT CAUSE FIX)

**STATUS: NOT STARTED**

> ⚠️ This phase addresses **Root Cause 1** from the critical section above.
> HTTP/2 bugs will persist until this is implemented.

### Problem

Connection state transitions are scattered across 6 files with 16 assignment sites:
- No validation of legal transitions
- No entry/exit actions
- No graceful shutdown (two-phase GOAWAY)
- Race conditions between cleanup paths

### Current State (4 states, 16 scattered transitions)

```c
// aio_internal.h:107-112
typedef enum __aio_http_conn_e {
  VALK_CONN_INIT,        // Missing: HANDSHAKING
  VALK_CONN_ESTABLISHED,
  VALK_CONN_CLOSING,     // Missing: GOAWAY_SENT, DRAINING
  VALK_CONN_CLOSED       // Missing: ERROR
} __aio_http_conn_e;
```

Transition sites (must be replaced with FSM calls):
```
aio_http2_conn.c:294    → CLOSING (nghttp2 error)
aio_http2_conn.c:317    → CLOSING (backpressure failure)
aio_http2_conn.c:326    → CLOSING (read error)
aio_http2_conn.c:349    → CLOSING (backpressure timeout)
aio_http2_conn.c:394    → ESTABLISHED (SSL complete)
aio_http2_conn.c:498    → CLOSED (disconnect)
aio_http2_client.c:196  → CLOSING (connect error)
aio_http2_client.c:222  → CLOSING (SSL error)
aio_http2_client.c:256  → CLOSING (nghttp2 error)
aio_http2_client.c:312  → INIT (new connection)
aio_http2_client.c:343  → CLOSING (setup error)
aio_http2_server.c:231  → INIT (accept)
aio_http2_server.c:322  → CLOSING (SSL error)
aio_maintenance.c:85    → CLOSING (idle timeout)
aio_maintenance.c:130   → CLOSING (backpressure timeout)
aio_uv.c:217           → CLOSING (shutdown)
```

### Target State (8 states, centralized FSM)

```c
// aio_http2_conn_fsm.h
typedef enum {
  VALK_CONN_INIT,           // TCP accepted, not yet handshaking
  VALK_CONN_HANDSHAKING,    // SSL/TLS in progress
  VALK_CONN_ESTABLISHED,    // HTTP/2 session active
  VALK_CONN_GOAWAY_SENT,    // First GOAWAY sent (max stream ID)
  VALK_CONN_DRAINING,       // Second GOAWAY sent, waiting for streams
  VALK_CONN_CLOSING,        // UV handle close initiated
  VALK_CONN_CLOSED,         // Terminal state
  VALK_CONN_ERROR,          // Error occurred, transitioning to CLOSING
} valk_conn_state_e;

typedef enum {
  VALK_CONN_EVT_SSL_COMPLETE,
  VALK_CONN_EVT_SSL_ERROR,
  VALK_CONN_EVT_DATA,
  VALK_CONN_EVT_GOAWAY_RECV,
  VALK_CONN_EVT_SHUTDOWN,
  VALK_CONN_EVT_DRAIN_TIMEOUT,
  VALK_CONN_EVT_CLOSE_TIMEOUT,
  VALK_CONN_EVT_ALL_STREAMS_CLOSED,
  VALK_CONN_EVT_IO_ERROR,
  VALK_CONN_EVT_PROTOCOL_ERROR,
} valk_conn_event_e;

// Single transition function - ALL state changes go through here
bool valk_conn_transition(valk_aio_handle_t *conn, valk_conn_event_e event);
```

### Implementation Steps

#### Step 8.1: Create FSM header and implementation

**Create:** `src/aio/http2/aio_http2_conn_fsm.h`
```c
#pragma once
#include "aio_internal.h"

typedef enum valk_conn_state_e { /* 8 states */ } valk_conn_state_e;
typedef enum valk_conn_event_e { /* 10 events */ } valk_conn_event_e;

typedef struct {
  void (*on_enter)(valk_aio_handle_t *conn);
  void (*on_exit)(valk_aio_handle_t *conn);
  const char *name;
} valk_conn_state_def_t;

bool valk_conn_transition(valk_aio_handle_t *conn, valk_conn_event_e event);
const char *valk_conn_state_name(valk_conn_state_e state);
const char *valk_conn_event_name(valk_conn_event_e event);
```

**Create:** `src/aio/http2/aio_http2_conn_fsm.c`
```c
#include "aio_http2_conn_fsm.h"

static const valk_conn_state_def_t state_defs[] = {
  [VALK_CONN_INIT] = { .on_enter = on_enter_init, .name = "INIT" },
  [VALK_CONN_HANDSHAKING] = { .on_enter = on_enter_handshaking, .name = "HANDSHAKING" },
  // ... etc
};

// Transition table: [current_state][event] = next_state
static const valk_conn_state_e transitions[VALK_CONN_STATE_COUNT][VALK_CONN_EVT_COUNT] = {
  [VALK_CONN_INIT] = {
    [VALK_CONN_EVT_SSL_COMPLETE] = VALK_CONN_HANDSHAKING,
    [VALK_CONN_EVT_SSL_ERROR] = VALK_CONN_ERROR,
    // ...
  },
  // ...
};

bool valk_conn_transition(valk_aio_handle_t *conn, valk_conn_event_e event) {
  valk_conn_state_e current = conn->http.state;
  valk_conn_state_e next = transitions[current][event];
  
  if (next == current) return false;  // No transition
  
  VALK_DEBUG("conn %p: %s + %s → %s",
             conn, state_defs[current].name,
             event_names[event], state_defs[next].name);
  
  if (state_defs[current].on_exit) state_defs[current].on_exit(conn);
  conn->http.state = next;
  if (state_defs[next].on_enter) state_defs[next].on_enter(conn);
  
  return true;
}
```

#### Step 8.2: Replace all direct state assignments

For each of the 16 sites, replace:
```c
// BEFORE
conn->http.state = VALK_CONN_CLOSING;

// AFTER
valk_conn_transition(conn, VALK_CONN_EVT_IO_ERROR);
```

#### Step 8.3: Implement two-phase GOAWAY (R3.7)

```c
static void on_enter_goaway_sent(valk_aio_handle_t *conn) {
  // Phase 1: Send GOAWAY with max stream ID
  nghttp2_submit_goaway(conn->http.session, NGHTTP2_FLAG_NONE,
                        INT32_MAX, NGHTTP2_NO_ERROR, NULL, 0);
  valk_http2_flush_pending(conn);
  
  // Start drain timer
  uv_timer_start(&conn->http.drain_timer, drain_timeout_cb,
                 conn->sys->config.drain_timeout_ms, 0);
}

static void on_enter_draining(valk_aio_handle_t *conn) {
  // Phase 2: Send GOAWAY with actual last stream ID
  i32 last_id = nghttp2_session_get_last_proc_stream_id(conn->http.session);
  nghttp2_submit_goaway(conn->http.session, NGHTTP2_FLAG_NONE,
                        last_id, NGHTTP2_NO_ERROR, NULL, 0);
  valk_http2_flush_pending(conn);
  
  // Start close timer
  uv_timer_start(&conn->http.close_timer, close_timeout_cb,
                 conn->sys->config.close_timeout_ms, 0);
}
```

### Verification

```bash
# After implementation, this must return 0:
grep -rn "http.state = " src/aio --include="*.c" | grep -v "conn_fsm.c" | wc -l

# And this must return >= 16:
grep -rn "valk_conn_transition" src/aio --include="*.c" | wc -l
```

---

## Phase 9: Arena Ownership Tokens (REQUIRED - ROOT CAUSE FIX)

**STATUS: NOT STARTED**

> ⚠️ This phase addresses **Root Cause 2** from the critical section above.
> Memory bugs (double-free, use-after-free, leaks) will persist until this is implemented.

### Problem

Arena ownership transfers via nullable pointers with no compiler enforcement:
- 11 `arena_slab_item =` assignment sites
- Transfer = assign to destination, set source to `nullptr`
- Easy to forget either step
- Defensive cleanup exists because normal paths leak

### Current Pattern (bug-prone)

```c
// Transfer arena from request to async context
http_ctx->arena_slab_item = req->arena_slab_item;
http_ctx->arena_slot = req->arena_slot;
req->arena_slab_item = nullptr;  // Easy to forget!
req->arena_slot = UINT32_MAX;

// Transfer back
stream_req->arena_slab_item = http->arena_slab_item;
stream_req->arena_slot = http->arena_slot;
http->arena_slab_item = nullptr;  // Easy to forget!
```

### Target Pattern (compiler-enforced)

```c
// aio_internal.h - new types
typedef struct {
  valk_slab_item_t *item;
  u32 slot;
  bool valid;  // Set to false after take
} valk_arena_ref_t;

typedef struct {
  valk_slab_item_t *item;
  u32 slot;
} valk_arena_token_t;

// Take ownership - invalidates source
static inline valk_arena_token_t valk_arena_take(valk_arena_ref_t *ref) {
  VALK_ASSERT(ref->valid, "Taking from invalid arena ref");
  valk_arena_token_t token = { .item = ref->item, .slot = ref->slot };
  ref->item = nullptr;
  ref->slot = UINT32_MAX;
  ref->valid = false;
  return token;
}

// Give ownership - token consumed
static inline void valk_arena_give(valk_arena_ref_t *ref, valk_arena_token_t token) {
  VALK_ASSERT(!ref->valid, "Giving to already-valid arena ref");
  ref->item = token.item;
  ref->slot = token.slot;
  ref->valid = true;
}

// Release to slab
static inline void valk_arena_release(valk_arena_ref_t *ref, valk_slab_t *slab) {
  if (ref->valid && ref->item) {
    valk_slab_release(slab, ref->item);
    ref->item = nullptr;
    ref->slot = UINT32_MAX;
    ref->valid = false;
  }
}
```

### Implementation Steps

#### Step 9.1: Add arena ref type to structures

```c
// In valk_http2_server_request_t:
// BEFORE:
valk_slab_item_t *arena_slab_item;
u32 arena_slot;

// AFTER:
valk_arena_ref_t arena;

// In valk_http_async_ctx_t:
// BEFORE:
void *arena_slab_item;
u32 arena_slot;

// AFTER:
valk_arena_ref_t arena;
```

#### Step 9.2: Replace all 11 assignment sites

Sites to update:
```
aio_async.c:70,72         - transfer back to request
aio_async.c:147           - standalone ctx init
aio_http2_session.c:245   - request init
aio_http2_session.c:573   - stream close clear
aio_http2_session.c:670   - async ctx init (nullptr)
aio_http2_session.c:731   - transfer to async ctx
aio_http2_session.c:735   - clear request
aio_http2_session.c:808   - pending stream promote
aio_http2_session.c:958   - clear after SSE
aio_http2_conn.c:543      - disconnect cleanup
```

### Verification

```bash
# After implementation, this must return 0:
grep -rn "arena_slab_item = " src/aio --include="*.c" | wc -l

# All arena operations go through the API:
grep -rn "valk_arena_take\|valk_arena_give\|valk_arena_release" src/aio --include="*.c" | wc -l
# Expected: >= 11
```

---

## Phase 10: Stream User Data Type Safety (REQUIRED - ROOT CAUSE FIX)

**STATUS: NOT STARTED**

> ⚠️ This phase addresses **Root Cause 3** from the critical section above.
> Crashes from incorrect stream data casting will persist until this is implemented.

### Problem

nghttp2 stream user data uses tagged pointers:
- High bit set = pending stream
- High bit clear = normal request (or nullptr)
- 8 sites must check before casting
- No compiler enforcement

### Current Pattern (crash-prone)

```c
void *stream_data = nghttp2_session_get_stream_user_data(session, stream_id);
if (__is_pending_stream(stream_data)) {
  pending_stream_t *ps = __get_pending_stream(stream_data);
  // Use ps...
} else {
  valk_http2_server_request_t *req = (valk_http2_server_request_t *)stream_data;
  // Use req... (might be nullptr!)
}
```

### Target Pattern (type-safe)

```c
// aio_internal.h - new types
typedef enum {
  STREAM_DATA_NONE,
  STREAM_DATA_REQUEST,
  STREAM_DATA_PENDING,
} valk_stream_data_type_e;

typedef struct {
  valk_stream_data_type_e type;
  union {
    valk_http2_server_request_t *request;
    valk_pending_stream_t *pending;
  };
} valk_stream_data_t;

static inline valk_stream_data_t valk_stream_get_data(
    nghttp2_session *session, i32 stream_id) {
  void *raw = nghttp2_session_get_stream_user_data(session, stream_id);
  if (!raw) {
    return (valk_stream_data_t){ .type = STREAM_DATA_NONE };
  }
  if ((uptr)raw & (1ULL << 63)) {
    return (valk_stream_data_t){
      .type = STREAM_DATA_PENDING,
      .pending = (valk_pending_stream_t *)((uptr)raw & ~(1ULL << 63))
    };
  }
  return (valk_stream_data_t){
    .type = STREAM_DATA_REQUEST,
    .request = (valk_http2_server_request_t *)raw
  };
}

// Usage:
valk_stream_data_t data = valk_stream_get_data(session, stream_id);
switch (data.type) {
  case STREAM_DATA_NONE:
    // Handle no data
    break;
  case STREAM_DATA_REQUEST:
    handle_request(data.request);
    break;
  case STREAM_DATA_PENDING:
    handle_pending(data.pending);
    break;
}
```

### Implementation Steps

#### Step 10.1: Add discriminated union type

Add `valk_stream_data_t` and `valk_stream_get_data()` to `aio_internal.h`.

#### Step 10.2: Replace all 8 tagged pointer sites

Sites to update:
```
aio_http2_session.c:84    - on_header_callback
aio_http2_session.c:547   - on_stream_close_callback
aio_http2_session.c:624   - on_frame_recv_callback
aio_http2_session.c:626   - pending stream check
aio_http2_session.c:787   - pending stream process
aio_http2_session.c:789   - assertion
aio_maintenance.c:109     - pending stream timeout
aio_maintenance.c:112     - RST_STREAM for pending
```

### Verification

```bash
# After implementation, this must return 0:
grep -rn "__is_pending_stream\|__get_pending_stream" src/aio --include="*.c" | grep -v "define" | wc -l

# All stream data access goes through the type-safe API:
grep -rn "valk_stream_get_data" src/aio --include="*.c" | wc -l
# Expected: >= 8
```

---

## Phase 11: Function Extraction (REQUIRED - COMPLEXITY FIX)

**STATUS: NOT STARTED**

> This phase completes the complexity reduction started in Phase 6.
> Requirement R6.1 (CC < 10) is not met until this is done.

### Problem

`valk_http2_on_frame_recv_callback` is ~175 lines with CC ≈ 25 and nesting 5-6 levels.

### Implementation Steps

#### Step 11.1: Extract frame type handlers

```c
// Extract from on_frame_recv_callback:
static int handle_goaway_frame(valk_aio_handle_t *conn, const nghttp2_frame *frame);
static int handle_rst_stream_frame(valk_aio_handle_t *conn, const nghttp2_frame *frame);
static int handle_headers_frame(nghttp2_session *session, valk_aio_handle_t *conn,
                                const nghttp2_frame *frame);
```

#### Step 11.2: Extract pending stream handler

```c
static int handle_pending_stream_headers(valk_aio_handle_t *conn,
                                         pending_stream_t *ps,
                                         i32 stream_id);
```

#### Step 11.3: Extract async response dispatch

```c
static int dispatch_async_response(nghttp2_session *session,
                                   i32 stream_id,
                                   valk_async_handle_t *handle,
                                   valk_http2_server_request_t *req,
                                   valk_http_async_ctx_t *http_ctx);
```

#### Step 11.4: Extract error response helper

```c
static int send_error_response(nghttp2_session *session,
                               i32 stream_id,
                               const char *status,
                               const char *message,
                               valk_mem_arena_t *arena);
```

### Target: `on_frame_recv_callback` after extraction

```c
int valk_http2_on_frame_recv_callback(nghttp2_session *session,
                                      const nghttp2_frame *frame,
                                      void *user_data) {
  VALK_GC_SAFE_POINT();
  valk_aio_handle_t *conn = (valk_aio_handle_t *)user_data;
  
  // Update activity timestamp
  if (conn->sys) {
    conn->http.last_activity_ms = conn->sys->ops->loop->now(conn->sys);
  }
  
  switch (frame->hd.type) {
    case NGHTTP2_GOAWAY:
      return handle_goaway_frame(conn, frame);
    case NGHTTP2_RST_STREAM:
      return handle_rst_stream_frame(conn, frame);
    case NGHTTP2_HEADERS:
      if (frame->headers.cat == NGHTTP2_HCAT_REQUEST) {
        return handle_headers_frame(session, conn, frame);
      }
      return 0;
    default:
      return 0;
  }
}
```

### Verification

```bash
# Count lines in on_frame_recv_callback - must be < 50
awk '/^int valk_http2_on_frame_recv_callback/,/^(int|static|void) [a-z]/' \
  src/aio/http2/aio_http2_session.c | head -n -1 | wc -l
```

---

## Phase 12: Dead Code Removal (CLEANUP)

**STATUS: NOT STARTED**

### Problem

`http2_ops_nghttp2.c` is 297 lines of abstraction that is never used.

### Decision Required

**Option A: Delete the abstraction**
- Remove `http2_ops.h`, `http2_ops_nghttp2.c`, `http2_ops_test.c`
- Remove `.http2` from `valk_aio_ops_t`
- Simplest, removes 300+ lines of dead code

**Option B: Migrate to use the abstraction**
- Replace all direct `nghttp2_*` calls with `ops->http2->*` calls
- Enables mocking nghttp2 for tests
- More work, but enables better testing

### Implementation (Option A)

```bash
# Delete files
rm src/aio/http2/http2_ops.h
rm src/aio/http2/http2_ops_nghttp2.c
rm src/aio/http2/http2_ops_test.c

# Remove from CMakeLists.txt
# Remove .http2 field from valk_aio_ops_t in aio_ops.h
# Remove .http2 initialization from aio_ops.c
```

### Verification

```bash
# Files removed
ls src/aio/http2/http2_ops* 2>/dev/null | wc -l
# Expected: 0

# No references remain
grep -rn "http2_ops" src/aio --include="*.c" --include="*.h" | wc -l
# Expected: 0
```

---

## Appendix: Current vs Target Comparison

| Aspect | Current | Target | Status |
|--------|---------|--------|--------|
| Metrics location | Standalone `metrics_v2` | Sibling system | ✅ Done |
| Diagnostics publisher | Lisp handler | Lisp handler | ✅ Done |
| SSE | Generic `stream/*` + Lisp | Generic streaming | ✅ Done |
| Load management naming | `aio_overload_*` | Unified "Overload" | ✅ Done |
| Code organization | `system/`, `http2/`, etc. | Hierarchical | ✅ Done |
| **Connection state machine** | **4 states, 16 scattered sites** | **8 states, centralized FSM** | ❌ NOT DONE |
| **Arena ownership** | **Implicit via nullptr** | **Explicit tokens** | ❌ NOT DONE |
| **Stream data typing** | **Tagged pointers** | **Discriminated union** | ❌ NOT DONE |
| **Session complexity** | **CC ≈ 25, nesting 5-6** | **CC < 10, nesting < 4** | ❌ NOT DONE |
| **Dead code** | **297 lines unused http2_ops** | **Delete or use** | ❌ NOT DONE |
| Two-phase GOAWAY | Not implemented | R3.7 graceful shutdown | ❌ NOT DONE |
| Backpressure watermarks | Ad-hoc thresholds | 80%/40% hysteresis | ❌ NOT DONE |

---

## Appendix: Verification Commands

**Use the Master Verification Script above.** It runs all checks and reports PASS/FAIL for each.

```bash
# Run the master script:
./scripts/verify_refactoring.sh

# Or create it from the script in the "Master Verification Script" section above
```

### Quick Manual Checks

These are the same checks from the master script, for quick manual verification:

```bash
# Phase 8: State Machine
grep -rn "http\.state = " src/aio --include="*.c" | grep -v "conn_fsm.c" | wc -l  # Must be 0
test -f src/aio/http2/aio_http2_conn_fsm.c && echo "FSM exists"                    # Must print
grep -c "VALK_CONN_" src/aio/http2/aio_http2_conn_fsm.h                            # Must be >= 8
grep -rn "valk_conn_transition" src/aio --include="*.c" | wc -l                    # Must be >= 16

# Phase 9: Arena Ownership
grep -rn "arena_slab_item\s*=" src/aio --include="*.c" | wc -l                     # Must be 0
grep -q "valk_arena_token_t" src/aio/aio_internal.h && echo "Token type exists"    # Must print
grep -c "valk_arena_take\|valk_arena_give" src/aio/http2/aio_http2_session.c       # Must be >= 6
grep -q "leaked_arenas" src/aio/http2/aio_http2_conn.c && echo "FAIL" || echo "OK" # Must print OK

# Phase 10: Stream Data Safety
grep -rn "__is_pending_stream" src/aio --include="*.c" | grep -v define | wc -l   # Must be 0
grep -q "STREAM_DATA_NONE" src/aio/aio_internal.h && echo "Enum exists"           # Must print
grep -c "valk_stream_get_data" src/aio/http2/aio_http2_session.c                  # Must be >= 8

# Phase 11: Complexity Reduction
awk '/^int valk_http2_on_frame_recv_callback/,/^(int|static) [a-z]/' \
  src/aio/http2/aio_http2_session.c | head -n -1 | wc -l                          # Must be < 50
grep -q "static int handle_goaway_frame" src/aio/http2/aio_http2_session.c        # Must match

# Phase 12: Dead Code
ls src/aio/http2/http2_ops*.c 2>/dev/null | wc -l                                 # Must be 0 (Option A)
# OR
grep -rn "ops->http2->" src/aio --include="*.c" | wc -l                           # Must be >= 20 (Option B)
```

### Anti-Gaming Notes

These checks are designed so that:

1. **Deleting code doesn't pass** - Positive checks require new code to exist
2. **Partial work doesn't pass** - Multiple positive checks must all pass
3. **Comments/dead code don't count** - Checks look for actual usage, not just definitions
4. **Tests must pass** - `make build && make test` is part of every verification

---

## Appendix: File Inventory (Current State)

Files that need modification for Phases 8-12:

| File | Lines | Phase 8 | Phase 9 | Phase 10 | Phase 11 |
|------|-------|---------|---------|----------|----------|
| `aio_internal.h` | 482 | Add states | Add arena types | Add stream data type | - |
| `aio_http2_session.c` | 964 | 1 site | 6 sites | 6 sites | Extract 4 functions |
| `aio_http2_conn.c` | 593 | 6 sites | 1 site | - | - |
| `aio_http2_client.c` | 346 | 5 sites | - | - | - |
| `aio_http2_server.c` | 374 | 2 sites | - | - | - |
| `aio_maintenance.c` | 145 | 2 sites | - | 2 sites | - |
| `aio_uv.c` | 272 | 1 site | - | - | - |
| `aio_async.c` | 508 | - | 3 sites | - | - |

Files to delete in Phase 12:
- `http2_ops.h` (interface)
- `http2_ops_nghttp2.c` (297 lines)
- `http2_ops_test.c` (test double)
