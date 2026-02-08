# Metrics System Fixes

Issues identified from analysis of `hey -n 100 -c 50 -h2 https://localhost:8443/slow` output.

## Critical Issues

### 1. Request Duration Metrics Broken for Async Handlers ✅ FIXED

**Problem**: The `/slow` endpoint uses `aio/sleep 2000` (2 second delay), but all requests show <1ms duration in the histogram.

**Root Cause**: Duration is measured from stream creation (`start_time_us` in `__http2_server_on_begin_headers_cb`) to stream close (`__http_server_on_stream_close_callback`). For async handlers using `aio/do`, the stream closes immediately after dispatching to the handler, not after the response is fully sent.

**Location**: `src/aio_uv.c:843` (start) and `src/aio_uv.c:1227` (end)

**Fix Applied**:
1. Added `response_sent_time_us` and `response_complete` fields to `valk_http2_server_request_t` (lines 480-481)
2. Implemented `__http_server_on_frame_send_callback` to capture timestamp when DATA+END_STREAM frame is sent (lines 1212-1234)
3. Updated `__http_server_on_stream_close_callback` to use actual response completion time if available (lines 1253-1260)

**Verification**: 4 new tests added to `test/test_aio_metrics.c`:
- `test_stream_metrics_with_duration`
- `test_request_duration_histogram`
- `test_metrics_duration_microsecond_sum`
- `test_stream_metrics_bytes_tracking`

---

### 2. GC Heap Metrics Always Zero ✅ FIXED

**Problem**: `valk_gc_heap_used_bytes` and `valk_gc_heap_total_bytes` are always 0.

**Root Cause**: `valk_builtin_vm_metrics_json` (parser.c:3874) reads from `valk_thread_ctx.heap`, which is thread-local storage. If the HTTP request handler runs in a context where `valk_thread_ctx` wasn't initialized, the heap pointer is NULL.

**Location**: `src/parser.c:3874`, `src/aio_metrics.c:657-661`

**Fix Applied** (Option 1 - Store heap pointer in AIO system):
1. Added `gc_heap` field to `valk_aio_system_t` struct (`src/aio_uv.c:543`)
2. Store heap pointer during AIO initialization (`src/aio_uv.c:3132`)
3. Added `valk_aio_get_gc_heap()` getter function (`src/aio_uv.c:3245-3248`, `src/aio.h:295`)
4. Updated `valk_builtin_vm_metrics_json` and `valk_builtin_vm_metrics_prometheus` to use AIO system heap (`src/parser.c:3873-3875`, `3901-3903`)

**Verification**: 4 new tests added to `test/test_aio_metrics.c`:
- `test_vm_metrics_collect_with_gc_heap`
- `test_vm_metrics_collect_null_heap`
- `test_vm_metrics_json_contains_heap_values`
- `test_vm_metrics_prometheus_contains_heap_values`

---

## Minor Issues

### 3. Request/Stream Count Accumulation

**Observation**: Metrics showed 730 requests when only 100 were sent.

**Status**: Not a bug - counters correctly accumulate across test runs. This is expected Prometheus counter behavior.

**Optional Enhancement**: Add a `/metrics/reset` debug endpoint for testing purposes (should NOT be exposed in production).

---

### 4. Streams vs Requests Off-by-One

**Observation**: `streams_total=731` vs `requests_total=730`

**Status**: Correct behavior - one stream was in-flight at snapshot time. The stream increments on creation, request increments on completion.

---

### 5. Connection Count Lower Than Expected

**Observation**: 21 connections for 100 requests with `-c 50` concurrency.

**Status**: Correct - HTTP/2 multiplexing allows multiple streams per connection. 21 connections handling 731 streams is efficient multiplexing.

---

## Verification Needed

### 6. GC Cycles = 0

**Observation**: No GC cycles recorded despite 156k evaluations.

**Status**: Likely correct - heap hasn't exceeded `gc_threshold` (16MB). However, cannot confirm because heap_used is broken (issue #2).

**Action**: After fixing issue #2, verify that:
- `heap_used_bytes` shows non-zero allocation
- GC triggers when threshold is exceeded
- Metrics update after collection

---

## Implementation Plan ✅ COMPLETED

### Phase 1: Fix Heap Metrics (Issue #2) ✅

1. ✅ Added `gc_heap` field to `valk_aio_system_t` struct in `src/aio_uv.c:543`
2. ✅ Stored heap pointer during AIO system initialization in `src/aio_uv.c:3132`
3. ✅ Added `valk_aio_get_gc_heap()` getter function
4. ✅ Updated `valk_builtin_vm_metrics_*` to use AIO system heap with fallback

### Phase 2: Fix Request Duration (Issue #1) ✅

1. ✅ Added `response_sent_time_us` and `response_complete` fields to request struct
2. ✅ Implemented `__http_server_on_frame_send_callback` for DATA+END_STREAM detection
3. ✅ Updated `__http_server_on_stream_close_callback` to use response completion time

### Phase 3: Testing ✅

All tests pass (175+ tests including 8 new metrics tests):

```
[14/14] /home/xyzyx/src/valkyria/test/test_aio_metrics.c Suite Results:
✅ test_metrics_init
✅ test_metrics_connection_tracking
✅ test_metrics_stream_tracking
✅ test_metrics_json_output
✅ test_metrics_prometheus_output
✅ test_system_stats_prometheus_output
✅ test_stream_metrics_with_duration          (NEW)
✅ test_request_duration_histogram            (NEW)
✅ test_metrics_duration_microsecond_sum      (NEW)
✅ test_stream_metrics_bytes_tracking         (NEW)
✅ test_vm_metrics_collect_with_gc_heap       (NEW)
✅ test_vm_metrics_collect_null_heap          (NEW)
✅ test_vm_metrics_json_contains_heap_values  (NEW)
✅ test_vm_metrics_prometheus_contains_heap_values (NEW)
```

---

## Files Modified

| File | Changes |
|------|---------|
| `src/aio.h` | Added `valk_aio_get_gc_heap()` declaration, included `gc.h` |
| `src/aio_uv.c` | Added `gc_heap` field, `__http_server_on_frame_send_callback`, response timing fields |
| `src/parser.c` | Updated VM metrics builtins to use AIO system heap |
| `test/test_aio_metrics.c` | Added 8 new comprehensive tests |
