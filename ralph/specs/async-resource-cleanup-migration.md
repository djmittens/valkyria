# Async Resource Cleanup Migration

## Overview

Migrate all async resource types to use `valk_async_handle_on_resource_cleanup` so every resource has a guaranteed cleanup path. Fix the `aio/sleep` timer memory leak. Add an integration test that verifies arena pool counts return to baseline after HTTP request + disconnect cycles.

After this spec, the pattern is enforced: every async resource is registered for cleanup on the handle that created it. The stream body linked list on connections remains for maintenance scanning (timeout/orphan checks) but is no longer a cleanup mechanism — cleanup happens via the handle.

## Dependencies

- Requires `async-handle-cleanup-list.md` (cleanup registration mechanism)
- Requires `async-structured-resource-ownership.md` (arena ownership on request)

## Requirements

### Fix `aio/sleep` Timer Memory Leak

In `src/aio/aio_comb_timers.c`, `valk_async_handle_uv_data_t` is allocated via `aligned_alloc` (line ~340) but never freed. The uv close callback `__sleep_timer_close_cb` is a no-op.

Fix: In `__sleep_timer_close_cb`, free the `valk_async_handle_uv_data_t`:

```c
static void __sleep_timer_close_cb(uv_handle_t *handle) {
  valk_async_handle_uv_data_t *data = (valk_async_handle_uv_data_t *)handle;
  free(data);
}
```

Additionally, register a cleanup on the sleep handle that stops and closes the timer if it hasn't fired yet:

```c
valk_async_handle_on_resource_cleanup(handle, __sleep_cleanup, data, NULL);
```

The `__sleep_cleanup` function must:
- Check if the timer is still active (`uv_is_active`)
- If so, stop it with `uv_timer_stop` and close it with `uv_close` (which triggers `__sleep_timer_close_cb` to free)
- If already closed, just free the data

### Register Stream Body Cleanup on Handle

In `src/aio/http2/stream/aio_stream_body.c`, when a stream body is created and associated with an async handle (via `closed_handle`), register a cleanup:

```c
valk_async_handle_on_resource_cleanup(closed_handle, __stream_body_cleanup, body, NULL);
```

The `__stream_body_cleanup` function must:
- Check `body->state` — if not already CLOSED, force-close it
- This is a safety net: the stream body may already be closed by the normal path (`close_all`, `close_by_stream_id`), in which case the cleanup is a no-op

This does NOT replace the connection-level `stream_bodies` list — that list is still needed for maintenance timer scanning (timeout checks, orphan detection). The cleanup is a guaranteed fallback that prevents leaks even if the connection-level cleanup misses something.

### Register Interval Timer Cleanup on Handle

In `src/aio/aio_comb_timers.c`, for `aio/interval` timers, register a cleanup that stops and closes the interval timer when the handle is cancelled or the connection closes:

```c
valk_async_handle_on_resource_cleanup(handle, __interval_cleanup, timer_data, NULL);
```

The `__interval_cleanup` function must stop the uv timer and release the callback handle reference.

### Register Schedule Timer Cleanup on Handle

In `src/aio/aio_comb_timers.c`, for `aio/schedule` timers, register a cleanup that stops the timer and releases the callback handle if it hasn't fired:

```c
valk_async_handle_on_resource_cleanup(handle, __schedule_cleanup, timer_data, NULL);
```

### Arena Pool Leak Detection Test

Add `test_arena_pool_no_leak_after_disconnect` to `test/test_http2.c` (or a new `test/test_arena_leak.c` if `test_http2.c` doesn't exist):

The test must:
1. Record the initial free count of `sys->httpStreamArenas`
2. Simulate an HTTP request that returns an async handle (triggering arena acquisition)
3. Simulate a client disconnect (triggering the cleanup cascade)
4. Verify the free count returns to the initial value
5. Repeat for SSE (stream body) case: start SSE stream, disconnect, verify arena freed

This test is the guardrail: if anyone adds a new resource path that skips cleanup, the pool count won't return to baseline and the test fails.

### Sleep Timer Leak Detection Test

Add `test_sleep_timer_no_leak` to `test/test_async.c`:

1. Record baseline memory (or use a counter on aligned_alloc/free)
2. Create and complete 100 `aio/sleep` handles
3. Verify all timer data was freed (no outstanding allocations)

## Non-Requirements

- This spec does NOT remove the `stream_bodies` linked list from connections — it's still used by the maintenance timer
- This spec does NOT change the `standalone_async_ctx_t` arena handling — that's a separate context not tied to HTTP connections

## Acceptance Criteria

- [ ] Sleep timer freed: `grep -c 'free(data)' src/aio/aio_comb_timers.c` returns >= 1 (in the close callback)
- [ ] Sleep cleanup registered: `grep -c 'on_resource_cleanup.*sleep\|on_resource_cleanup.*__sleep' src/aio/aio_comb_timers.c` returns >= 1
- [ ] Interval cleanup registered: `grep -c 'on_resource_cleanup.*interval\|on_resource_cleanup.*__interval' src/aio/aio_comb_timers.c` returns >= 1
- [ ] Schedule cleanup registered: `grep -c 'on_resource_cleanup.*schedule\|on_resource_cleanup.*__schedule' src/aio/aio_comb_timers.c` returns >= 1
- [ ] Stream body cleanup registered: `grep -c 'on_resource_cleanup' src/aio/http2/stream/aio_stream_body.c` returns >= 1
- [ ] Arena leak test exists and passes: `make test` passes including the new arena pool leak test
- [ ] `make build` succeeds
- [ ] `make test` passes
- [ ] `make test-c-asan` passes
