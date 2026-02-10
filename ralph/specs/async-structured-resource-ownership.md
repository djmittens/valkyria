# Structured Async Resource Ownership

## Overview

Eliminate the arena ownership transfer between requests and async handles. Arenas stay on the request that created them and are released via the handle cleanup list (from `async-handle-cleanup-list.md`). Remove the `is_closed` suppression mechanism that silently cancels handles and prevents cleanup. Remove the orphan arena sweep and associated dead code.

The result: one ownership model (request owns arena, handle cleanup releases it), one cleanup path (handle reaches terminal state → cleanups run), no silent suppression.

## Dependencies

- Requires `async-reach-terminal.md` (`is_closed` checks already removed from `complete`/`fail` paths)
- Requires `async-handle-cleanup-list.md` (cleanup registration mechanism on handles)

## Requirements

### Stop Arena Transfer in `__async_state_pending`

In `src/aio/http2/aio_http2_session.c`, function `__async_state_pending` (line ~642):

**Remove:**
- The call to `valk_http2_remove_from_active_arenas(ctx->conn, ctx->req->arena_ref.slot)`
- The `valk_arena_ref_give(&ctx->http_ctx->arena_ref, valk_arena_ref_take(&ctx->req->arena_ref))` transfer

The arena stays in `req->arena_ref` and stays linked in `conn->http.active_arena_head`. The function body becomes just a debug log and `return 1`.

### Simplify `valk_http_async_ctx_t`

In `src/aio/aio_internal.h`, remove the `arena_ref` field from `valk_http_async_ctx_t`:

```c
typedef struct valk_http_async_ctx {
  void *session;
  i32 stream_id;
  struct valk_aio_handle_t *conn;
  valk_mem_arena_t *arena;
} valk_http_async_ctx_t;
```

The ctx provides a pointer to the arena (for allocations during response sending) but does not own the arena's slab slot.

### Register Arena Cleanup on Handle

In `__handle_async_response` in `src/aio/http2/aio_http2_session.c` (line ~661), after creating the http_ctx and before the state dispatch:

Register a cleanup that releases the arena when the handle completes:

```c
valk_async_handle_on_resource_cleanup(handle, __release_arena_cleanup, req, conn);
```

The cleanup function `__release_arena_cleanup` must:
- Cast `data` to `valk_http2_server_request_t *`
- Cast `ctx` to `valk_aio_handle_t *` (the connection)
- Check `valk_arena_ref_valid(req->arena_ref)` — if not valid, return (already released)
- Call `valk_http2_metrics_on_arena_release(conn)`
- Call `valk_http2_remove_from_active_arenas(conn, req->arena_ref.slot)`
- Call `valk_arena_ref_release(&req->arena_ref, conn->http.server->sys->httpStreamArenas)`
- Exit arena backpressure if needed

This mirrors the existing release logic in `on_stream_close_callback` (line ~532-546).

### Simplify `valk_http_async_done_callback`

In `src/aio/aio_async.c`, simplify `valk_http_async_done_callback`:

**Remove:**
- The `clear_is_closed_ctx_recursive` call and the `clear_is_closed_ctx_recursive` function
- The arena_ref transfer back to `stream_req` (`valk_arena_ref_give` / `valk_arena_ref_take`)
- The `cleanup:` label's arena_ref release logic (cleanup list handles this now)

The function's job becomes: check if connection is alive, if so send the HTTP response using `http->arena`, done. No resource ownership management.

The arena pointer `http->arena` is still valid during `on_done` because cleanups run AFTER `on_done`.

### Remove `is_closed` from Propagation

NOTE: The `is_closed` checks in `valk_async_handle_complete` and `valk_async_handle_fail` were already removed in `async-reach-terminal.md`. This spec handles the remaining `is_closed` removals.

In `src/aio/aio_comb_propagate.c`:

**Remove** the `valk_async_is_chain_closed` function entirely (lines 16-43).

**Remove** the `is_chain_closed` check in `valk_async_propagate_single` (line ~71-74) and the per-child `is_chain_closed` check (line ~90-94).

When a connection dies, the disconnect handler already cancels handles via `valk_stream_body_close_all` → `force_close` → `closed_handle` completion. Propagation doesn't need to independently check connection state.

### Remove `is_closed` Fields and Functions

**In `src/async_handle.h`**: Remove `is_closed` and `is_closed_ctx` fields from `valk_async_handle_t`.

**In `src/aio/aio_types.h`**: Remove `valk_async_is_closed_fn` typedef.

**In `src/aio/aio_async.h`**: Remove `valk_async_is_resource_closed` and `valk_http_async_is_closed_callback` declarations.

**In `src/aio/aio_combinators_internal.h`**: Remove `valk_async_is_resource_closed` extern.

**In `src/aio/aio_async.c`**: Remove `valk_async_is_resource_closed` function and `valk_http_async_is_closed_callback` function.

**In `src/aio/http2/aio_http2_session.c`**: Remove the `is_closed`/`is_closed_ctx` assignments in `__handle_async_response` (lines ~673-674) and the `extern` declaration of `valk_http_async_is_closed_callback`.

**In `src/aio/aio_comb_propagate.c`**: Remove `is_closed` transfer during `then`-chain rewiring (lines ~134-135 where `inner->is_closed = child->is_closed`).

**In `src/aio/http2/stream/aio_stream_body.c`**: Remove the `is_closed`/`is_closed_ctx` clearing on `closed_handle` in `__stream_body_finish_close`.

### Remove Orphan Arena Sweep

**In `src/aio/http2/aio_http2_conn.c`**:

- Delete `__disconnect_release_orphaned_arenas` function (lines ~540-582)
- Remove its call in `valk_http2_conn_on_disconnect` (line ~646)
- Remove the debug `fprintf` statements at the top of `valk_http2_conn_on_disconnect` (lines ~626-631)

The orphan sweep is no longer needed because:
1. For sync responses: `on_stream_close_callback` releases the arena (unchanged)
2. For async responses: the arena stays on the request, and the handle's cleanup releases it when the handle reaches terminal state
3. For disconnects: `close_all` force-closes stream bodies → completes `closed_handle` → cascades to parent handle → parent reaches terminal → cleanup releases arena

### Adjust `on_stream_close_callback` Arena Release

In `valk_http2_server_on_stream_close_callback` (line ~532-546):

The existing arena release for non-stream-body streams (`!has_stream_body` branch) must be guarded: only release if the request does NOT have a pending async handle. If an async handle is pending, the handle's cleanup will release the arena.

Add a check: if `req->has_async_handler` (or equivalent flag — set in `__handle_async_response`), skip the direct arena release. The handle cleanup owns it.

Add a `bool has_async_handler` field to `valk_http2_server_request_t` if one doesn't already exist.

## Non-Requirements

- This spec does NOT introduce a session abstraction — that's a follow-up
- This spec does NOT change how `valk_standalone_async_ctx_t` works — standalone contexts are a separate concern
- This spec does NOT change the stream body linked list on connections — that's a follow-up

## Acceptance Criteria

- [ ] Arena ref not transferred: `grep -n 'arena_ref_take.*req->arena_ref' src/aio/http2/aio_http2_session.c` returns no matches
- [ ] `http_async_ctx_t` has no `arena_ref` field: `grep 'arena_ref' src/aio/aio_internal.h | grep -c 'http_async_ctx'` returns 0
- [ ] `is_closed` field removed: `grep -c 'is_closed' src/async_handle.h` returns 0
- [ ] `is_closed` typedef removed: `grep -c 'is_closed_fn' src/aio/aio_types.h` returns 0
- [ ] `valk_async_is_resource_closed` removed: `grep -rn 'is_resource_closed' src/aio/` returns no matches
- [ ] `is_chain_closed` removed: `grep -rn 'is_chain_closed' src/aio/` returns no matches
- [ ] Orphan sweep removed: `grep -rn 'orphaned_arena' src/aio/http2/aio_http2_conn.c` returns no matches
- [ ] Debug fprintf removed: `grep -n 'fprintf.*DBG.*disconnect' src/aio/http2/aio_http2_conn.c` returns no matches
- [ ] Cleanup registered for async arenas: `grep -c 'valk_async_handle_on_resource_cleanup' src/aio/http2/aio_http2_session.c` returns >= 1
- [ ] `make build` succeeds
- [ ] `make test` passes
- [ ] `make test-c-asan` passes (no arena leaks under address sanitizer)
