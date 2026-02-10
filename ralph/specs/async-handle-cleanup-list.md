# Async Handle Cleanup List

## Overview

Add a resource cleanup mechanism to `valk_async_handle_t` so that C resources (timers, stream bodies, arena refs) are released automatically when a handle reaches a terminal state. This is separate from the existing `cleanup_fn` (which frees combinator memory on refcount=0). Resource cleanups run at terminal state transition, before the handle is deallocated.

The pattern: acquire a resource, register its release on the handle, forget about it. Inspired by Erlang supervisor shutdown and Rust's `Drop`.

## Dependencies

- Requires `async-reach-terminal.md` (`__reach_terminal` must exist as the single terminal transition function)

## Requirements

### Cleanup Entry Struct

Define in `src/async_handle.h`, before the `valk_async_handle_t` struct:

```c
typedef struct {
  void (*fn)(void *data, void *ctx);
  void *data;
  void *ctx;
} valk_async_cleanup_entry_t;
```

The `fn` signature takes both `data` (the resource to clean up) and `ctx` (e.g., the slab pool for arena release). Two-arg avoids needing wrapper closures.

### Handle Fields

Add to `valk_async_handle_t`, after the existing `cleanup_fn`/`cleanup_ctx` fields:

| Field | Type | Purpose |
|-------|------|---------|
| `resource_cleanups` | `valk_async_cleanup_entry_t *` | Array of registered resource cleanups |
| `resource_cleanup_count` | `u16` | Number of registered resource cleanups |
| `resource_cleanup_capacity` | `u16` | Allocated capacity |

Keep the existing `cleanup_fn`/`cleanup_ctx` fields unchanged — they serve a different purpose (combinator context deallocation on refcount=0 in `valk_async_handle_unref`).

### Registration Function

Declare in `src/aio/aio_async.h`, implement in `src/aio/aio_async.c`:

`void valk_async_handle_on_resource_cleanup(valk_async_handle_t *handle, void (*fn)(void *data, void *ctx), void *data, void *ctx)`

Must:
- Grow `resource_cleanups` array if at capacity (start at 2, double on growth)
- Allocate via `malloc` (not region — cleanups must survive arena release)
- Append entry at `resource_cleanup_count++`
- Be callable multiple times to register multiple cleanups on the same handle
- Be a no-op if `handle` is NULL

### Cleanup Execution

Add a static function in `src/aio/aio_async.c`:

`static void __run_resource_cleanups(valk_async_handle_t *handle)`

Must:
- Run registered cleanups in **reverse** order (LIFO — last registered runs first)
- Set `resource_cleanup_count = 0` after running (prevent double-run)
- Free the `resource_cleanups` array after running
- Be safe to call on a handle with zero cleanups

### Integration into Terminal Transitions

Call `__run_resource_cleanups(handle)` inside `__reach_terminal` (from `async-reach-terminal.md`), as the final step after the notification sequence:

1. `valk_async_notify_parent(handle)`
2. `valk_async_notify_done(handle)`
3. `valk_async_propagate_completion(handle)`
4. `__run_resource_cleanups(handle)` — **add this**

Cleanups run AFTER `on_done` and AFTER notification cascades. This ordering is critical: `on_done` sends the HTTP response using the arena, then cleanup releases the arena. Because `__reach_terminal` is the single terminal transition function, this guarantees cleanups run on every path (complete, fail, AND cancel).

### Handle Initialization

In `valk_async_handle_init` (or wherever handles are zero-initialized), ensure `resource_cleanups = NULL`, `resource_cleanup_count = 0`, `resource_cleanup_capacity = 0`.

### Handle Deallocation Safety

In `valk_async_handle_unref`, when refcount drops to 0, call `__run_resource_cleanups` as a safety net before `valk_async_handle_free`. This catches handles that were abandoned without reaching a terminal state (should not happen, but prevents leaks).

## Non-Requirements

- This spec does NOT change arena ownership or `is_closed` behavior — those come in a follow-up spec
- This spec does NOT register any new resource cleanups — it only adds the mechanism
- This spec does NOT change the existing `cleanup_fn`/`cleanup_ctx` mechanism

## Acceptance Criteria

- [ ] `valk_async_cleanup_entry_t` defined in `src/async_handle.h`: `grep -c 'valk_async_cleanup_entry_t' src/async_handle.h` returns >= 1
- [ ] `valk_async_handle_on_resource_cleanup` declared: `grep -c 'on_resource_cleanup' src/aio/aio_async.h` returns >= 1
- [ ] Existing `cleanup_fn` preserved: `grep -c 'cleanup_fn' src/async_handle.h` returns >= 1
- [ ] Cleanups run on complete: add test `test_resource_cleanup_runs_on_complete` to `test/test_async.c` — register 2 cleanups, complete the handle, verify both ran in reverse order
- [ ] Cleanups run on fail: add test `test_resource_cleanup_runs_on_fail` — register cleanup, fail the handle, verify it ran
- [ ] Cleanups run on cancel: add test `test_resource_cleanup_runs_on_cancel` — register cleanup, cancel the handle, verify it ran
- [ ] Double-run safe: add test `test_resource_cleanup_no_double_run` — complete handle, verify cleanups don't run again on subsequent complete attempts
- [ ] `make build` succeeds
- [ ] `make test` passes
