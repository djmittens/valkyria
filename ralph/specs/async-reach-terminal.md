# Async Handle: __reach_terminal Unification

## Overview

Unify all terminal state transitions (complete, fail, cancel) through a single `__reach_terminal` function that atomically transitions the handle and runs the full notification sequence. Currently, `valk_async_cancel_task` transitions to CANCELLED but skips `notify_parent`, `notify_done`, and `propagate_completion` — causing parent combinators to hang and resource cleanups to never run. The `is_closed` paths in `complete`/`fail` have the same bug. This spec fixes both by routing everything through one function.

Verified via TLA+ model checking: the proposed design satisfies P1-P5 (terminal completeness, notification symmetry, resource release, cancellation propagation, no double-fire) across all interleavings with 2 concurrent workers. The current design violates P2 and P3. Model: `tla/AsyncHandle.tla`.

## Dependencies

None. This is the foundational change that subsequent specs (cleanup list, structured ownership) build on.

## Requirements

### __reach_terminal Function

Add a static function in `src/aio/aio_async.c`:

`static bool __reach_terminal(valk_async_handle_t *handle, valk_async_status_t new_status)`

Must:
- Attempt CAS from PENDING to `new_status`; if that fails, attempt CAS from RUNNING to `new_status`
- If both CAS attempts fail, return `false` (another thread won the race)
- If CAS succeeds, execute the notification sequence in this exact order:
  1. `valk_async_notify_parent(handle)`
  2. `valk_async_notify_done(handle)`
  3. `valk_async_propagate_completion(handle)`
- Return `true`

The CAS is the linearization point. Exactly one caller wins per handle. The winner runs the full notification sequence; all losers get `false` and do nothing.

### Refactor valk_async_handle_complete

Replace the body of `valk_async_handle_complete` (`src/aio/aio_async.c`):

- Remove the `is_closed` check and its silent CANCELLED transition (lines ~262-267)
- Store `result` via `atomic_store_explicit` with `memory_order_release` (existing behavior)
- Call `__reach_terminal(handle, VALK_ASYNC_COMPLETED)`
- Remove the manual CAS attempts and the inline notification calls

Signature unchanged: `void valk_async_handle_complete(valk_async_handle_t *handle, valk_lval_t *result)`

### Refactor valk_async_handle_fail

Same transformation as `complete`:

- Remove the `is_closed` check and its silent CANCELLED transition (lines ~292-297)
- Store `error` via `atomic_store_explicit` with `memory_order_release`
- Call `__reach_terminal(handle, VALK_ASYNC_FAILED)`
- Remove the manual CAS attempts and the inline notification calls

Signature unchanged: `void valk_async_handle_fail(valk_async_handle_t *handle, valk_lval_t *error)`

### Refactor valk_async_cancel_task

This is the critical fix. Replace the body of `valk_async_cancel_task` (`src/aio/aio_async.c`):

- Call `__reach_terminal(handle, VALK_ASYNC_CANCELLED)`. If it returns `false`, return early.
- Set `cancel_requested` AFTER the CAS succeeds (existing behavior, keep the `atomic_store_explicit`)
- Keep the UV timer stopping logic (the `uv_handle_ptr` magic number dispatch)
- Keep the `on_cancel` callback invocation
- Keep the child cancellation cascade (enqueue `valk_async_cancel_task` for each child)
- The key change: `__reach_terminal` now calls `notify_parent`, `notify_done`, and `propagate_completion` — previously skipped entirely

### Remove is_closed from Complete/Fail Paths

The `valk_async_is_resource_closed` check in `complete` and `fail` silently transitions to CANCELLED without notifications. Remove these checks entirely:

- Delete the `if (valk_async_is_resource_closed(handle))` block from `valk_async_handle_complete`
- Delete the `if (valk_async_is_resource_closed(handle))` block from `valk_async_handle_fail`

The `is_closed` mechanism itself (`valk_async_is_resource_closed`, the `is_closed`/`is_closed_ctx` fields, `valk_async_is_chain_closed`) is NOT removed in this spec — only its usage in `complete`/`fail` is removed. Full removal comes in a follow-up spec.

### Combinator Notification — Already Correct

The combinator resolution functions (`valk_async_all_child_completed`, `valk_async_race_child_resolved`, `valk_async_within_child_resolved`, etc.) already call `notify_parent`, `notify_done`, and `propagate_completion` after their own CAS transitions. These do NOT need to use `__reach_terminal` — they have combinator-specific logic between the CAS and the notifications (building result lists, cancelling siblings, etc.).

However, verify that all combinator completion paths call all three notifications. If any are missing, add them.

### Early Terminal Check

Both `complete` and `fail` currently check `valk_async_handle_is_terminal(current)` before attempting the CAS. Keep this early-exit optimization — it avoids unnecessary work when the handle is already terminal. The `__reach_terminal` function's CAS provides the actual safety; the early check is just a fast path.

## Non-Requirements

- This spec does NOT add the `resource_cleanups` mechanism — that comes in `async-handle-cleanup-list.md`
- This spec does NOT remove the `is_closed`/`is_closed_ctx` fields from the handle struct — that comes in `async-structured-resource-ownership.md`
- This spec does NOT change `valk_async_is_chain_closed` usage in `propagate_single` — that is a separate concern
- This spec does NOT change combinator internals — only the three core functions (`complete`, `fail`, `cancel_task`)

## Acceptance Criteria

- [ ] `__reach_terminal` exists: `grep -c '__reach_terminal' src/aio/aio_async.c` returns >= 3 (definition + 3 call sites)
- [ ] `is_closed` check removed from complete: `grep -c 'is_resource_closed' src/aio/aio_async.c` returns 1 (only the function definition itself remains)
- [ ] Cancel calls notify_parent: in `valk_async_cancel_task`, `__reach_terminal` calls `valk_async_notify_parent` — verify by adding test `test_cancel_notifies_parent` to `test/test_async.c`: cancel a child of an `all` combinator, verify the `all` parent transitions to FAILED
- [ ] Cancel calls notify_done: add test `test_cancel_fires_on_done` to `test/test_async.c`: set `on_done` on a handle, cancel it, verify `on_done` was called
- [ ] Cancel fires cleanup: add test `test_cancel_fires_cleanup` — set `cleanup_fn` on a handle, cancel it, verify cleanup ran (this validates cleanup happens on the cancel path even before resource_cleanups exists)
- [ ] No double notification: add test `test_concurrent_complete_and_cancel` — from two threads, race `complete` and `cancel` on the same handle, verify `on_done` fires exactly once
- [ ] `make build` succeeds
- [ ] `make test` passes
- [ ] `make test-c-asan` passes (no memory errors on cancel path)
