# AIO System Lifecycle Refactor

## Overview

AIO systems are runtime-owned resources using the wrong abstraction. They
register as generic "subsystems" via `valk_system_add_subsystem`, but the
subsystem mechanism exists solely for AIO — nothing else uses it. The
subsystem slot is never freed on `aio/stop`, leaking slots and forcing test
hacks (shared-sys globals). `aio/stop` returns nil, so callers can't wait
for cleanup to finish.

Fix: delete the subsystem abstraction entirely. AIO systems are slab-allocated
directly on `valk_system_t`. `aio/stop` returns an async handle that completes
when teardown is done and the slot is released. `aio/run` is removed — use
`(aio/await (aio/stop sys))` instead.

## Non-Requirements

- No changes to `aio/start` config parsing or `valk_aio_system_config_t`
- No changes to event loop internals, HTTP/2 stack, or handle slab
- No changes to GC coordination (thread registration, STW protocol)

## Requirements

### Delete Subsystem Abstraction

Remove from `src/gc.h`:
- `valk_subsystem_t` struct
- `subsystems[]` array, `subsystems_lock`, `subsystem_count` from `valk_system_t`
- `valk_system_add_subsystem()` and `valk_system_remove_subsystem()` declarations
- `VALK_SYSTEM_MAX_SUBSYSTEMS` define

Remove from `src/gc.c`:
- `valk_system_add_subsystem()` and `valk_system_remove_subsystem()` functions
- `subsystems_lock` init/destroy in create/destroy
- Subsystem iteration in `valk_system_initiate_shutdown()` and `valk_system_shutdown()`

### AIO System Slab on valk_system_t

Add to `valk_system_t` in `src/gc.h`:

| Field | Type | Description |
|-------|------|-------------|
| `aio_systems` | `struct valk_slab_t *` | Slab of `valk_aio_system_t` |

Forward-declare `struct valk_slab_t` (already exists in `gc.h`).

Initialize in `valk_system_create()`:
- `valk_slab_new(sizeof(valk_aio_system_t), 16)` — 16 max AIO systems

Destroy in `valk_system_destroy()`:
- `valk_slab_free(sys->aio_systems)`

The slab is lock-free (Treiber stack), no separate mutex needed.

### Allocate AIO Systems from Slab

In `valk_aio_start_with_config()` (`src/aio/system/aio_system.c`):

- Replace `valk_mem_alloc(sizeof(valk_aio_system_t))` with
  `valk_slab_aquire(valk_sys->aio_systems)`
- Remove `valk_system_add_subsystem()` call
- If slab acquire returns NULL, return NULL (limit reached)

### Unify stop/wait/destroy

Merge `valk_aio_wait_for_shutdown` and `valk_aio_destroy` into `valk_aio_stop`.

New signature: `valk_async_handle_t *valk_aio_stop(valk_aio_system_t *sys)`

Behavior:
1. CAS `shuttingDown` to true (existing)
2. Allocate a shutdown handle (malloc, not from system's slab — slab freed during cleanup)
3. Store handle on `sys->shutdown_handle`
4. Send stopper signal via `uv_async_send` (existing)
5. Return the handle

Add `valk_async_handle_t *shutdown_handle` field to `valk_aio_system_t`.

In `__event_loop()` (`src/aio/aio_uv.c`), after `uv_run` returns and the
drain loop finishes:
1. Run existing cleanup (join thread, free queues/slabs/arenas/semaphore)
2. Capture `shutdown_handle` before releasing
3. Release struct back to `valk_sys->aio_systems` slab
4. Complete the shutdown handle

Delete `valk_aio_wait_for_shutdown()` and `valk_aio_destroy()` from
`aio_system.c` and their declarations from `aio_system.h`.

### Process Shutdown Stops Remaining AIO Systems

In `valk_system_shutdown()` (`src/gc.c`), replace subsystem iteration with:
- Walk `sys->aio_systems` slab bitmap to find active (in-use) slots
- For each active system, call `valk_aio_stop()` then await completion
  (join the event loop thread directly since we're shutting down)

This requires `gc.c` to include the AIO header — acceptable since shutdown
is the one place the runtime needs to know about AIO.

### aio/stop Builtin Returns Handle

In `valk_builtin_aio_stop()` (`src/builtins_aio.c`):
- Call `valk_aio_stop(sys)` which now returns `valk_async_handle_t *`
- Return `valk_lval_handle(handle)`
- Callers use `(aio/await (aio/stop sys))` for synchronous teardown

### Remove aio/run Builtin

Delete `valk_builtin_aio_run()` from `src/builtins_aio.c` and its
registration `"aio/run"` in `valk_register_aio_builtins`.

`(aio/run sys)` was a busy-wait loop polling `shuttingDown`. The replacement
is `(aio/await (aio/stop sys))` — same semantics, proper async.

### Update Lisp Callers

Replace all `(aio/run sys)` with `(aio/await (aio/stop sys))`.

Replace bare `(aio/stop sys)` (returning nil) with `(aio/await (aio/stop sys))`
where the caller needs to wait for cleanup (tests, tools).

In `test/test_aio_builtins_coverage.valk`: remove `shared-sys` pattern. Each
test creates its own system and tears it down. The slab reuse guarantees no
slot exhaustion.

Key files to update (non-exhaustive, grep for `aio/run` and `aio/stop`):
- `test/test_aio_retry.valk` — already does per-test start/stop
- `test/test_aio_within.valk`
- `tools/test_server.valk`, `tools/test_client.valk`, `tools/hey.valk`
- `examples/webserver_demo.valk`
- `src/modules/test.valk`
- stress tests

### Update C Tests

In `test/test_system.c`:
- Remove `test_subsystem_add_remove` (subsystem mechanism deleted)
- Remove `test_subsystem_shutdown_order` (subsystem mechanism deleted)
- Remove `test_aio_registers_as_subsystem` (no longer uses subsystems)
- Update `test_system_shutdown_stops_aio` to verify slab-based teardown
- Add `test_aio_slab_reuse`: start/stop 20 AIO systems sequentially,
  verify slab count returns to original after each stop

## Acceptance Criteria

- [ ] Subsystem mechanism removed: `grep -rn 'valk_subsystem_t\|add_subsystem\|remove_subsystem' src/` returns 0
- [ ] AIO slab on system: `grep -c 'aio_systems' src/gc.h` returns >= 1
- [ ] AIO allocated from slab: `grep -c 'valk_slab_aquire.*aio_systems' src/aio/system/aio_system.c` returns >= 1
- [ ] `valk_aio_wait_for_shutdown` gone: `grep -rn 'valk_aio_wait_for_shutdown' src/` returns 0
- [ ] `valk_aio_destroy` gone: `grep -rn 'void valk_aio_destroy' src/` returns 0
- [ ] `aio/stop` returns handle: builtin returns `valk_lval_handle`
- [ ] `aio/run` removed: `grep -rn 'aio/run' src/builtins_aio.c` returns 0
- [ ] No `aio/run` in non-comment Valk code: `grep -n '^[^;].*aio/run' src/ test/ tools/ examples/` returns 0
- [ ] No shared-sys hack: `grep -c 'shared-sys' test/test_aio_builtins_coverage.valk` returns 0
- [ ] Slab reuse: `test_aio_slab_reuse` in `test/test_system.c` starts/stops 20 systems without exhaustion
- [ ] `make build` succeeds
- [ ] `make test` passes
- [ ] `make test-c-asan` passes
