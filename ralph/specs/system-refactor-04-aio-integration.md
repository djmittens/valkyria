# AIO Subsystem Integration

## Overview

Make AIO register itself as a generic subsystem via `valk_system_add_subsystem` instead of the AIO-specific `g_aio_systems[]` registry. Event loop threads register with `wake_fn` pointing to `uv_async_send` so the GC can wake them without knowing about AIO. Remove the per-loop fallback heap — event loop threads share `valk_sys->heap` via TLABs.

## Dependencies

- Requires `system-refactor-03-stw-protocol.md` (barrier-based STW works, `valk_system_wake_threads` used by GC)

## Requirements

### AIO System Registration

In `valk_aio_start_with_config()` in `src/aio/system/aio_system.c` (around line 307):

1. Remove the call to `valk_aio_register_system(sys)`
2. Add: `valk_system_add_subsystem(valk_sys, (void(*)(void*))valk_aio_stop, (void(*)(void*))valk_aio_wait_for_shutdown, (void(*)(void*))valk_aio_destroy, sys)`

### Split valk_aio_wait_for_shutdown

The current `valk_aio_wait_for_shutdown()` does both cleanup and free. Split into two:

- `valk_aio_wait_for_shutdown(sys)` — join the event loop thread, clean up task queues and slabs (existing wait/join logic)
- `valk_aio_destroy(sys)` — new function that frees the `valk_aio_system_t` struct itself (currently the last thing `wait_for_shutdown` does)

Declare `valk_aio_destroy` in `src/aio/system/aio_system.h`.

### Event Loop Thread Registration

In `__event_loop()` in `src/aio/aio_uv.c`:

1. Remove the `if (sys->config.thread_onboard_fn)` / `else` branch that either calls `thread_onboard_fn()` or creates a fallback `loop_gc_heap`
2. Replace with: `valk_system_register_thread(valk_sys, (void(*)(void*))uv_async_send, &sys->gc_wakeup)`
3. Remove `valk_gc_heap_create(0)` call — event loop shares `valk_sys->heap` via TLABs
4. Remove `valk_gc_heap_destroy(sys->loop_gc_heap)` call
5. Move `valk_system_unregister_thread(valk_sys)` to right after `uv_run` returns, before the drain loop (drain doesn't allocate GC objects)

### Remove AIO-Specific GC Functions

Delete from `src/aio/system/aio_system.c`:
- `g_aio_systems[]` array and `g_aio_systems_lock` mutex (lines 12-13)
- `valk_aio_register_system()` (lines 17-26)
- `valk_aio_unregister_system()` (lines 28-37)
- `valk_aio_wake_all_for_gc()` (lines 40-49)
- `valk_aio_wait_for_all_systems()` (lines 51-69)

Remove their declarations from `src/aio/system/aio_system.h`.

### Move Metrics Init

Remove `valk_metrics_registry_init()` call from `src/aio/system/aio_system.c` (line ~279) and the `static bool metrics_initialized` guard. This call now lives in `valk_system_create` (added in spec-02).

### Add AIO Integration Tests to test_system.c

Add to `test/test_system.c`:

- `test_aio_registers_as_subsystem` — after `valk_aio_start()`, verify `sys->subsystem_count >= 1`
- `test_event_loop_thread_has_wake_fn` — after AIO start, find a thread slot with non-NULL `wake_fn`
- `test_event_loop_shares_system_heap` — verify the event loop thread's `ctx->heap` equals `sys->heap`
- `test_system_shutdown_stops_aio` — call `valk_system_shutdown(sys, 5000)` and verify `threads_registered == 1` and `subsystem_count == 0` afterward

## Acceptance Criteria

- [ ] `make build` succeeds
- [ ] `make test-c` passes
- [ ] `make test-valk` passes
- [ ] `build/test_system` passes all tests including the 4 new AIO integration tests
- [ ] `grep -rn 'g_aio_systems\|valk_aio_register_system\|valk_aio_unregister_system\|valk_aio_wake_all_for_gc\|valk_aio_wait_for_all_systems' src/` returns no matches
- [ ] `grep -rn '#include.*aio' src/gc.c src/gc_mark.c src/gc_checkpoint.c` returns no matches (compile-time decoupling verified)
- [ ] `grep -rn 'loop_gc_heap' src/aio/` returns no matches (no per-loop heap)
