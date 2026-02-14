# System Lifecycle: Create, Destroy, Register

## Overview

Implement `valk_system_create`, `valk_system_destroy`, `valk_system_shutdown`, `valk_system_register_thread`, `valk_system_unregister_thread`, `valk_system_add_subsystem`, `valk_system_remove_subsystem`, and `valk_system_wake_threads` in `src/gc.c`. Replace `valk_runtime_init` and `valk_runtime_shutdown` callers with the new API. The system struct owns the heap, handle table, and thread registry.

## Dependencies

- Requires `system-refactor-01-types.md` (types and shims exist)

## Requirements

### System API Functions

Implement in `src/gc.c`, declare in `src/gc.h`:

| Function | Signature | Purpose |
|----------|-----------|---------|
| `valk_system_create` | `valk_system_t *valk_system_create(valk_system_config_t *config)` | Allocate system via `calloc`, create heap, init handle table, init metrics, init phase to IDLE, init per-thread mark queues, init subsystems_lock, set `valk_sys`, auto-register calling thread |
| `valk_system_destroy` | `void valk_system_destroy(valk_system_t *sys)` | Destroy heap, free handle table, destroy barrier if initialized, destroy mark queues, destroy subsystems_lock, clear `valk_sys`, free struct |
| `valk_system_shutdown` | `void valk_system_shutdown(valk_system_t *sys, u64 deadline_ms)` | Set `shutting_down=true`, call `stop()` on all subsystems, spin-wait for `threads_registered` to reach 1 (with deadline), then call `wait()`+`destroy()` on all subsystems |
| `valk_system_register_thread` | `void valk_system_register_thread(valk_system_t *sys, void (*wake_fn)(void *), void *wake_ctx)` | Init malloc allocator, set thread ctx heap+system, atomic increment `threads_registered` to get slot, populate `threads[slot]` |
| `valk_system_unregister_thread` | `void valk_system_unregister_thread(valk_system_t *sys)` | Call `VALK_GC_SAFE_POINT()`, deactivate slot, clear wake_fn, atomic decrement `threads_registered` |
| `valk_system_add_subsystem` | `void valk_system_add_subsystem(valk_system_t *sys, void (*stop)(void *), void (*wait)(void *), void (*destroy)(void *), void *ctx)` | Lock, append to `subsystems[]` if under max, unlock |
| `valk_system_remove_subsystem` | `void valk_system_remove_subsystem(valk_system_t *sys, void *ctx)` | Lock, find by ctx pointer, swap-remove with last, unlock |
| `valk_system_wake_threads` | `void valk_system_wake_threads(valk_system_t *sys)` | Iterate `threads[]`, call `wake_fn(wake_ctx)` for active threads with non-NULL `wake_fn` |

### Replace valk_runtime_* Callers

In `src/repl.c`:
- Replace `valk_runtime_config_t` with `valk_system_config_t` and `valk_runtime_config_default()` with `valk_system_config_default()` (line ~40-44)
- Replace `valk_runtime_init(&runtime_cfg)` with `valk_system_t *sys = valk_system_create(&runtime_cfg)` (line 46) — note: `valk_system_create` returns a pointer, not an error code, so remove the `if (... != 0)` check
- Replace `valk_runtime_get_heap()` with `sys->heap` (line 51) — type is now `valk_gc_heap_t*` not `valk_gc_malloc_heap_t*`
- Replace `valk_runtime_shutdown()` with `valk_system_shutdown(sys, 5000); valk_system_destroy(sys)` at both exit paths (lines 151 and 218)

### Remove Old Functions

Delete from `src/gc.c`: `valk_runtime_init`, `valk_runtime_shutdown`, `valk_runtime_get_heap`, `valk_runtime_is_initialized`, `valk_runtime_get_onboard_fn`, `valk_runtime_thread_onboard`, `valk_gc_coordinator_init`.

Delete declarations from `src/gc.h`: all `valk_runtime_*` function declarations.

### Add test_system.c

Create `test/test_system.c` with the test skeleton (including 30-second alarm handler). Register it in `CMakeLists.txt` and the Makefile test runner.

Add these tests:
- `test_system_create_sets_valk_sys` — verifies `valk_sys` is set, heap exists, `initialized=true`, `threads_registered==1`, calling thread is registered
- `test_system_thread_register_gets_unique_slot` — two registrations get different `gc_thread_id` values, unregister decrements count
- `test_system_heap_alloc_works_after_create` — can allocate 64 bytes from `sys->heap` after create
- `test_system_subsystem_add_remove` — add increments count, remove-by-ctx decrements it
- `test_system_shutdown_calls_subsystem_stop_wait_destroy` — verifies `stop()` then `wait()` then `destroy()` order via sequence counters

## Acceptance Criteria

- [ ] `make build` succeeds
- [ ] `make test-c` passes (all existing tests, using shims for `valk_gc_coord`)
- [ ] `make test-valk` passes
- [ ] `build/test_system` passes all 5 new tests
- [ ] `grep -rn 'valk_runtime_init\|valk_runtime_shutdown\|valk_runtime_get_heap' src/` returns no matches
- [ ] `grep -rn 'valk_gc_coordinator_init' src/` returns no matches
