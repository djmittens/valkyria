# Dead Code Removal and Final Verification

## Overview

Remove dead code left from the refactor: `g_live_heaps[]` heap registry, `loop_gc_heap` field, and all `valk_runtime_*` declarations. Update existing test files to use the new API. Run sanitizers and stress tests to verify correctness.

## Dependencies

- Requires `system-refactor-06-mechanical-renames.md` (all shims removed, all code uses `valk_sys->` directly)

## Requirements

### Remove Heap Registry

Delete from `src/gc_heap.c`:
- `g_live_heaps[]` static array
- `valk_gc_register_heap()` function
- `valk_gc_unregister_heap()` function
- `valk_gc_is_heap_alive()` function

Remove their declarations from headers.

### Remove loop_gc_heap Field

If `loop_gc_heap` field still exists in the AIO system struct (`src/aio/aio_internal.h`), remove it. It was replaced by shared heap access via TLABs in spec-04.

### Update Existing Test Files

Update `test/test_memory.c` and `test/unit/test_gc.c` to use `valk_system_create`/`valk_system_destroy` instead of `valk_runtime_init`/`valk_runtime_shutdown`/`valk_runtime_get_heap`. Replace `valk_gc_malloc_heap_t*` with `valk_gc_heap_t*`.

### Update LSAN Suppressions

In `lsan_suppressions.txt`:
- Replace `leak:valk_runtime_init` with `leak:valk_system_create`
- Remove any suppressions referencing deleted functions

### Final Symbol Verification

No old symbols should remain in source or test files:

```bash
grep -rE 'valk_gc_coord[^_]|valk_global_handle_table|valk_runtime_|g_aio_systems|g_live_heaps|heap2_|tlab2_|page2_|stats2_|valk_gc_malloc_' src/ test/
```

This must return no matches.

## Acceptance Criteria

- [ ] `make build` succeeds
- [ ] `make test-c` passes (all C tests including test_system.c)
- [ ] `make test-valk` passes (all Valk tests including shutdown/exit tests)
- [ ] `make test-c-asan` passes (AddressSanitizer: no memory errors)
- [ ] `make test-c-tsan` passes (ThreadSanitizer: no data races)
- [ ] `make lint` passes (static analysis clean)
- [ ] `for i in $(seq 50); do build/test_system --test barrier_two_threads_no_deadlock || exit 1; done` passes
- [ ] `grep -rE 'valk_gc_coord[^_]|valk_global_handle_table|valk_runtime_|g_aio_systems|g_live_heaps|heap2_|tlab2_|page2_|stats2_|valk_gc_malloc_' src/ test/` returns no matches
