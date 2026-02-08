# Shim Removal and Mechanical Renames

## Overview

Remove the `#define valk_gc_coord` and `#define valk_global_handle_table` compatibility shims. Replace all remaining uses of these names with direct `valk_sys->` field access. Replace `valk_runtime_is_initialized()` calls with `(valk_sys != NULL)`.

## Dependencies

- Requires `system-refactor-05-bootstrap-rewrite.md` (all callers use new API, shims only used in residual references)

## Requirements

### Remove Shims

Delete from `src/gc.h`:
```c
#define valk_gc_coord (*valk_sys)
#define valk_global_handle_table (valk_sys->handle_table)
```

### Replace valk_gc_coord References

Replace `valk_gc_coord.` with `valk_sys->` in all remaining files. Expected locations:
- `src/gc_stats.c` — references to `valk_gc_coord.parallel_cycles`, `valk_gc_coord.parallel_pause_us_total`
- `src/gc_mark.c` — any remaining references not already updated in spec-03

### Replace valk_global_handle_table References

Replace `valk_global_handle_table` with `valk_sys->handle_table` in:
- `src/builtins_server.c`
- `src/aio/aio_comb_timers.c`
- `src/aio/aio_http2_server.c`
- `src/aio/aio_http2_client.c`
- `src/aio/aio_http2_session.c`
- `src/aio/aio_stream_builtins.c`
- `src/aio/aio_stream_body.c`

### Replace valk_runtime_is_initialized

Replace `valk_runtime_is_initialized()` with `(valk_sys != NULL)` in `src/builtins_aio.c` and any other callers.

### Remove valk_gc_coordinator_t

Delete the `valk_gc_coordinator_t` typedef from `src/gc.h` (lines 313-329) and the `extern valk_gc_coordinator_t valk_gc_coord` declaration (line 331). The `VALK_GC_SAFE_POINT` macro (lines 337-343) already references `valk_sys->phase` via the shim — update it to use `valk_sys->phase` directly.

### Set thread_ctx.system in register_thread

Verify that `valk_system_register_thread` sets `valk_thread_ctx.system = sys`. Add test.

### Add Thread Context Test

Add to `test/test_system.c`:
- `test_thread_context_has_system_pointer` — after `valk_system_create`, verify `valk_thread_ctx.system == sys`

## Acceptance Criteria

- [ ] `make build` succeeds
- [ ] `make test-c` passes
- [ ] `make test-valk` passes
- [ ] `build/test_system` passes all tests including `test_thread_context_has_system_pointer`
- [ ] `grep -n 'define valk_gc_coord\|define valk_global_handle_table' src/gc.h` returns no matches
- [ ] `grep -rn 'valk_gc_coord[^_]' src/` returns no matches
- [ ] `grep -rn 'valk_global_handle_table' src/` returns no matches
- [ ] `grep -rn 'valk_gc_coordinator_t' src/` returns no matches
- [ ] `grep -rn 'valk_runtime_is_initialized' src/` returns no matches
