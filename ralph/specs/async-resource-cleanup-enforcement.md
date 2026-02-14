# Async Resource Cleanup Enforcement

## Overview

Add compile-time and test-time guardrails that prevent async resources from being created without cleanup registration. After the cleanup list was added (spec 1), arena ownership was fixed (spec 2), and existing resources were migrated (spec 3), this spec closes the loop: make it structurally difficult to create a leaky resource path.

Three mechanisms: a `VALK_ASSERT` in resource creation functions, a AGENTS.md rule for AI, and a CI-friendly leak detector test.

## Dependencies

- Requires `async-resource-cleanup-migration.md` (all resources migrated to cleanup pattern)

## Requirements

### Resource Cleanup Audit Assertion

Add a debug-build assertion helper to `src/aio/aio_async.h`:

```c
#ifdef VALK_DEBUG_BUILD
#define VALK_ASSERT_HAS_CLEANUP(handle) \
  VALK_ASSERT((handle)->resource_cleanup_count > 0, \
    "async handle %llu has no resource cleanups registered", (handle)->id)
#else
#define VALK_ASSERT_HAS_CLEANUP(handle) ((void)0)
#endif
```

Insert `VALK_ASSERT_HAS_CLEANUP(handle)` at the point where async handles are dispatched for execution — specifically in `__handle_async_response` in `src/aio/http2/aio_http2_session.c`, after the cleanup registration and before the state dispatch. This catches any code path that creates an HTTP async response without registering a cleanup.

Also add the assertion after timer init functions in `src/aio/aio_comb_timers.c` — after the `on_resource_cleanup` call for sleep, schedule, and interval.

### Slab Pool Watermark Tracking

Add watermark tracking to `valk_slab_t` in `src/memory.h` (or wherever the slab is defined):

| Field | Type | Purpose |
|-------|------|---------|
| `high_watermark` | `_Atomic u64` | Peak number of items simultaneously in use |
| `total_acquires` | `_Atomic u64` | Total number of acquire calls |
| `total_releases` | `_Atomic u64` | Total number of release calls |

Update `valk_slab_acquire` to increment `total_acquires` and update `high_watermark`.
Update `valk_slab_release` to increment `total_releases`.

These counters enable leak detection tests: after a test cycle, `total_acquires == total_releases` means no leaks.

### Arena Leak Detection Test Helper

Add to `src/aio/aio_async.h` (or a test helper header):

```c
typedef struct {
  u64 acquires;
  u64 releases;
} valk_slab_snapshot_t;

static inline valk_slab_snapshot_t valk_slab_snapshot(valk_slab_t *slab) {
  return (valk_slab_snapshot_t){
    .acquires = atomic_load(&slab->total_acquires),
    .releases = atomic_load(&slab->total_releases),
  };
}

static inline bool valk_slab_snapshot_balanced(valk_slab_t *slab, valk_slab_snapshot_t before) {
  valk_slab_snapshot_t after = valk_slab_snapshot(slab);
  u64 delta_acq = after.acquires - before.acquires;
  u64 delta_rel = after.releases - before.releases;
  return delta_acq == delta_rel;
}
```

This enables any test to bracket a section with `before = snapshot(); ... ; assert(balanced(slab, before))`.

### TLA+ Model Reference

The async handle state machine and notification protocol are formally verified in `tla/AsyncHandle.tla`. The model checks invariants P1-P5 (terminal completeness, notification symmetry, resource release, cancellation propagation, no double-fire) across all interleavings with concurrent workers.

When modifying async handle lifecycle code, run the TLA+ model checker:

```bash
/usr/lib/jvm/java-21-openjdk/bin/java -XX:+UseParallelGC -cp tools/tla2tools.jar \
  tlc2.TLC -workers auto -nowarning tla/AsyncHandleAll -config tla/AsyncHandleAll.cfg
```

Scenario modules: `AsyncHandleAll`, `AsyncHandleRace`, `AsyncHandleWithin`, `AsyncHandleCancelTree`. All must pass.

Add a Makefile target `make tla` that runs all 4 scenarios and reports pass/fail.

### AGENTS.md Async Resource Rule

Add to the "Code Style" or "Error Handling" section of `AGENTS.md`:

```markdown
## Async Resource Pattern (MANDATORY)

Every C resource created inside an async handler MUST be registered for cleanup:

    valk_async_handle_on_resource_cleanup(handle, cleanup_fn, resource, ctx);

This includes: arenas, timers, stream bodies, slab items, file descriptors.

If you create a resource and don't register cleanup, the debug build will
assert and tests will fail with arena pool count mismatches.

The cleanup function runs when the handle reaches any terminal state
(completed, failed, cancelled). It runs AFTER on_done, so the resource
is still valid during response sending.
```

This gives AI implementors the pattern in context when they read AGENTS.md.

## Non-Requirements

- This spec does NOT add runtime leak detection in production builds — assertions are debug-build only
- This spec does NOT change the cleanup list mechanism itself — only adds enforcement around it

## Acceptance Criteria

- [ ] Assert macro defined: `grep -c 'VALK_ASSERT_HAS_CLEANUP' src/aio/aio_async.h` returns >= 1
- [ ] Assert used in HTTP dispatch: `grep -c 'VALK_ASSERT_HAS_CLEANUP' src/aio/http2/aio_http2_session.c` returns >= 1
- [ ] Slab watermark fields exist: `grep -c 'total_acquires\|total_releases\|high_watermark' src/memory.h` returns >= 3
- [ ] Snapshot helper exists: `grep -c 'valk_slab_snapshot' src/aio/aio_async.h` returns >= 1 (or in a test helper)
- [ ] AGENTS.md has async resource rule: `grep -c 'on_resource_cleanup' AGENTS.md` returns >= 1
- [ ] `make build` succeeds
- [ ] `make test` passes
