# STW Protocol: Replace Condvars with Barriers

## Overview

Replace the broken condvar-based stop-the-world protocol with the barrier mechanism already used by GC mark/sweep phases. The current protocol in `gc_checkpoint.c` and `gc_mark.c` uses `threads_paused` counter + `all_paused`/`gc_done` condvars that deadlock ~1-2% of the time due to missed wakeups. The barrier internally uses mutex+condvar+counter where the last thread to arrive broadcasts — no missed wakeups possible.

## Dependencies

- Requires `system-refactor-02-lifecycle.md` (system API exists, `valk_sys` is set, `valk_system_wake_threads` exists)

## Requirements

### Remove Old Condvar Fields

Remove these fields from `valk_gc_coordinator_t` in `src/gc.h` (lines 313-329):
- `_Atomic u64 threads_paused`
- `_Atomic u64 checkpoint_epoch`
- `pthread_mutex_t lock`
- `pthread_cond_t all_paused`
- `pthread_cond_t gc_done`

Since the shim `#define valk_gc_coord (*valk_sys)` maps to `valk_system_t` which doesn't have these fields, any code still referencing them will fail to compile — this is intentional and forces the rewrite.

### Rewrite valk_checkpoint_request_stw

In `src/gc_checkpoint.c` (currently lines 80-118), replace the condvar-based implementation:

1. CAS `valk_sys->phase` from `IDLE` to `CHECKPOINT_REQUESTED`
2. If only 1 thread, reset to IDLE and return
3. Reset or init `valk_sys->barrier` to `num_threads`
4. Call `valk_system_wake_threads(valk_sys)` (replaces `valk_aio_wake_all_for_gc()`)
5. `valk_barrier_wait(&valk_sys->barrier)` — ENTRY barrier, all threads arrive

### Rewrite valk_checkpoint_release_stw

In `src/gc_checkpoint.c` (currently lines 120-130), replace condvar broadcast:

1. Check phase is `CHECKPOINT_REQUESTED`
2. Set phase to `IDLE`
3. `valk_barrier_wait(&valk_sys->barrier)` — EXIT barrier, release responders

### Rewrite valk_gc_heap_request_stw

In `src/gc_mark.c` (currently `valk_gc_heap2_request_stw` at lines 279-328 — renamed in spec-00):

1. CAS `valk_sys->phase` from `IDLE` to `STW_REQUESTED`
2. Get `num_threads`, return false if 0
3. Reset or init `valk_sys->barrier` to `num_threads`
4. Store heap into `__gc_heap_current`
5. Call `valk_system_wake_threads(valk_sys)` (replaces `valk_aio_wake_all_for_gc()`)
6. `valk_barrier_wait(&valk_sys->barrier)` — ENTRY barrier

### Rewrite valk_gc_safe_point_slow

In `src/gc.c`, replace the current safe point implementation:

1. Load `valk_sys->phase`
2. If `CHECKPOINT_REQUESTED`: two barrier waits (ENTRY + EXIT), return
3. If `STW_REQUESTED`: checkpoint own scratch if available, barrier wait (ENTRY), then `valk_gc_participate_in_parallel_gc()`

### Remove AIO Include from GC Files

After these changes, `src/gc_checkpoint.c` and `src/gc_mark.c` no longer call `valk_aio_wake_all_for_gc()` — they call `valk_system_wake_threads()` instead. Remove `#include` of any `aio*.h` headers from `src/gc.c`, `src/gc_mark.c`, and `src/gc_checkpoint.c`.

### Add STW Tests to test_system.c

Add to `test/test_system.c`:

- `test_barrier_two_threads_no_deadlock` — start system + AIO, run 20 GC cycles with `valk_gc_heap_collect`, verify no deadlock (30-second alarm kills test if hung)
- `test_checkpoint_does_not_deadlock_with_aio` — start system + AIO with scratch arena, run 20 `valk_checkpoint` calls, verify no deadlock
- `test_gc_phase_returns_to_idle` — after `valk_gc_heap_collect`, verify `valk_sys->phase == VALK_GC_PHASE_IDLE`

## Acceptance Criteria

- [ ] `make build` succeeds
- [ ] `make test-c` passes
- [ ] `make test-valk` passes
- [ ] `build/test_system` passes all tests including the 3 new STW tests
- [ ] `for i in $(seq 50); do build/test_system --test barrier_two_threads_no_deadlock || exit 1; done` passes (50x deadlock stress test)
- [ ] `grep -rn '#include.*aio' src/gc.c src/gc_mark.c src/gc_checkpoint.c` returns no matches
- [ ] `grep -rn 'threads_paused\|checkpoint_epoch\|all_paused\|gc_done' src/gc.h` returns no matches (old condvar fields removed)
