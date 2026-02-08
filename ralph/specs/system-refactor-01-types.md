# System Type Definitions and Compatibility Shims

## Overview

Define the `valk_system_t` struct, `valk_subsystem_t` interface, and `valk_system_config_t` in `src/gc.h`. Add `#define` compatibility shims so existing code using `valk_gc_coord` and `valk_global_handle_table` continues to compile unchanged. This spec adds types only — no new function implementations.

## Dependencies

- Requires `system-refactor-00-heap-rename.md` (all heap types use post-rename names)

## Requirements

### valk_subsystem_t Interface

Add to `src/gc.h`, before the `valk_system_t` definition:

```c
typedef struct {
  void (*stop)(void *ctx);
  void (*wait)(void *ctx);
  void (*destroy)(void *ctx);
  void *ctx;
} valk_subsystem_t;
```

### valk_system_t Struct

Add to `src/gc.h`. Define constants and the struct:

```c
#define VALK_SYSTEM_MAX_THREADS 64
#define VALK_SYSTEM_MAX_SUBSYSTEMS 16

typedef struct valk_system {
  valk_gc_heap_t *heap;
  valk_handle_table_t handle_table;

  _Atomic valk_gc_phase_e phase;
  _Atomic u64 threads_registered;
  valk_barrier_t barrier;
  bool barrier_initialized;
  valk_gc_thread_info_t threads[VALK_SYSTEM_MAX_THREADS];
  _Atomic u64 parallel_cycles;
  _Atomic u64 parallel_pause_us_total;

  pthread_mutex_t subsystems_lock;
  valk_subsystem_t subsystems[VALK_SYSTEM_MAX_SUBSYSTEMS];
  int subsystem_count;

  _Atomic bool shutting_down;
  int exit_code;
  bool initialized;
} valk_system_t;

extern valk_system_t *valk_sys;
```

The field names `phase`, `threads_registered`, `barrier`, `barrier_initialized`, `threads`, `parallel_cycles`, `parallel_pause_us_total` intentionally match the corresponding fields in the existing `valk_gc_coordinator_t` (lines 313-329 of `src/gc.h`). This enables the compatibility shims below.

### valk_system_config_t

Replace `valk_runtime_config_t` with:

```c
typedef struct {
  u64 gc_heap_size;
} valk_system_config_t;

static inline valk_system_config_t valk_system_config_default(void) {
  return (valk_system_config_t){.gc_heap_size = 0};
}
```

### Compatibility Shims

Add after the `valk_system_t` definition and `extern valk_sys` declaration in `src/gc.h`:

```c
#define valk_gc_coord (*valk_sys)
#define valk_global_handle_table (valk_sys->handle_table)
```

These shims let all existing code that uses `valk_gc_coord.phase`, `valk_gc_coord.barrier`, `valk_global_handle_table`, etc. compile against the new struct. Code referencing the old condvar fields (`lock`, `all_paused`, `gc_done`, `threads_paused`, `checkpoint_epoch`) will intentionally fail — those fields are removed by the STW protocol fix in `system-refactor-03-stw-protocol.md`.

### Thread Info Extension

Add `wake_fn` and `wake_ctx` fields to `valk_gc_thread_info_t` in `src/gc.h` (currently lines 293-298). Add them after the `mark_queue` field:

```c
void (*wake_fn)(void *wake_ctx);
void *wake_ctx;
```

### Thread Context Extension

Add `struct valk_system *system` field to `valk_thread_context_t` in `src/memory.h` (currently lines 303-326). Add it after the `allocator` field.

## Acceptance Criteria

- [ ] `make build` succeeds — all existing code compiles via shims
- [ ] `make test-c` passes — no behavioral changes
- [ ] `grep -n 'valk_system_t' src/gc.h` shows the struct definition
- [ ] `grep -n 'valk_subsystem_t' src/gc.h` shows the interface definition
- [ ] `grep -n 'valk_system_config_t' src/gc.h` shows the config struct
- [ ] `grep -n 'define valk_gc_coord' src/gc.h` shows the shim macro
- [ ] `grep -n 'wake_fn' src/gc.h` shows the field in `valk_gc_thread_info_t`
