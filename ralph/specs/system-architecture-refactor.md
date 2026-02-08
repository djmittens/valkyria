# System Architecture Refactor

## Overview

Replace the scattered global state in the Valkyria C runtime with a unified `valk_system_t` struct that owns the GC heap, GC coordinator, handle table, and metrics registry. Fix the broken checkpoint STW protocol by replacing ad-hoc condvars with the barrier mechanism already used by the GC mark/sweep phases. Add a generic subsystem interface for graceful shutdown coordination, decoupling the GC from AIO at compile time. Rewrite the bootstrap loop so `(shutdown)` returns a code to the caller instead of calling `exit()`. Clean up vestigial "2" suffixes from the heap type migration.

## Requirements

### Dependencies

- Existing barrier implementation in `src/gc.c` (`valk_barrier_init/wait/reset/destroy`) — used unchanged
- Existing AIO drain loop in `src/aio/aio_uv.c` (100ms/300ms/500ms phases) — used unchanged
- Existing handle table internals in `src/gc.c` — used unchanged
- Existing heap struct in `src/gc_heap.h` (currently `valk_gc_heap2_t`, renamed to `valk_gc_heap_t` in Phase 0) — internals unchanged

### Problem Statement

The runtime has 6 unrelated globals that should be one struct:

| Global | Location | Purpose |
|--------|----------|---------|
| `valk_gc_coord` | `gc.c` | GC coordinator (phase, barriers, threads, condvars) |
| `__runtime_heap` | `gc.c` (static) | Singleton GC heap |
| `valk_global_handle_table` | `gc.c` | Cross-thread GC root slots |
| `g_aio_systems[]` | `aio_system.c` (static) | AIO event loop registry |
| `g_live_heaps[]` | `gc_heap.c` (static) | Heap validity registry |
| `g_metrics` | `metrics_v2.c` | Metrics registry (init buried in AIO startup) |

The checkpoint STW protocol uses condvars (`threads_paused` + `all_paused`/`gc_done`) that deadlock ~1-2% of the time due to missed wakeups. The STW GC protocol uses barriers and works correctly.

Shutdown is ad-hoc: `(exit N)` calls `exit()` directly, `(shutdown N)` searches the env for a symbol named `aio`.

Additionally, all heap-related types and functions carry a vestigial "2" suffix (`valk_gc_heap2_t`, `valk_gc_page2_t`, etc.) from a migration that replaced the original malloc-based heap. The original heap no longer exists — the "2" suffix is meaningless and should be removed.

### Phase 0: Heap Rename (Prerequisite)

Before the architecture refactor, clean up all vestigial "2" suffixes from heap types and functions. This is a purely mechanical rename — no logic changes.

**Type renames** (these are exact text replacements):

| Old | New |
|-----|-----|
| `struct valk_gc_page2` | `struct valk_gc_page` |
| `valk_gc_page2_t` | `valk_gc_page_t` |
| `struct valk_gc_tlab2` | `struct valk_gc_tlab` |
| `valk_gc_tlab2_t` | `valk_gc_tlab_t` |
| `struct valk_gc_heap2` | `struct valk_gc_heap` |
| `valk_gc_heap2_t` | `valk_gc_heap_t` |
| `struct valk_gc_stats2` | `struct valk_gc_stats` |
| `valk_gc_stats2_t` | `valk_gc_stats_t` |
| `struct valk_gc_mark_ctx2` | `struct valk_gc_mark_ctx` |
| `valk_gc_mark_ctx2_t` | `valk_gc_mark_ctx_t` |
| `valk_gc_malloc_heap_t` | `valk_gc_heap_t` (remove the typedef in `gc_heap.h:279`) |

**Function renames** (exact text replacements):

| Old | New |
|-----|-----|
| `valk_gc_heap2_create` | `valk_gc_heap_create` |
| `valk_gc_heap2_destroy` | `valk_gc_heap_destroy` |
| `valk_gc_heap2_alloc` | `valk_gc_heap_alloc` |
| `valk_gc_heap2_realloc` | `valk_gc_heap_realloc` |
| `valk_gc_heap2_used_bytes` | `valk_gc_heap_used_bytes` |
| `valk_gc_heap2_get_stats` | `valk_gc_heap_get_stats` |
| `valk_gc_heap2_collect` | `valk_gc_heap_collect` |
| `valk_gc_heap2_mark_object` | `valk_gc_heap_mark_object` |
| `valk_gc_heap2_parallel_mark` | `valk_gc_heap_parallel_mark` |
| `valk_gc_heap2_parallel_sweep` | `valk_gc_heap_parallel_sweep` |
| `valk_gc_heap2_request_stw` | `valk_gc_heap_request_stw` |
| `valk_gc_heap2_alloc_large` | `valk_gc_heap_alloc_large` |
| `valk_gc_heap2_try_emergency_gc` | `valk_gc_heap_try_emergency_gc` |
| `valk_gc_heap2_offer_termination` | `valk_gc_heap_offer_termination` |
| `valk_gc_tlab2_init` | `valk_gc_tlab_init` |
| `valk_gc_tlab2_reset` | `valk_gc_tlab_reset` |
| `valk_gc_tlab2_abandon` | `valk_gc_tlab_abandon` |
| `valk_gc_tlab2_invalidate_heap` | `valk_gc_tlab_invalidate_heap` |
| `valk_gc_tlab2_refill` | `valk_gc_tlab_refill` |
| `valk_gc_tlab2_alloc` | `valk_gc_tlab_alloc` |
| `valk_gc_page2_alloc_bitmap` | `valk_gc_page_alloc_bitmap` |
| `valk_gc_page2_mark_bitmap` | `valk_gc_page_mark_bitmap` |
| `valk_gc_page2_slots` | `valk_gc_page_slots` |
| `valk_gc_page2_slot_ptr` | `valk_gc_page_slot_ptr` |
| `valk_gc_page2_try_mark` | `valk_gc_page_try_mark` |
| `valk_gc_page2_is_marked` | `valk_gc_page_is_marked` |
| `valk_gc_page2_is_allocated` | `valk_gc_page_is_allocated` |
| `valk_gc_page2_alloc` (static in gc_heap.c) | `valk_gc_page_alloc` |
| `valk_gc_page2_find_free_slots` (static in gc_heap.c) | `valk_gc_page_find_free_slots` |
| `valk_gc_sweep_page2` | `valk_gc_sweep_page` |
| `mark_children2` | `mark_children` |
| `mark_env2` | `mark_env` |
| `mark_lval2` | `mark_lval` |

**Static variable renames** (in `src/gc_mark.c`):

| Old | New |
|-----|-----|
| `__gc_heap2_offered` | `__gc_heap_offered` |
| `__gc_heap2_terminated` | `__gc_heap_terminated` |
| `__gc_heap2_current` | `__gc_heap_current` |
| `__gc_heap2_term_lock` | `__gc_heap_term_lock` |
| `__gc_heap2_term_cond` | `__gc_heap_term_cond` |

**`valk_gc_malloc_*` wrapper removal:**

The `valk_gc_malloc_*` functions in `src/gc.c` are thin wrappers around `valk_gc_heap_*`. Replace all callers with direct calls:

| Old wrapper call | Replace with |
|-----------------|--------------|
| `valk_gc_malloc_heap_init(size)` | `valk_gc_heap_create(size)` |
| `valk_gc_malloc_heap_alloc(heap, size, type)` | `valk_gc_heap_alloc(heap, size, type)` |
| `valk_gc_malloc_heap_destroy(heap)` | `valk_gc_heap_destroy(heap)` |
| `valk_gc_malloc_collect(heap, root)` | `valk_gc_heap_collect(heap)` |

Functions with their own logic get simple renames:

| Old | New |
|-----|-----|
| `valk_gc_malloc_set_root` | `valk_gc_set_root` |
| `valk_gc_malloc_should_collect` | `valk_gc_should_collect` |
| `valk_gc_malloc_print_stats` | `valk_gc_print_stats` |

**Additional cleanup:**
- Remove orphaned forward declaration `struct valk_gc_tlab;` from `src/memory.h` (line ~301)
- Remove the `typedef valk_gc_heap2_t valk_gc_malloc_heap_t;` line from `src/gc_heap.h`
- Update `lsan_suppressions.txt`: `leak:valk_gc_heap2_alloc` -> `leak:valk_gc_heap_alloc`, `leak:valk_gc_malloc_heap_alloc` -> `leak:valk_gc_heap_alloc`

**Files affected** (all require `sed` or equivalent replacements):

Source: `src/gc_heap.h`, `src/gc_heap.c`, `src/gc_heap_lifecycle.c`, `src/gc_heap_sweep.c`, `src/gc_mark.c`, `src/gc.h`, `src/gc.c`, `src/gc_stats.c`, `src/gc_checkpoint.c`, `src/gc_evacuation.c`, `src/gc_region.c`, `src/memory.h`, `src/memory.c`, `src/lenv.c`, `src/repl.c`, `src/builtins_io.c`, `src/builtins_aio.c`, `src/builtins_mem.c`, `src/aio/aio.h`, `src/aio/aio_uv.c`, `src/aio/aio_internal.h`, `src/aio/aio_metrics.h`, `src/aio/aio_metrics.c`, `src/aio/aio_diagnostics_builtins.c`, `src/aio/system/aio_system.c`, `src/aio/system/aio_system.h`

Tests: `test/test_memory.c`, `test/unit/test_gc.c`

Other: `lsan_suppressions.txt`

### Migration Strategy

This refactor uses temporary compatibility shims to keep the build working at each phase. The shims are `#define` macros that redirect old names to new locations.

**Phase 1-2 shim** (added in `src/gc.h` after `valk_system_t` definition, removed in Phase 5):

```c
#define valk_gc_coord (*valk_sys)
#define valk_global_handle_table (valk_sys->handle_table)
```

These shims let all existing code that references `valk_gc_coord.phase`, `valk_gc_coord.threads_registered`, `valk_gc_coord.barrier`, etc. compile against `valk_sys->phase`, `valk_sys->threads_registered`, `valk_sys->barrier`, etc. without changing every file at once.

**Important**: The shim `#define valk_gc_coord (*valk_sys)` works because `valk_system_t` has the same field names as the old `valk_gc_coordinator_t` for the fields that matter: `phase`, `threads_registered`, `barrier`, `barrier_initialized`, `threads[]`, `parallel_cycles`, `parallel_pause_us_total`. The old condvar fields (`lock`, `all_paused`, `gc_done`, `threads_paused`, `checkpoint_epoch`) are NOT in `valk_system_t` — code referencing them will fail to compile, which is intentional (Phase 3 rewrites that code).

### `valk_system_t` Struct Definition

Define in `src/gc.h` (note: uses `valk_gc_heap_t` — the post-Phase-0 name):

```c
#define VALK_SYSTEM_MAX_THREADS 64
#define VALK_SYSTEM_MAX_SUBSYSTEMS 16

typedef struct {
  void (*stop)(void *ctx);
  void (*wait)(void *ctx);
  void (*destroy)(void *ctx);
  void *ctx;
} valk_subsystem_t;

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

### Thread Info with Wake Function

Add `wake_fn` and `wake_ctx` to `valk_gc_thread_info_t` in `src/gc.h`. The current struct has fields `ctx`, `thread_id`, `active`, `mark_queue`. Add the two new fields after `mark_queue`:

```c
typedef struct valk_gc_thread_info {
  void *ctx;
  pthread_t thread_id;
  bool active;
  valk_gc_mark_queue_t mark_queue;
  void (*wake_fn)(void *wake_ctx);
  void *wake_ctx;
} valk_gc_thread_info_t;
```

Event loop threads register with `wake_fn` pointing to a wrapper around `uv_async_send` and `wake_ctx = &sys->gc_wakeup`. Main thread registers with `wake_fn = NULL`.

### System API

Declare in `src/gc.h`, implement in `src/gc.c`:

| Function | Signature | Purpose |
|----------|-----------|---------|
| `valk_system_create` | `valk_system_t *valk_system_create(valk_system_config_t *config)` | Allocate system, create heap, init handle table, init metrics, onboard calling thread |
| `valk_system_destroy` | `void valk_system_destroy(valk_system_t *sys)` | Free heap, handle table, barrier, mark queues, the struct itself |
| `valk_system_shutdown` | `void valk_system_shutdown(valk_system_t *sys, u64 deadline_ms)` | Stop subsystems, wait for threads to unregister, wait+destroy subsystems |
| `valk_system_register_thread` | `void valk_system_register_thread(valk_system_t *sys, void (*wake_fn)(void *), void *wake_ctx)` | Set thread ctx heap, assign TLAB, increment threads_registered |
| `valk_system_unregister_thread` | `void valk_system_unregister_thread(valk_system_t *sys)` | Participate in pending STW, decrement threads_registered |
| `valk_system_add_subsystem` | `void valk_system_add_subsystem(valk_system_t *sys, void (*stop)(void *), void (*wait)(void *), void (*destroy)(void *), void *ctx)` | Register shutdown participant |
| `valk_system_remove_subsystem` | `void valk_system_remove_subsystem(valk_system_t *sys, void *ctx)` | Unregister shutdown participant |
| `valk_system_wake_threads` | `void valk_system_wake_threads(valk_system_t *sys)` | Iterate threads[], call wake_fn(wake_ctx) where non-NULL |

### System API Implementation

These are the complete function bodies for `src/gc.c` (using post-Phase-0 names):

```c
valk_system_t *valk_sys = NULL;

valk_system_t *valk_system_create(valk_system_config_t *config) {
  valk_system_t *sys = calloc(1, sizeof(valk_system_t));

  sys->heap = valk_gc_heap_create(config->gc_heap_size);
  valk_handle_table_init(&sys->handle_table);
  valk_metrics_registry_init();

  atomic_store(&sys->phase, VALK_GC_PHASE_IDLE);
  atomic_store(&sys->threads_registered, 0);
  atomic_store(&sys->shutting_down, false);

  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    sys->threads[i].active = false;
    valk_gc_mark_queue_init(&sys->threads[i].mark_queue);
  }

  pthread_mutex_init(&sys->subsystems_lock, NULL);

  valk_sys = sys;
  sys->initialized = true;

  valk_system_register_thread(sys, NULL, NULL);

  return sys;
}

void valk_system_shutdown(valk_system_t *sys, u64 deadline_ms) {
  atomic_store(&sys->shutting_down, true);

  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++)
    sys->subsystems[i].stop(sys->subsystems[i].ctx);
  pthread_mutex_unlock(&sys->subsystems_lock);

  u64 start = now_us() / 1000;
  while (atomic_load(&sys->threads_registered) > 1) {
    if (now_us() / 1000 - start > deadline_ms) {
      fprintf(stderr, "WARN: Shutdown deadline expired, %llu threads still registered\n",
              (unsigned long long)(atomic_load(&sys->threads_registered) - 1));
      break;
    }
    usleep(1000);
  }

  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    sys->subsystems[i].wait(sys->subsystems[i].ctx);
    sys->subsystems[i].destroy(sys->subsystems[i].ctx);
  }
  sys->subsystem_count = 0;
  pthread_mutex_unlock(&sys->subsystems_lock);
}

void valk_system_destroy(valk_system_t *sys) {
  valk_gc_heap_destroy(sys->heap);
  valk_handle_table_free(&sys->handle_table);

  if (sys->barrier_initialized)
    valk_barrier_destroy(&sys->barrier);

  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++)
    valk_gc_mark_queue_destroy(&sys->threads[i].mark_queue);

  pthread_mutex_destroy(&sys->subsystems_lock);

  if (valk_sys == sys) valk_sys = NULL;
  free(sys);
}

void valk_system_register_thread(valk_system_t *sys,
                                  void (*wake_fn)(void *),
                                  void *wake_ctx) {
  valk_mem_init_malloc();
  valk_thread_ctx.heap = sys->heap;
  valk_thread_ctx.system = sys;

  u64 slot = atomic_fetch_add(&sys->threads_registered, 1);
  valk_thread_ctx.gc_thread_id = slot;
  valk_thread_ctx.gc_registered = true;

  sys->threads[slot].ctx = &valk_thread_ctx;
  sys->threads[slot].thread_id = pthread_self();
  sys->threads[slot].active = true;
  sys->threads[slot].wake_fn = wake_fn;
  sys->threads[slot].wake_ctx = wake_ctx;
}

void valk_system_unregister_thread(valk_system_t *sys) {
  VALK_GC_SAFE_POINT();

  u64 id = valk_thread_ctx.gc_thread_id;
  sys->threads[id].active = false;
  sys->threads[id].wake_fn = NULL;
  atomic_fetch_sub(&sys->threads_registered, 1);
  valk_thread_ctx.gc_registered = false;
}

void valk_system_wake_threads(valk_system_t *sys) {
  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (sys->threads[i].active && sys->threads[i].wake_fn)
      sys->threads[i].wake_fn(sys->threads[i].wake_ctx);
  }
}

void valk_system_add_subsystem(valk_system_t *sys,
                                void (*stop)(void *),
                                void (*wait)(void *),
                                void (*destroy)(void *),
                                void *ctx) {
  pthread_mutex_lock(&sys->subsystems_lock);
  if (sys->subsystem_count < VALK_SYSTEM_MAX_SUBSYSTEMS) {
    sys->subsystems[sys->subsystem_count++] = (valk_subsystem_t){
      .stop = stop, .wait = wait, .destroy = destroy, .ctx = ctx
    };
  }
  pthread_mutex_unlock(&sys->subsystems_lock);
}

void valk_system_remove_subsystem(valk_system_t *sys, void *ctx) {
  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    if (sys->subsystems[i].ctx == ctx) {
      sys->subsystems[i] = sys->subsystems[--sys->subsystem_count];
      break;
    }
  }
  pthread_mutex_unlock(&sys->subsystems_lock);
}
```

### `valk_system_config_t`

Replace `valk_runtime_config_t` with:

```c
typedef struct {
  u64 gc_heap_size;
} valk_system_config_t;

static inline valk_system_config_t valk_system_config_default(void) {
  return (valk_system_config_t){.gc_heap_size = 0};
}
```

### Globals to Remove

| Old | Replacement |
|-----|-------------|
| `valk_gc_coordinator_t valk_gc_coord` | Fields inlined into `valk_system_t` |
| `__runtime_heap` (static in gc.c) | `valk_sys->heap` |
| `valk_global_handle_table` | `valk_sys->handle_table` |
| `g_aio_systems[]` (static in aio_system.c) | `valk_sys->subsystems[]` (generic) |
| `g_aio_systems_lock` | `valk_sys->subsystems_lock` |
| `g_live_heaps[]` (static in gc_heap.c) | Removed (one heap per system) |
| `threads_paused`, `checkpoint_epoch` | Removed (barriers handle counting) |
| `all_paused` condvar, `gc_done` condvar | Removed (barriers replace them) |
| `valk_gc_coord.lock` mutex | Removed (barriers replace it) |

### Functions to Remove

| Old | Replacement |
|-----|-------------|
| `valk_runtime_init` | `valk_system_create` |
| `valk_runtime_shutdown` | `valk_system_shutdown` + `valk_system_destroy` |
| `valk_runtime_get_heap` | `valk_sys->heap` |
| `valk_runtime_is_initialized` | `valk_sys != NULL` |
| `valk_runtime_get_onboard_fn` | Removed (threads register directly) |
| `valk_runtime_thread_onboard` | `valk_system_register_thread` |
| `valk_gc_coordinator_init` | Inlined into `valk_system_create` |
| `valk_aio_register_system` | `valk_system_add_subsystem` |
| `valk_aio_unregister_system` | `valk_system_remove_subsystem` |
| `valk_aio_wake_all_for_gc` | `valk_system_wake_threads` |
| `valk_aio_wait_for_all_systems` | `valk_system_shutdown` |
| `valk_gc_register_heap` | Removed |
| `valk_gc_unregister_heap` | Removed |
| `valk_gc_is_heap_alive` | Removed |

### STW Protocol Fix

Replace the broken condvar-based checkpoint protocol with the barrier mechanism already used by GC mark/sweep.

**`valk_checkpoint_request_stw()` in `src/gc_checkpoint.c` — new implementation:**

```c
static void valk_checkpoint_request_stw(void) {
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_sys->phase, &expected,
                                       VALK_GC_PHASE_CHECKPOINT_REQUESTED))
    return;

  u64 num_threads = atomic_load(&valk_sys->threads_registered);
  if (num_threads <= 1) {
    atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);
    return;
  }

  if (valk_sys->barrier_initialized)
    valk_barrier_reset(&valk_sys->barrier, num_threads);
  else {
    valk_barrier_init(&valk_sys->barrier, num_threads);
    valk_sys->barrier_initialized = true;
  }

  valk_system_wake_threads(valk_sys);
  valk_barrier_wait(&valk_sys->barrier);  // ENTRY — all threads arrive
}
```

**`valk_checkpoint_release_stw()` in `src/gc_checkpoint.c` — new implementation:**

```c
static void valk_checkpoint_release_stw(void) {
  if (atomic_load(&valk_sys->phase) != VALK_GC_PHASE_CHECKPOINT_REQUESTED)
    return;

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);
  valk_barrier_wait(&valk_sys->barrier);  // EXIT — release responders
}
```

**`valk_gc_heap_request_stw()` in `src/gc_mark.c` — new implementation** (note: renamed from `valk_gc_heap2_request_stw` in Phase 0):

```c
bool valk_gc_heap_request_stw(valk_gc_heap_t *heap) {
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_sys->phase, &expected,
                                       VALK_GC_PHASE_STW_REQUESTED))
    return false;

  u64 num_threads = atomic_load(&valk_sys->threads_registered);
  if (num_threads == 0) return false;

  if (valk_sys->barrier_initialized)
    valk_barrier_reset(&valk_sys->barrier, num_threads);
  else {
    valk_barrier_init(&valk_sys->barrier, num_threads);
    valk_sys->barrier_initialized = true;
  }

  atomic_store(&__gc_heap_current, heap);
  atomic_thread_fence(memory_order_seq_cst);

  valk_system_wake_threads(valk_sys);
  valk_barrier_wait(&valk_sys->barrier);  // ENTRY — all threads arrive
  return true;
}
```

**`valk_gc_safe_point_slow()` in `src/gc.c` — new implementation:**

```c
void valk_gc_safe_point_slow(void) {
  valk_gc_phase_e phase = atomic_load(&valk_sys->phase);

  if (phase == VALK_GC_PHASE_CHECKPOINT_REQUESTED) {
    valk_barrier_wait(&valk_sys->barrier);   // ENTRY
    valk_barrier_wait(&valk_sys->barrier);   // EXIT
    return;
  }

  if (phase == VALK_GC_PHASE_STW_REQUESTED) {
    if (valk_thread_ctx.scratch && valk_thread_ctx.scratch->offset > 0 &&
        valk_thread_ctx.heap && valk_thread_ctx.root_env) {
      valk_checkpoint(valk_thread_ctx.scratch, valk_thread_ctx.heap,
                      valk_thread_ctx.root_env);
    }

    valk_barrier_wait(&valk_sys->barrier);   // ENTRY
    valk_gc_participate_in_parallel_gc();     // internal barriers for mark/sweep
  }
}
```

**Protocol diagram:**

```
Requester (checkpoint or GC):
  1. CAS phase -> REQUESTED
  2. Reset barrier(threads_registered)
  3. valk_system_wake_threads(sys)
  4. barrier_wait()                  // ENTRY — all threads arrive

  ... requester does work ...

  5. phase -> IDLE
  6. barrier_wait()                  // EXIT — release responders

Responder (checkpoint case):
  1. barrier_wait()                  // ENTRY
  2. barrier_wait()                  // EXIT
  3. return

Responder (STW GC case):
  1. Checkpoint own scratch
  2. barrier_wait()                  // ENTRY
  3. Participate in parallel mark/sweep (internal barriers)
  4. return
```

The barrier internally uses mutex + condvar + counter. Last thread to arrive broadcasts. No missed wakeups possible.

### Checkpoint Edge Case: Called During STW GC

When `valk_checkpoint()` is called from `safe_point_slow` during STW GC (workers checkpoint their scratch before GC), the CAS in `checkpoint_request_stw` fails (phase is already STW_REQUESTED). `request_stw` returns early without touching the barrier. Evacuation runs uncoordinated — correct because all threads are already paused.

### Shutdown Protocol

```c
void valk_system_shutdown(valk_system_t *sys, u64 deadline_ms) {
  // 1. Set shutting_down flag
  atomic_store(&sys->shutting_down, true);

  // 2. Stop all subsystems (AIO: uv_async_send -> uv_stop -> drain loop)
  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++)
    sys->subsystems[i].stop(sys->subsystems[i].ctx);
  pthread_mutex_unlock(&sys->subsystems_lock);

  // 3. Wait for threads to unregister (event loop threads unregister after drain)
  u64 start = now_us() / 1000;
  while (atomic_load(&sys->threads_registered) > 1) {
    if (now_us() / 1000 - start > deadline_ms) {
      fprintf(stderr, "WARN: Shutdown deadline expired, %llu threads still registered\n",
              (unsigned long long)(atomic_load(&sys->threads_registered) - 1));
      break;
    }
    usleep(1000);
  }

  // 4. Wait + destroy subsystems
  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    sys->subsystems[i].wait(sys->subsystems[i].ctx);
    sys->subsystems[i].destroy(sys->subsystems[i].ctx);
  }
  sys->subsystem_count = 0;
  pthread_mutex_unlock(&sys->subsystems_lock);
}
```

In-flight Lisp callbacks complete naturally. No preemption. The current callback finishes, response is sent, then `uv_run` sees the stop flag and returns. The existing drain loop (100ms graceful -> 300ms force-close -> 500ms hard deadline) handles cleanup.

### Bootstrap Eval Loop

Rewrite `repl.c` to use `valk_system_create/shutdown/destroy` instead of `valk_runtime_init/shutdown` and `valk_aio_wait_for_all_systems`.

**Changes to `repl.c` `main()`:**

1. Replace `valk_runtime_config_t` with `valk_system_config_t` and `valk_runtime_config_default()` with `valk_system_config_default()`
2. Replace `valk_runtime_init(&runtime_cfg)` with `valk_system_create(&runtime_cfg)` — returns a `valk_system_t*` pointer (not an int error code), so remove the error check `if (... != 0)`
3. Replace `valk_runtime_get_heap()` with `sys->heap` (where `sys` is the return value of `valk_system_create`). Note: after Phase 0, the heap type is `valk_gc_heap_t*` (not `valk_gc_malloc_heap_t*`)
4. In script mode exit path (line ~134-154): replace `valk_aio_wait_for_all_systems()` and `valk_runtime_shutdown()` with `valk_system_shutdown(sys, 5000)` and `valk_system_destroy(sys)`
5. In REPL exit path (line ~209-218): remove the manual AIO stop code (lines 210-215 that look up `aio` symbol and call `valk_aio_stop`), replace `valk_runtime_shutdown()` with `valk_system_shutdown(sys, 5000)` and `valk_system_destroy(sys)`

### `(shutdown N)` Builtin Changes

Current `valk_builtin_shutdown()` in `src/builtins_aio.c` (line ~304) does two things:
1. Sets `VALK_EXIT_CODE` in env
2. Looks up `aio` symbol in env and calls `valk_aio_stop()` on it

**New behavior**: Only set `VALK_EXIT_CODE` and return. Remove the AIO lookup/stop code (lines ~314-318). The bootstrap loop in `repl.c` reads `VALK_EXIT_CODE`, then calls `valk_system_shutdown()` which stops all registered subsystems generically.

```c
static valk_lval_t* valk_builtin_shutdown(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_LE(a, a, 1);
  int code = 0;
  if (valk_lval_list_count(a) == 1) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
    code = (int)valk_lval_list_nth(a, 0)->num;
  }
  valk_lenv_def(e, valk_lval_sym("VALK_EXIT_CODE"), valk_lval_num(code));
  return valk_lval_num(code);
}
```

### `(exit N)` Builtin

Remove `valk_builtin_exit()` from `src/builtins_aio.c` (lines ~292-301). In `valk_register_aio_builtins()` (line ~339), change `"exit"` to point to `valk_builtin_shutdown` instead.

### AIO Event Loop Thread Changes

Simplify `__event_loop()` in `src/aio/aio_uv.c`:

1. Remove the `if (sys->config.thread_onboard_fn)` / `else` branch that either calls `thread_onboard_fn()` or creates a fallback `loop_gc_heap`
2. Replace with a single call: `valk_system_register_thread(valk_sys, (void(*)(void*))uv_async_send, &sys->gc_wakeup)`
3. Remove `valk_gc_heap_create(0)` call (was `valk_gc_malloc_heap_init(0)` before Phase 0; event loop shares `valk_sys->heap` via TLABs)
4. Remove `valk_gc_heap_destroy(sys->loop_gc_heap)` call (was `valk_gc_malloc_heap_destroy` before Phase 0)
5. Move `valk_system_unregister_thread(valk_sys)` to right after `uv_run` returns, before the drain loop (drain doesn't allocate GC objects)

### AIO System Registration

In `valk_aio_start_with_config()` in `src/aio/system/aio_system.c`:

1. Remove the call to `valk_aio_register_system(sys)`
2. Add: `valk_system_add_subsystem(valk_sys, (void(*)(void*))valk_aio_stop, (void(*)(void*))valk_aio_wait_for_shutdown, (void(*)(void*))valk_aio_destroy, sys)`
3. Split the existing `valk_aio_wait_for_shutdown()` into two functions:
   - `valk_aio_wait_for_shutdown(sys)` — joins the event loop thread, cleans up task queues and slabs (the existing wait/join logic)
   - `valk_aio_destroy(sys)` — new function that frees the `valk_aio_system_t` struct itself (currently the last thing `valk_aio_wait_for_shutdown` does)
4. Remove `valk_metrics_registry_init()` call (now called in `valk_system_create`)
5. Remove the `static bool metrics_initialized` guard

### Compile-Time Decoupling

After all phases:
- `gc.h` does NOT include `aio.h`
- `gc.c`, `gc_mark.c`, `gc_checkpoint.c` do NOT include `aio.h` or any `aio/*.h`
- GC wakes threads via `wake_fn` pointers in the thread registry
- AIO registers itself with the system at startup
- Dependency direction: `aio -> gc` (one-way), never `gc -> aio`

### Mechanical Renames

These are exact text replacements across files. Use `sed` or equivalent:

| Pattern | Replacement | Files |
|---------|-------------|-------|
| `valk_global_handle_table` | `valk_sys->handle_table` | `builtins_server.c`, `aio_comb_timers.c`, `aio_http2_server.c`, `aio_http2_client.c`, `aio_http2_session.c`, `aio_stream_builtins.c`, `aio_stream_body.c` |
| `valk_runtime_get_heap()` | `valk_sys->heap` | `gc_evacuation.c`, `gc_region.c` |
| `valk_gc_coord.` | `valk_sys->` | `gc_stats.c`, `gc_mark.c` (any remaining after Phase 3) |
| `valk_runtime_is_initialized()` | `(valk_sys != NULL)` | `builtins_aio.c` |

### Thread Context Update

Add `struct valk_system *system` field to `valk_thread_context_t` in `src/memory.h`. Add it after the `allocator` field. It is set during `valk_system_register_thread`.

### Metrics Init

Move `valk_metrics_registry_init()` call from `src/aio/system/aio_system.c` into `valk_system_create()`. Remove the `static bool metrics_initialized` guard variable in `aio_system.c`.

### Kept Unchanged

- `valk_gc_heap_t` struct internals (pages, TLABs, size classes, bitmaps) — only the name changes in Phase 0
- All mark/sweep logic (just uses `valk_sys->` instead of `valk_gc_coord.`)
- All evacuation logic
- Handle table internals
- Barrier implementation (`valk_barrier_init/wait/reset/destroy`)
- Metrics registry internals
- AIO drain loop phases (100ms/300ms/500ms)

### Non-Requirements

- This refactor does NOT change the GC algorithm (still stop-the-world mark/sweep)
- This refactor does NOT change the heap layout (pages, TLABs, size classes)
- This refactor does NOT add build-time modularity (stripping AIO from binary is a future concern)
- This refactor does NOT change the Lisp-level API for `(aio/start)`, `(aio/stop)`, etc.

## Formal Requirements

These are the invariants that must hold at the end of each phase. They are tested by targeted C tests in `test/test_system.c` and targeted Valk tests where specified. Each phase's tests are cumulative — later phases must not break earlier tests.

Add `test/test_system.c` to `CMakeLists.txt` and the Makefile test runner during Phase 2 (when the system API first becomes callable). The test file grows with each phase. Tests for phases that haven't been implemented yet should not be added — add each phase's tests as that phase is completed.

### Test File Setup

Create `test/test_system.c` with this skeleton at Phase 2. Add tests to it as each phase is completed:

```c
#include "testing.h"
#include "gc.h"
#include "memory.h"
#include "parser.h"
#include "aio/aio.h"
#include "aio/aio_internal.h"
#include <signal.h>
#include <unistd.h>
#include <pthread.h>
#include <string.h>

static volatile sig_atomic_t timed_out = 0;

static void alarm_handler(int sig) {
  (void)sig;
  timed_out = 1;
  fprintf(stderr, "TIMEOUT: test_system hung\n");
  _exit(1);
}

int main(int argc, const char **argv) {
  UNUSED(argc); UNUSED(argv);
  alarm(30);
  signal(SIGALRM, alarm_handler);
  valk_mem_init_malloc();
  valk_test_suite_t *suite = valk_testsuite_empty(__FILE__);

  // Tests added per phase (see below)

  int res = valk_testsuite_run(suite);
  valk_testsuite_print(suite);
  valk_testsuite_free(suite);
  return res;
}
```

### Phase 0: Heap Rename

**Intent**: Mechanical `sed` rename. No logic changes. The rename is correct if and only if existing tests still pass and no old symbols remain. No new targeted tests needed — the existing test suite IS the validation (hundreds of call sites exercise the renamed functions).

**Procedure**: Apply renames in this order (longer names first to avoid partial matches):
1. Type renames: `valk_gc_malloc_heap_t` → `valk_gc_heap_t`, `valk_gc_mark_ctx2_t` → `valk_gc_mark_ctx_t`, `valk_gc_stats2_t` → `valk_gc_stats_t`, `valk_gc_heap2_t` → `valk_gc_heap_t`, `struct valk_gc_heap2` → `struct valk_gc_heap`, `valk_gc_tlab2_t` → `valk_gc_tlab_t`, `struct valk_gc_tlab2` → `struct valk_gc_tlab`, `valk_gc_page2_t` → `valk_gc_page_t`, `struct valk_gc_page2` → `struct valk_gc_page`, `struct valk_gc_mark_ctx2` → `struct valk_gc_mark_ctx`, `struct valk_gc_stats2` → `struct valk_gc_stats`
2. Function renames: `valk_gc_heap2_` → `valk_gc_heap_`, `valk_gc_tlab2_` → `valk_gc_tlab_`, `valk_gc_page2_` → `valk_gc_page_`, `valk_gc_sweep_page2` → `valk_gc_sweep_page`, `mark_children2` → `mark_children`, `mark_env2` → `mark_env`, `mark_lval2` → `mark_lval`
3. Static variables in `gc_mark.c`: `__gc_heap2_offered` → `__gc_heap_offered`, `__gc_heap2_terminated` → `__gc_heap_terminated`, `__gc_heap2_current` → `__gc_heap_current`, `__gc_heap2_term_lock` → `__gc_heap_term_lock`, `__gc_heap2_term_cond` → `__gc_heap_term_cond`
4. Remove `typedef valk_gc_heap2_t valk_gc_malloc_heap_t;` from `gc_heap.h`
5. Remove `valk_gc_malloc_*` wrappers — inline callers to direct `valk_gc_heap_*` calls. Rename functions with own logic: `valk_gc_malloc_set_root` → `valk_gc_set_root`, `valk_gc_malloc_should_collect` → `valk_gc_should_collect`, `valk_gc_malloc_print_stats` → `valk_gc_print_stats`
6. Remove orphaned `struct valk_gc_tlab;` from `memory.h`
7. Update `lsan_suppressions.txt`

**Gate**: `grep -rE "heap2|tlab2|page2|stats2|mark_ctx2|valk_gc_malloc_" src/ test/` returns nothing.

### Phase 1: Define New Types and Shims

**Intent**: Define the new type hierarchy. The old code must still compile unchanged via shims.

**Procedure**: See Requirements section for exact struct definitions.

**Gate**: `make build` succeeds. No test changes needed — shims redirect all old names.

### Phase 2: System Lifecycle Implementation

**Intent**: `valk_system_create` replaces `valk_runtime_init`. The system struct owns the heap, handle table, and thread registry. Threads register/unregister with the system, and each gets a TLAB from the shared heap.

**Targeted tests** (add to `test/test_system.c`):

```c
void test_system_create_sets_valk_sys(VALK_TEST_ARGS()) {
  VALK_TEST();
  // valk_system_create must set the global valk_sys pointer
  // AND auto-register the calling thread (threads_registered == 1)
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);
  ASSERT_NOT_NULL(sys);
  ASSERT_TRUE(valk_sys == sys);
  ASSERT_NOT_NULL(sys->heap);
  ASSERT_TRUE(sys->initialized);
  ASSERT_EQ(atomic_load(&sys->threads_registered), 1);
  ASSERT_TRUE(valk_thread_ctx.gc_registered);
  ASSERT_TRUE(valk_thread_ctx.heap == sys->heap);
  valk_system_destroy(sys);
  ASSERT_NULL(valk_sys);
  VALK_PASS();
}

void test_system_thread_register_gets_unique_slot(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Two threads registering must get different gc_thread_ids.
  // Also: after unregister, threads_registered must decrement.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);
  u64 main_id = valk_thread_ctx.gc_thread_id;

  // Simulate second thread registration on this thread (hack: save/restore ctx)
  valk_thread_context_t saved = valk_thread_ctx;
  memset(&valk_thread_ctx, 0, sizeof(valk_thread_ctx));
  valk_system_register_thread(sys, NULL, NULL);
  u64 second_id = valk_thread_ctx.gc_thread_id;
  ASSERT_NE(main_id, second_id);
  ASSERT_EQ(atomic_load(&sys->threads_registered), 2);

  valk_system_unregister_thread(sys);
  ASSERT_EQ(atomic_load(&sys->threads_registered), 1);

  valk_thread_ctx = saved;
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_system_heap_alloc_works_after_create(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Must be able to allocate from valk_sys->heap after create.
  // This catches: heap not created, TLAB not initialized, thread not registered.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);
  void *ptr = valk_gc_heap_alloc(sys->heap, 64);
  ASSERT_NOT_NULL(ptr);
  valk_system_destroy(sys);
  VALK_PASS();
}

// File-scope helpers for subsystem tests (clang doesn't support nested functions)
static int __sub_stop_called = 0, __sub_wait_called = 0, __sub_destroy_called = 0;
static void __sub_dummy_stop(void *ctx) { (void)ctx; __sub_stop_called++; }
static void __sub_dummy_wait(void *ctx) { (void)ctx; __sub_wait_called++; }
static void __sub_dummy_destroy(void *ctx) { (void)ctx; __sub_destroy_called++; }

static int __sub_sequence[3] = {0, 0, 0};
static int __sub_seq_idx = 0;
static void __sub_order_stop(void *ctx)    { (void)ctx; __sub_sequence[__sub_seq_idx++] = 1; }
static void __sub_order_wait(void *ctx)    { (void)ctx; __sub_sequence[__sub_seq_idx++] = 2; }
static void __sub_order_destroy(void *ctx) { (void)ctx; __sub_sequence[__sub_seq_idx++] = 3; }

static int __wake_count = 0;
static void __test_wake_fn(void *ctx) { (void)ctx; __wake_count++; }

void test_system_subsystem_add_remove(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Add a subsystem, verify count. Remove it, verify count goes back.
  // Catches: off-by-one in count, wrong ctx match in remove.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  __sub_stop_called = __sub_wait_called = __sub_destroy_called = 0;

  int sentinel = 42;
  valk_system_add_subsystem(sys, __sub_dummy_stop, __sub_dummy_wait,
                            __sub_dummy_destroy, &sentinel);
  ASSERT_EQ(sys->subsystem_count, 1);

  valk_system_remove_subsystem(sys, &sentinel);
  ASSERT_EQ(sys->subsystem_count, 0);

  valk_system_destroy(sys);
  VALK_PASS();
}

void test_system_shutdown_calls_subsystem_stop_wait_destroy(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Shutdown must call stop, then wait, then destroy — in that order.
  // Catches: missing calls, wrong order, not calling all three.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  __sub_seq_idx = 0;
  memset(__sub_sequence, 0, sizeof(__sub_sequence));

  int sentinel = 0;
  valk_system_add_subsystem(sys, __sub_order_stop, __sub_order_wait,
                            __sub_order_destroy, &sentinel);

  valk_system_shutdown(sys, 1000);

  ASSERT_EQ(__sub_seq_idx, 3);
  ASSERT_EQ(__sub_sequence[0], 1);  // stop first
  ASSERT_EQ(__sub_sequence[1], 2);  // wait second
  ASSERT_EQ(__sub_sequence[2], 3);  // destroy third

  valk_system_destroy(sys);
  VALK_PASS();
}

void test_system_wake_threads_calls_wake_fn(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Register a thread with a wake_fn, call wake_threads, verify it was called.
  // Catches: wake_fn field not set during register, wake_threads skipping active entries.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  __wake_count = 0;

  // Main thread registered with NULL wake_fn. Register a second "thread" with wake_fn.
  valk_thread_context_t saved = valk_thread_ctx;
  memset(&valk_thread_ctx, 0, sizeof(valk_thread_ctx));
  valk_system_register_thread(sys, __test_wake_fn, NULL);

  valk_system_wake_threads(sys);
  ASSERT_EQ(__wake_count, 1);  // Only the second thread has wake_fn

  valk_system_unregister_thread(sys);
  valk_thread_ctx = saved;
  valk_system_destroy(sys);
  VALK_PASS();
}
```

### Phase 3: STW Protocol Fix

**Intent**: Replace condvar-based STW with barrier-based. The barrier protocol must not deadlock and must actually pause all threads before returning.

**Targeted tests** (add to `test/test_system.c`):

```c
void test_barrier_two_threads_no_deadlock(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Start system + AIO. Run 20 GC cycles. If the barrier protocol is broken,
  // this will deadlock and the 30-second alarm kills the test.
  // Catches: barrier count mismatch, missed wakeups, wrong phase transitions.
  valk_system_config_t cfg = valk_system_config_default();
  cfg.gc_heap_size = 1024 * 1024;
  valk_system_t *sys = valk_system_create(&cfg);

  valk_lenv_t *env = valk_lenv_empty();
  valk_gc_set_root(sys->heap, env);
  valk_thread_ctx.root_env = env;

  valk_aio_system_t *aio = valk_aio_start();
  ASSERT_NOT_NULL(aio);
  usleep(50000);  // let event loop thread register

  ASSERT_GE(atomic_load(&sys->threads_registered), 2);

  for (int i = 0; i < 20; i++) {
    valk_gc_heap_collect(sys->heap);
    usleep(5000);
  }

  // Teardown: use whatever AIO shutdown API exists at this phase.
  // Phase 3: valk_aio_stop + valk_aio_wait_for_shutdown (no destroy yet).
  // Phase 4+: update to valk_aio_stop + wait + destroy, or use valk_system_shutdown.
  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_checkpoint_does_not_deadlock_with_aio(VALK_TEST_ARGS()) {
  VALK_TEST();
  // Start system + AIO. Run 20 checkpoints with scratch arena.
  // Catches: checkpoint barrier misconfigured, condvar leftover, missing wake.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  size_t arena_size = 256 * 1024;
  valk_mem_arena_t *arena = malloc(arena_size);
  valk_mem_arena_init(arena, arena_size - sizeof(*arena));
  valk_thread_ctx.scratch = arena;

  valk_lenv_t *env = valk_lenv_empty();
  valk_gc_set_root(sys->heap, env);
  valk_thread_ctx.root_env = env;

  valk_aio_system_t *aio = valk_aio_start();
  usleep(50000);

  for (int i = 0; i < 20; i++) {
    // Allocate something in scratch to make checkpoint non-trivial
    VALK_WITH_ALLOC((void *)arena) {
      valk_lval_num(i);
    }
    valk_checkpoint(arena, sys->heap, env);
    usleep(5000);
  }

  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  free(arena);
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_gc_phase_returns_to_idle(VALK_TEST_ARGS()) {
  VALK_TEST();
  // After a GC cycle completes, phase must be IDLE.
  // Catches: phase left in STW_REQUESTED or MARKING after collection.
  valk_system_config_t cfg = valk_system_config_default();
  cfg.gc_heap_size = 1024 * 1024;
  valk_system_t *sys = valk_system_create(&cfg);

  valk_lenv_t *env = valk_lenv_empty();
  valk_gc_set_root(sys->heap, env);

  valk_gc_heap_collect(sys->heap);

  valk_gc_phase_e phase = atomic_load(&sys->phase);
  ASSERT_EQ(phase, VALK_GC_PHASE_IDLE);

  valk_system_destroy(sys);
  VALK_PASS();
}
```

**Note**: The `barrier_two_threads_no_deadlock` test is the critical one. The old condvar protocol deadlocked ~1-2% of runs. Run this test 50 times to validate:
```bash
for i in $(seq 50); do build/test_system --test barrier_two_threads_no_deadlock || echo "FAIL $i"; done
```

### Phase 4: AIO Integration

**Intent**: AIO registers as a subsystem. Event loop thread registers with `wake_fn`. No separate per-loop heap. GC has zero compile-time knowledge of AIO.

**Note**: When adding Phase 4 tests, also update the Phase 3 test teardown sequences. Replace `valk_aio_stop(aio); valk_aio_wait_for_shutdown(aio);` with `valk_aio_stop(aio); valk_aio_wait_for_shutdown(aio); valk_aio_destroy(aio);` since `valk_aio_destroy` now exists as a separate function.

**Targeted tests** (add to `test/test_system.c`):

```c
void test_aio_registers_as_subsystem(VALK_TEST_ARGS()) {
  VALK_TEST();
  // After aio_start, sys->subsystem_count must be >= 1.
  // Catches: forgot to call valk_system_add_subsystem in aio_start.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  ASSERT_EQ(sys->subsystem_count, 0);

  valk_aio_system_t *aio = valk_aio_start();
  ASSERT_NOT_NULL(aio);
  usleep(50000);

  ASSERT_GE(sys->subsystem_count, 1);

  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  valk_aio_destroy(aio);
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_event_loop_thread_has_wake_fn(VALK_TEST_ARGS()) {
  VALK_TEST();
  // After AIO starts, one of the thread slots (not slot 0 = main) must have
  // a non-NULL wake_fn. Catches: wake_fn not passed to register_thread.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  valk_aio_system_t *aio = valk_aio_start();
  usleep(50000);

  bool found_wake = false;
  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (sys->threads[i].active && sys->threads[i].wake_fn != NULL) {
      found_wake = true;
      break;
    }
  }
  ASSERT_TRUE(found_wake);

  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  valk_aio_destroy(aio);
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_event_loop_shares_system_heap(VALK_TEST_ARGS()) {
  VALK_TEST();
  // The event loop thread must use valk_sys->heap, not its own heap.
  // Verify: after AIO start + GC, the event loop's thread context heap
  // is the same pointer as sys->heap. We check indirectly: if the event
  // loop had its own heap, threads_registered would still be 2 but
  // the second thread's ctx->heap would differ from sys->heap.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  valk_aio_system_t *aio = valk_aio_start();
  usleep(50000);

  // Find the event loop thread's context
  valk_gc_heap_t *el_heap = NULL;
  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (sys->threads[i].active && sys->threads[i].wake_fn != NULL) {
      valk_thread_context_t *tc = sys->threads[i].ctx;
      if (tc) el_heap = tc->heap;
      break;
    }
  }
  ASSERT_NOT_NULL(el_heap);
  ASSERT_TRUE(el_heap == sys->heap);

  valk_aio_stop(aio);
  valk_aio_wait_for_shutdown(aio);
  valk_aio_destroy(aio);
  valk_system_destroy(sys);
  VALK_PASS();
}

void test_system_shutdown_stops_aio(VALK_TEST_ARGS()) {
  VALK_TEST();
  // valk_system_shutdown must stop AIO without the caller knowing about AIO.
  // After shutdown, threads_registered must be 1 (only main thread).
  // Catches: subsystem stop/wait/destroy not called, event loop thread not unregistered.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  valk_aio_system_t *aio = valk_aio_start();
  usleep(50000);
  ASSERT_GE(atomic_load(&sys->threads_registered), 2);

  // Shutdown without naming AIO — the subsystem interface handles it
  valk_system_shutdown(sys, 5000);

  ASSERT_EQ(atomic_load(&sys->threads_registered), 1);
  ASSERT_EQ(sys->subsystem_count, 0);

  valk_system_destroy(sys);
  VALK_PASS();
}
```

**Compile-time decoupling check**: After Phase 4, add this to the gate:
```bash
# gc.c, gc_mark.c, gc_checkpoint.c must not include any aio header
grep -rn '#include.*aio' src/gc.c src/gc_mark.c src/gc_checkpoint.c && echo "FAIL: GC still depends on AIO" && exit 1
```

### Phase 5: Thread Context and Mechanical Renames

**Intent**: Remove shims. All code uses `valk_sys->` directly. `valk_thread_ctx.system` is set.

**Targeted test** (add to `test/test_system.c`):

```c
void test_thread_context_has_system_pointer(VALK_TEST_ARGS()) {
  VALK_TEST();
  // After system_create, the calling thread's context must have system set.
  // Catches: forgot to set system field in register_thread.
  valk_system_config_t cfg = valk_system_config_default();
  valk_system_t *sys = valk_system_create(&cfg);

  ASSERT_TRUE(valk_thread_ctx.system == sys);

  valk_system_destroy(sys);
  VALK_PASS();
}
```

**Gate**: Shims must be gone — this compile-time check catches incomplete removal:
```bash
grep -n 'define valk_gc_coord\|define valk_global_handle_table' src/gc.h && echo "FAIL: shims still present" && exit 1
```

### Phase 6: Remove Dead Code

**Intent**: `g_live_heaps[]`, `loop_gc_heap`, and heap registry functions are gone. One heap per system, no registry needed.

**Gate**: Compile-time — if any code still references these symbols, it won't build.

### Phase 7: Bootstrap and Shutdown Rewrite

**Intent**: `repl.c` uses `valk_system_create/shutdown/destroy`. `(shutdown N)` only sets `VALK_EXIT_CODE` — the bootstrap loop calls `valk_system_shutdown` which generically stops all subsystems.

**Targeted Valk tests** (create `test/test_shutdown.valk`):

```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

; Start AIO
(def {aio} (aio/await (aio/start)))

; shutdown should return the exit code
(def {result} (shutdown 0))

; If we get here, shutdown did NOT call exit() — correct behavior.
; The bootstrap loop reads VALK_EXIT_CODE after eval returns.
(test/run (list
  (test "shutdown-returns-code"
    {(== result 0)})
) {:suite-name "Shutdown"})
```

Also create `test/test_exit_alias.valk`:
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

; (exit N) must behave identically to (shutdown N) — same function
(def {result} (exit 42))

(test/run (list
  (test "exit-is-shutdown-alias"
    {(== result 42)})
) {:suite-name "Exit Alias"})
```

**What these catch**: If `(shutdown)` still calls `exit()` or still looks up the `aio` symbol, the first test will either abort the process (test runner sees non-zero exit) or fail because the AIO symbol lookup crashes. If `(exit)` was removed instead of aliased to `(shutdown)`, the second test gets an undefined symbol error.

### Phase 8: Test Updates

**Intent**: Migrate existing test files to the new API. No new tests — just update call sites.

**Gate**: All existing tests pass. The Phase 2-7 targeted tests still pass (regression check).

### Phase 9: Final Verification

**Formal requirements** — these are the project-level invariants that must hold:

**R1 — Single ownership**: There is exactly one `valk_system_t` instance. It owns the heap, handle table, and thread registry.
- Verified by: `test_system_create_sets_valk_sys` (Phase 2)

**R2 — Thread safety**: All threads (main + event loop) register/unregister with the system and get unique slots.
- Verified by: `test_system_thread_register_gets_unique_slot` (Phase 2), `test_event_loop_thread_has_wake_fn` (Phase 4)

**R3 — No deadlocks**: The barrier-based STW protocol does not deadlock under repeated GC cycles with an active event loop.
- Verified by: `test_barrier_two_threads_no_deadlock` (Phase 3), repeated 50x

**R4 — Compile-time decoupling**: GC source files have zero `#include` of AIO headers.
- Verified by: `grep -rn '#include.*aio' src/gc.c src/gc_mark.c src/gc_checkpoint.c` returns nothing

**R5 — Generic shutdown**: `valk_system_shutdown` stops all subsystems without knowing their concrete types. AIO shuts down through the subsystem interface, not through direct API calls.
- Verified by: `test_system_shutdown_stops_aio` (Phase 4), `test_system_shutdown_calls_subsystem_stop_wait_destroy` (Phase 2)

**R6 — Shared heap**: Event loop threads share `valk_sys->heap` via TLABs, not a separate heap.
- Verified by: `test_event_loop_shares_system_heap` (Phase 4)

**R7 — Clean shutdown from Lisp**: `(shutdown N)` returns control to the bootstrap loop with exit code N. It does not call `exit()` and does not directly reference AIO.
- Verified by: `test/test_shutdown.valk`, `test/test_exit_alias.valk` (Phase 7)

**R8 — No old symbols**: All vestigial names (`heap2`, `valk_gc_coord`, `valk_runtime_*`, `g_aio_systems`, `valk_gc_malloc_*`) are gone from source.
- Verified by: `grep -rE "valk_gc_coord[^_]|valk_global_handle_table|valk_runtime_|g_aio_systems|g_live_heaps|heap2_|tlab2_|page2_|stats2_|valk_gc_malloc_" src/ test/` returns nothing

**Stress validation** (run after all phases):
```bash
# 50x GC+AIO deadlock check (C test)
for i in $(seq 50); do build/test_system --test barrier_two_threads_no_deadlock || { echo "DEADLOCK at iteration $i"; exit 1; }; done

# 50x full Valk async test (exercises shutdown + GC + AIO end-to-end)
for i in $(seq 50); do timeout 30 build/valk test/test_async_http_handlers.valk || { echo "FAIL at iteration $i"; exit 1; }; done
```

**Sanitizer runs** (catch memory and threading bugs the targeted tests don't cover):
```bash
make test-c-asan && make test-valk-asan    # memory errors
make test-c-tsan && make test-valk-tsan    # data races
make lint                                   # static analysis
```
