# Valkyria System Architecture Refactor Plan

## Problem Statement

The current runtime has no central abstraction. State is scattered across unrelated globals:

1. `valk_gc_coord` (gc.c) — GC coordinator with thread registry, barriers, condvars
2. `__runtime_heap` (gc.c, static) — the singleton GC heap
3. `valk_global_handle_table` (gc.c) — handle table for cross-thread GC roots
4. `g_aio_systems[]` (aio_system.c, static) — registry of AIO event loop systems
5. `g_live_heaps[]` (gc_heap.c, static) — registry of live heaps for TLAB validity
6. `g_metrics` (metrics_v2.c) — metrics registry, init buried in AIO startup

The checkpoint STW protocol uses ad-hoc condvars that deadlock ~1-2% of the time.
Shutdown is ad-hoc — `(exit)` calls `exit()` directly, `(shutdown)` searches the env
for a symbol named `aio` and stops it. No graceful teardown with deadlines.

## Design Principles

1. **The runtime IS the process.** `valk_system_t` is the Lisp runtime. When it shuts
   down, the process exits. There is no "outside" to return to.

2. **The system owns what it must coordinate.** GC heap, handle table, thread registry,
   and metrics registry are owned directly. Subsystems that need graceful shutdown (AIO)
   register via a generic interface — the system doesn't know their types.

3. **Subsystems are decoupled at compile time.** `gc.h` never includes `aio.h`. AIO
   registers itself with the system. The dependency arrow is one-way: `aio → system`.
   An embedded Lisp without AIO links without libuv.

4. **Thread coordination, not system coordination.** GC doesn't know about AIO systems.
   It knows about threads. Each thread optionally provides a `wake_fn` for STW wakeup.
   Event loop threads set this to `uv_async_send(&gc_wakeup)`.

5. **Shutdown is best-effort with deadlines.** Stop subsystems, wait for threads to
   leave, tear down. If the deadline expires, log and proceed.

## Architecture

### System Ownership

```
┌──────────────────────────────────────────────────────────────┐
│                        valk_system_t                          │
│                     (global: valk_sys)                        │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐    │
│  │ GC Coordinator                                       │    │
│  │   _Atomic phase          (IDLE / STW / CHECKPOINT)   │    │
│  │   _Atomic threads_registered                         │    │
│  │   valk_barrier_t barrier (reused for all STW)        │    │
│  │   threads[64]            (per-thread info + wake_fn) │    │
│  │   mark queues            (per-thread work stealing)  │    │
│  └──────────────────────────────────────────────────────┘    │
│                                                              │
│  ┌──────────────────┐  ┌──────────────┐  ┌──────────────┐   │
│  │ GC Heap          │  │ Handle Table │  │ Metrics      │   │
│  │ pages, TLABs,    │  │ slots[],     │  │ registry     │   │
│  │ size classes,    │  │ generations, │  │ (g_metrics)  │   │
│  │ large objects    │  │ free list    │  │ lock-free    │   │
│  └──────────────────┘  └──────────────┘  └──────────────┘   │
│                                                              │
│  ┌──────────────────────────────────────────────────────┐    │
│  │ Subsystems (generic, for shutdown coordination)      │    │
│  │   subsystems[16]  — each has stop/wait/destroy fns   │    │
│  │   AIO systems register here on (aio/start)           │    │
│  └──────────────────────────────────────────────────────┘    │
│                                                              │
│  _Atomic bool shutting_down                                  │
│  int exit_code                                               │
└──────────────────────────────────────────────────────────────┘
```

### Thread Participation

Threads register with the system to participate in Lisp execution.
Each thread gets a TLAB from the shared heap. Event loop threads
provide a wake function so GC can interrupt `epoll_wait`.

```
┌─────────────────────────────────────────────────────────────┐
│                    Thread Registry                            │
│                                                              │
│  threads[0]: main thread                                     │
│    ctx = &valk_thread_ctx    active = true                   │
│    wake_fn = NULL            (hits safe points naturally)    │
│                                                              │
│  threads[1]: AIO event loop                                  │
│    ctx = &valk_thread_ctx    active = true                   │
│    wake_fn = uv_async_send   wake_ctx = &sys->gc_wakeup     │
│                                                              │
│  threads[2..63]: unused                                      │
│    active = false                                            │
└─────────────────────────────────────────────────────────────┘

Registration:
  valk_system_register_thread(sys, wake_fn, wake_ctx)
    → assigns TLAB from sys->heap
    → sets valk_thread_ctx.heap = sys->heap
    → increments threads_registered

Unregistration:
  valk_system_unregister_thread(sys)
    → participates in any pending STW first (VALK_GC_SAFE_POINT)
    → decrements threads_registered
```

### Subsystem Interface (for shutdown)

```
┌──────────────────────────────────┐
│ valk_subsystem_t                 │
│   void (*stop)(void *ctx)        │  ← initiate graceful stop
│   void (*wait)(void *ctx)        │  ← block until stopped
│   void (*destroy)(void *ctx)     │  ← free resources
│   void *ctx                      │  ← opaque pointer
└──────────────────────────────────┘

System does NOT include aio.h.
AIO registers itself:

  valk_system_add_subsystem(valk_sys,
    (void(*)(void*))valk_aio_stop,
    (void(*)(void*))valk_aio_wait_for_shutdown,
    (void(*)(void*))valk_aio_destroy,
    aio_sys);
```

### GC ↔ Thread Coordination (no AIO dependency)

```
STW Request (checkpoint or GC):

  Requester (main thread)           Responder threads
  ─────────────────────────         ───────────────────────
  CAS phase → REQUESTED
  reset barrier(N threads)
  wake_threads():                   [blocked in epoll_wait]
    for each thread:
      if wake_fn: wake_fn(ctx) ──────► uv_async_send fires
                                       gc_wakeup_cb fires
                                       → gc_safe_point_slow()
  barrier_wait() ◄─────────────────► barrier_wait()
  ┄┄┄┄┄┄┄┄ all threads paused ┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄
  ... do work ...                   ... wait ...
  phase → IDLE
  barrier_wait() ◄─────────────────► barrier_wait()
  ┄┄┄┄┄┄┄┄ all threads released ┄┄┄┄┄┄┄┄┄┄┄┄┄┄

  gc.c/gc_mark.c/gc_checkpoint.c never include aio.h.
  They just call wake_fn pointers from the thread registry.
```

### Shutdown Sequence

```
(shutdown 0)  →  returns shutdown code to bootstrap loop

Bootstrap:
  valk_system_shutdown(sys, 5000)    // 5 second deadline
  valk_system_destroy(sys)
  return exit_code

valk_system_shutdown(sys, deadline_ms):
  ┌─────────────────────────────────────────────────┐
  │ 1. Set sys->shutting_down = true                │
  │                                                 │
  │ 2. Stop all subsystems:                         │
  │    for each subsystem:                          │
  │      subsystem.stop(ctx)                        │
  │    (AIO: uv_async_send → uv_stop → drain loop) │
  │                                                 │
  │ 3. Wait for threads to unregister:              │
  │    while threads_registered > 1:                │
  │      if deadline expired: log, break            │
  │      sleep(1ms)                                 │
  │    (event loop threads unregister after drain)  │
  │                                                 │
  │ 4. Wait + destroy subsystems:                   │
  │    for each subsystem:                          │
  │      subsystem.wait(ctx)                        │
  │      subsystem.destroy(ctx)                     │
  │                                                 │
  │ 5. sys->exit_code = code                        │
  └─────────────────────────────────────────────────┘

valk_system_destroy(sys):
  ┌─────────────────────────────────────────────────┐
  │ 1. Destroy GC heap                              │
  │ 2. Destroy handle table                         │
  │ 3. Destroy barrier                              │
  │ 4. Destroy thread mark queues                   │
  │ 5. valk_sys = NULL                              │
  │ 6. free(sys)                                    │
  └─────────────────────────────────────────────────┘
```

### Bootstrap Eval Loop

```c
int main(int argc, char *argv[]) {
  valk_system_t *sys = valk_system_create(&cfg);
  // ... setup env, scratch, parse files ...

  for (;;) {
    valk_lval_t *result = valk_system_eval(sys, ast);

    if (is_shutdown_code(result)) {
      int code = get_shutdown_code(result);
      valk_system_shutdown(sys, 5000);
      valk_system_destroy(sys);
      return code;
    }

    if (is_expression(result)) {
      ast = result;
      continue;
    }

    // Value or error — print and exit
    valk_lval_println(result);
    valk_system_shutdown(sys, 5000);
    valk_system_destroy(sys);
    return 0;
  }
}
```

### In-Flight Work During Shutdown

```
Event loop thread at shutdown time:

  ┌──────────────────────────────────────────────────────┐
  │ Event loop is running uv_run()                       │
  │                                                      │
  │ subsystem.stop() → uv_async_send(stopper)            │
  │                                                      │
  │ ... current Lisp callback completes naturally ...     │
  │ (eval finishes, response is sent)                    │
  │                                                      │
  │ uv_run processes stopper:                            │
  │   __aio_uv_stop() fires:                             │
  │     uv_stop()                                        │
  │     walk-close all handles (listeners, connections)  │
  │                                                      │
  │ uv_run returns                                       │
  │                                                      │
  │ Drain loop (already implemented):                    │
  │   Phase 1: 100ms graceful drain (NOWAIT)             │
  │   Phase 2: 300ms force close remaining handles       │
  │   Phase 3: 500ms hard deadline, log + break          │
  │                                                      │
  │ valk_system_unregister_thread(valk_sys)              │
  │   → decrements threads_registered                    │
  │   → main thread's wait loop sees it                  │
  │                                                      │
  │ Thread exits                                         │
  └──────────────────────────────────────────────────────┘

  Key: no preemption. The current callback finishes.
  New connections are not accepted (listener closing).
  In-flight requests complete and drain naturally.
```

### Dependency Graph (compile-time)

```
                 ┌─────────┐
                 │  repl.c  │
                 │ (main)   │
                 └────┬─────┘
                      │ includes gc.h, aio.h
              ┌───────┴────────┐
              ▼                ▼
         ┌─────────┐    ┌──────────┐
         │  gc.h   │    │  aio.h   │
         │ system, │    │ AIO API  │
         │ GC API  │    └────┬─────┘
         └────┬────┘         │ includes gc.h
              │              ▼
              │    ┌──────────────────┐
              │    │ aio_system.c     │
              │    │ aio_uv.c        │
              │    │ calls:           │
              │    │  register_thread │
              │    │  add_subsystem   │
              │    │  SAFE_POINT()    │
              │    └──────────────────┘
              │
              ▼
    ┌──────────────────────┐
    │ gc.c, gc_mark.c,     │
    │ gc_checkpoint.c      │
    │                      │
    │ calls:               │
    │   wake_fn(ctx)       │  ← generic fn ptr, NOT aio
    │   barrier_wait()     │
    │                      │
    │ does NOT include     │
    │ aio.h                │
    └──────────────────────┘

    Arrow = "includes" or "calls into"
    No cycle between gc and aio at compile time.
```

### What Lval/Lenv Are (NOT subsystems)

```
  Lval/Lenv are DATA TYPES, not systems.
  They are structs allocated on heap or scratch.
  They have no lifecycle, no state, no coordination.

  "AIO depends on Lval" = "AIO allocates structs on the heap"
  "Eval depends on Lval" = "eval manipulates structs"

  The only real system-level resources are:
    heap, GC coordinator, handle table, metrics registry

  Everything else (lval, lenv, region, evacuation_ctx) is just
  data that lives in those resources.
```

## The `valk_system_t` Struct

```c
// gc.h

#define VALK_SYSTEM_MAX_THREADS 64
#define VALK_SYSTEM_MAX_SUBSYSTEMS 16

typedef struct {
  void (*stop)(void *ctx);
  void (*wait)(void *ctx);
  void (*destroy)(void *ctx);
  void *ctx;
} valk_subsystem_t;

typedef struct valk_gc_thread_info {
  void *ctx;
  pthread_t thread_id;
  bool active;
  valk_gc_mark_queue_t mark_queue;

  void (*wake_fn)(void *wake_ctx);
  void *wake_ctx;
} valk_gc_thread_info_t;

typedef struct valk_system {
  // --- GC Heap ---
  valk_gc_heap2_t *heap;

  // --- Handle Table ---
  valk_handle_table_t handle_table;

  // --- GC Coordinator ---
  _Atomic valk_gc_phase_e phase;
  _Atomic u64 threads_registered;

  valk_barrier_t barrier;
  bool barrier_initialized;

  valk_gc_thread_info_t threads[VALK_SYSTEM_MAX_THREADS];

  _Atomic u64 parallel_cycles;
  _Atomic u64 parallel_pause_us_total;

  // --- Subsystems (for shutdown coordination) ---
  pthread_mutex_t subsystems_lock;
  valk_subsystem_t subsystems[VALK_SYSTEM_MAX_SUBSYSTEMS];
  int subsystem_count;

  // --- Lifecycle ---
  _Atomic bool shutting_down;
  int exit_code;
  bool initialized;
} valk_system_t;

extern valk_system_t *valk_sys;
```

## What Gets Removed

| Old                          | New                                        |
|------------------------------|--------------------------------------------|
| `valk_gc_coordinator_t`      | Fields inlined into `valk_system_t`        |
| `valk_gc_coord` global       | `valk_sys->phase`, etc.                    |
| `__runtime_heap` static      | `valk_sys->heap`                           |
| `valk_global_handle_table`   | `valk_sys->handle_table`                   |
| `g_aio_systems[]` static     | `valk_sys->subsystems[]` (generic)         |
| `g_aio_systems_lock`         | `valk_sys->subsystems_lock`                |
| `g_live_heaps[]` static      | Removed (one heap per system)              |
| `checkpoint_epoch`           | Removed (barriers don't need it)           |
| `threads_paused`             | Removed (barriers handle counting)         |
| `all_paused` condvar         | Removed (barriers replace it)              |
| `gc_done` condvar            | Removed (barriers replace it)              |
| `valk_gc_coord.lock` mutex   | Removed (barriers replace it)              |
| `valk_runtime_config_t`      | `valk_system_config_t`                     |
| `valk_runtime_init`          | `valk_system_create`                       |
| `valk_runtime_shutdown`      | `valk_system_shutdown` + `_destroy`        |
| `valk_runtime_get_heap`      | `valk_sys->heap`                           |
| `valk_runtime_is_initialized`| `valk_sys != NULL`                         |
| `valk_runtime_get_onboard_fn`| Removed (threads call register directly)   |
| `valk_runtime_thread_onboard`| `valk_system_register_thread`              |
| `thread_onboard_fn` in config| Removed                                    |
| `valk_aio_register_system`   | `valk_system_add_subsystem`                |
| `valk_aio_unregister_system` | `valk_system_remove_subsystem`             |
| `valk_aio_wake_all_for_gc`   | `valk_system_wake_threads` (via wake_fn)   |
| `valk_aio_wait_for_all_systems` | `valk_system_shutdown`                  |
| `loop_gc_heap` per event loop| Removed (shares sys->heap via TLABs)      |

## What Gets Kept (Unchanged)

- `VALK_GC_SAFE_POINT()` macro — points at `valk_sys->phase` instead of `valk_gc_coord.phase`
- `valk_thread_ctx` TLS — adds `system` field, keeps `heap`, `scratch`, etc.
- `valk_gc_heap2_t` — the heap struct is unchanged
- All heap internals (pages, TLABs, size classes, bitmaps) — unchanged
- All mark/sweep logic — unchanged, just references `valk_sys`
- All evacuation logic — unchanged
- Handle table internals — unchanged
- `valk_gc_malloc_*` wrapper API — kept for compatibility, forwards to `valk_sys->heap`
- Barrier implementation — unchanged
- Metrics registry internals — unchanged (just init moves to system_create)

## STW Protocol Fix (Unified Barrier-Based)

### Current Broken Protocol (Checkpoint)

```
Requester:
  1. CAS phase → CHECKPOINT_REQUESTED
  2. threads_paused++ for self
  3. condvar wait on all_paused until threads_paused == registered
  4. ... do work ...
  5. Set phase → IDLE
  6. threads_paused = 0
  7. broadcast gc_done

Responder (safe_point_slow):
  1. threads_paused++
  2. if last: signal all_paused
  3. condvar wait on gc_done until epoch changes
```

**Bug**: Missed wakeup between step 2 and 3 on requester side — if responder
signals `all_paused` before requester starts waiting, the signal is lost.

### New Unified Protocol (Both Checkpoint and GC)

Both use the same barrier:

```
Requester (request_stw):
  1. CAS phase → REQUESTED
  2. Reset barrier with threads_registered count
  3. valk_system_wake_threads(sys)   // calls wake_fn per thread
  4. barrier_wait()                  // ENTRY — blocks until all arrive

  ... all threads paused, requester does work ...

Requester (release_stw):
  5. Set phase → IDLE
  6. barrier_wait()                  // EXIT — releases responders

Responder (safe_point_slow, checkpoint case):
  1. barrier_wait()                  // ENTRY — rendezvous
  2. barrier_wait()                  // EXIT — wait for requester
  3. return

Responder (safe_point_slow, STW GC case):
  1. Checkpoint own scratch (if needed)
  2. barrier_wait()                  // ENTRY — rendezvous
  3. Participate in parallel mark/sweep (existing internal barriers)
  4. return
```

### Edge Cases

**Checkpoint called during STW GC:** CAS fails (phase already STW_REQUESTED).
request_stw returns early. Checkpoint evacuation runs uncoordinated — correct
because all threads are already paused.

**Thread unregisters during barrier:** Thread calls `VALK_GC_SAFE_POINT()` before
decrementing `threads_registered`. Participates in any active barrier first.

## File-by-File Changes

### Phase 1: Core System Struct

#### `src/gc.h`

**Remove:**
- `valk_gc_coordinator_t` struct
- `extern valk_gc_coordinator_t valk_gc_coord`
- `valk_runtime_config_t`, `valk_runtime_init/shutdown/thread_onboard/get_heap/is_initialized/get_onboard_fn`

**Add:**
- `valk_subsystem_t` struct (stop/wait/destroy function pointers)
- `valk_system_t` struct (as defined above)
- `extern valk_system_t *valk_sys`
- `valk_system_create/destroy/shutdown`
- `valk_system_register_thread/unregister_thread` (with wake_fn/wake_ctx)
- `valk_system_add_subsystem/remove_subsystem`
- `valk_system_wake_threads` (iterates thread wake_fn pointers)

**Modify `valk_gc_thread_info_t`:**
- Add `wake_fn` and `wake_ctx` fields

**Modify `VALK_GC_SAFE_POINT()` macro:**
```c
#define VALK_GC_SAFE_POINT() \
  do { \
    if (__builtin_expect(atomic_load_explicit(&valk_sys->phase, \
                         memory_order_acquire) != VALK_GC_PHASE_IDLE, 0)) { \
      valk_gc_safe_point_slow(); \
    } \
  } while (0)
```

#### `src/gc.c`

**Remove:**
- `__runtime_heap`, `__runtime_initialized`
- `valk_runtime_init/shutdown/thread_onboard/get_onboard_fn/get_heap/is_initialized`
- `valk_gc_coordinator_init()`

**Add:**
```c
valk_system_t *valk_sys = NULL;

valk_system_t *valk_system_create(valk_system_config_t *config) {
  valk_system_t *sys = calloc(1, sizeof(valk_system_t));

  sys->heap = valk_gc_heap2_create(config->gc_heap_size);
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

  // Onboard the calling (main) thread
  valk_system_register_thread(sys, NULL, NULL);

  return sys;
}

void valk_system_shutdown(valk_system_t *sys, u64 deadline_ms) {
  atomic_store(&sys->shutting_down, true);

  // Stop all subsystems
  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++)
    sys->subsystems[i].stop(sys->subsystems[i].ctx);
  pthread_mutex_unlock(&sys->subsystems_lock);

  // Wait for non-main threads to unregister
  u64 start = now_us() / 1000;
  while (atomic_load(&sys->threads_registered) > 1) {
    if (now_us() / 1000 - start > deadline_ms) {
      VALK_WARN("Shutdown: %llu threads still registered",
                atomic_load(&sys->threads_registered) - 1);
      break;
    }
    usleep(1000);
  }

  // Wait + destroy subsystems
  pthread_mutex_lock(&sys->subsystems_lock);
  for (int i = 0; i < sys->subsystem_count; i++) {
    sys->subsystems[i].wait(sys->subsystems[i].ctx);
    sys->subsystems[i].destroy(sys->subsystems[i].ctx);
  }
  sys->subsystem_count = 0;
  pthread_mutex_unlock(&sys->subsystems_lock);
}

void valk_system_destroy(valk_system_t *sys) {
  valk_gc_heap2_destroy(sys->heap);
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
  VALK_GC_SAFE_POINT();  // participate in any pending STW

  u64 id = valk_thread_ctx.gc_thread_id;
  sys->threads[id].active = false;
  sys->threads[id].wake_fn = NULL;
  atomic_fetch_sub(&sys->threads_registered, 1);
  valk_thread_ctx.gc_registered = false;
}

void valk_system_wake_threads(valk_system_t *sys) {
  for (u64 i = 0; i < VALK_SYSTEM_MAX_THREADS; i++) {
    if (sys->threads[i].active && sys->threads[i].wake_fn) {
      sys->threads[i].wake_fn(sys->threads[i].wake_ctx);
    }
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

**Modify `valk_gc_safe_point_slow`:**
```c
void valk_gc_safe_point_slow(void) {
  valk_gc_phase_e phase = atomic_load(&valk_sys->phase);

  if (phase == VALK_GC_PHASE_CHECKPOINT_REQUESTED) {
    valk_barrier_wait(&valk_sys->barrier);   // ENTRY
    valk_barrier_wait(&valk_sys->barrier);   // EXIT
    return;
  }

  if (phase == VALK_GC_PHASE_STW_REQUESTED) {
    // Checkpoint own scratch before joining GC
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

#### `src/gc_checkpoint.c`

**Replace `valk_checkpoint_request_stw()`:**
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
  valk_barrier_wait(&valk_sys->barrier);  // ENTRY
}
```

**Replace `valk_checkpoint_release_stw()`:**
```c
static void valk_checkpoint_release_stw(void) {
  if (atomic_load(&valk_sys->phase) != VALK_GC_PHASE_CHECKPOINT_REQUESTED)
    return;

  atomic_store(&valk_sys->phase, VALK_GC_PHASE_IDLE);
  valk_barrier_wait(&valk_sys->barrier);  // EXIT
}
```

#### `src/gc_mark.c`

**Replace `valk_gc_heap2_request_stw()`:**
```c
bool valk_gc_heap2_request_stw(valk_gc_heap2_t *heap) {
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

  atomic_store(&__gc_heap2_current, heap);
  atomic_thread_fence(memory_order_seq_cst);

  valk_system_wake_threads(valk_sys);
  valk_barrier_wait(&valk_sys->barrier);  // ENTRY
  return true;
}
```

**Other changes in gc_mark.c:**
- Replace `valk_gc_coord.` → `valk_sys->` throughout
- Remove `threads_paused` increment/reset, `gc_done` broadcast
- Remove `#include "aio/aio.h"` (no longer calls `valk_aio_wake_all_for_gc`)

#### `src/gc_checkpoint.c` — additional

- Remove `#include "aio/aio.h"` (no longer calls `valk_aio_wake_all_for_gc`)

### Phase 2: Thread Context

#### `src/memory.h`

Add `system` field to `valk_thread_context_t`:
```c
typedef struct {
  valk_mem_allocator_t *allocator;
  struct valk_system *system;       // the system this thread belongs to
  void *heap;                       // GC heap (= system->heap)
  valk_mem_arena_t *scratch;
  struct valk_lenv_t *root_env;
  float checkpoint_threshold;
  bool checkpoint_enabled;
  u64 call_depth;
  struct valk_request_ctx *request_ctx;
  u64 gc_thread_id;
  bool gc_registered;
  struct valk_lval_t **root_stack;
  sz root_stack_count;
  sz root_stack_capacity;
  void *eval_stack;
  struct valk_lval_t *eval_expr;
  struct valk_lval_t *eval_value;
} valk_thread_context_t;
```

### Phase 3: AIO Integration

#### `src/aio/aio_uv.c`

**Simplify `__event_loop()`:**
```c
void __event_loop(void *arg) {
  valk_aio_system_t *sys = arg;

  // Register with the system — get heap, TLAB, GC participation
  // Provide wake function so GC can interrupt epoll_wait
  valk_system_register_thread(valk_sys, 
    (void(*)(void*))uv_async_send, &sys->gc_wakeup);

  // ... slab init, maintenance timer, task queue ...

  uv_sem_post(&sys->startup_sem);
  sys->ops->loop->run(sys, VALK_IO_RUN_DEFAULT);

  // Unregister before drain loop (drain doesn't allocate GC objects)
  valk_system_unregister_thread(valk_sys);

  // ... existing drain loop (100ms/300ms/500ms phases) ...
  // ... slab cleanup ...
}
```

**Remove:**
- `thread_onboard_fn` callback and the `if/else` branch
- `loop_gc_heap` creation and destruction (shares `valk_sys->heap`)

#### `src/aio/system/aio_system.c`

**Remove:**
- `g_aio_systems[]` static array
- `g_aio_systems_lock` mutex
- `valk_aio_register_system()` / `valk_aio_unregister_system()`
- `valk_aio_wake_all_for_gc()`
- `valk_aio_wait_for_all_systems()`

**Modify `valk_aio_start_with_config()`:**
- After creating the AIO system, register as subsystem:
```c
valk_system_add_subsystem(valk_sys,
  (void(*)(void*))valk_aio_stop,
  (void(*)(void*))valk_aio_wait_for_shutdown,
  (void(*)(void*))valk_aio_destroy,   // new: just the free part
  sys);
```

**Modify `__gc_wakeup_cb()`:**
```c
static void __gc_wakeup_cb(uv_async_t *handle) {
  valk_aio_system_t *sys = handle->data;
  if (!sys) return;
  valk_gc_safe_point_slow();
}
```
(Same as before — shutdown goes through subsystem.stop, not through the GC wakeup.)

**Split `valk_aio_wait_for_shutdown` into wait + destroy:**
- `valk_aio_wait_for_shutdown(sys)` — joins thread, cleans up queues (wait part)
- `valk_aio_destroy(sys)` — frees the struct itself

**Modify `valk_aio_reset_after_fork()`:**
- Clear `valk_sys->subsystems[]` instead of `g_aio_systems[]`

**Move `valk_metrics_registry_init()`:**
- Remove from `valk_aio_start_with_config()`
- Already called in `valk_system_create()`

#### `src/builtins_aio.c`

**Simplify `valk_builtin_aio_start()`:**
```c
// Remove:
config.thread_onboard_fn = valk_runtime_get_onboard_fn();

// The event loop thread calls valk_system_register_thread directly.
// No callback indirection needed.
```

**Rewrite `valk_builtin_shutdown()`:**
```c
static valk_lval_t* valk_builtin_shutdown(valk_lenv_t* e, valk_lval_t* a) {
  int code = 0;
  if (valk_lval_list_count(a) >= 1) {
    LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);
    code = (int)valk_lval_list_nth(a, 0)->num;
  }
  valk_lenv_def(e, valk_lval_sym("VALK_EXIT_CODE"), valk_lval_num(code));
  return valk_lval_num(code);
  // Shutdown code propagates to bootstrap loop.
  // Bootstrap calls valk_system_shutdown.
}
```

**Remove `valk_builtin_exit()`:**
- No more direct `exit()` calls. Everything goes through shutdown.

### Phase 4: Mechanical Renames

#### Handle table: `valk_global_handle_table` → `valk_sys->handle_table`

Files: `builtins_server.c`, `aio_comb_timers.c`, `aio_http2_server.c`,
`aio_http2_client.c`, `aio_http2_session.c`, `aio_stream_builtins.c`,
`aio_stream_body.c`

#### Heap access: `valk_runtime_get_heap()` → `valk_sys->heap`

Files: `gc_evacuation.c`, `gc_region.c`

#### Coordinator: `valk_gc_coord.` → `valk_sys->`

Files: `gc_stats.c`, `gc_mark.c` (any remaining refs)

#### Runtime check: `valk_runtime_is_initialized()` → `valk_sys != NULL`

Files: `builtins_aio.c`

### Phase 5: Cleanup

#### Remove `g_live_heaps[]` from `gc_heap.c`

One heap per system. No heap registry needed. Remove `valk_gc_register_heap()`,
`valk_gc_unregister_heap()`, `valk_gc_is_heap_alive()`.

#### Remove `loop_gc_heap` from `aio_internal.h`

Event loop threads share `valk_sys->heap`. Remove the field and its
creation/destruction in `aio_uv.c`.

#### Remove `thread_onboard_fn` from `aio_config.h`

No longer needed. Event loop threads register directly.

## Bootstrap (`repl.c`) Rewrite

```c
int main(int argc, char *argv[]) {
  valk_system_config_t cfg = valk_system_config_default();
  const char *limit_env = getenv("VALK_HEAP_HARD_LIMIT");
  if (limit_env && limit_env[0])
    cfg.gc_heap_size = strtoull(limit_env, NULL, 10);

  valk_system_t *sys = valk_system_create(&cfg);
  valk_gc_heap2_t *heap = sys->heap;

  // Scratch arena — per-thread, not system-owned
  valk_mem_arena_t *scratch = malloc(SCRATCH_SIZE);
  valk_mem_arena_init(scratch, SCRATCH_SIZE - sizeof(*scratch));
  valk_thread_ctx.allocator = (void *)heap;
  valk_thread_ctx.scratch = scratch;
  valk_thread_ctx.checkpoint_threshold = VALK_CHECKPOINT_THRESHOLD_DEFAULT;
  valk_thread_ctx.checkpoint_enabled = true;

  valk_lenv_t *env = valk_lenv_empty();
  valk_lenv_builtins(env);
  valk_gc_malloc_set_root(heap, env);
  valk_thread_ctx.root_env = env;

  // Parse + eval (script mode)
  int exit_code = 0;
  if (argc >= 2) {
    for (int i = 1; i < argc; i++) {
      valk_lval_t *ast = valk_parse_file(argv[i]);
      // ... eval loop, checkpoint between exprs, GC ...
    }
    exit_code = get_exit_code(env);
  } else {
    // REPL loop
    // ...
  }

  free(scratch);
  valk_system_shutdown(sys, 5000);
  valk_system_destroy(sys);
  return exit_code;
}
```

## Files Changed Summary

| File | Change | Description |
|------|--------|-------------|
| `src/gc.h` | **Major** | New `valk_system_t`, `valk_subsystem_t`, remove coordinator type |
| `src/gc.c` | **Major** | System lifecycle, thread reg with wake_fn, subsystem mgmt |
| `src/gc_mark.c` | **Moderate** | Barrier-based STW, remove AIO include, `valk_sys->` |
| `src/gc_checkpoint.c` | **Moderate** | Barrier-based checkpoint, remove AIO include |
| `src/gc_heap.c` | **Moderate** | Remove `g_live_heaps[]` |
| `src/gc_heap_lifecycle.c` | **Minor** | Remove heap registry calls |
| `src/gc_evacuation.c` | **Minor** | `valk_runtime_get_heap()` → `valk_sys->heap` |
| `src/gc_region.c` | **Minor** | Same |
| `src/gc_stats.c` | **Minor** | `valk_gc_coord.` → `valk_sys->` |
| `src/memory.h` | **Minor** | Add `system` field to thread context |
| `src/repl.c` | **Moderate** | Bootstrap eval loop, `system_create/shutdown/destroy` |
| `src/aio/system/aio_system.c` | **Moderate** | Remove global array, register as subsystem, split wait/destroy |
| `src/aio/aio_uv.c` | **Moderate** | Direct thread reg with wake_fn, remove loop heap |
| `src/aio/aio_config.h` | **Minor** | Remove `thread_onboard_fn` |
| `src/aio/aio_internal.h` | **Minor** | Remove `loop_gc_heap` field |
| `src/builtins_aio.c` | **Minor** | Remove onboard_fn, rewrite shutdown, remove exit |
| `src/builtins_io.c` | **Minor** | `valk_sys->heap` |
| `src/builtins_mem.c` | **Minor** | `valk_sys->heap` |
| `src/builtins_server.c` | **Minor** | `valk_sys->handle_table` |
| `src/aio/aio_comb_timers.c` | **Minor** | Same |
| `src/aio/http2/aio_http2_server.c` | **Minor** | Same |
| `src/aio/http2/aio_http2_client.c` | **Minor** | Same |
| `src/aio/http2/aio_http2_session.c` | **Minor** | Same |
| `src/aio/http2/stream/aio_stream_builtins.c` | **Minor** | Same |
| `src/aio/http2/stream/aio_stream_body.c` | **Minor** | Same |
| `src/metrics_v2.c` | **Minor** | Remove `static bool metrics_initialized` guard |
| `test/test_memory.c` | **Minor** | Update init calls |
| `test/test_gc_*.c` | **Minor** | Update init calls |

## Implementation Order

1. `src/gc.h` — define new types alongside old ones
2. `src/gc.c` — implement `valk_system_create/destroy/shutdown`, thread reg, subsystem mgmt
3. Add `#define valk_gc_coord (*valk_sys)` shim temporarily
4. Add `#define valk_global_handle_table (valk_sys->handle_table)` shim temporarily
5. `src/gc_checkpoint.c` — barrier-based checkpoint
6. `src/gc_mark.c` — barrier-based STW, remove AIO include
7. `src/memory.h` — add system field
8. `src/aio/aio_uv.c` — direct thread registration, remove loop heap
9. `src/aio/system/aio_system.c` — register as subsystem, remove globals
10. `src/repl.c` — bootstrap rewrite
11. Mechanical renames (handle table, heap access, coordinator refs)
12. Remove shims from step 3-4
13. Cleanup: remove `g_live_heaps[]`, `thread_onboard_fn`, `loop_gc_heap`
14. `make build && make test && make lint`
15. `make test-c-asan && make test-valk-asan`
16. Stress: `test_async_http_handlers.valk` 100+ times

## Test Plan

1. `make build` — compilation
2. `make test` — all C and Valk tests pass
3. `make lint` — clang-tidy clean
4. `make test-c-asan` / `make test-valk-asan` — no memory errors
5. `make test-c-tsan` / `make test-valk-tsan` — no data races
6. Stress: run `test_async_http_handlers.valk` 100+ times natively
7. Verify checkpoint deadlock is fixed (was ~1-2% failure, should be 0%)
8. Test `(shutdown 0)` with multiple AIO systems running
9. Test deadline expiry — start AIO, don't stop it, call shutdown with 1s deadline
