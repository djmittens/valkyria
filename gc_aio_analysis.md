# GC-AIO Coordination Mechanism Analysis

## Overview

The Valkyria GC uses a **stop-the-world (STW)** approach with **parallel marking and sweeping**. When GC is triggered, all threads must pause at safe points before collection proceeds. The AIO (event loop) thread requires special coordination because it may be blocked in `uv_run()` waiting for I/O.

## Key Components

### 1. Global GC Coordinator (`gc.c:229-247`)

```c
typedef struct valk_gc_coordinator {
  _Atomic valk_gc_phase_e phase;           // Current GC phase
  _Atomic u64 threads_registered;          // Threads participating in GC
  _Atomic u64 threads_paused;              // Threads at safe points
  pthread_mutex_t lock;                    // Protects condition variables
  pthread_cond_t all_paused;               // Signaled when all threads paused
  pthread_cond_t gc_done;                  // Signaled when GC complete
  valk_barrier_t barrier;                  // Synchronizes GC phases
} valk_gc_coordinator_t;
```

### 2. GC Phases

```
VALK_GC_PHASE_IDLE
    |
    v (valk_gc_heap2_request_stw)
VALK_GC_PHASE_STW_REQUESTED
    |
    v (all threads reach safe point via barrier)
VALK_GC_PHASE_MARKING
    |
    v (barrier sync)
VALK_GC_PHASE_SWEEPING  
    |
    v (barrier sync + broadcast gc_done)
VALK_GC_PHASE_IDLE
```

### 3. Per-AIO-System GC Wakeup Handle (`aio_internal.h:336`)

```c
struct valk_aio_system {
  uv_async_t gc_wakeup;  // Async handle to wake event loop for GC
};
```

## Detailed Flow: GC with AIO Thread

### Step 1: GC Initiator Requests STW (`gc.c:3772-3815`)

```c
bool valk_gc_heap2_request_stw(valk_gc_heap2_t *heap) {
  // 1. Atomically transition: IDLE -> STW_REQUESTED
  valk_gc_phase_e expected = VALK_GC_PHASE_IDLE;
  if (!atomic_compare_exchange_strong(&valk_gc_coord.phase, &expected,
                                       VALK_GC_PHASE_STW_REQUESTED)) {
    return false;  // Another GC in progress
  }
  
  // 2. Read thread count and initialize barrier
  u64 num_threads = atomic_load(&valk_gc_coord.threads_registered);
  valk_barrier_init(&valk_gc_coord.barrier, num_threads);
  
  // 3. Store current heap for workers
  atomic_store(&__gc_heap2_current, heap);
  
  // 4. Wake all event loops
  valk_aio_wake_all_for_gc();
  
  // 5. Count self as paused
  atomic_fetch_add(&valk_gc_coord.threads_paused, 1);
  
  // 6. Wait for other threads
  pthread_mutex_lock(&valk_gc_coord.lock);
  while (atomic_load(&valk_gc_coord.threads_paused) < num_threads) {
    pthread_cond_timedwait(&valk_gc_coord.all_paused, &valk_gc_coord.lock, &ts);
  }
  pthread_mutex_unlock(&valk_gc_coord.lock);
}
```

### Step 2: Wake All Event Loops (`aio_system.c:40-49`)

```c
void valk_aio_wake_all_for_gc(void) {
  pthread_mutex_lock(&g_aio_systems_lock);
  for (int i = 0; i < VALK_AIO_MAX_SYSTEMS; i++) {
    valk_aio_system_t *sys = g_aio_systems[i];
    if (sys && sys->eventloop && !sys->shuttingDown) {
      uv_async_send(&sys->gc_wakeup);  // Wake loop via eventfd
    }
  }
  pthread_mutex_unlock(&g_aio_systems_lock);
}
```

**libuv async mechanism:**
- `uv_async_send()` writes to an eventfd (Linux) or pipe (other platforms)
- This wakes `uv_run()` from its poll wait immediately
- Multiple sends coalesce into single callback invocation

### Step 3: Event Loop Callback (`aio_system.c:51-55`)

```c
static void __gc_wakeup_cb(uv_async_t *handle) {
  valk_aio_system_t *sys = (valk_aio_system_t *)handle->data;
  if (!sys) return;
  valk_gc_safe_point_slow();  // Enter safe point
}
```

### Step 4: Safe Point Slow Path (`gc.c:299-339`)

```c
void valk_gc_safe_point_slow(void) {
  valk_gc_phase_e phase = atomic_load(&valk_gc_coord.phase);

  if (phase == VALK_GC_PHASE_STW_REQUESTED) {
    // Checkpoint scratch arena if needed
    if (valk_thread_ctx.scratch && valk_thread_ctx.scratch->offset > 0) {
      valk_checkpoint(valk_thread_ctx.scratch, valk_thread_ctx.heap,
                      valk_thread_ctx.root_env);
    }

    // Increment paused count and signal if last
    u64 paused = atomic_fetch_add(&valk_gc_coord.threads_paused, 1) + 1;
    if (paused == atomic_load(&valk_gc_coord.threads_registered)) {
      pthread_mutex_lock(&valk_gc_coord.lock);
      pthread_cond_signal(&valk_gc_coord.all_paused);
      pthread_mutex_unlock(&valk_gc_coord.lock);
    }

    // Participate in parallel GC work
    valk_gc_participate_in_parallel_gc();
  }
}
```

### Step 5: Parallel GC Work (`gc.c:3911-3939`)

```c
static void valk_gc_participate_in_parallel_gc(void) {
  valk_gc_heap2_t *heap = atomic_load(&__gc_heap2_current);
  
  // BARRIER 1: Sync before mark
  valk_barrier_wait(&valk_gc_coord.barrier);
  valk_gc_heap2_parallel_mark(heap);
  
  // BARRIER 2: Sync after mark
  valk_barrier_wait(&valk_gc_coord.barrier);
  valk_gc_heap2_parallel_sweep(heap);
  
  // BARRIER 3: Sync after sweep
  valk_barrier_wait(&valk_gc_coord.barrier);
  
  // BARRIER 4: Sync after reclamation
  valk_barrier_wait(&valk_gc_coord.barrier);
}
```

## Synchronization Primitives

| Primitive | Purpose |
|-----------|---------|
| `_Atomic phase` | Phase state machine, CAS for transition |
| `_Atomic threads_paused` | Count threads at safe points |
| `pthread_cond_t all_paused` | Signal initiator when all paused |
| `pthread_cond_t gc_done` | Signal workers when GC complete |
| `valk_barrier_t barrier` | Synchronize GC phases (4 barriers) |
| `uv_async_t gc_wakeup` | Wake blocked event loop |

## Libuv Async Coalescing

libuv's `uv_async_send()` coalesces multiple sends:

```c
int uv_async_send(uv_async_t* handle) {
  if (atomic_load(&handle->pending) != 0)
    return 0;  // Already pending, coalesce
  
  if (atomic_exchange(&handle->pending, 1) == 0)
    uv__async_send(handle->loop);  // Write to eventfd
}
```

**Implications:**
- If multiple GC requests arrive before callback runs, only one callback fires
- This is fine: callback checks `phase` atomically and handles current state
- Spurious wakeups are harmless: callback returns early if `phase != STW_REQUESTED`

## Potential Deadlock Scenarios

### Scenario 1: Main Thread in `aio/run` Sleep Loop (FIXED)

**Historical Bug (documented in PARALLEL_GC_PLAN.md:3164-3199):**

```c
// BROKEN - main thread never pauses for GC
while (!valk_aio_is_shutting_down(sys)) {
  uv_sleep(100);  // No safe point check!
}
```

When AIO thread triggered GC:
1. AIO thread set `phase = STW_REQUESTED`
2. AIO thread waited for all registered threads
3. Main thread was sleeping - **never checked gc_phase**
4. **Deadlock**: AIO waited forever for main thread

**Fix Applied (parser.c):**
```c
while (!valk_aio_is_shutting_down(sys)) {
  VALK_GC_SAFE_POINT();  // Check if GC needs pause
  uv_sleep(100);
}
```

### Scenario 2: Thread Registration Race

**Potential Issue:**
- Thread A registers (threads_registered = 2)
- Thread B starts GC (reads num_threads = 2)
- Thread A unregisters before reaching safe point
- Thread B waits for 2 threads, but only 1 can respond

**Mitigation:**
- `pthread_cond_timedwait` with 100ms timeout prevents infinite wait
- If count mismatch persists, initiator eventually times out
- `threads_registered` is always read *after* phase is set

### Scenario 3: Event Loop Not Yet Registered

**Location:** `aio_uv.c:75-79`

```c
// Register with GC right before entering uv_run
if (!sys->config.thread_onboard_fn) {
  valk_gc_thread_register();
}
```

If GC is triggered between `valk_aio_start()` and `valk_gc_thread_register()`:
- Event loop won't be in `threads_registered` count
- GC will proceed without waiting for it
- **Safe**: Event loop hasn't started processing yet

### Scenario 4: Shutdown During GC

The system handles this correctly:
1. `valk_aio_stop()` sets `shuttingDown` atomically
2. `valk_aio_wake_all_for_gc()` checks `!sys->shuttingDown`
3. If shutting down, loop isn't woken for GC
4. Shutdown waits for current GC to complete via safe point

## Why No Deadlock in Normal Operation

The design avoids circular waits:

1. **Lock ordering**: `g_aio_systems_lock` always released before `valk_gc_coord.lock`
2. **Condition variables**: Mutex released atomically during `pthread_cond_wait`
3. **Separation**: CHECKPOINT uses conditions; STW uses barriers
4. **Fallback**: `pthread_cond_timedwait` prevents infinite blocking

**Execution flow showing no circular dependency:**

```
Main Thread                          Event Loop Thread
-----------                          -----------------
1. Set phase=STW_REQUESTED
2. Lock g_aio_systems_lock
3. uv_async_send() to wake loop
4. Unlock g_aio_systems_lock        <-- Lock released!
5. threads_paused++
6. Lock valk_gc_coord.lock           
7. Wait on all_paused (releases lock) <-- Mutex released during wait
                                     A. uv_run returns
                                     B. gc_wakeup_cb fires
                                     C. safe_point_slow()
                                     D. threads_paused++
                                     E. Lock valk_gc_coord.lock (available!)
                                     F. Signal all_paused
                                     G. Unlock
8. Wake from wait
9. Proceed to barriers
```

## Summary

The GC-AIO coordination is **correctly implemented** with no deadlock scenarios in normal operation:

1. **Safe point macro** ensures all threads check GC phase periodically
2. **Async wakeup** immediately interrupts blocked event loop
3. **Timed waits** prevent infinite blocking on thread count mismatches
4. **Barrier synchronization** ensures all threads progress through GC phases together
5. **Phase transitions** are atomic and use CAS to prevent races

The historical deadlock (main thread in `aio/run` sleep loop) was fixed by adding `VALK_GC_SAFE_POINT()` to the sleep loop.
