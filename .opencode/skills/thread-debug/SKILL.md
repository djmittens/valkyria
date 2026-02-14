---
name: thread-debug
description: Thread debugging with ThreadSanitizer and Helgrind - detect data races, deadlocks, and thread safety issues
license: MIT
metadata:
  platform: linux,macos
  category: debugging
---

# Thread Debugging for Valkyria

Detect threading issues including data races, deadlocks, lock order violations, and thread safety problems.

## ThreadSanitizer (TSAN)

TSAN is built into Clang/GCC and detects data races with ~5-15x slowdown.

### Building with TSAN

```bash
# Use the Makefile target
make build-tsan

# Manual build
cmake -DTSAN=1 -S . -B build-tsan
cmake --build build-tsan
```

### Running with TSAN

```bash
# Basic run
build-tsan/valk src/prelude.valk test/test_prelude.valk

# Run TSAN tests (per AGENTS.md, REDIRECT OUTPUT!)
TSAN_OPTIONS="log_path=build/tsan.log" make test-c-tsan
echo "TSAN: $(grep -c 'WARNING: ThreadSanitizer' build/tsan.log 2>/dev/null || echo 0) races"
grep -A2 "WARNING: ThreadSanitizer" build/tsan.log | grep "#0" | sort -u | head -5

# Run single test with TSAN
build-tsan/test_memory
```

### TSAN Options

```bash
# Common options
export TSAN_OPTIONS="
  halt_on_error=1
  second_deadlock_stack=1
  history_size=7
  verbosity=1
"

# Log to file (recommended for CI)
export TSAN_OPTIONS="log_path=tsan.log"

# Suppress known issues
export TSAN_OPTIONS="suppressions=tsan_suppressions.txt"
```

### Interpreting TSAN Output

#### Data Race

```
WARNING: ThreadSanitizer: data race (pid=12345)
  Write of size 8 at 0x... by thread T1:
    #0 worker_thread src/thread.c:50
    #1 pthread_start

  Previous read of size 8 at 0x... by main thread:
    #0 main_loop src/main.c:100
    #1 main

  Location is global 'shared_counter' of size 8 at 0x...
```

Key parts:
- **Two accesses**: One write (or two writes) to same location
- **Different threads**: T1 vs main thread
- **No synchronization**: Between the accesses

#### Deadlock

```
WARNING: ThreadSanitizer: lock-order-inversion (potential deadlock)
  Cycle in lock order graph:
    M1 (0x...) -> M2 (0x...)
    M2 (0x...) -> M1 (0x...)

  Thread T1 acquired M1 then M2:
    #0 pthread_mutex_lock
    #1 func_a src/sync.c:20
    ...

  Thread T2 acquired M2 then M1:
    #0 pthread_mutex_lock
    #1 func_b src/sync.c:40
```

### TSAN Suppressions

Create `tsan_suppressions.txt`:
```
# Suppress race in third-party library
race:third_party_lib

# Suppress specific function
race:known_benign_race

# Suppress deadlock detection for specific mutex
deadlock:intentionally_ordered_locks

# Suppress by call stack
race:^worker_thread$
called_from_lib:libpthread
```

## Valgrind Helgrind (Linux)

Helgrind is Valgrind's thread error detector, slower but more thorough.

### Running Helgrind

```bash
# Basic run
valgrind --tool=helgrind build/valk src/prelude.valk

# With more detail
valgrind --tool=helgrind \
  --history-level=full \
  --conflict-cache-size=10000000 \
  build/valk src/prelude.valk
```

### Helgrind Output

```
==12345== Possible data race during read of size 4 at 0x... by thread #2
==12345== Locks held: none
==12345==    at 0x...: worker (thread.c:50)
==12345==    by 0x...: mythread_wrapper (...)
==12345==
==12345== This conflicts with a previous write of size 4 by thread #1
==12345== Locks held: none
==12345==    at 0x...: main (main.c:100)
```

### Helgrind Suppressions

```
{
   benign_race
   Helgrind:Race
   fun:known_benign_function
}
```

## Valgrind DRD (Linux)

DRD is another Valgrind thread checker, sometimes catches different issues.

```bash
# Basic run
valgrind --tool=drd build/valk src/prelude.valk

# With extra checks
valgrind --tool=drd \
  --check-stack-var=yes \
  --trace-barrier=yes \
  --trace-cond=yes \
  --trace-mutex=yes \
  build/valk src/prelude.valk
```

## Common Threading Issues

### Data Race

**Problem**: Two threads access shared data without synchronization, at least one is a write.

**Detection**:
```bash
TSAN_OPTIONS=halt_on_error=1 build-tsan/valk src/prelude.valk
```

**Fix patterns**:
```c
// Option 1: Mutex
pthread_mutex_lock(&mutex);
shared_data = new_value;
pthread_mutex_unlock(&mutex);

// Option 2: Atomic
atomic_store(&shared_data, new_value);

// Option 3: Thread-local storage
__thread int thread_local_data;
```

### Deadlock

**Problem**: Two or more threads waiting for each other's locks.

**Detection**:
```bash
TSAN_OPTIONS=second_deadlock_stack=1 build-tsan/valk src/prelude.valk
```

**Fix patterns**:
```c
// Always acquire locks in consistent order
// If need A and B, always get A first, then B

// Or use trylock with backoff
if (pthread_mutex_trylock(&mutex_b) != 0) {
    pthread_mutex_unlock(&mutex_a);
    // back off and retry
}
```

### Use-After-Free (Threading)

**Problem**: One thread frees memory while another still uses it.

**Detection**: TSAN often catches this as a race, or ASAN catches the memory error.

**Fix**: Use reference counting or ensure proper synchronization on object lifetime.

### Lock Order Inversion

**Problem**: Acquiring locks in inconsistent order across threads.

**Detection**:
```bash
TSAN_OPTIONS=second_deadlock_stack=1 build-tsan/valk
```

**Fix**: Establish and document a global lock ordering.

## Project-Specific Commands

```bash
# Build and test with TSAN (per AGENTS.md)
make build-tsan
TSAN_OPTIONS="log_path=build/tsan.log" make test-c-tsan

# Summarize TSAN results
echo "TSAN: $(grep -c 'WARNING: ThreadSanitizer' build/tsan.log 2>/dev/null || echo 0) races"
grep -A2 "WARNING: ThreadSanitizer" build/tsan.log | grep "#0" | sort -u | head -5

# Run specific threading test
build-tsan/test_thread_posix_unit
build-tsan/test_chase_lev_unit
build-tsan/test_task_queue_unit
```

## Debugging with GDB/LLDB

### GDB Thread Commands

```gdb
(gdb) info threads
(gdb) thread 2
(gdb) thread apply all bt
(gdb) set scheduler-locking on  # Freeze other threads
(gdb) break func thread 2       # Break only in thread 2
```

### LLDB Thread Commands

```lldb
(lldb) thread list
(lldb) thread select 2
(lldb) thread backtrace all
(lldb) thread continue -b  # Continue current thread only
```

## Atomic Operations Debugging

### Check Memory Ordering

```c
// Use relaxed ordering only when safe
atomic_load_explicit(&var, memory_order_relaxed);

// Use acquire/release for synchronization
atomic_store_explicit(&flag, 1, memory_order_release);
while (!atomic_load_explicit(&flag, memory_order_acquire));
```

### TSAN Annotations

```c
#include <sanitizer/tsan_interface.h>

// Tell TSAN about happens-before
__tsan_acquire(&sync_var);
__tsan_release(&sync_var);

// Ignore benign races
__tsan_ignore_thread_begin();
benign_racy_operation();
__tsan_ignore_thread_end();
```

## Tips

1. **Always redirect TSAN output** - it can flood your terminal
2. Fix races one at a time - they can mask each other
3. TSAN and ASAN cannot be used together - pick one per run
4. Use `halt_on_error=1` to stop at first issue
5. Lock ordering issues are easier to fix early - establish conventions
6. Consider using thread-local storage to avoid sharing
7. Prefer higher-level synchronization (channels, queues) over raw locks
8. Document which data is accessed by which threads
9. Use `second_deadlock_stack=1` to see both sides of potential deadlocks
10. Helgrind and DRD sometimes catch different issues - try both
