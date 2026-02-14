---
name: rr-debug
description: Time-travel debugging with rr (Linux) or alternatives (macOS) - record test execution, replay deterministically, step backwards to find root cause of flaky tests and crashes
license: MIT
metadata:
  platform: linux,macos
  category: debugging
---

# Time-Travel Debugging with rr

rr records program execution deterministically. When a test fails, you can replay it unlimited times, step backwards, and set watchpoints to find exactly when/where state changed.

**Note: rr is Linux-only.** For macOS, see the "macOS Alternatives" section at the end.

## Setup (Linux)

```bash
# Install rr
apt install rr

# Enable perf events (required)
echo 1 | sudo tee /proc/sys/kernel/perf_event_paranoid

# Verify
rr --version
```

## Quick Start - Valkyria Tests

```bash
# Record a single C test
RR=1 make test-c TEST=test_networking

# Record a single Valk test  
RR=1 make test-valk TEST=test/test_http_integration.valk

# Run until failure (for flaky tests)
make test-rr-until-fail TEST=test_networking MAX=100

# Replay the recording
rr replay
```

## Recording Options

### Basic Recording
```bash
# Record with default options
rr record ./build/test_networking

# Record with chaos mode (randomizes scheduling to expose races)
rr record --chaos ./build/test_networking

# Disable fork following (for forked test children)
VALK_TEST_NO_FORK=1 rr record ./build/test_networking
```

### Recording Flaky Tests
```bash
# Loop until failure, keeping the failing recording
for i in {1..100}; do
  echo "Attempt $i..."
  if ! rr record --chaos ./build/test_networking; then
    echo "Failed on attempt $i - recording saved"
    break
  fi
done
```

## Replay and Debug

### Start Replay
```bash
# Replay most recent recording
rr replay

# Replay specific recording
rr replay ~/.local/share/rr/test_networking-42/

# Replay with specific GDB
rr replay -d /usr/bin/gdb
```

### Essential GDB Commands in rr

```gdb
# Run forward to crash/end
continue

# Run BACKWARDS to previous stop
reverse-continue

# Step backwards (reverse single step)
reverse-step
reverse-stepi
reverse-next
reverse-nexti

# Go to specific event number
run 12345

# Show current event number  
when

# Set hardware watchpoint (stops when value changes)
watch -l some_variable
# Then reverse-continue to find who changed it

# Find when a memory location was written
watch *(int*)0x7fff5678
reverse-continue

# Checkpoints (save/restore points in time)
checkpoint
restart 1
```

### Common Debugging Workflows

#### Find Who Corrupted Memory
```gdb
# 1. Run to crash
continue

# 2. Inspect corrupted state
print *corrupted_ptr

# 3. Set watchpoint on the memory
watch -l *corrupted_ptr

# 4. Go backwards to find the write
reverse-continue

# 5. You're now at the exact instruction that corrupted it
bt
```

#### Find Race Condition
```gdb
# 1. Run to failure point
continue

# 2. Note the unexpected value
print shared_counter

# 3. Watch the variable
watch -l shared_counter

# 4. Reverse to each modification
reverse-continue  # First write
reverse-continue  # Second write (the race!)
info threads
bt
```

#### Find Deadlock
```gdb
# 1. Interrupt hung process
Ctrl+C

# 2. See all threads
info threads
thread apply all bt

# 3. Find lock state
print mutex_variable

# 4. Watch the lock
watch -l mutex_variable.__data.__lock

# 5. Reverse to see acquisition order
reverse-continue
```

## rr Tips

### Performance
- rr adds ~1.5x slowdown (much less than Valgrind)
- Recording size: ~1GB per minute of execution
- Keep recordings small: test minimal reproducer

### Limitations
- Linux only (no macOS, no Windows)
- x86/x86_64 only (no ARM)
- No GPU/hardware access
- Some syscalls not supported

### Chaos Mode
```bash
# Randomize scheduling to expose races
rr record --chaos ./test

# More aggressive chaos
rr record --chaos --wait ./test
```

### Environment Variables
```bash
# Disable ASLR (sometimes needed)
setarch $(uname -m) -R rr record ./test

# Record with specific CPU features disabled
rr record --disable-cpuid-features=0xffffffff ./test
```

## Valkyria-Specific Notes

### Fork-Based Tests
The test framework forks for isolation. rr follows forks by default, but this can complicate debugging:

```bash
# Option 1: Disable fork in tests
VALK_TEST_NO_FORK=1 rr record ./build/test_networking

# Option 2: Let rr follow forks (default)
rr record ./build/test_networking
# In replay, switch to child process:
rr replay -f <child-pid>
```

### GC/Threading Issues
For GC coordination bugs:

```gdb
# Watch GC phase transitions
watch -l valk_gc_coord.phase
reverse-continue

# Watch thread pause count
watch -l valk_gc_coord.threads_paused
```

### Async/Event Loop Issues
For libuv event loop bugs:

```gdb
# Break on event loop iteration
break uv_run

# Watch pending handle count
watch -l loop->active_handles
```

## Recordings Location

```bash
# Default location
ls ~/.local/share/rr/

# List recordings
rr ls

# Delete old recordings
rr rm test_networking-42
rr rm --all  # Delete everything
```

## Integration with CI

For flaky tests in CI, record failures for later analysis:

```bash
#!/bin/bash
# ci-test-with-rr.sh

if ! rr record --chaos ./build/$TEST; then
  # Upload recording as artifact
  tar czf "rr-$TEST-$(date +%s).tar.gz" ~/.local/share/rr/latest-trace/
  exit 1
fi
```

## macOS Alternatives

macOS doesn't have rr. Use these approaches instead:

### Core Dumps with LLDB
```bash
# Enable core dumps
sudo sysctl kern.coredump=1

# Core dumps go to /cores/
ls -la /cores/

# Debug a core dump
lldb -c /cores/core.12345 build/test_networking
```

### Run Until Failure + LLDB
```bash
# Loop until failure
for i in {1..100}; do
  echo "Iteration $i..."
  build/test_networking || { echo "Failed on $i"; break; }
done

# Then debug interactively
lldb -- build/test_networking
```

### Instruments for Profiling
```bash
# Time Profiler (find CPU hotspots)
xcrun xctrace record --template 'Time Profiler' --launch -- build/test_networking

# System Trace (syscalls, scheduling)
xcrun xctrace record --template 'System Trace' --launch -- build/test_networking

# Open in Instruments.app
open *.trace
```

### LLDB Watchpoints (Manual Time-Travel)
```bash
lldb -- build/test_networking
```

```lldb
# Set watchpoint on variable
watchpoint set variable some_global

# When it triggers, examine state
bt
frame variable

# Unfortunately no reverse-continue on macOS
# But you can re-run with conditional breakpoints
breakpoint set -n some_function -c 'counter > 50'
```

### Address Sanitizer
ASAN works on both Linux and macOS and is often sufficient:
```bash
make test-c-asan TEST=test_networking
make test-asan-abort  # Generates core dump on failure
```

## See Also

- `man rr`
- https://rr-project.org/
- https://github.com/rr-debugger/rr/wiki
- LLDB docs: https://lldb.llvm.org/
- Instruments: https://developer.apple.com/instruments/
