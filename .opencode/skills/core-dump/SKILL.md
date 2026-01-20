---
name: core-dump
description: Core dump analysis for post-mortem debugging - configure core dumps, analyze crashes, and extract debug info from crashed processes
license: MIT
metadata:
  platform: linux,macos
  category: debugging
---

# Core Dump Analysis for Valkyria

Analyze core dumps for post-mortem debugging of crashes, segfaults, and other fatal errors.

## Enabling Core Dumps

### Linux

```bash
# Check current limit
ulimit -c

# Enable unlimited core dumps (current shell)
ulimit -c unlimited

# Permanent (add to /etc/security/limits.conf)
* soft core unlimited
* hard core unlimited

# Or in systemd (add to service file)
[Service]
LimitCORE=infinity
```

### Core Dump Location (Linux)

```bash
# Check current pattern
cat /proc/sys/kernel/core_pattern

# Common patterns:
# core                         -> ./core (current directory)
# /var/crash/core.%e.%p.%t    -> /var/crash/core.<name>.<pid>.<time>
# |/usr/lib/systemd/systemd-coredump  -> systemd-coredump handling

# Set pattern (requires root)
echo "/tmp/core.%e.%p" | sudo tee /proc/sys/kernel/core_pattern

# Pattern specifiers:
# %e = executable name
# %p = PID
# %t = timestamp
# %u = UID
# %s = signal number
```

### systemd-coredump (Modern Linux)

```bash
# List core dumps
coredumpctl list

# Show info for latest
coredumpctl info

# Debug with GDB
coredumpctl gdb

# Debug specific dump
coredumpctl gdb <pid>
coredumpctl gdb /path/to/executable

# Extract core file
coredumpctl dump -o /tmp/core
```

### macOS

```bash
# Core dumps go to /cores/ by default
# Must enable with:
ulimit -c unlimited

# Check location
ls /cores/

# Or check system report
ls ~/Library/Logs/DiagnosticReports/

# Crash reports are in:
# ~/Library/Logs/DiagnosticReports/
# /Library/Logs/DiagnosticReports/
```

## Generating Test Core Dumps

```bash
# Method 1: Kill with signal
kill -SIGABRT $(pgrep valk)
kill -SIGSEGV $(pgrep valk)

# Method 2: gcore (while running)
gcore -o /tmp/core $(pgrep valk)

# Method 3: Debugger
gdb -p $(pgrep valk)
(gdb) generate-core-file /tmp/valk.core
(gdb) detach

# lldb
lldb -p $(pgrep valk)
(lldb) process save-core /tmp/valk.core
(lldb) detach
```

## Analyzing Core Dumps

### GDB (Linux)

```bash
# Load core with executable
gdb build/valk /path/to/core

# Basic analysis
(gdb) bt                    # Backtrace of crash
(gdb) bt full               # With local variables
(gdb) info registers        # CPU registers at crash
(gdb) info threads          # All threads
(gdb) thread apply all bt   # Backtrace all threads

# Examine crash location
(gdb) frame 0               # Select crash frame
(gdb) list                  # Show source (if available)
(gdb) info locals           # Local variables
(gdb) info args             # Function arguments

# Examine memory
(gdb) x/10xg $rsp           # Stack
(gdb) x/i $rip              # Instruction at crash
(gdb) p *ptr                # Dereference pointer
```

### LLDB (macOS)

```bash
# Load core
lldb --core /cores/core.12345 build/valk

# Or with crash report
lldb
(lldb) target create build/valk
(lldb) target symbols add build/valk.dSYM
(lldb) process load /cores/core.12345

# Analysis
(lldb) bt                   # Backtrace
(lldb) bt all               # All threads
(lldb) frame info           # Current frame details
(lldb) register read        # Registers
(lldb) memory read $rsp     # Stack memory
```

## Interpreting Crash Information

### Signal Types

```
SIGSEGV (11) - Segmentation fault
  - Invalid memory access
  - NULL pointer dereference
  - Access after free
  - Stack overflow

SIGABRT (6) - Abort
  - assert() failure
  - abort() called
  - ASAN error
  - malloc corruption detected

SIGBUS (7) - Bus error
  - Misaligned memory access
  - Invalid physical address

SIGFPE (8) - Floating point exception
  - Division by zero
  - Integer overflow (with -ftrapv)

SIGILL (4) - Illegal instruction
  - Corrupted code
  - Wrong architecture
  - Stack smashing (jumped to bad address)
```

### Common Crash Patterns

#### NULL Pointer Dereference

```
Program received signal SIGSEGV
0x0000555555555234 in valk_lval_copy (v=0x0) at parser.c:150
(gdb) bt
#0  valk_lval_copy (v=0x0) at parser.c:150
#1  valk_lval_eval (e=0x5555..., v=0x5555...) at parser.c:300

# v=0x0 indicates NULL pointer
# Fix: Add NULL check or fix caller
```

#### Use After Free

```
Program received signal SIGSEGV
0x0000555555555500 in valk_lval_del (v=0x5555deadbeef)
(gdb) p *v
$1 = {type = 1431655765, ...}  # Garbage values

# Memory was freed, contains junk
# Use ASAN to find where it was freed
```

#### Stack Overflow

```
Program received signal SIGSEGV
(gdb) bt
#0  valk_lval_eval (...) at parser.c:300
#1  valk_lval_eval (...) at parser.c:350
#2  valk_lval_eval (...) at parser.c:350
... (thousands of frames)

# Infinite recursion
# Fix: Add base case or iteration limit
```

#### Buffer Overflow

```
Program received signal SIGSEGV
0x4141414141414141 in ?? ()
(gdb) info registers
rip = 0x4141414141414141

# RIP contains "AAAA..." - corrupted return address
# Use ASAN to find the overflow
```

## ASAN Core Dumps

When running with ASAN, enable abort on error:

```bash
ASAN_OPTIONS=abort_on_error=1:disable_coredump=0 build-asan/valk src/prelude.valk

# Core dump will be generated, plus ASAN output
# ASAN output gives more detail than the core dump
```

## Project-Specific Analysis

### Debug GC Crash

```bash
gdb build/valk core
(gdb) bt
# Look for gc_* functions
(gdb) frame <gc_frame_number>
(gdb) p *gc
(gdb) p gc->roots
(gdb) p gc->heap_size
```

### Debug Parser Crash

```bash
gdb build/valk core
(gdb) bt
# Look for valk_lval_* functions
(gdb) frame <parser_frame>
(gdb) p *lval
(gdb) p lval->cell[0]
(gdb) list  # Show source context
```

### Debug Networking Crash

```bash
gdb build/valk core
(gdb) bt
# Look for uv_*, ssl_*, socket functions
(gdb) info threads
(gdb) thread apply all bt  # Check all threads
```

## Automated Core Analysis Script

Create `scripts/analyze-core.sh`:
```bash
#!/bin/bash
# Usage: ./scripts/analyze-core.sh <executable> <core-file>

EXECUTABLE="${1:-build/valk}"
COREFILE="${2:-core}"

if [ ! -f "$COREFILE" ]; then
    echo "Core file not found: $COREFILE"
    echo "Available cores:"
    coredumpctl list 2>/dev/null || ls /cores/ 2>/dev/null || ls core* 2>/dev/null
    exit 1
fi

echo "=== Core Dump Analysis ==="
echo "Executable: $EXECUTABLE"
echo "Core file: $COREFILE"
echo

gdb -batch \
    -ex "file $EXECUTABLE" \
    -ex "core-file $COREFILE" \
    -ex "echo === Signal ===\n" \
    -ex "info signal" \
    -ex "echo \n=== Backtrace ===\n" \
    -ex "bt full" \
    -ex "echo \n=== Registers ===\n" \
    -ex "info registers" \
    -ex "echo \n=== All Threads ===\n" \
    -ex "thread apply all bt" \
    -ex "echo \n=== Memory Map ===\n" \
    -ex "info proc mappings" \
    -ex "quit"
```

## Tips

1. **Always build with debug symbols** (`-g`) for meaningful backtraces
2. **Keep executables matching core dumps** - mismatched versions give wrong info
3. **Use ASAN for memory bugs** - it provides better diagnostics than core dumps
4. **Check signal type first** - it tells you the class of bug
5. **Look at registers** - RIP/PC shows where, RSP shows stack state
6. **Examine all threads** - bug might be in different thread than crash
7. **Save core dumps** - they're invaluable for intermittent bugs
8. **Use coredumpctl on modern Linux** - it manages dumps automatically
9. **On macOS, check DiagnosticReports** - crash reports have symbolicated stacks
10. **Core dumps can be large** - compress or delete after analysis
