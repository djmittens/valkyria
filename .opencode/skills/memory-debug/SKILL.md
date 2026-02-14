---
name: memory-debug
description: Memory debugging with AddressSanitizer and Valgrind - detect leaks, buffer overflows, use-after-free, and heap corruption
license: MIT
metadata:
  platform: linux,macos
  category: debugging
---

# Memory Debugging for Valkyria

Detect memory errors including leaks, buffer overflows, use-after-free, double-free, and heap corruption.

## AddressSanitizer (ASAN)

ASAN is built into Clang/GCC and provides fast memory error detection with ~2x slowdown.

### Building with ASAN

```bash
# Use the Makefile target
make build-asan

# Manual build
cmake -DASAN=1 -S . -B build-asan
cmake --build build-asan
```

### Running with ASAN

```bash
# Basic run
build-asan/valk src/prelude.valk test/test_prelude.valk

# With environment options
ASAN_OPTIONS=detect_leaks=1:halt_on_error=1:abort_on_error=1 \
LSAN_OPTIONS=verbosity=1:log_threads=1 \
build-asan/valk src/prelude.valk

# Run ASAN tests
make test-c-asan
make test-valk-asan
```

### ASAN Options

```bash
# Common options
export ASAN_OPTIONS="
  detect_leaks=1
  halt_on_error=1
  abort_on_error=1
  print_stats=1
  check_initialization_order=1
  detect_stack_use_after_return=1
  strict_string_checks=1
  detect_invalid_pointer_pairs=2
"

# For debugging with GDB
export ASAN_OPTIONS="abort_on_error=1:disable_coredump=0"
gdb --args build-asan/valk src/prelude.valk
```

### Interpreting ASAN Output

```
==12345==ERROR: AddressSanitizer: heap-buffer-overflow on address 0x...
READ of size 4 at 0x... thread T0
    #0 0x... in valk_lval_copy parser.c:150
    #1 0x... in valk_lval_eval parser.c:300
    ...
0x... is located 4 bytes to the right of 100-byte region [0x...,0x...)
allocated by thread T0 here:
    #0 0x... in malloc
    #1 0x... in valk_lval_new memory.c:50
```

Key parts:
- **Error type**: heap-buffer-overflow, use-after-free, etc.
- **Stack trace**: Where the bad access happened
- **Memory info**: Where the memory was allocated/freed

### LeakSanitizer (LSAN)

LSAN is part of ASAN and detects memory leaks.

```bash
# Enable leak detection
export ASAN_OPTIONS=detect_leaks=1

# LSAN-specific options
export LSAN_OPTIONS="
  verbosity=1
  log_threads=1
  print_suppressions=1
"
```

### Suppressions

Create `lsan_suppressions.txt` (already exists in project):
```
# Suppress known issues
leak:third_party_lib
leak:intentional_leak_func
```

Use with:
```bash
LSAN_OPTIONS=suppressions=lsan_suppressions.txt build-asan/valk
```

## Valgrind (Linux)

Valgrind provides more detailed analysis but with ~20x slowdown.

### Memcheck (Memory Errors)

```bash
# Basic memcheck
valgrind --leak-check=full build/valk src/prelude.valk

# Detailed leak report
valgrind --leak-check=full --show-leak-kinds=all --track-origins=yes \
  build/valk src/prelude.valk

# With GDB integration
valgrind --vgdb=yes --vgdb-error=0 build/valk src/prelude.valk
# In another terminal:
gdb build/valk
(gdb) target remote | vgdb
```

### Valgrind Options

```bash
valgrind \
  --leak-check=full \
  --show-leak-kinds=all \
  --track-origins=yes \
  --verbose \
  --log-file=valgrind.log \
  --suppressions=valgrind.supp \
  build/valk src/prelude.valk
```

### Interpreting Valgrind Output

```
==12345== Invalid read of size 4
==12345==    at 0x...: valk_lval_copy (parser.c:150)
==12345==    by 0x...: valk_lval_eval (parser.c:300)
==12345==  Address 0x... is 4 bytes after a block of size 100 alloc'd
==12345==    at 0x...: malloc (vg_replace_malloc.c:...)
==12345==    by 0x...: valk_lval_new (memory.c:50)
```

### Memory Leak Report

```
==12345== LEAK SUMMARY:
==12345==    definitely lost: 1,024 bytes in 10 blocks
==12345==    indirectly lost: 2,048 bytes in 20 blocks
==12345==      possibly lost: 512 bytes in 5 blocks
==12345==    still reachable: 4,096 bytes in 40 blocks
==12345==         suppressed: 0 bytes in 0 blocks
```

- **definitely lost**: Memory with no pointers to it (real leak)
- **indirectly lost**: Memory reachable only from definitely lost
- **possibly lost**: Memory with interior pointers only
- **still reachable**: Memory with pointers but not freed (often OK)

### Valgrind Suppressions

Create `valgrind.supp`:
```
{
   dlopen_leak
   Memcheck:Leak
   match-leak-kinds: reachable
   fun:malloc
   ...
   fun:dlopen
}
```

## macOS-Specific Tools

### Guard Malloc

```bash
# Enable guard malloc (very slow but catches overflows)
DYLD_INSERT_LIBRARIES=/usr/lib/libgmalloc.dylib build/valk src/prelude.valk

# With MallocGuardEdges
export MallocGuardEdges=1
export MallocScribble=1
export MallocCheckHeapStart=1000
export MallocCheckHeapEach=100
build/valk src/prelude.valk
```

### malloc Debug Options

```bash
export MallocStackLogging=1
export MallocStackLoggingNoCompact=1
export MallocScribble=1  # Fill freed memory with 0x55
export MallocPreScribble=1  # Fill allocated memory with 0xAA

build/valk src/prelude.valk

# View allocations
leaks --atExit -- build/valk src/prelude.valk
malloc_history <pid> -allBySize
```

## Debugging Patterns

### Finding Buffer Overflows

1. Run with ASAN
2. Look for "heap-buffer-overflow" or "stack-buffer-overflow"
3. Check the allocation size vs access offset
4. Fix the bounds check or allocation size

### Finding Use-After-Free

1. Run with ASAN
2. Look for "heap-use-after-free"
3. Note the allocation and free stack traces
4. Trace object lifetime to find premature free

### Finding Memory Leaks

1. Run with ASAN (detect_leaks=1) or Valgrind
2. Look at "definitely lost" first
3. Check allocation stack traces
4. Add missing free() or destructor calls

### Finding Uninitialized Memory

```bash
# Valgrind catches this well
valgrind --track-origins=yes build/valk src/prelude.valk

# Or use MSAN (Memory Sanitizer)
cmake -DMSAN=1 -S . -B build-msan
```

## Project-Specific Commands

```bash
# Run all ASAN tests (per AGENTS.md, redirect output!)
ASAN_OPTIONS="log_path=build/asan.log" make test-c-asan
grep -c "ERROR: AddressSanitizer" build/asan.log 2>/dev/null || echo "0 errors"

# Run specific test with ASAN
ASAN_OPTIONS=detect_leaks=1:halt_on_error=1 build-asan/test_memory

# Find uncovered branches (for improving test coverage)
python3 scripts/find-uncovered-branches.py src/memory.c
```

## Combining with Debugger

### ASAN + GDB

```bash
ASAN_OPTIONS=abort_on_error=1:disable_coredump=0 gdb --args build-asan/valk src/prelude.valk
(gdb) run
# ASAN will abort on error, dropping you into GDB
(gdb) bt
```

### Valgrind + GDB

```bash
# Terminal 1
valgrind --vgdb=yes --vgdb-error=0 build/valk src/prelude.valk

# Terminal 2
gdb build/valk
(gdb) target remote | vgdb
(gdb) continue
```

## Tips

1. Always run CI with ASAN enabled
2. Use ASAN for quick checks, Valgrind for deep analysis
3. Fix "definitely lost" leaks first
4. Enable `detect_stack_use_after_return` for stack issues
5. Use `track-origins=yes` with Valgrind to find uninitialized memory sources
6. Keep suppressions minimal - fix the real issues
7. Memory errors often cascade - fix the first one, rerun
