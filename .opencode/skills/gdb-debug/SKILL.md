---
name: gdb-debug
description: Interactive debugging with GDB on Linux - breakpoints, watchpoints, memory inspection, and reverse debugging for C programs
license: MIT
metadata:
  platform: linux
  category: debugging
---

# GDB Debugging for Valkyria

Use GDB for interactive debugging of the Valkyria interpreter on Linux.

## Quick Start

```bash
# Basic debug session
gdb --args build/valk src/prelude.valk test/test_prelude.valk

# Or use the Makefile target (Linux)
make debug
```

## Essential Commands

### Running and Breakpoints

```gdb
# Set breakpoint at function
(gdb) break valk_lval_eval
(gdb) b parser.c:150

# Conditional breakpoint
(gdb) break valk_lval_eval if lval->type == LVAL_ERR

# Run with arguments
(gdb) run src/prelude.valk test/test_prelude.valk

# Continue, step, next
(gdb) c          # continue
(gdb) s          # step into
(gdb) n          # step over
(gdb) fin        # finish current function
(gdb) until 200  # run until line 200
```

### Inspecting State

```gdb
# Print variables
(gdb) p lval
(gdb) p *lval
(gdb) p lval->cell[0]

# Print with format
(gdb) p/x ptr       # hex
(gdb) p/t flags     # binary
(gdb) p/a address   # address

# Examine memory
(gdb) x/10xg ptr    # 10 giant words (8 bytes) in hex
(gdb) x/20i $pc     # 20 instructions at PC
(gdb) x/s str       # string

# Print array
(gdb) p *array@10   # print 10 elements

# Pretty print struct
(gdb) set print pretty on
(gdb) p *lval
```

### Watchpoints (Data Breakpoints)

```gdb
# Break when variable changes
(gdb) watch lval->count

# Break when expression is true
(gdb) watch -l *(int*)0x12345678

# Hardware watchpoint (faster)
(gdb) watch lval->type
(gdb) info watchpoints
```

### Backtrace and Frames

```gdb
# Full backtrace
(gdb) bt
(gdb) bt full      # with local variables

# Navigate frames
(gdb) frame 3      # select frame 3
(gdb) up           # go up one frame
(gdb) down         # go down one frame
(gdb) info frame   # current frame details
(gdb) info locals  # local variables
(gdb) info args    # function arguments
```

### Threads

```gdb
# List threads
(gdb) info threads

# Switch to thread
(gdb) thread 2

# Apply command to all threads
(gdb) thread apply all bt

# Break in specific thread
(gdb) break func thread 2
```

## Advanced Techniques

### Reverse Debugging

```gdb
# Enable recording (must be at program start or after a checkpoint)
(gdb) record

# Step backwards
(gdb) reverse-stepi
(gdb) reverse-continue
(gdb) reverse-next

# Set reverse breakpoint
(gdb) break some_func
(gdb) reverse-continue
```

### Catchpoints

```gdb
# Catch signals
(gdb) catch signal SIGSEGV

# Catch syscalls
(gdb) catch syscall write

# Catch C++ exceptions
(gdb) catch throw
(gdb) catch catch
```

### Memory Debugging

```gdb
# Find memory leaks pattern
(gdb) break malloc
(gdb) commands
> silent
> bt 2
> continue
> end

# Check heap (with glibc)
(gdb) call malloc_stats()
(gdb) call malloc_info(0, stdout)

# Find address of symbol
(gdb) info address valk_lval_new
(gdb) info symbol 0x12345678
```

### Scripting GDB

```gdb
# Define custom command
(gdb) define print_lval
> set $l = $arg0
> printf "type=%d count=%d\n", $l->type, $l->count
> end

# Run commands on breakpoint
(gdb) break valk_gc_collect
(gdb) commands
> printf "GC triggered, heap_size=%zu\n", gc->heap_size
> continue
> end
```

## Valkyria-Specific Debugging

### Inspect lval Objects

```gdb
# Custom pretty printer for lval
define print_lval_type
  if $arg0->type == 0
    printf "LVAL_NUM"
  end
  if $arg0->type == 1
    printf "LVAL_ERR"
  end
  # ... etc
end

# Print lval recursively
define print_lval_tree
  set $l = $arg0
  set $i = 0
  printf "lval@%p type=%d count=%d\n", $l, $l->type, $l->count
  while $i < $l->count
    printf "  [%d]: ", $i
    print_lval_tree $l->cell[$i]
    set $i = $i + 1
  end
end
```

### Debug GC Issues

```gdb
# Break on GC
(gdb) break valk_gc_collect
(gdb) break valk_gc_mark

# Watch root set
(gdb) watch gc->roots[0]

# Print GC stats
(gdb) p *gc
```

### Debug Parser Issues

```gdb
# Break on parse errors
(gdb) break valk_lval_err

# Trace tokenization
(gdb) break parser.c:tokenize
```

## GDB Init File

Create `~/.gdbinit` for persistent settings:

```gdb
set history save on
set history size 10000
set print pretty on
set print array on
set print array-indexes on
set pagination off

# Valkyria-specific
define pv
  p *(valk_lval_t*)$arg0
end

# Catch common signals
handle SIGPIPE nostop noprint
```

## Running with ASAN

```bash
# Build with ASAN
make build-asan

# GDB needs special handling for ASAN
ASAN_OPTIONS=abort_on_error=1:disable_coredump=0 gdb --args build-asan/valk src/prelude.valk
```

## Debugging Core Dumps

```bash
# Enable core dumps
ulimit -c unlimited

# Generate core on crash
# ... program crashes ...

# Load core dump
gdb build/valk core

# Or specify core file
gdb build/valk -c /var/crash/core.12345
```

## Tips

1. Use `tui enable` for a curses-based interface
2. Use `layout src` to see source code
3. Press Ctrl+X+A to toggle TUI mode
4. Use `info registers` to see CPU registers
5. Use `disassemble` to see assembly
6. Use `set disassembly-flavor intel` for Intel syntax
