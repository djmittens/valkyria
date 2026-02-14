---
name: lldb-debug
description: Interactive debugging with LLDB on macOS - breakpoints, watchpoints, memory inspection, and Python scripting for C programs
license: MIT
metadata:
  platform: macos
  category: debugging
---

# LLDB Debugging for Valkyria

Use LLDB for interactive debugging of the Valkyria interpreter on macOS.

## Quick Start

```bash
# Basic debug session
lldb -- build/valk src/prelude.valk test/test_prelude.valk

# Or use the Makefile target (macOS)
make debug

# Attach to running process
lldb -p $(pgrep valk)
```

## Essential Commands

### Running and Breakpoints

```lldb
# Set breakpoint at function
(lldb) breakpoint set -n valk_lval_eval
(lldb) b valk_lval_eval
(lldb) b parser.c:150

# Conditional breakpoint
(lldb) breakpoint set -n valk_lval_eval -c 'lval->type == 3'

# Breakpoint with action
(lldb) breakpoint set -n valk_gc_collect
(lldb) breakpoint command add 1
> p gc->heap_size
> continue
> DONE

# Run with arguments
(lldb) run src/prelude.valk test/test_prelude.valk
(lldb) r

# Continue, step, next
(lldb) c          # continue
(lldb) s          # step into
(lldb) n          # step over
(lldb) finish     # finish current function
(lldb) thread until 200  # run until line 200
```

### Inspecting State

```lldb
# Print variables
(lldb) p lval
(lldb) p *lval
(lldb) p lval->cell[0]

# Print with format
(lldb) p/x ptr       # hex
(lldb) p/t flags     # binary

# Expression evaluation
(lldb) expr lval->count
(lldb) expr -f hex -- ptr

# Frame variables
(lldb) frame variable
(lldb) fr v
(lldb) fr v -r      # recursive

# Memory read
(lldb) memory read ptr
(lldb) x/10xg ptr    # 10 giant words in hex
(lldb) x/20i $pc     # 20 instructions
(lldb) memory read -f s ptr  # as string
```

### Watchpoints

```lldb
# Watch variable
(lldb) watchpoint set variable lval->count
(lldb) w s v lval->count

# Watch expression
(lldb) watchpoint set expression -- &lval->type

# Watch memory address
(lldb) watchpoint set expression -w write -- 0x12345678

# List watchpoints
(lldb) watchpoint list
```

### Backtrace and Frames

```lldb
# Full backtrace
(lldb) bt
(lldb) bt all       # all threads

# Navigate frames
(lldb) frame select 3
(lldb) up
(lldb) down
(lldb) frame info
(lldb) frame variable  # locals and args
```

### Threads

```lldb
# List threads
(lldb) thread list

# Switch thread
(lldb) thread select 2

# Backtrace all threads
(lldb) thread backtrace all

# Thread-specific breakpoint
(lldb) breakpoint set -n func -t 2
```

## Advanced Techniques

### Type Lookup and Formatting

```lldb
# Show type info
(lldb) type lookup valk_lval_t
(lldb) image lookup -t valk_lval_t

# Custom type summary
(lldb) type summary add valk_lval_t --summary-string "type=${var.type} count=${var.count}"

# Custom formatter (Python)
(lldb) type summary add -x "^valk_lval_t$" -F my_formatters.lval_summary
```

### Process Info

```lldb
# Memory regions
(lldb) memory region --all

# Loaded libraries
(lldb) image list

# Find symbol
(lldb) image lookup -n valk_lval_eval
(lldb) image lookup -a 0x12345678

# Disassemble
(lldb) disassemble -n valk_lval_eval
(lldb) di -f          # current function
(lldb) di -s $pc -c 20  # 20 instructions from PC
```

### Signals and Exceptions

```lldb
# Handle signals
(lldb) process handle SIGPIPE -n true -p true -s false

# Break on signal
(lldb) process handle SIGSEGV -s true

# Break on C++ exceptions
(lldb) breakpoint set -E c++ -O true  # on throw
```

### Python Scripting

```lldb
# Run Python
(lldb) script print(lldb.frame.FindVariable("lval"))

# Define Python command
(lldb) command script add -f my_commands.print_lval pl
```

Create `~/.lldb/my_commands.py`:
```python
import lldb

def print_lval(debugger, command, result, internal_dict):
    target = debugger.GetSelectedTarget()
    process = target.GetProcess()
    thread = process.GetSelectedThread()
    frame = thread.GetSelectedFrame()
    
    lval = frame.FindVariable(command)
    if lval.IsValid():
        print(f"type: {lval.GetChildMemberWithName('type').GetValue()}")
        print(f"count: {lval.GetChildMemberWithName('count').GetValue()}")
```

## Valkyria-Specific Debugging

### Custom lval Formatter

Add to `~/.lldbinit`:
```lldb
type summary add valk_lval_t -F valkyria_formatters.lval_summary
```

Create `~/.lldb/valkyria_formatters.py`:
```python
import lldb

LVAL_TYPES = {
    0: "NUM", 1: "ERR", 2: "SYM", 3: "STR",
    4: "FUN", 5: "SEXPR", 6: "QEXPR"
}

def lval_summary(valobj, internal_dict):
    type_val = valobj.GetChildMemberWithName('type').GetValueAsUnsigned()
    count = valobj.GetChildMemberWithName('count').GetValueAsUnsigned()
    type_name = LVAL_TYPES.get(type_val, f"UNKNOWN({type_val})")
    return f"[{type_name}] count={count}"
```

### Debug GC

```lldb
# Set breakpoints for GC debugging
(lldb) b valk_gc_collect
(lldb) b valk_gc_mark
(lldb) b valk_gc_sweep

# Watch heap size
(lldb) watchpoint set variable gc->heap_size
```

### Debug Parser

```lldb
# Break on parse entry
(lldb) b valk_read

# Break on specific error
(lldb) b valk_lval_err
(lldb) breakpoint command add
> bt 5
> continue
> DONE
```

## LLDB Init File

Create `~/.lldbinit`:
```lldb
settings set target.load-cwd-lldbinit true
settings set auto-confirm true
settings set target.x86-disassembly-flavor intel

# Aliases
command alias bpl breakpoint list
command alias bpc breakpoint clear
command alias bpd breakpoint delete

# Handle SIGPIPE silently
process handle SIGPIPE -n true -p true -s false

# Load custom formatters
command script import ~/.lldb/valkyria_formatters.py
```

## Running with ASAN

```bash
# Build with ASAN
make build-asan

# LLDB with ASAN (macOS handles this better than Linux)
lldb -- build-asan/valk src/prelude.valk

# Set ASAN options if needed
(lldb) settings set target.env-vars ASAN_OPTIONS=abort_on_error=1
(lldb) run
```

## Debugging with dSYM

```bash
# Ensure dSYM is generated (Makefile does this automatically)
dsymutil build/valk

# Verify symbols loaded
(lldb) image list build/valk
```

## GUI Mode

```bash
# Launch with GUI (if available)
lldb --gui -- build/valk src/prelude.valk

# Or in session
(lldb) gui
```

## Tips

1. Use `apropos <keyword>` to find commands
2. Use `help <command>` for detailed help
3. Tab completion works for most things
4. Use `--` to separate lldb args from program args
5. Use `script` to drop into Python REPL
6. Use `target create` to load without running
7. Use `register read` to see CPU registers
8. Use `register read -a` for all registers including SIMD
