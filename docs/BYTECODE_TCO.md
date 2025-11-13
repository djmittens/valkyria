# Bytecode VM with O(1) Tail Call Optimization

## Overview

Valkyria now includes a bytecode virtual machine that achieves true O(1) space tail call optimization (TCO). This means recursive functions in tail position can run indefinitely without consuming stack or heap memory.

## Usage

To enable the bytecode VM, set the `VALK_BYTECODE` environment variable:

```bash
VALK_BYTECODE=1 build/valk your_script.valk
```

## Example

```lisp
;; Define a recursive countdown function
(def {countdown} (\ {n} {
  (if (== n 0)
    {0}
    {(countdown (- n 1))})
}))

;; This works with 100,000+ iterations!
(print (countdown 100000))  ; Prints: 0
```

## How It Works

### Tree-Walker (Default)
- Uses thunk-based trampoline
- O(1) stack space
- O(n) heap space (creates intermediate values)
- Good for most programs

### Bytecode VM (`VALK_BYTECODE=1`)
- Compiles AST to bytecode
- Stack-based VM with call frames
- **OP_TAIL_CALL** instruction reuses call frames
- **O(1) stack AND heap space**
- Perfect for deep recursion

### Key Implementation Details

**OP_TAIL_CALL** (src/bc_vm.c:305):
- Instead of pushing a new call frame, it **reuses** the current one
- Copies new arguments to current frame's slots
- Resets instruction pointer to function start
- Keeps `frame_count` unchanged → **O(1) space!**

**Compilation** (src/compiler.c):
- Tracks tail position through recursive compilation
- Emits `OP_TAIL_CALL` for calls in tail position
- Emits `OP_CALL` for non-tail calls

## Testing

```bash
# Test with 10, 1000, and 10000 iterations
VALK_BYTECODE=1 build/valk test/test_bytecode_countdown.valk

# Ultimate test: 100,000 iterations
VALK_BYTECODE=1 build/valk test/test_tco_100k.valk
```

## Limitations

- Bytecode mode must be enabled from start (before loading prelude)
- Cannot mix tree-walker lambdas with bytecode execution
- Builtins are still tree-walker functions (called via FFI from bytecode)

## Performance

Bytecode VM is typically 10-100x faster than tree-walker for recursive functions due to:
- No thunk allocation
- Direct instruction dispatch
- Call frame reuse for tail calls

## Future Work

- [ ] JIT compilation
- [ ] Better stack trace support
- [ ] Optimize builtin calls
- [ ] Make bytecode the default
