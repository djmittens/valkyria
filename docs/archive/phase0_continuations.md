# Phase 0: Shift/Reset Continuations

**Duration**: 6 weeks
**Status**: Starting
**Goal**: Replace ARC-based futures with delimited continuations

## Problem

Current async system has major issues:
- ARCs create overhead with atomic operations
- Callbacks can't properly bind Lisp closures
- Reference cycles never get collected
- Complex lifetime management

## Solution

Implement shift/reset delimited continuations:
- Continuations are just GC'd values (no reference counting)
- Natural composition like regular functions
- Direct lexical scope capture
- "Pause and resume" mental model

## Implementation Plan

### Week 1-2: Core Infrastructure

**Files to modify**:
- `src/parser.h`: Add `LVAL_CONT` and `LVAL_PROMPT` types
- `src/vm.c`: Implement continuation capture/resume
- `src/parser.c`: Add shift/reset/call-cc builtins

**Key functions**:
```c
valk_vm_capture_continuation()  // Capture stack to delimiter
valk_vm_resume_continuation()   // Resume with value
valk_builtin_shift()            // (shift k expr)
valk_builtin_reset()            // (reset expr)
```

**Deliverable**: Basic shift/reset working in REPL

### Week 3-4: Async Integration

**Files to modify**:
- `src/aio_uv.c`: Replace futures with continuations
- `src/prelude.valk`: Add await/async helpers

**Key changes**:
- Remove `valk_promise` and `valk_future`
- Callbacks resume continuations instead
- Add timeout and racing support

**Deliverable**: File I/O using continuations

### Week 5: Remove ARCs

**Files to modify**:
- `src/concurrency.c`: Remove ARC infrastructure
- `src/concurrency.h`: Remove ARC macros

**Remove**:
- `valk_arc_box`
- `valk_arc_retain/release`
- All atomic refcounting

**Deliverable**: No ARCs in codebase

### Week 6: Testing & Polish

**New tests**:
- `test/test_continuations.c`: Unit tests
- `test/test_async_cont.valk`: Integration tests

**Documentation**:
- User guide for shift/reset
- Migration examples
- Performance benchmarks

**Deliverable**: Production-ready continuation system

## Success Criteria

- [ ] All existing tests pass
- [ ] 20% reduction in memory usage
- [ ] 30% reduction in code complexity
- [ ] Zero memory leaks
- [ ] Equal or better performance

## Example Code

Before (with ARCs):
```c
valk_future* fut = async_read_file(path);
valk_future_and_then(fut, callback);
valk_arc_release(fut);
```

After (with continuations):
```lisp
(reset
  (let ((data (await (read-file path))))
    (process data)))
```

## Next Phase

[Phase 1: Complete Networking](phase1_networking.md)