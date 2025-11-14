# Phase 2: Bytecode Compiler

**Duration**: 3 weeks
**Status**: Not started (50% existing work)
**Goal**: 10-100x performance improvement

## Current State

- `src/bytecode.h/c`: Basic infrastructure exists
- `test/test_bytecode.c`: Some tests written
- VM interpreter partially implemented

## Implementation Plan

### Week 9-10: Complete Compiler

**Files to modify**:
- `src/bytecode.c`: Finish bytecode generation
- `src/vm.c`: Complete bytecode interpreter

**Opcodes needed**:
```c
OP_CALL_CONT    // Call continuation
OP_CAPTURE_CONT // Capture continuation
OP_TAIL_CALL    // Optimized tail call
OP_CLOSURE      // Create closure
```

**Compilation phases**:
1. Parse → AST
2. AST → Bytecode
3. Bytecode → Optimized bytecode
4. Execute in VM

**Deliverable**: All Lisp compiles to bytecode

### Week 11: Optimization

**Optimizations**:
- Constant folding
- Dead code elimination
- Tail call optimization
- Inline caching
- JIT hooks preparation

**Performance targets**:
- 10x faster for compute-heavy code
- 100x faster for tight loops
- Memory usage comparable to interpreter

**Deliverable**: Optimized bytecode execution

## Success Criteria

- [ ] All code runs as bytecode
- [ ] 10-100x performance improvement
- [ ] No functionality regression
- [ ] Memory usage acceptable
- [ ] Debugger still works

## Benchmarks

```lisp
; Before (interpreter): ~1000ms
; After (bytecode): ~10ms
(def {fib} (lambda {n}
  (if (<= n 1)
      n
      (+ (fib (- n 1)) (fib (- n 2))))))

(time (fib 30))
```

## Next Phase

[Phase 3: Production Ready](phase3_production.md)