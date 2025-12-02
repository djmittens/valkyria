# Layer 2: Memory

**Status**: Allocators and GC complete, escape analysis partial

**Timeline**: ~2-5 weeks

---

## Current State

### Complete ✓
- [x] Arena allocator (636 LOC) - bump allocation
- [x] Scratch arena (REPL only) - resets after each expression
- [x] Slab allocator - fixed-size blocks with lock-free freelist (Treiber stack)
- [x] GC Heap (643 LOC) - malloc-based with mark & sweep
- [x] Stop-the-world GC - marks reachable, sweeps unreachable
- [x] Escape analysis - marking works (3/6 tests passing)

### Remaining Work
- [ ] Complete escape analysis (S - 1-3 days) - **PRIORITY**
- [ ] Intern to heap (S - 1-3 days)
- [ ] Generational GC (L - 2-4 weeks) - **OPTIONAL**

---

## Feature 1: Complete Escape Analysis (S - 1-3 days)

**Unlocks**: Stack allocation optimization, fewer GC pauses

**Status**: Currently 3/6 tests passing. Need to handle:
1. Return value promotion (values returned from functions)
2. Closure capture detection
3. Indirect escapes (stored in escaping structures)

### Tasks

- [ ] **2.1: Analyze Current Test Failures** (2-3 hours)
  - File: `test/test_escape.c`
  - Run tests with `ASAN_OPTIONS=detect_leaks=1 build/test_escape`
  - Identify which 3 tests are failing
  - Document expected vs actual behavior
  - **Output**: List of specific failure modes
  - **Test**: Re-run to confirm current state

- [ ] **2.2: Implement Return Value Tracking** (4-6 hours)
  - File: `src/gc.c` (escape analysis section)
  - When value is returned from function, mark as escaping
  - **Algorithm**: Walk AST, find `return` statements, mark returned values
  - Handle implicit returns (last expression in function)
  - **Challenge**: Anonymous functions, closures
  - **Test**: `(lambda (x) (cons x x))` - result escapes

- [ ] **2.3: Implement Closure Capture Detection** (4-6 hours)
  - File: `src/gc.c`
  - Values captured by closures must escape (closure outlives function)
  - **Algorithm**: Walk function body, find free variables
  - Mark all captured values as escaping
  - **Test**: `(lambda (x) (lambda () x))` - `x` escapes

- [ ] **2.4: Implement Indirect Escape Analysis** (4-6 hours)
  - File: `src/gc.c`
  - If value is stored in escaping structure, it escapes too
  - **Algorithm**: Transitive closure of escape relation
  - Example: `(cons x y)` escapes → both `x` and `y` escape
  - **Test**: `(let ((p (cons a b))) (foo p))` - if `p` escapes, so do `a` and `b`

- [ ] **2.5: Validate All Escape Tests Pass** (1-2 hours)
  - Run `build/test_escape` and ensure all 6 tests pass
  - Run with leak detection: `ASAN_OPTIONS=detect_leaks=1`
  - No memory leaks, no incorrect promotions
  - **Test**: All escape analysis tests green

- [ ] **2.6: Benchmark Escape Analysis Impact** (2-3 hours)
  - Create benchmark: allocate-heavy workload
  - Measure GC pauses before/after complete escape analysis
  - Expected: Fewer allocations, shorter pauses
  - **Test cases**:
    - Recursive fibonacci (many temp values)
    - List processing (map/filter)
    - Tree construction
  - **Document**: Results in session notes

---

## Feature 2: Intern to Heap (S - 1-3 days)

**Unlocks**: Long-lived values survive scratch arena resets

**Status**: Partial implementation (function exists but not fully integrated)

### Tasks

- [ ] **2.7: Review valk_intern Implementation** (1-2 hours)
  - File: `src/parser.c` or `src/gc.c`
  - Understand current `valk_intern(env, val)` function
  - What does it do? Deep copy to GC heap?
  - Check if it handles all value types correctly
  - **Test**: Call `valk_intern` on scratch value, verify copied to heap

- [ ] **2.8: Auto-Intern Escaping Values** (3-4 hours)
  - Integration point: After escape analysis marks value
  - Before value escapes scope, automatically intern to heap
  - **Algorithm**:
    ```c
    if (valk_value_escapes(val) && val->allocator == ALLOC_SCRATCH) {
      val = valk_intern(heap, val);
    }
    ```
  - **Test**: Scratch value captured by closure is interned

- [ ] **2.9: Intern in REPL** (2-3 hours)
  - REPL results should be interned (survive scratch reset)
  - After evaluating expression, intern result before printing
  - **Location**: `src/repl.c`, main eval loop
  - **Test**: Define function in REPL, call it later (after scratch reset)

- [ ] **2.10: Test Intern Behavior** (2-3 hours)
  - File: `test/test_intern.c` or `test/test_intern.valk`
  - Test: Value interned is deep-copied (not shallow)
  - Test: Original scratch value unchanged
  - Test: Interned value survives GC
  - Test: Circular structures handled (don't infinite loop)
  - **Run**: Add to `make test`

---

## Feature 3: Generational GC (L - 2-4 weeks) **[OPTIONAL]**

**Unlocks**: Better GC performance via generational hypothesis

**Background**: Most objects die young. Separate young/old generations, collect young gen more frequently.

**Dependency**: This is a performance optimization, not required for correctness.

### Tasks

- [ ] **2.11: Design Generational Strategy** (2-3 days)
  - Research: 2-generation vs 3-generation
  - Decide: When to promote young → old?
  - Decide: Write barrier implementation (track old → young pointers)
  - **Research**: V8, JVM, Go GC designs
  - **Document**: Design doc with diagrams

- [ ] **2.12: Implement Young Generation** (3-4 days)
  - File: `src/gc.c`
  - Add young gen heap (small, collected frequently)
  - Allocations go to young gen first
  - **Algorithm**: Copy collection (Cheney's algorithm)
  - **Test**: Allocate in young gen, verify collected

- [ ] **2.13: Implement Write Barrier** (3-4 days)
  - Track old → young pointers (remembered set)
  - Insert write barrier on pointer stores
  - **Challenge**: Performance overhead
  - **Options**: Card marking, sequential store buffer
  - **Test**: Old object points to young object, young collected

- [ ] **2.14: Implement Promotion** (2-3 days)
  - Young objects that survive N collections → promote to old gen
  - **Heuristic**: N = 2 or 3
  - Handle promotion during collection
  - **Test**: Object survives multiple collections, gets promoted

- [ ] **2.15: Tune Collection Heuristics** (3-5 days)
  - When to collect young gen? (heap % full, allocation rate)
  - When to collect old gen? (old gen full, time-based)
  - Benchmark with real workloads
  - **Metrics**: GC pause time, throughput, memory usage
  - **Test**: Workloads from benchmark suite

- [ ] **2.16: Generational GC Tests** (2-3 days)
  - File: `test/test_generational_gc.c`
  - Test: Young gen collected without scanning old gen
  - Test: Write barrier tracks old → young pointers
  - Test: Promotion happens after N collections
  - Test: Full collection (both generations) works
  - **Run**: Add to `make test`

---

## Progress Tracking

### Velocity
- **Week 1**: ___ tasks completed
- **Week 2**: ___ tasks completed

### Current Status
- **Feature**: ___
- **Task**: ___
- **Blocker**: ___

### Notes
- Session notes here

---

## Resources

### Escape Analysis
- "Escape Analysis for Java" paper: https://dl.acm.org/doi/10.1145/320384.320386
- LLVM Escape Analysis: https://llvm.org/docs/AliasAnalysis.html
- JVM Escape Analysis: https://shipilev.net/jvm/anatomy-quarks/18-scalar-replacement/

### Generational GC
- "Garbage Collection" book by Jones & Lins
- V8 GC design: https://v8.dev/blog/trash-talk
- Go GC design: https://go.dev/blog/ismmkeynote
- "The Garbage Collection Handbook": http://gchandbook.org/

### Memory Management
- "Memory Management Reference": https://www.memorymanagement.org/
- Boehm GC (conservative): https://www.hboehm.info/gc/
