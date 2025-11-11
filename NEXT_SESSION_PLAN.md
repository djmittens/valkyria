# Next Session Plan: Memory Management & Immutability

## Session Goals
1. Understand and document arena memory usage patterns
2. Implement immutability enforcement with freeze flags
3. Begin garbage collection implementation
4. Fix memory-constrained workarounds

## Current State Summary

### What's Working
- ✅ All 5 mutation bugs fixed (tail, head, cons, join, init)
- ✅ Printf and time-us builtins implemented
- ✅ Test framework with emoji output and timing
- ✅ All test files passing (test_prelude.valk, test_simple.valk, test_namespace.valk, test_varargs.valk)

### Key Issue Discovered
- **64MB global arena without GC** causes OOM during recursive operations
- Located in `repl.c:17-19`: "Global arena needs GC or better reclamation"
- Even 60-80 levels of recursion exhausts memory
- Forces non-idiomatic workarounds (e.g., dot padding in test.valk)

---

## Phase 1: Arena Memory Investigation
**Goal**: Profile and document memory usage patterns

### Tasks
- [ ] Create memory profiling test file (`test/test_arena_usage.valk`)
  - Test recursive functions at different depths
  - Test operations that create intermediate values (map, filter, join)
  - Measure arena usage with different workloads

- [ ] Add arena statistics reporting
  - Add `arena-stats` builtin to report current usage
  - Log arena growth during test execution
  - Identify which operations are most memory-intensive

- [ ] Document findings
  - Create `docs/MEMORY_ANALYSIS.md` with results
  - List operations that need optimization
  - Propose interim solutions (arena reset points?)

### Files to examine
- `src/memory.c:378-380` - Arena allocation code
- `src/repl.c:17-26` - Arena initialization (64MB global, 16MB scratch)
- `src/parser.c` - Where most allocations happen during evaluation

---

## Phase 2: Immutability Enforcement
**Goal**: Prevent mutation of frozen values

### Tasks
- [ ] Add freeze bit to value flags
  ```c
  // In parser.h
  #define LVAL_FLAG_FROZEN (1 << 8)  // Add to flags field
  ```

- [ ] Implement freeze/thaw checking
  - Modify mutation operations to check freeze flag
  - Add error reporting for frozen value mutations
  - Ensure child values inherit freeze status appropriately

- [ ] Add freeze/thaw builtins
  ```lisp
  (freeze val)   ; Returns frozen copy
  (frozen? val)  ; Check if frozen
  (thaw val)     ; Returns mutable copy (deep copy)
  ```

- [ ] Update existing operations
  - `valk_builtin_head` - check if list is frozen
  - `valk_builtin_tail` - check if list is frozen
  - `valk_builtin_init` - check if list is frozen
  - `valk_builtin_cons` - check if list is frozen
  - `valk_builtin_join` - check if lists are frozen

- [ ] Create immutability tests
  - `test/test_immutability.valk`
  - Test freeze/thaw operations
  - Verify mutation prevention
  - Test deep vs shallow freezing

### Files to modify
- `src/parser.h` - Add freeze flag definition
- `src/parser.c:1271-1320` - Update list operations
- `src/parser.c:1990+` - Add freeze/thaw builtins

---

## Phase 3: Garbage Collection Implementation
**Goal**: Implement mark-sweep GC for arena allocator

### Design Decisions
- Mark-sweep algorithm (simpler than generational for first implementation)
- Triggered when arena usage exceeds threshold (e.g., 80% full)
- Root set: global environment + current evaluation stack

### Tasks
- [ ] Add GC infrastructure
  ```c
  // In memory.h
  typedef struct valk_gc_stats {
    size_t collections;
    size_t bytes_freed;
    size_t collection_time_us;
  } valk_gc_stats_t;
  ```

- [ ] Implement marking phase
  - Add mark bit to value flags (`LVAL_FLAG_MARKED`)
  - Traverse from roots (env + stack)
  - Mark all reachable values

- [ ] Implement sweep phase
  - Scan arena for unmarked values
  - Compact live values (or use free list)
  - Reset arena pointer

- [ ] Add GC triggers
  - Check arena usage in `valk_mem_arena_alloc`
  - Trigger collection at threshold
  - Add manual `(gc)` builtin for testing

- [ ] Create GC tests
  - `test/test_gc.c` - C-level GC tests
  - `test/test_gc.valk` - Lisp-level GC tests
  - Verify no live values are collected
  - Test collection triggers

### Files to modify
- `src/memory.h` - GC data structures
- `src/memory.c` - GC implementation
- `src/parser.c` - Root marking, GC builtin

---

## Phase 4: Remove Memory Workarounds
**Goal**: Clean up code that works around arena limitations

### Tasks
- [ ] Rewrite test.valk dot padding
  - Use simple recursion now that GC is available
  - Remove complex nested-if workaround
  - Achieve perfect 80-character alignment

- [ ] Enable deeper recursion tests
  - Uncomment disabled deep recursion test in test_prelude.valk
  - Add factorial/fibonacci tests with large inputs
  - Verify no OOM with GC enabled

- [ ] Profile improvements
  - Compare memory usage before/after GC
  - Measure performance impact
  - Document in `docs/GC_PERFORMANCE.md`

---

## Testing Plan

### Test Execution Order
1. Run existing tests to ensure no regression
2. Add memory profiling tests
3. Add immutability tests
4. Add GC tests
5. Re-enable deep recursion tests
6. Full test suite validation

### Critical Test Files
```bash
# Core functionality
make test

# Memory profiling (new)
build/valk test/test_arena_usage.valk

# Immutability (new)
build/valk test/test_immutability.valk

# GC verification (new)
build/test_gc
build/valk test/test_gc.valk

# Deep recursion (currently disabled)
build/valk test/test_deep_recursion.valk
```

---

## Success Criteria
- [ ] No OOM errors during normal recursive operations (up to 1000 levels)
- [ ] Immutability enforcement prevents all mutation bugs
- [ ] GC successfully reclaims at least 50% of garbage in typical workloads
- [ ] All existing tests still pass
- [ ] Test output alignment is perfect (exactly 80 characters)
- [ ] Documentation complete for memory management and GC

---

## Notes for Implementation

### Memory Layout Reference
```
Global Arena:  64 MiB (accumulates garbage)
Scratch Arena: 16 MiB (reset between REPL expressions)
Problem: Scripts use global arena, never reset
```

### Key Code Locations
- Arena OOM: `memory.c:380` - "Arena OOM" error
- Arena init: `repl.c:19-26` - Size definitions
- TODO comment: `repl.c:17-18` - Existing GC TODO

### Potential Challenges
1. **Root identification**: Need to track all live references
2. **Cycle handling**: Ensure circular references don't prevent collection
3. **Performance**: GC pause times should be minimal
4. **Safety**: Must not collect values still in use

---

## Time Estimate
- Phase 1 (Investigation): 1-2 hours
- Phase 2 (Immutability): 2-3 hours
- Phase 3 (GC Implementation): 4-6 hours
- Phase 4 (Cleanup): 1 hour
- **Total: 8-12 hours**

---

## Questions to Resolve
1. Should GC be incremental or stop-the-world?
2. Should we add reference counting as optimization?
3. Do we need weak references?
4. Should frozen values be allocated differently?
5. How to handle GC during async operations?

---

## References
- [repl.c:17-18] - Original GC TODO
- [memory.c:378-403] - Arena allocator implementation
- [parser.c:376-402] - Value copying (major allocation site)
- [test.valk:28-50] - Current dot padding workaround