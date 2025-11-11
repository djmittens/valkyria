# Immutable Values + Heap GC + Zero-Copy Implementation Plan

## Core Principle
**Values are immutable after construction. No mutation = no aliasing bugs = no deep copies needed.**

---

## Phase 1: Analyze Current Mutation Points

### Goals
- Find every place where we mutate lval structs
- Categorize mutations as: construction, illegal mutation, or necessary mutation
- Document the mutation surface area

### Tasks
- [ ] 1.1. Search for all `lval->expr.cell[i] = ` assignments
- [ ] 1.2. Search for all `lval->expr.count` modifications
- [ ] 1.3. Search for all `lval->str` reassignments
- [ ] 1.4. Find all calls to `valk_lval_pop`, `valk_lval_add`
- [ ] 1.5. Document each mutation site with category in `docs/MUTATION_AUDIT.md`

### Test Plan
**Validation Method**: Code audit + documentation
- **Success Criteria**:
  - [ ] Complete list of all mutation sites in `MUTATION_AUDIT.md`
  - [ ] Each site categorized as: CONSTRUCTION, ILLEGAL, or NECESSARY
  - [ ] Identified at least 3 illegal mutation bugs
- **How to Verify**:
  ```bash
  # Check documentation exists and is complete
  cat docs/MUTATION_AUDIT.md
  # Should show categorized list of all mutation sites
  ```

### Expected Findings
- **Construction mutations**: Inside `valk_lval_add`, during parsing
- **Illegal mutations**: `tail`, `head`, `join` might be reusing cells
- **Necessary mutations**: Global env updates via `def`, `=`

---

## Phase 2: Add Immutability Enforcement

### Goals
- Add runtime checks that prevent mutation after construction
- Make violations crash loudly during development
- Provide clear construction/finalization boundaries

### Tasks

#### 2.1. Add Immutability Infrastructure
- [ ] Add `LVAL_FLAG_FROZEN` bit to `parser.h`
- [ ] Implement `valk_lval_freeze(lval)` - recursively freezes value tree
- [ ] Implement `valk_lval_assert_mutable(lval)` - crashes if frozen
- [ ] Add `VALK_ENABLE_FREEZE_CHECKS` compile flag

#### 2.2. Protect Mutation Operations
- [ ] Add freeze check to `valk_lval_add`
- [ ] Add freeze check to `valk_lval_pop`
- [ ] Add freeze checks to all identified `->expr.cell[i] = ` sites
- [ ] Add freeze checks to all identified `->str = ` sites

#### 2.3. Freeze at Boundary Points
- [ ] Freeze values returned from `valk_lval_eval`
- [ ] Freeze values after parsing completes (`valk_lval_read`)
- [ ] Do NOT freeze during construction (while building in `valk_lval_add`)

#### 2.4. Special Case: Environment Mutation
- [ ] Allow global env to remain mutable
- [ ] Freeze local envs after function evaluation
- [ ] Add `valk_lenv_freeze` for local environments

### Test Plan
**Validation Method**: Unit tests + assertions

#### Test 2.1: Freeze Infrastructure Works
```c
void test_freeze_basic() {
    valk_lval_t* v = valk_lval_qexpr_empty();
    ASSERT_FALSE(LVAL_IS_FROZEN(v));

    valk_lval_freeze(v);
    ASSERT_TRUE(LVAL_IS_FROZEN(v));
}
```
- [ ] Test runs and passes
- [ ] `LVAL_IS_FROZEN` macro works correctly

#### Test 2.2: Mutation After Freeze Crashes
```c
void test_mutation_after_freeze_crashes() {
    valk_lval_t* v = valk_lval_qexpr_empty();
    valk_lval_add(v, valk_lval_num(1));
    valk_lval_freeze(v);

    // This should trigger assertion and crash
    #ifdef VALK_ENABLE_FREEZE_CHECKS
    EXPECT_DEATH(valk_lval_add(v, valk_lval_num(2)));
    #endif
}
```
- [ ] Test compiles with `VALK_ENABLE_FREEZE_CHECKS`
- [ ] Attempting to mutate frozen value triggers assertion
- [ ] Error message is clear: "Attempted to mutate frozen value"

#### Test 2.3: Construction Still Works
```c
void test_construction_still_works() {
    valk_lval_t* v = valk_lval_qexpr_empty();
    valk_lval_add(v, valk_lval_num(1));
    valk_lval_add(v, valk_lval_num(2));
    valk_lval_freeze(v);

    ASSERT_EQ(v->expr.count, 2);
    ASSERT_EQ(v->expr.cell[0]->num, 1);
}
```
- [ ] Can construct values normally before freezing
- [ ] Freezing doesn't corrupt data

#### Test 2.4: Eval Returns Frozen Values
```c
void test_eval_returns_frozen() {
    valk_lenv_t* env = valk_lenv_empty();
    valk_lval_t* result = valk_eval(env, "{1 2 3}");

    ASSERT_TRUE(LVAL_IS_FROZEN(result));
    EXPECT_DEATH(valk_lval_add(result, valk_lval_num(4)));
}
```
- [ ] All eval results are frozen
- [ ] Cannot mutate eval results

**Success Criteria**:
- [ ] All 4 tests pass
- [ ] Existing C test suite still passes
- [ ] Any mutation bugs found are documented

---

## Phase 3: Fix Mutation Bugs

### Goals
- Fix operations that incorrectly mutate shared values
- Ensure `tail`, `head`, `join` create new values instead of mutating
- Make all illegal mutations into legal construction

### Tasks

#### 3.1. Fix `tail` - Should Create New List
- [ ] Modify `valk_builtin_tail` to create new QEXPR
- [ ] Copy references (not deep copy) from original list
- [ ] Freeze result before returning

#### 3.2. Fix `head` - Should Create New List
- [ ] Modify `valk_builtin_head` to create new QEXPR
- [ ] Copy first element reference
- [ ] Freeze result before returning

#### 3.3. Fix `join` - Should Create New List
- [ ] Modify `valk_lval_join` to create new QEXPR
- [ ] Copy references from both input lists
- [ ] Do NOT mutate input `x` parameter
- [ ] Freeze result before returning

#### 3.4. Verify Other Builtins
- [ ] Audit `init`, `cons`, `len` for mutations
- [ ] Fix any that mutate inputs
- [ ] Ensure all return frozen values

### Test Plan
**Validation Method**: Regression tests + new tests

#### Test 3.1: Tail Creates New List
```c
void test_tail_creates_new_list() {
    valk_lenv_t* env = valk_lenv_empty();
    valk_lenv_builtins(env);

    valk_lval_t* original = valk_eval(env, "{1 2 3 4}");
    valk_lval_t* tail_result = valk_eval(env, "(tail {1 2 3 4})");

    // Tail should be {2 3 4}
    ASSERT_EQ(tail_result->expr.count, 3);
    ASSERT_EQ(tail_result->expr.cell[0]->num, 2);

    // Original should be unchanged
    ASSERT_EQ(original->expr.count, 4);

    // Results should be frozen
    ASSERT_TRUE(LVAL_IS_FROZEN(tail_result));
}
```
- [ ] Test passes
- [ ] Tail doesn't affect original list

#### Test 3.2: Head Creates New List
```c
void test_head_creates_new_list() {
    valk_lval_t* result = valk_eval(env, "(head {1 2 3})");

    ASSERT_EQ(result->expr.count, 1);
    ASSERT_EQ(result->expr.cell[0]->num, 1);
    ASSERT_TRUE(LVAL_IS_FROZEN(result));
}
```
- [ ] Test passes
- [ ] Head returns new list with first element

#### Test 3.3: Join Doesn't Mutate Inputs
```c
void test_join_doesnt_mutate() {
    valk_lval_t* list1 = valk_eval(env, "{1 2}");
    valk_lval_t* list2 = valk_eval(env, "{3 4}");

    size_t count1_before = list1->expr.count;
    size_t count2_before = list2->expr.count;

    valk_lval_t* joined = valk_eval(env, "(join {1 2} {3 4})");

    // Joined should be {1 2 3 4}
    ASSERT_EQ(joined->expr.count, 4);

    // Inputs should be unchanged
    ASSERT_EQ(list1->expr.count, count1_before);
    ASSERT_EQ(list2->expr.count, count2_before);
}
```
- [ ] Test passes
- [ ] Join doesn't affect input lists

#### Test 3.4: Split Works Correctly (Regression)
```c
void test_split_regression() {
    valk_lval_t* res = valk_eval(env, "(split 3 {1 2 3 4 5 6 7 8})");

    ASSERT_EQ(res->expr.count, 2);
    ASSERT_EQ(res->expr.cell[0]->expr.count, 3);  // lhs {1 2 3}
    ASSERT_EQ(res->expr.cell[1]->expr.count, 5);  // rhs {4 5 6 7 8}
}
```
- [ ] Test passes (this was failing before)
- [ ] Split creates independent lists

**Success Criteria**:
- [ ] All Phase 3 tests pass
- [ ] `test_prelude_split` C test now passes
- [ ] All existing C tests still pass
- [ ] No freeze assertion failures in test suite

---

## Phase 4: Implement Heap GC

### Goals
- Add GC heap as third allocator (scratch, global, heap)
- Implement mark-sweep collection
- Track heap usage and trigger GC automatically

### Tasks

#### 4.1. Add Heap Structure
- [ ] Add `valk_gc_heap_t` structure to `memory.h`
- [ ] Add `gc_next` pointer to `valk_lval_t` for linked list
- [ ] Implement `valk_gc_heap_init(size_t threshold)`
- [ ] Add `VALK_MEM_GC_HEAP` to allocator enum

#### 4.2. Implement Mark Phase
- [ ] Implement `valk_gc_mark(lval)` - recursive marker
- [ ] Implement `valk_gc_mark_env(env)` - mark environment
- [ ] Handle all lval types (SEXPR, QEXPR, FUN, ENV, STR, etc)
- [ ] Set `LVAL_FLAG_GC_MARK` on reachable objects

#### 4.3. Implement Sweep Phase
- [ ] Implement `valk_gc_sweep(heap)` - free unmarked objects
- [ ] Walk linked list and free unmarked nodes
- [ ] Clear mark bits for next collection
- [ ] Update `allocated_bytes` counter

#### 4.4. Implement Collection Trigger
- [ ] Implement `valk_gc_heap_alloc` with threshold check
- [ ] Trigger `valk_gc_collect` when threshold exceeded
- [ ] Add objects to linked list on allocation
- [ ] Track allocated bytes

#### 4.5. Integrate with Allocator System
- [ ] Wire up `valk_gc_heap_alloc` in `valk_mem_allocator_alloc`
- [ ] Implement `valk_gc_heap_realloc`
- [ ] Implement `valk_gc_heap_free` (mark as freeable)
- [ ] Add `valk_gc_collect` manual trigger function

### Test Plan
**Validation Method**: Unit tests + integration tests

#### Test 4.1: Heap Allocates Objects
```c
void test_heap_allocates() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024 * 1024);

    VALK_WITH_ALLOC(heap) {
        valk_lval_t* v = valk_lval_num(42);
        ASSERT_EQ(v->num, 42);
        ASSERT_EQ(LVAL_ALLOC(v), LVAL_ALLOC_HEAP);
    }

    ASSERT_GT(heap->allocated_bytes, 0);
}
```
- [ ] Can allocate from heap
- [ ] Objects tracked in linked list
- [ ] Allocated bytes tracked

#### Test 4.2: Mark Phase Marks Reachable
```c
void test_mark_phase() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024 * 1024);
    valk_lenv_t* env = valk_lenv_empty();

    VALK_WITH_ALLOC(heap) {
        valk_lval_t* v = valk_lval_qexpr_empty();
        valk_lval_add(v, valk_lval_num(1));
        valk_lval_add(v, valk_lval_num(2));
        valk_lenv_put(env, valk_lval_sym("x"), v);
    }

    valk_gc_mark_env(env);

    valk_lval_t* x = valk_lenv_get(env, valk_lval_sym("x"));
    ASSERT_TRUE(x->flags & LVAL_FLAG_GC_MARK);
    ASSERT_TRUE(x->expr.cell[0]->flags & LVAL_FLAG_GC_MARK);
}
```
- [ ] Mark phase sets GC_MARK flag
- [ ] Mark recursively marks children
- [ ] Environment values get marked

#### Test 4.3: Sweep Collects Garbage
```c
void test_sweep_collects_garbage() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024 * 1024);

    size_t before = heap->allocated_bytes;

    // Create garbage (not stored anywhere)
    VALK_WITH_ALLOC(heap) {
        for (int i = 0; i < 100; i++) {
            valk_lval_num(i);
        }
    }

    size_t after_alloc = heap->allocated_bytes;
    ASSERT_GT(after_alloc, before);

    // Collect with no roots - everything is garbage
    valk_gc_collect(heap, NULL);

    size_t after_gc = heap->allocated_bytes;
    ASSERT_EQ(after_gc, 0);  // All garbage collected
}
```
- [ ] Sweep frees unmarked objects
- [ ] Allocated bytes decreases
- [ ] No live objects collected

#### Test 4.4: GC Preserves Live Objects
```c
void test_gc_preserves_live() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024 * 1024);
    valk_lenv_t* env = valk_lenv_empty();

    VALK_WITH_ALLOC(heap) {
        valk_lenv_put(env, valk_lval_sym("x"), valk_lval_num(42));

        // Create garbage
        for (int i = 0; i < 100; i++) {
            valk_lval_num(i);
        }
    }

    valk_gc_collect(heap, env);

    // x should still exist
    valk_lval_t* x = valk_lenv_get(env, valk_lval_sym("x"));
    ASSERT_TYPE(x, LVAL_NUM);
    ASSERT_EQ(x->num, 42);
}
```
- [ ] Live objects not collected
- [ ] Can access live objects after GC
- [ ] Garbage collected, live objects remain

#### Test 4.5: Auto-Trigger on Threshold
```c
void test_auto_gc_trigger() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024);  // Small threshold

    size_t collections_before = heap->num_collections;

    // Allocate until GC triggers
    VALK_WITH_ALLOC(heap) {
        for (int i = 0; i < 1000; i++) {
            valk_lval_qexpr_empty();
        }
    }

    // Should have triggered at least one collection
    ASSERT_GT(heap->num_collections, collections_before);
}
```
- [ ] GC automatically triggers
- [ ] Threshold respected
- [ ] Collection counter increments

**Success Criteria**:
- [ ] All 5 GC tests pass
- [ ] Heap allocator integrated with existing system
- [ ] Can manually trigger GC with `valk_gc_collect(heap, root_env)`
- [ ] Auto-trigger prevents unbounded growth

---

## Phase 5: Escape Analysis & Optimization

### Goals
- Determine which values need heap vs scratch
- Values that escape need heap, temporaries use scratch
- Avoid deep copies by sharing immutable heap values

### Tasks

#### 5.1. Define Escape Points
- [ ] Add `LVAL_FLAG_ESCAPES` bit to flags
- [ ] Document escape conditions in code comments

#### 5.2. Mark Escaping Values
- [ ] Mark values in `valk_lenv_put` as escaping
- [ ] Mark closure captures as escaping (`valk_builtin_lambda`)
- [ ] Mark function return values as escaping (in `valk_lval_eval`)

#### 5.3. Smart Intern (Zero-Copy for Immutables)
- [ ] Implement zero-copy path for frozen heap values
- [ ] Ensure `valk_lval_copy` does shallow copy for immutable children
- [ ] Add metrics to track copy savings

#### 5.4. Allocate Escaping Values on Heap
- [ ] Use scratch for temporaries during eval
- [ ] Promote escaping values to heap before storing
- [ ] Implement `valk_lval_promote_to_heap` helper

### Test Plan
**Validation Method**: Performance tests + correctness tests

#### Test 5.1: Escaping Values Marked
```c
void test_escape_marking() {
    valk_lenv_t* env = valk_lenv_empty();
    valk_lval_t* v = valk_lval_num(42);

    ASSERT_FALSE(v->flags & LVAL_FLAG_ESCAPES);

    valk_lenv_put(env, valk_lval_sym("x"), v);

    valk_lval_t* x = valk_lenv_get(env, valk_lval_sym("x"));
    ASSERT_TRUE(x->flags & LVAL_FLAG_ESCAPES);
}
```
- [ ] Values stored in env marked as escaping
- [ ] Non-escaping values not marked

#### Test 5.2: Zero-Copy Sharing Works
```c
void test_zero_copy_sharing() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024 * 1024);
    valk_lenv_t* env = valk_lenv_empty();
    env->allocator = heap;

    VALK_WITH_ALLOC(heap) {
        valk_lval_t* original = valk_lval_num(42);
        valk_lval_freeze(original);

        // Intern should return same pointer (zero copy)
        valk_lval_t* interned = valk_intern(env, original);
        ASSERT_EQ(original, interned);  // Same pointer!
    }
}
```
- [ ] Frozen heap values shared (not copied)
- [ ] Pointers are identical
- [ ] No allocation for sharing

#### Test 5.3: Scratch Used for Temporaries
```c
void test_scratch_for_temporaries() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024 * 1024);
    valk_mem_arena_t* scratch = valk_mem_arena_init(...);

    size_t heap_before = heap->allocated_bytes;

    // Eval temporary expression
    VALK_WITH_ALLOC(scratch) {
        valk_lval_t* temp = valk_eval(env, "(+ 1 2)");
        // temp is in scratch, not heap
        ASSERT_EQ(LVAL_ALLOC(temp), LVAL_ALLOC_SCRATCH);
    }

    // Heap unchanged (no allocation)
    ASSERT_EQ(heap->allocated_bytes, heap_before);
}
```
- [ ] Temporaries allocated in scratch
- [ ] Heap not used for non-escaping values
- [ ] Scratch can be reset after eval

#### Test 5.4: Map Uses Bounded Memory
```c
void test_map_bounded_memory() {
    valk_gc_heap_t* heap = valk_gc_heap_init(1024 * 1024);
    valk_lenv_t* env = valk_lenv_empty();
    valk_lenv_builtins(env);
    env->allocator = heap;

    size_t before = heap->allocated_bytes;

    // Map over 1000 element list
    valk_eval(env, "(map (\\ {x} {* 2 x}) (range 1 1000))");

    valk_gc_collect(heap, env);
    size_t after = heap->allocated_bytes;

    // Should use reasonable memory (not 1000x growth)
    ASSERT_LT(after - before, 100 * 1024);  // Less than 100KB
}
```
- [ ] Map doesn't leak memory
- [ ] GC collects intermediate values
- [ ] Memory usage bounded

**Success Criteria**:
- [ ] All 4 escape analysis tests pass
- [ ] Zero-copy demonstrated (same pointers)
- [ ] Memory usage reduced compared to always-copy baseline
- [ ] Can revert global arena to 16MB and tests still pass

---

## Phase 6: Integration & Validation

### Goals
- Run full test suite with all features enabled
- Validate memory usage improvements
- Prove correctness under all scenarios

### Tasks

#### 6.1. Integration Testing
- [ ] Run all C tests with GC heap enabled
- [ ] Run all Lisp tests (`test/test_prelude.valk`)
- [ ] Run stress tests (loops, recursion, map/filter)

#### 6.2. Memory Usage Validation
- [ ] Measure arena usage before/after
- [ ] Track GC collection frequency
- [ ] Verify no memory leaks with valgrind

#### 6.3. Performance Benchmarks
- [ ] Measure allocation rate improvement
- [ ] Measure GC pause times
- [ ] Compare to baseline (current implementation)

### Test Plan
**Validation Method**: Full system tests

#### Test 6.1: All C Tests Pass
```bash
make test
# All tests should pass:
# ✅ test_parsing_prelude
# ✅ test_prelude_fun
# ✅ test_prelude_curry
# ... (all 11+ tests)
```
- [ ] `make test` exits 0
- [ ] All C tests pass
- [ ] No assertion failures

#### Test 6.2: All Lisp Tests Pass
```bash
./build/valk test/test_prelude.valk
# Should run all 24 tests and pass
```
- [ ] All 24 Lisp tests pass
- [ ] No OOM errors
- [ ] Tests complete in <5 seconds

#### Test 6.3: Memory Usage Improved
```bash
# Before (current): Needs 64MB global arena
# After: Should work with 16MB heap + GC

./build/valk test/test_prelude.valk
# Monitor memory usage
```
- [ ] Tests pass with 16MB heap (4x reduction)
- [ ] GC triggers periodically (not too often)
- [ ] Peak memory <20MB total

#### Test 6.4: No Memory Leaks
```bash
valgrind --leak-check=full ./build/valk test/test_prelude.valk
# Should show:
# "All heap blocks were freed -- no leaks are possible"
```
- [ ] Valgrind reports no leaks
- [ ] All allocated memory freed
- [ ] GC correctly cleans up

#### Test 6.5: Stress Test
```c
void test_stress_loop() {
    valk_lenv_t* env = valk_lenv_empty();
    valk_lenv_builtins(env);

    // Run 100k iterations with map
    valk_eval(env,
        "(fun {stress n} "
        "  {if (<= n 0) {0} "
        "    {do (map (\\ {x} {* 2 x}) {1 2 3 4 5}) "
        "        (stress (- n 1))}})");

    valk_lval_t* result = valk_eval(env, "(stress 100000)");
    ASSERT_TYPE(result, LVAL_NUM);

    // Should complete without OOM
}
```
- [ ] Stress test completes
- [ ] No OOM errors
- [ ] Memory usage stays bounded

**Success Criteria**:
- [ ] All 5 integration tests pass
- [ ] Memory usage reduced by 4x (64MB → 16MB)
- [ ] No memory leaks detected
- [ ] All tests complete in reasonable time (<30s total)

---

## Implementation Order

### Week 1: Immutability
- **Day 1-2**: Phase 1 (Mutation Audit)
- **Day 3-4**: Phase 2 (Freeze Infrastructure)
- **Day 5**: Phase 3 (Fix Mutation Bugs)

### Week 2: Garbage Collection
- **Day 1-2**: Phase 4.1-4.3 (Heap + Mark + Sweep)
- **Day 3-4**: Phase 4.4-4.5 (Auto-trigger + Integration)
- **Day 5**: Phase 4 Testing

### Week 3: Optimization
- **Day 1-2**: Phase 5 (Escape Analysis)
- **Day 3-4**: Phase 6 (Integration Testing)
- **Day 5**: Performance tuning + documentation

---

## Rollback Plan

If any phase fails:

1. **Phase 2 fails**: Disable freeze checks with `#ifdef`, continue with audit
2. **Phase 3 fails**: Revert to deep-copy semantics, document bugs for later
3. **Phase 4 fails**: Fall back to arena-only allocation
4. **Phase 5 fails**: Skip optimization, keep correct but slower implementation

Each phase is independently testable and can be disabled without breaking earlier work.

---

## Success Metrics

### Final Validation Checklist
- [ ] All 11 C tests pass
- [ ] All 24 Lisp tests pass
- [ ] No freeze assertion failures
- [ ] No GC corruption bugs
- [ ] Memory usage ≤16MB for test suite
- [ ] No memory leaks in valgrind
- [ ] GC triggers <10 times during test suite
- [ ] Zero-copy demonstrated (pointer equality tests)
- [ ] Performance within 20% of baseline
- [ ] Code documented and maintainable

### Quantitative Goals
- **Memory**: 64MB → 16MB (4x reduction)
- **Allocations**: 50% reduction via sharing
- **GC frequency**: <1% of eval calls
- **Test time**: <30 seconds total
- **Code quality**: <5% increase in LOC

---

## Current Status

**Completed**:
- ✅ Added `origin_allocator` tracking to all lvals
- ✅ Identified core problem (mutation of shared values)
- ✅ Created comprehensive implementation plan

**Next Step**:
→ **Begin Phase 1: Mutation Audit** ←

Start with: `grep -rn "->expr.cell\[.*\] =" src/`
