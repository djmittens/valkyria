# Next Session Plan: Full Cons List Migration + GC

## What We Completed This Session ✅

### 1. Immutability Infrastructure (100% Complete)
- ✅ Added `LVAL_FLAG_FROZEN` bit (parser.h:24)
- ✅ Implemented `valk_lval_freeze()` - recursively freezes value trees (parser.c:374-411)
- ✅ Implemented `valk_lval_assert_mutable()` - crashes if frozen (parser.c:413-420)
- ✅ Added freeze checks to `valk_lval_add()` and `valk_lval_pop()`
- ✅ Created 5 comprehensive freeze tests (test/test_freeze.c)
- ✅ All 33 tests passing (28 existing + 5 new)

### 2. Cons List Foundation (100% Complete)
- ✅ Renamed `car`/`cdr` → `head`/`tail` throughout entire codebase
  - Much clearer naming! No more IBM 704 register names
  - Updated: parser.h, parser.c, vm.c, test_std.c, test_freeze.c
- ✅ Updated `init` builtin to use cons lists with `valk_cons_init()` helper
- ✅ Marked `expr` field as DEPRECATED (parser.h:79-83)
- ✅ Documented that `cons` will be used by LVAL_CONS, LVAL_SEXPR, LVAL_QEXPR

### 3. Key Benefits Achieved
- **Immutability**: Prevents mutation bugs, safe foundation for GC
- **Better naming**: head/tail instead of cryptic car/cdr
- **No regressions**: All existing tests still pass
- **Clear path forward**: Structure ready for full cons migration

---

## Next Session: Full Cons Migration (Estimated 3-4 hours)

### Current State
SEXPR/QEXPR still use arrays (`expr.cell[]`) with conversion to cons for operations:
```c
// Current (hybrid):
head/tail/cons/init: QEXPR → cons → operate → QEXPR
```

### Goal State
SEXPR/QEXPR directly stored as cons lists:
```c
// Target (pure cons):
SEXPR/QEXPR are cons lists, no conversion needed
```

### Migration Strategy (Incremental with Testing)

#### Phase 1: Update Constructors & Parser (1-1.5 hours)
**Make SEXPR/QEXPR build cons lists from the start**

1. Update `valk_lval_sexpr_empty()` → return nil
2. Update `valk_lval_qexpr_empty()` → return nil
3. Update `valk_lval_read_expr()` - build cons instead of arrays
   - Currently: calls `valk_lval_add()` to build array
   - After: cons elements together during parse
4. **Test**: Run test_std after each change

#### Phase 2: Update Core Operations (1-1.5 hours)
**Make list operations work directly on cons**

1. Update `valk_lval_copy()` - handle SEXPR/QEXPR as cons
   - Currently: copies expr.cell[] arrays
   - After: traverse cons.head/cons.tail
2. Update `valk_lval_finalize()` - no array cleanup needed
3. Update `valk_lval_freeze()` - already handles cons! ✅
4. **Test**: Run test_freeze after each change

#### Phase 3: Update Evaluation (1 hour)
**Make eval traverse cons instead of arrays**

1. Update `valk_lval_eval_sexpr()`:
   - Replace `expr.count` checks with nil checks
   - Replace `expr.cell[i]` with cons traversal
   - Build result as cons list
2. Update `valk_lval_eval_call()`:
   - Traverse args as cons list
   - Build evaluated args as cons
3. **Test**: Run all Lisp tests

#### Phase 4: Update Builtins (~30 min)
**Remove all expr.cell[] access**

Pattern to replace:
```c
// BEFORE:
for (size_t i = 0; i < list->expr.count; i++) {
    do_something(list->expr.cell[i]);
}

// AFTER:
for (valk_lval_t* curr = list; !valk_lval_is_nil(curr); curr = curr->cons.tail) {
    do_something(curr->cons.head);
}
```

Files to update:
- `valk_builtin_len` - count cons list
- `valk_builtin_def` - traverse symbols/values
- `valk_builtin_lambda` - handle formals as cons
- All comparison/equality functions
- Environment operations

**Test**: Full test suite after each builtin

#### Phase 5: Update Print Functions (~20 min)
**Print SEXPR/QEXPR as cons**

1. Update `valk_lval_print()` - SEXPR/QEXPR cases
2. Remove distinction between SEXPR and CONS printing
3. **Test**: Visual output validation

#### Phase 6: Cleanup (~20 min)
**Remove deprecated array operations**

1. Delete `expr` field from union (parser.h)
2. Delete `valk_lval_add()` (no longer needed)
3. Delete `valk_lval_pop()` (no longer needed)
4. Delete conversion functions:
   - `valk_qexpr_to_cons()`
   - `valk_cons_to_qexpr()`
5. **Test**: Full test suite

---

## Testing Strategy

### After Each Phase:
```bash
make test  # All 33 tests must pass
```

### Regression Detection:
- If tests fail, debug that phase before moving forward
- Git commit after each successful phase
- Can rollback to last working state

---

## Success Criteria

- [ ] All 33 tests passing
- [ ] No `expr.cell[]` or `expr.count` in codebase
- [ ] `valk_lval_add` and `valk_lval_pop` deleted
- [ ] SEXPR/QEXPR internally stored as cons lists
- [ ] Print output identical to before migration
- [ ] Ready to implement GC on pure cons structure

---

## After Cons Migration: GC Implementation

Once cons migration is complete, we'll have a clean foundation for GC:

### GC Design (Mark-Sweep)
```c
typedef struct valk_gc_heap_t {
    valk_lval_t *objects;     // Linked list of all heap objects
    size_t allocated_bytes;
    size_t threshold;
    size_t num_collections;
} valk_gc_heap_t;
```

### Mark Phase (Traverse cons naturally!)
```c
void valk_gc_mark(valk_lval_t* lval) {
    if (!lval || (lval->flags & LVAL_FLAG_GC_MARK)) return;
    lval->flags |= LVAL_FLAG_GC_MARK;

    switch (LVAL_TYPE(lval)) {
        case LVAL_SEXPR:
        case LVAL_QEXPR:
        case LVAL_CONS:
            valk_gc_mark(lval->cons.head);  // Mark head
            valk_gc_mark(lval->cons.tail);  // Mark tail
            break;
        // ... other types
    }
}
```

Much simpler with pure cons lists!

---

## Estimated Total Time

- **Full cons migration**: 3-4 hours
- **GC implementation**: 4-6 hours
- **GC testing & tuning**: 1-2 hours

**Total**: 8-12 hours for complete cons + GC

---

## Files Modified This Session

**Added:**
- test/test_freeze.c (5 new tests)

**Modified:**
- src/parser.h (freeze flags, head/tail rename, marked expr deprecated)
- src/parser.c (freeze functions, head/tail rename, cons helpers)
- src/vm.c (head/tail rename)
- test/test_std.c (head/tail rename)
- test/test_freeze.c (head/tail rename)
- Makefile (added test_freeze)
- CMakeLists.txt (added test_freeze target)

**Test Status:**
- ✅ All 33 tests passing
- ✅ No regressions
- ✅ Freeze infrastructure working correctly

---

## Notes

- **Immutability is solid** - no known bugs
- **head/tail naming** - much clearer than car/cdr
- **Cons foundation** - ready for full migration
- **Test coverage** - excellent, will catch any cons migration issues
- **Next session** - can jump straight into Phase 1 of cons migration
