# Cons Lists vs Arrays for Immutable Values

## The Fundamental Question

Before implementing freeze checks, we should decide on the data structure:
- **Current**: Dynamic arrays (`expr.cell[]`)
- **Alternative**: Cons lists (classic Lisp structure)

---

## Current Structure: Dynamic Arrays

```c
struct valk_lval_t {
    struct {
        valk_lval_t **cell;  // Array of pointers
        size_t count;         // Number of elements
    } expr;
};
```

### Operations with Arrays
```c
// tail {1 2 3} → {2 3}
// PROBLEM: Must allocate new array and copy 2 pointers
valk_lval_t* tail = valk_lval_qexpr_empty();
for (size_t i = 1; i < list->expr.count; i++) {
    valk_lval_add(tail, list->expr.cell[i]);  // Copy pointer
}
return tail;  // New allocation required
```

### Pros
- ✅ **Fast random access**: O(1) to get nth element
- ✅ **Cache friendly**: Contiguous memory
- ✅ **Simple implementation**: Standard array operations

### Cons
- ❌ **Must copy on tail/head**: Can't share structure
- ❌ **Wasted allocations**: Every operation needs new array
- ❌ **Split problem**: Creating sublists requires new arrays
- ❌ **Not idiomatic Lisp**: Lists should be cons cells

---

## Alternative: Cons Lists (Linked Structure)

```c
struct valk_lval_t {
    union {
        // For cons cells
        struct {
            valk_lval_t *car;  // Head element
            valk_lval_t *cdr;  // Tail (rest of list)
        } cons;

        // For atoms
        long num;
        char *str;
        // ... other types
    };
};
```

### Operations with Cons Lists
```c
// tail {1 2 3} → {2 3}
// ZERO ALLOCATION: Just return pointer to existing cdr!
valk_lval_t* valk_builtin_tail(valk_lenv_t* e, valk_lval_t* a) {
    return a->cons.cdr;  // Instant, shares structure!
}

// cons x {1 2 3} → {x 1 2 3}
// ONE ALLOCATION: Just allocate head node
valk_lval_t* valk_builtin_cons(valk_lval_t* x, valk_lval_t* xs) {
    valk_lval_t* cell = valk_lval_cons();
    cell->cons.car = x;
    cell->cons.cdr = xs;  // Share existing list!
    valk_lval_freeze(cell);
    return cell;
}

// join {1 2} {3 4} → {1 2 3 4}
// Recursive construction sharing tail
valk_lval_t* valk_lval_join(valk_lval_t* x, valk_lval_t* y) {
    if (x == nil) return y;  // Share entire y!

    valk_lval_t* cell = valk_lval_cons();
    cell->cons.car = x->cons.car;
    cell->cons.cdr = valk_lval_join(x->cons.cdr, y);  // Recursive
    return cell;
}
```

### Pros
- ✅ **Perfect structural sharing**: tail/head/init are FREE (return pointer)
- ✅ **Zero copy**: Most operations just allocate new head nodes
- ✅ **Immutability natural**: Can't mutate a cons cell, only create new ones
- ✅ **Classic Lisp**: Idiomatic for a Lisp interpreter
- ✅ **Memory efficient**: Lists share tails
- ✅ **GC friendly**: Natural tree structure for mark phase

### Cons
- ❌ **Slower random access**: O(n) to get nth element (must traverse)
- ❌ **More allocations**: Each element is separate node vs array
- ❌ **Cache unfriendly**: Nodes scattered vs contiguous array
- ❌ **Reverse is expensive**: O(n) allocations vs array reverse

---

## Performance Comparison

### Common Operations

| Operation | Array | Cons List |
|-----------|-------|-----------|
| `head {1 2 3}` | O(1) - Copy 1 pointer | O(1) - Return car |
| `tail {1 2 3}` | O(n) - Allocate + copy | **O(1) - Return cdr** ✨ |
| `init {1 2 3}` | O(n) - Allocate + copy | O(n) - Cons without last |
| `cons x xs` | O(n) - Allocate + copy all | **O(1) - Allocate 1 node** ✨ |
| `nth n xs` | **O(1) - Array index** ✨ | O(n) - Traverse |
| `len xs` | **O(1) - count field** ✨ | O(n) - Traverse (unless cached) |
| `join xs ys` | O(n+m) - Allocate + copy | O(n) - Cons nodes sharing ys |
| `map f xs` | O(n) - Allocate array | O(n) - Allocate n cons nodes |

### Memory Impact

**Example**: `(split 3 {1 2 3 4 5 6 7 8})`

**With Arrays**:
- Original list: 1 array (8 pointers)
- Left list `{1 2 3}`: NEW array (3 pointers)
- Right list `{4 5 6 7 8}`: NEW array (5 pointers)
- **Total**: 3 arrays, 16 pointers

**With Cons Lists**:
- Original list: 8 cons nodes
- Left list: 3 NEW nodes pointing to original atoms
- Right list: Just POINTER to 4th node of original!
- **Total**: 11 cons nodes (3 new, 8 shared)

**Winner**: Cons lists - right list is FREE!

---

## Real-World Impact Analysis

### Current Test Suite Usage

Looking at prelude.valk operations:
```lisp
(fun {tail _l} ...)       ; Used HEAVILY in recursion
(fun {head _l} ...)       ; Used in pattern matching
(fun {map f l} ...)       ; Recursive with tail
(fun {filter f l} ...)    ; Recursive with tail
(fun {foldl f z l} ...)   # Recursive with tail
```

**Key insight**: Most operations are RECURSIVE using tail/head. These would all benefit from O(1) cons list operations!

### nth is 1-indexed (Current Code)
```lisp
(fun {nth n _l} {
  if (== n 1)
    {eval (head _l)}
    {nth (- n 1) (tail _l)}  ; Recursive tail traversal!
})
```

Even `nth` is implemented via tail traversal! So we're ALREADY paying O(n) cost - array indexing advantage is unused!

---

## Hybrid Approach (Compromise)

We could use **different structures for different purposes**:

```c
typedef enum {
    LVAL_NIL,       // Empty list
    LVAL_CONS,      // Cons cell (car/cdr)
    LVAL_VEC,       // Array/vector (for fast indexing)
    LVAL_NUM,
    LVAL_SYM,
    // ...
} valk_ltype_e;
```

### When to use each:

**Cons Lists (LVAL_CONS)**:
- S-expressions (code)
- Q-expressions (lists)
- Recursive data structures
- 90% of list operations

**Vectors (LVAL_VEC)**:
- Environment symbol/value arrays (need fast lookup)
- Large datasets needing random access
- Interop with C arrays
- 10% of use cases

### Conversion:
```lisp
(vec->list {1 2 3})  ; Convert vector to cons list
(list->vec {1 2 3})  ; Convert cons list to vector
```

---

## Recommendation

### Option A: Full Cons Lists (Recommended) ✨

**Pros**:
- Solves immutability problem elegantly
- Natural for Lisp semantics
- Massive performance win for tail/head/cons (used everywhere)
- Eliminates deep copy problem entirely
- Simpler mental model

**Cons**:
- Breaking change to data structures
- Need to migrate all code
- Slower nth/len (but already traversing anyway!)

**Effort**: 2-3 days to migrate, but solves Phase 3 bugs automatically

### Option B: Arrays + Freeze Checks (Current Plan)

**Pros**:
- Less disruptive
- Keeps fast random access
- Incremental improvement

**Cons**:
- Still need to allocate/copy for tail/head/join
- Doesn't solve the fundamental structural sharing problem
- More complex freeze checking

**Effort**: Follows plan, but doesn't address root cause

### Option C: Hybrid (Complex)

**Pros**:
- Best of both worlds theoretically

**Cons**:
- Complexity in choosing when to use each
- Conversion overhead
- Two implementations to maintain

---

## Migration Path for Option A

If we go with cons lists, here's the plan:

### Step 1: Add Cons Type
```c
// parser.h
#define LVAL_CONS  (existing types + 1)

struct valk_lval_t {
    uint64_t flags;
    void *origin_allocator;
    union {
        struct {  // LVAL_CONS
            valk_lval_t *car;
            valk_lval_t *cdr;
        } cons;
        struct {  // Keep expr for backwards compat during migration
            valk_lval_t **cell;
            size_t count;
        } expr;
        long num;
        char *str;
        // ...
    };
};
```

### Step 2: Implement Cons Primitives
```c
valk_lval_t* valk_lval_cons(valk_lval_t* car, valk_lval_t* cdr);
valk_lval_t* valk_lval_nil();  // Empty list
valk_lval_t* valk_lval_car(valk_lval_t* cons);
valk_lval_t* valk_lval_cdr(valk_lval_t* cons);
bool valk_lval_is_nil(valk_lval_t* v);
```

### Step 3: Update Builtins
```c
// head becomes trivial
valk_lval_t* valk_builtin_head(valk_lenv_t* e, valk_lval_t* a) {
    return valk_lval_cons(a->cons.car, valk_lval_nil());
}

// tail becomes FREE
valk_lval_t* valk_builtin_tail(valk_lenv_t* e, valk_lval_t* a) {
    return a->cons.cdr;  // Just return pointer!
}
```

### Step 4: Update Parser
- Change `valk_lval_qexpr_empty()` to return nil
- Change `valk_lval_add(list, x)` to cons onto list
- Update print functions for cons format

### Step 5: Migrate Tests
- Update assertions for cons structure
- Verify sharing works (pointer equality tests)

---

## Decision Time

**Question for you**: Which path should we take?

**A. Full Cons Lists** - 2-3 day migration, solves problem elegantly, true Lisp
**B. Arrays + Freeze** - Follow current plan, incremental, safe
**C. Hybrid** - Both structures, more complexity

My recommendation: **Option A (Full Cons Lists)**

Reasoning:
1. We're already doing tail traversal for nth - no perf loss
2. Solves the 5 mutation bugs automatically
3. Makes freeze checks simpler (just freeze car/cdr pointers)
4. Massive win for recursive operations (90% of code)
5. More idiomatic for a Lisp
6. Sets us up better for GC (tree structure)

What do you think?
