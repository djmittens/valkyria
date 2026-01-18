# Source Location Propagation for Comprehensive Coverage Tracking

## Problem Statement

Currently, Valkyria tracks branch coverage by implementing conditional forms (`if`, `select`) as C builtins that manually extract source location from QEXPR clauses before evaluation. This approach **does not scale** because:

1. Every conditional pattern (`case`, `cond`, `and`, `or`, `when`, `unless`, etc.) would need a separate builtin
2. User-defined macros/functions with lazy evaluation cannot participate in coverage tracking
3. Source location is lost when AST is transformed during macro-style expansion

### Example: Lost Coverage

```lisp
; select defined as user function in prelude.valk
(fun {select-impl cs} {
     if (== cs nil)
       {error "No selection found"}
       {if (eval (fst (fst cs))) {eval (snd (fst cs))} {select-impl (tail cs)}}
})
(fun {select & cs} {select-impl cs})

; Usage:
(select
  {(== x 1) "one"}    ; Line 10 - no branch coverage tracked
  {(== x 2) "two"}    ; Line 11 - no branch coverage tracked  
  {otherwise "many"}) ; Line 12 - no branch coverage tracked
```

Coverage only tracks the inner `if` in `select-impl`, not each clause's source line.

---

## Solution: Source Location Propagation

The standard technique used by production Lisp implementations (Racket, SBCL, Clojure) is **source location propagation**: ensure AST nodes carry source metadata through all transformations.

### Core Principle

Every `valk_lval_t` should maintain its original source location through:
- Copying operations (`valk_lval_copy`)
- List construction (`valk_lval_cons`, `valk_lval_list`, `valk_lval_join`)
- Type conversions (`valk_qexpr_to_cons`)
- Evaluation (preserve location on result when meaningful)

---

## Implementation Plan

### Phase 1: Consistent Source Location Copying

**Goal:** Ensure all AST manipulation functions preserve source location.

#### 1.1 Audit and Fix Copy Functions

| Function | Current Behavior | Required Fix |
|----------|------------------|--------------|
| `valk_lval_copy()` | Copies source loc | Verify correct |
| `valk_qexpr_to_cons()` | Copies source loc | Verify correct |
| `valk_lval_cons()` | Does NOT copy source loc | **Add source loc parameter** |
| `valk_lval_list()` | Does NOT preserve source loc | **Inherit from first element** |
| `valk_lval_join()` | Does NOT preserve source loc | **Inherit from left operand** |
| `valk_lval_pop()` | Creates new cons, loses loc | **Copy from original** |

#### 1.2 New Helper Functions

```c
#ifdef VALK_COVERAGE

// Copy source location from src to dst
static inline void valk_copy_source_loc(valk_lval_t* dst, valk_lval_t* src) {
  if (src != NULL && dst != NULL) {
    dst->cov_file_id = src->cov_file_id;
    dst->cov_line = src->cov_line;
    dst->cov_column = src->cov_column;
  }
}

// Create cons cell inheriting source location from template
valk_lval_t* valk_lval_cons_with_loc(valk_lval_t* head, valk_lval_t* tail, valk_lval_t* loc_source);

// Inherit source location from first element if available
#define INHERIT_SOURCE_LOC(dst, src) do { \
  if ((src) != NULL && (dst) != NULL && (src)->cov_line > 0) { \
    valk_copy_source_loc(dst, src); \
  } \
} while(0)

#else
#define valk_copy_source_loc(dst, src) ((void)0)
#define INHERIT_SOURCE_LOC(dst, src) ((void)0)
#endif
```

#### 1.3 Modify Core Functions

**`valk_lval_cons()`:**
```c
valk_lval_t* valk_lval_cons(valk_lval_t* head, valk_lval_t* tail) {
  valk_lval_t* x = valk_lval_alloc();
  x->flags = LVAL_CONS | valk_alloc_flags_from_allocator(valk_thread_ctx.allocator);
  VALK_SET_ORIGIN_ALLOCATOR(x);
  x->cons.head = head;
  x->cons.tail = tail;
  // Inherit source location from head element
  INHERIT_SOURCE_LOC(x, head);
  return x;
}
```

**`valk_lval_list()`:**
```c
valk_lval_t* valk_lval_list(valk_lval_t* arr[], size_t count) {
  if (count == 0) return valk_lval_nil();
  
  valk_lval_t* result = valk_lval_nil();
  for (size_t i = count; i > 0; i--) {
    result = valk_lval_cons(arr[i - 1], result);
  }
  // First element's source location is inherited by cons
  return result;
}
```

---

### Phase 2: Coverage Recording at Eval Boundaries

**Goal:** Record coverage at the right granularity - when expressions are actually evaluated.

#### 2.1 Current Recording Points

| Location | What's Recorded | Issue |
|----------|-----------------|-------|
| `valk_lval_eval()` entry | All evaluated expressions | Good |
| `valk_builtin_if()` | Branch taken | Good |
| `valk_builtin_select()` | Each clause | Good (but as builtin) |

#### 2.2 New Strategy: Record at QEXPR-to-CONS Conversion

The key insight: In Valkyria, lazy evaluation is achieved through QEXPR (quoted expressions). When a QEXPR is converted to CONS for evaluation, **that's when we should record coverage**.

```c
// In valk_qexpr_to_cons() or wherever QEXPR becomes CONS:
static valk_lval_t* valk_qexpr_to_cons(valk_lval_t* qexpr) {
  if (qexpr == NULL || LVAL_TYPE(qexpr) == LVAL_NIL) {
    return valk_lval_nil();
  }
  
#ifdef VALK_COVERAGE
  // Record that this quoted expression is now being evaluated
  // This captures the moment of "activation" for lazy expressions
  VALK_COVERAGE_RECORD_LVAL(qexpr);
#endif
  
  valk_lval_t* res = valk_lval_cons(qexpr->cons.head, valk_qexpr_to_cons(qexpr->cons.tail));
  valk_copy_source_loc(res, qexpr);
  return res;
}
```

#### 2.3 Branch Coverage Enhancement

Currently branch coverage is recorded as true/false for a single line. Enhance to support **multiple branches per line** (like LCOV BRDA format):

```c
// Enhanced branch recording with branch ID
void valk_coverage_record_branch_id(uint16_t file_id, uint16_t line, 
                                     uint16_t branch_id, bool taken);

// In valk_builtin_if:
#ifdef VALK_COVERAGE
  uint16_t file_id = cond->cov_file_id;  // Use condition's location
  uint16_t line = cond->cov_line;
  // branch_id 0 = true branch, 1 = false branch
  VALK_COVERAGE_RECORD_BRANCH_ID(file_id, line, condition ? 0 : 1, true);
#endif
```

---

### Phase 3: User-Space Coverage Instrumentation

**Goal:** Allow user-defined functions with lazy evaluation to participate in coverage tracking.

#### 3.1 Expose Coverage Recording to Valk

Add builtins that allow Valk code to record coverage:

```c
// (coverage-mark expr) - Mark an expression as potentially executable
// Returns the expression unchanged, but records its location
static valk_lval_t* valk_builtin_coverage_mark(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  VALK_COVERAGE_MARK_LVAL(expr);
  return expr;
}

// (coverage-record expr) - Record that an expression was executed
// Returns the expression unchanged, records execution
static valk_lval_t* valk_builtin_coverage_record(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
  VALK_COVERAGE_RECORD_LVAL(expr);
  return expr;
}

// (coverage-branch line taken?) - Record a branch decision
static valk_lval_t* valk_builtin_coverage_branch(valk_lenv_t* e, valk_lval_t* a) {
  // ... implementation
}
```

#### 3.2 Instrumented Prelude Definitions

With user-space coverage builtins, `select` can be defined in Valk while still tracking coverage:

```lisp
; In prelude.valk (coverage-aware version)
(fun {select-impl cs} {
  if (== cs nil)
    {error "No selection found"}
    {do
      ; Extract clause
      (= {clause} (fst cs))
      (= {cond-expr} (fst clause))
      (= {result-expr} (snd clause))
      
      ; Evaluate condition
      (= {cond-val} (eval cond-expr))
      
      ; Record branch coverage for this clause
      (coverage-branch (source-line clause) cond-val)
      
      (if cond-val
        {eval (coverage-record result-expr)}  ; Record execution of result
        {select-impl (tail cs)})}
})
```

**Note:** This requires a `source-line` builtin to extract line number from an expression:

```c
// (source-line expr) - Returns the source line of an expression, or 0
static valk_lval_t* valk_builtin_source_line(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  valk_lval_t* expr = valk_lval_list_nth(a, 0);
#ifdef VALK_COVERAGE
  return valk_lval_num(expr->cov_line);
#else
  return valk_lval_num(0);
#endif
}
```

---

### Phase 4: Macro System with Source Tracking (Future)

**Goal:** If/when Valkyria adds a proper macro system, ensure it preserves source locations.

#### 4.1 Syntax Objects (Advanced)

The gold standard (used by Racket) is **syntax objects**: values that wrap expressions with metadata.

```lisp
; Conceptual - not current Valkyria syntax
(define-syntax (my-if stx)
  (syntax-case stx ()
    [(_ cond then else)
     ; #' preserves source location from original syntax
     #'(if cond then else)]))
```

For Valkyria, a simpler approach would be a `with-source` special form:

```lisp
; (with-source template expr) - Assign template's source location to expr
(with-source original-clause (if cond result fallback))
```

This would be implemented as:

```c
// (with-source template expr) - Copies source loc from template to expr
static valk_lval_t* valk_builtin_with_source(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 2);
  valk_lval_t* template = valk_lval_list_nth(a, 0);
  valk_lval_t* expr = valk_lval_list_nth(a, 1);
  
  // Deep copy expr to avoid mutating original
  valk_lval_t* result = valk_lval_copy(expr);
  
#ifdef VALK_COVERAGE
  // Recursively set source location on all nodes
  valk_propagate_source_loc(result, template);
#endif
  
  return result;
}
```

---

## Test Plan

### Test Categories

1. **Unit Tests (C)** - Test source location preservation in core functions
2. **Integration Tests (Valk)** - Test coverage tracking for various patterns
3. **LCOV Validation** - Verify generated coverage data is correct

### Test File: `test/test_source_loc.c`

```c
#ifdef VALK_COVERAGE
#include "testing.h"
#include "parser.h"
#include "coverage.h"
#include "source_loc.h"

// Test: Source location preserved through valk_lval_copy
void test_copy_preserves_source_loc(void) {
  TEST_START();
  
  valk_lval_t* original = valk_lval_num(42);
  original->cov_file_id = 1;
  original->cov_line = 10;
  original->cov_column = 5;
  
  valk_lval_t* copy = valk_lval_copy(original);
  
  ASSERT_EQ(copy->cov_file_id, 1);
  ASSERT_EQ(copy->cov_line, 10);
  ASSERT_EQ(copy->cov_column, 5);
  
  TEST_PASS();
}

// Test: Source location preserved through qexpr_to_cons
void test_qexpr_to_cons_preserves_loc(void) {
  TEST_START();
  
  // Create a QEXPR with source location
  valk_lval_t* elem = valk_lval_num(1);
  valk_lval_t* qexpr = valk_lval_qcons(elem, valk_lval_nil());
  qexpr->cov_file_id = 2;
  qexpr->cov_line = 20;
  qexpr->cov_column = 3;
  
  valk_lval_t* cons = valk_qexpr_to_cons(qexpr);
  
  ASSERT_EQ(cons->cov_file_id, 2);
  ASSERT_EQ(cons->cov_line, 20);
  ASSERT_EQ(cons->cov_column, 3);
  
  TEST_PASS();
}

// Test: valk_lval_cons inherits location from head
void test_cons_inherits_head_loc(void) {
  TEST_START();
  
  valk_lval_t* head = valk_lval_num(1);
  head->cov_file_id = 3;
  head->cov_line = 30;
  head->cov_column = 7;
  
  valk_lval_t* tail = valk_lval_nil();
  valk_lval_t* cons = valk_lval_cons(head, tail);
  
  ASSERT_EQ(cons->cov_file_id, 3);
  ASSERT_EQ(cons->cov_line, 30);
  ASSERT_EQ(cons->cov_column, 7);
  
  TEST_PASS();
}

// Test: valk_lval_list inherits location from first element
void test_list_inherits_first_elem_loc(void) {
  TEST_START();
  
  valk_lval_t* elems[3];
  elems[0] = valk_lval_num(1);
  elems[0]->cov_file_id = 4;
  elems[0]->cov_line = 40;
  elems[1] = valk_lval_num(2);
  elems[2] = valk_lval_num(3);
  
  valk_lval_t* list = valk_lval_list(elems, 3);
  
  ASSERT_EQ(list->cov_file_id, 4);
  ASSERT_EQ(list->cov_line, 40);
  
  TEST_PASS();
}

// Test: Branch coverage records correct line
void test_branch_coverage_records_line(void) {
  TEST_START();
  
  valk_coverage_init();
  valk_line_coverage_init();
  
  uint16_t file_id = valk_source_register_file("test_branch.valk");
  
  // Simulate branch at line 15, taken=true
  valk_coverage_record_branch(file_id, 15, true);
  
  // Simulate same branch, taken=false
  valk_coverage_record_branch(file_id, 15, false);
  
  valk_line_coverage_file_t* fc = valk_coverage_get_file(file_id);
  ASSERT_NOT_NULL(fc);
  
  // Find branch record for line 15
  valk_branch_t* br = fc->branches;
  while (br != NULL && br->line != 15) br = br->next;
  
  ASSERT_NOT_NULL(br);
  ASSERT_EQ(br->true_count, 1);
  ASSERT_EQ(br->false_count, 1);
  
  valk_line_coverage_reset();
  
  TEST_PASS();
}

// Test: Nested function calls preserve source locations
void test_nested_calls_preserve_loc(void) {
  TEST_START();
  
  // Parse a simple expression and verify source locations
  const char* code = "(+ 1 2)";
  uint16_t file_id = valk_source_register_file("test_nested.valk");
  
  valk_parse_ctx_t ctx = {
    .source = code,
    .pos = 0,
    .line = 1,
    .line_start = 0,
    .file_id = file_id
  };
  
  valk_lval_t* expr = valk_lval_read_expr_ctx(&ctx);
  
  ASSERT_EQ(expr->cov_file_id, file_id);
  ASSERT_EQ(expr->cov_line, 1);
  
  TEST_PASS();
}

REGISTER_TEST(test_copy_preserves_source_loc);
REGISTER_TEST(test_qexpr_to_cons_preserves_loc);
REGISTER_TEST(test_cons_inherits_head_loc);
REGISTER_TEST(test_list_inherits_first_elem_loc);
REGISTER_TEST(test_branch_coverage_records_line);
REGISTER_TEST(test_nested_calls_preserve_loc);

#endif // VALK_COVERAGE
```

### Test File: `test/test_coverage_integration.valk`

```lisp
; Coverage Integration Tests
; Run with: VALK_COVERAGE=1 ./build-coverage/valk test/test_coverage_integration.valk

(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "Coverage Integration")

; ============================================================================
; Test: Basic if branch coverage
; Expected: Both true and false branches recorded for line with 'if'
; ============================================================================
(test/define "if-both-branches"
  {do
    (fun {test-if x} {
      if (> x 0)         ; Line A - branch point
        {"positive"}     ; Line B - true branch
        {"non-positive"} ; Line C - false branch
    })
    ; Exercise both branches
    (test/assert-eq "positive" (test-if 5) "true branch")
    (test/assert-eq "non-positive" (test-if -1) "false branch")
    true
  })

; ============================================================================
; Test: Nested if coverage
; Expected: All nested branches recorded with correct line numbers
; ============================================================================
(test/define "nested-if-coverage"
  {do
    (fun {classify x} {
      if (> x 0)
        {if (> x 100)
          {"large"}
          {"small"}}
        {"non-positive"}
    })
    ; Exercise all paths
    (test/assert-eq "large" (classify 200) "large path")
    (test/assert-eq "small" (classify 50) "small path")
    (test/assert-eq "non-positive" (classify -5) "non-positive path")
    true
  })

; ============================================================================
; Test: Select clause coverage (builtin version)
; Expected: Each select clause gets branch coverage
; ============================================================================
(test/define "select-clause-coverage"
  {do
    (fun {day-type d} {
      select
        {(== d 0) "sunday"}     ; Clause 1
        {(== d 6) "saturday"}   ; Clause 2
        {otherwise "weekday"}   ; Clause 3
    })
    ; Exercise multiple clauses
    (test/assert-eq "sunday" (day-type 0) "sunday")
    (test/assert-eq "saturday" (day-type 6) "saturday")
    (test/assert-eq "weekday" (day-type 3) "weekday")
    true
  })

; ============================================================================
; Test: Case expression coverage
; Expected: Each case clause gets coverage when matched
; ============================================================================
(test/define "case-coverage"
  {do
    (fun {num-word n} {
      case n
        {{1} "one"}
        {{2} "two"}
        {{3} "three"}
    })
    (test/assert-eq "one" (num-word 1) "case 1")
    (test/assert-eq "two" (num-word 2) "case 2")
    (test/assert-eq "three" (num-word 3) "case 3")
    true
  })

; ============================================================================
; Test: Short-circuit evaluation (and/or patterns)
; Expected: Source location preserved through user-defined and/or
; ============================================================================
(test/define "short-circuit-coverage"
  {do
    ; Define short-circuit and
    (fun {my-and a b} {
      if a
        {if b {true} {false}}
        {false}
    })
    
    ; Exercise all paths
    (test/assert-eq 1 (my-and true true) "both true")
    (test/assert-eq 0 (my-and true false) "second false")
    (test/assert-eq 0 (my-and false true) "first false - short circuit")
    true
  })

; ============================================================================
; Test: Map/filter with lambdas
; Expected: Lambda body gets coverage when called
; ============================================================================
(test/define "higher-order-coverage"
  {do
    ; Each lambda invocation should record coverage
    (= {doubled} (map (\ {x} {* x 2}) {1 2 3}))  ; Lambda at line X
    (= {evens} (filter (\ {x} {== 0 (% x 2)}) {1 2 3 4}))  ; Lambda at line Y
    
    (test/assert-eq 3 (len doubled) "map result length")
    (test/assert-eq 2 (len evens) "filter result length")
    true
  })

; ============================================================================
; Test: Recursive function coverage
; Expected: Each recursive call records coverage at function definition line
; ============================================================================
(test/define "recursive-coverage"
  {do
    (fun {factorial n} {
      if (<= n 1)
        {1}
        {* n (factorial (- n 1))}
    })
    (test/assert-eq 120 (factorial 5) "factorial 5")
    true
  })

; ============================================================================
; Test: Multi-expression do block
; Expected: Each expression in do block records coverage
; ============================================================================
(test/define "do-block-coverage"
  {do
    (= {a} 1)    ; Line 1
    (= {b} 2)    ; Line 2  
    (= {c} 3)    ; Line 3
    (+ a b c)    ; Line 4
  })

; ============================================================================
; Test: Let block scoping with coverage
; Expected: Expressions inside let get coverage with correct line numbers
; ============================================================================
(test/define "let-scope-coverage"
  {do
    (= {outer} 10)
    (let {do
      (= {inner} 20)      ; Should have coverage
      (+ outer inner)     ; Should have coverage
    })
    true
  })

; ============================================================================
; Test: Error paths don't corrupt coverage
; Expected: Coverage data remains consistent after error
; ============================================================================
(test/define "error-path-coverage"
  {do
    (fun {safe-div a b} {
      if (== b 0)
        {0}  ; Error case - should have coverage when hit
        {/ a b}
    })
    (test/assert-eq 0 (safe-div 10 0) "div by zero handled")
    (test/assert-eq 5 (safe-div 10 2) "normal division")
    true
  })

(test/run {})
```

### Test File: `test/test_lcov_output.sh`

```bash
#!/bin/bash
# Test that LCOV output is correctly formatted and contains expected data

set -e

VALK_BIN="./build-coverage/valk"
TEST_FILE="test/test_coverage_lcov_check.valk"
LCOV_OUTPUT="build-coverage/coverage-valk.info"

# Create test file with known structure
cat > "$TEST_FILE" << 'EOF'
; Test file for LCOV validation
; Line 1: comment
; Line 2: comment
(load "src/prelude.valk")     ; Line 3: executable
; Line 4: comment
(= {x} 10)                    ; Line 5: executable
(= {y} 20)                    ; Line 6: executable
; Line 7: comment
(if (> x 5)                   ; Line 8: branch point
  {(= {z} 1)}                 ; Line 9: true branch (executed)
  {(= {z} 2)})                ; Line 10: false branch (not executed)
; Line 11: comment
(print z)                     ; Line 12: executable
(shutdown 0)
EOF

# Run with coverage enabled
rm -f "$LCOV_OUTPUT"
VALK_COVERAGE=1 VALK_COVERAGE_OUTPUT="$LCOV_OUTPUT" "$VALK_BIN" "$TEST_FILE" 2>/dev/null || true

# Validate LCOV output exists
if [ ! -f "$LCOV_OUTPUT" ]; then
  echo "FAIL: LCOV output file not created"
  exit 1
fi

# Check for source file entry
if ! grep -q "SF:.*test_coverage_lcov_check.valk" "$LCOV_OUTPUT"; then
  echo "FAIL: Source file not in LCOV output"
  exit 1
fi

# Check for line data entries (DA:line,count format)
DA_COUNT=$(grep -c "^DA:" "$LCOV_OUTPUT" || true)
if [ "$DA_COUNT" -lt 3 ]; then
  echo "FAIL: Expected at least 3 DA entries, got $DA_COUNT"
  exit 1
fi

# Check for branch data (BRDA format) 
BRDA_COUNT=$(grep -c "^BRDA:" "$LCOV_OUTPUT" || true)
if [ "$BRDA_COUNT" -lt 2 ]; then
  echo "FAIL: Expected at least 2 BRDA entries (true/false), got $BRDA_COUNT"
  exit 1
fi

# Validate branch tracking - line 8 should have both branches recorded
# BRDA:8,0,0,1 means line 8, block 0, branch 0 (true), taken 1 time
# BRDA:8,0,1,- means line 8, block 0, branch 1 (false), not taken
if ! grep -q "BRDA:.*,1" "$LCOV_OUTPUT"; then
  echo "FAIL: No taken branch found in BRDA entries"
  exit 1
fi

# Check line counts
LF=$(grep "^LF:" "$LCOV_OUTPUT" | head -1 | cut -d: -f2)
LH=$(grep "^LH:" "$LCOV_OUTPUT" | head -1 | cut -d: -f2)

if [ -z "$LF" ] || [ -z "$LH" ]; then
  echo "FAIL: Missing LF or LH in LCOV output"
  exit 1
fi

if [ "$LH" -gt "$LF" ]; then
  echo "FAIL: Lines hit ($LH) greater than lines found ($LF)"
  exit 1
fi

# Check branch counts
BRF=$(grep "^BRF:" "$LCOV_OUTPUT" | head -1 | cut -d: -f2)
BRH=$(grep "^BRH:" "$LCOV_OUTPUT" | head -1 | cut -d: -f2)

if [ -z "$BRF" ] || [ "$BRF" -eq 0 ]; then
  echo "FAIL: No branches found (BRF=0 or missing)"
  exit 1
fi

echo "PASS: LCOV output validation"
echo "  Lines: $LH/$LF hit"
echo "  Branches: $BRH/$BRF hit"
echo "  DA entries: $DA_COUNT"
echo "  BRDA entries: $BRDA_COUNT"

# Cleanup
rm -f "$TEST_FILE"

exit 0
```

### Edge Case Tests

#### Test: Multi-line Expression

```lisp
; test/test_coverage_multiline.valk
; Verify coverage for expressions spanning multiple lines

(if (and (> x 0)
         (< x 100)    ; Line continuation
         (even? x))   ; More conditions
  {do
    (print "valid")   ; Multi-line body
    (process x)}
  {error "invalid"})
```

**Expected:** Coverage recorded at line where expression starts (the `if` line).

#### Test: Macro-Generated Code

```lisp
; test/test_coverage_macro.valk  
; Verify coverage for code generated by macro-like patterns

; Define a "repeat" pattern using eval
(fun {repeat n body} {
  if (<= n 0)
    {nil}
    {do (eval body) (repeat (- n 1) body)}
})

; Use it - coverage should be at call site, not inside repeat
(repeat 3 {print "hello"})  ; Line 10 - should show coverage
```

**Expected:** Coverage at line 10, not at the `eval body` inside `repeat`.

#### Test: Tail-Recursive Function

```lisp
; test/test_coverage_tco.valk
; Verify coverage works correctly with TCO

(fun {sum-to-helper n acc} {
  if (<= n 0)
    {acc}                              ; Base case
    {sum-to-helper (- n 1) (+ acc n)}  ; Recursive case (TCO)
})

(fun {sum-to n} {sum-to-helper n 0})

(sum-to 1000)  ; Should not stack overflow, coverage should work
```

**Expected:** Both branches of inner `if` get coverage after running.

#### Test: Closure Captures Environment

```lisp
; test/test_coverage_closure.valk
; Verify coverage in closures preserves original source location

(fun {make-adder n} {
  (\ {x} {+ x n})  ; Line 5 - closure definition
})

(= {add5} (make-adder 5))
(= {add10} (make-adder 10))

(add5 3)   ; Should record coverage at line 5
(add10 7)  ; Should also record coverage at line 5
```

**Expected:** Line 5 has execution count of 2.

---

## Implementation Checklist

### Phase 1: Source Location Propagation (Week 1)

- [ ] Audit all `valk_lval_*` functions for source location handling
- [ ] Modify `valk_lval_cons()` to inherit source loc from head
- [ ] Modify `valk_lval_list()` to inherit source loc from first element
- [ ] Modify `valk_lval_join()` to inherit source loc from left operand
- [ ] Modify `valk_lval_pop()` to preserve source loc
- [ ] Add `valk_copy_source_loc()` helper
- [ ] Add `INHERIT_SOURCE_LOC()` macro
- [ ] Write C unit tests for source location preservation

### Phase 2: Coverage Recording Points (Week 2)

- [ ] Add coverage recording in `valk_qexpr_to_cons()`
- [ ] Verify `valk_builtin_if()` records at correct line
- [ ] Verify `valk_builtin_select()` records at each clause line
- [ ] Review all special forms for coverage implications
- [ ] Add enhanced branch ID support for multiple branches per line
- [ ] Write integration tests for branch coverage

### Phase 3: User-Space Coverage (Week 3)

- [ ] Implement `coverage-mark` builtin
- [ ] Implement `coverage-record` builtin
- [ ] Implement `coverage-branch` builtin
- [ ] Implement `source-line` builtin
- [ ] Document coverage builtins
- [ ] Write Valk tests using coverage builtins
- [ ] Optional: Update prelude.valk to use coverage builtins

### Phase 4: LCOV Validation (Week 4)

- [ ] Create LCOV validation test script
- [ ] Test multi-line expression handling
- [ ] Test macro/eval code coverage
- [ ] Test TCO function coverage
- [ ] Test closure coverage
- [ ] Verify `make coverage` produces valid report
- [ ] Integration with CI pipeline

---

## Success Criteria

1. **All existing tests pass** - No regression in functionality
2. **Source locations preserved** - C unit tests verify propagation
3. **Branch coverage accurate** - LCOV shows correct branch hits
4. **User-defined conditionals trackable** - `select`, `case` defined in prelude still get coverage
5. **LCOV validates** - `genhtml` produces correct report
6. **Zero overhead in normal builds** - Build without VALK_COVERAGE has no performance impact

---

## Open Questions

1. **Should we track column numbers?** Current impl stores column but doesn't use it for coverage. Useful for IDE integration.

2. **How to handle `eval` of dynamically constructed code?** Code built at runtime won't have source locations. Options:
   - Record as "synthetic" location
   - Skip coverage for dynamic code
   - Inherit location from `eval` call site

3. **Function-level coverage:** Should we track function definitions and call counts separately from line coverage? LCOV supports FN/FNDA entries.

4. **Coverage for loaded files:** When `(load "file.valk")` is used, should coverage be:
   - Aggregated into main file's coverage?
   - Reported separately per file? (Current behavior)
   - Both?
