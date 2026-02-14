# Layer 7: Type System (FUTURE)

**Status**: Not started

**Timeline**: ~3-5 months

**Priority**: LOW - Wait until language stabilizes

---

## Overview

Optional gradual type system for Valk. Types checked at compile time when provided, runtime otherwise.

**Benefits**:
- Earlier error detection
- Better tooling (autocomplete, refactoring)
- Documentation in code
- Performance hints for compiler

**Approach**: Gradual typing (like TypeScript, Python type hints)

---

## Feature 1: Type Annotations (S - 1-3 days)

**Unlocks**: Document expected types in code

### Tasks

- [ ] **7.1: Type Syntax Design** (1 day)
  - Decide syntax: `: type` suffix or `^type` metadata?
  - Examples:
    ```lisp
    (fun add (x : Int) (y : Int) : Int
      (+ x y))
    
    ; Or alternative:
    (fun add (x y) : Int
      ^{:param-types [Int Int] :return Int}
      (+ x y))
    ```
  - **Document**: Type syntax spec

- [ ] **7.2: Parse Type Annotations** (1-2 days)
  - Extend parser to recognize type annotations
  - Store types in AST
  - **Test**: Parse function with types

---

## Feature 2: Type Checker (M - 1-2 weeks)

**Unlocks**: Compile-time type verification

### Tasks

- [ ] **7.3: Type Environment** (2-3 days)
  - Track known types of variables
  - Type inference for unannotated code
  - **Test**: Build type environment

- [ ] **7.4: Type Rules** (1 week)
  - Implement typing rules for each expression
  - Arithmetic: `Int -> Int -> Int`
  - Function calls: Check argument types
  - **Test**: Type check simple expressions

- [ ] **7.5: Error Reporting** (2-3 days)
  - Helpful error messages for type mismatches
  - Show expected vs actual types
  - **Test**: Intentional type errors produce good messages

---

## Feature 3: Type Inference (L - 2-4 weeks)

**Unlocks**: Infer types without annotations

**Algorithm**: Hindley-Milner or bidirectional type checking

### Tasks

- [ ] **7.6: Constraint Generation** (1 week)
  - Generate type constraints from AST
  - **Test**: Generate constraints

- [ ] **7.7: Constraint Solving** (1-2 weeks)
  - Unification algorithm
  - **Test**: Solve constraints

- [ ] **7.8: Generalization** (3-4 days)
  - Polymorphic types: `forall a. a -> a`
  - **Test**: Infer polymorphic types

---

## Feature 4: ADTs (M - 1-2 weeks)

**Unlocks**: Algebraic data types (sum/product types)

### Tasks

- [ ] **7.9: Define ADTs** (3-4 days)
  - Syntax: `(deftype Maybe (Some value) None)`
  - **Test**: Define Maybe, Either, Tree types

- [ ] **7.10: Constructors** (2-3 days)
  - Generate constructor functions
  - **Test**: Create values with constructors

---

## Feature 5: Pattern Matching (M - 1-2 weeks)

**Unlocks**: Destructure ADTs

### Tasks

- [ ] **7.11: Match Syntax** (1 week)
  - `(match value (pattern1 result1) (pattern2 result2))`
  - **Test**: Match on ADTs

- [ ] **7.12: Exhaustiveness Check** (3-4 days)
  - Warn if patterns don't cover all cases
  - **Test**: Missing pattern triggers warning

---

## Resources

- Hindley-Milner: https://en.wikipedia.org/wiki/Hindley–Milner_type_system
- Bidirectional type checking: https://arxiv.org/abs/1908.05839
- Gradual typing: https://wphomes.soic.indiana.edu/jsiek/what-is-gradual-typing/
- TypeScript: https://www.typescriptlang.org/docs/handbook/type-checking-javascript-files.html
