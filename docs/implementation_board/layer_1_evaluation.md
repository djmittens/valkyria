# Layer 1: Evaluation

**Status**: Complete except macro hygiene

**Timeline**: ~1-2 weeks

---

## Current State

### Complete ✓
- [x] Tree-walker interpreter (eval loop)
- [x] Environments (symbol tables with parent chain)
- [x] Closures (captured environment)
- [x] Lexical scope (parent chain lookup)
- [x] Builtins (40+ C functions)
- [x] Varargs (variable argument functions)
- [x] `& rest` parameters (collect rest args)
- [x] Lambda (`\` syntax for anonymous functions)
- [x] `fun` macro (named function definition)
- [x] Basic macros (work but no hygiene)

### Remaining Work
- [ ] Macro hygiene system (M - 1-2 weeks)

---

## Feature: Macro Hygiene (M - 1-2 weeks)

**Unlocks**: Safe macros that don't capture unintended variables

**Background**: Current macros can accidentally capture variables from the calling context (variable capture problem).

**Example of problem**:
```lisp
; Buggy macro without hygiene
(defmacro swap (a b)
  `(let ((tmp ,a))
     (set! ,a ,b)
     (set! ,b tmp)))

; Breaks if user has variable named 'tmp'
(let ((tmp 1) (x 2) (y 3))
  (swap x y)  ; tmp gets clobbered!
  tmp)  ; Expected 1, got 2!
```

**Solution**: Hygiene system ensures macro-introduced identifiers are unique.

### Tasks

- [ ] **1.1: Research Hygiene Systems** (1-2 days)
  - Study Scheme's syntax-rules hygiene
  - Study Racket's syntax/datum approach
  - Study Common Lisp's gensym approach
  - **Decision**: Choose between automatic (Scheme-like) or manual (CL-like)
  - **Recommendation**: Start with gensym (simpler), add automatic later
  - **Document**: Write design doc with examples

- [ ] **1.2: Implement gensym** (1 day)
  - File: `src/parser.c` (builtins)
  - Implement `(gensym prefix)` - generates unique symbol
  - Use global counter: `_G0`, `_G1`, `_G2`, ...
  - Store counter in global state or thread-local
  - **Test**: `(gensym "x")` → `x_G0`, next call → `x_G1`

- [ ] **1.3: Macro Expansion Tracking** (2-3 days)
  - File: `src/parser.c` (macro expansion)
  - Track macro expansion context (depth, source location)
  - Add field to `valk_lval_t`: `struct { ... } macro_ctx;`
  - Store: Where was this code generated? (macro name, line, col)
  - **Use case**: Better error messages from macro-generated code
  - **Test**: Expand macro, check context attached to generated code

- [ ] **1.4: Automatic Symbol Renaming** (3-4 days)
  - During macro expansion, rename all locally-bound variables
  - **Algorithm**:
    1. Walk macro body
    2. Find `let`, `lambda` bindings
    3. Rename bound vars to gensyms
    4. Update references to use renamed vars
  - **Example**: `(let ((x 1)) ...)` → `(let ((x_G5 1)) ...)`
  - **Test**: Macro with `let` doesn't capture calling context

- [ ] **1.5: defmacro with Hygiene** (2-3 days)
  - Update `defmacro` to apply hygiene transformation
  - Add optional flag: `(defmacro/unhygienic ...)` for old behavior
  - **Breaking change**: Existing macros might break if they rely on capture
  - **Migration**: Provide tool to identify problematic macros
  - **Test**: `swap` macro now works correctly

- [ ] **1.6: Quasi-quote Hygiene** (2-3 days)
  - Handle hygiene in backquote/unquote
  - Unquoted values should use calling context scope
  - Quoted symbols should use macro context scope
  - **Example**:
    ```lisp
    (defmacro my-let (bindings body)
      `(let ,bindings  ; 'let' is hygienic
         ,body))       ; body uses caller's scope
    ```
  - **Test**: Mixed quoted/unquoted code maintains correct scoping

- [ ] **1.7: Hygiene Tests** (1-2 days)
  - File: `test/test_hygiene.valk`
  - Test: `swap` macro with `tmp` variable in context
  - Test: Nested macros with same variable names
  - Test: Macro that intentionally breaks hygiene (using `(unquote-splicing ...)`)
  - Test: Error messages from macro-generated code are clear
  - **Run**: Add to `make test`

- [ ] **1.8: Documentation** (1 day)
  - Document hygiene behavior in `docs/LANGUAGE.md`
  - Provide examples of hygienic vs unhygienic macros
  - Explain when to use `gensym` manually
  - Explain escape hatches for intentional capture
  - **Example**: Anaphoric macros that intentionally capture `it`

---

## Future Enhancements

### Syntactic Closures (Optional, FUTURE)
- More powerful than hygiene alone
- Allows fine-grained control of binding contexts
- See MIT Scheme's approach
- **Timeline**: 2-4 weeks

### Macros with Pattern Matching (Optional, FUTURE)
- Like Scheme's `syntax-rules`
- Pattern-based macro definitions
- **Timeline**: 2-3 weeks

### Compiler Macros (Optional, FUTURE)
- Macros that run during compilation (Layer 6)
- Can optimize based on static information
- **Dependency**: Requires compilation layer
- **Timeline**: 1-2 weeks

---

## Progress Tracking

### Velocity
- **Week 1**: ___ tasks completed
- **Week 2**: ___ tasks completed

### Current Status
- **Task**: ___
- **Blocker**: ___

### Notes
- Session notes here

---

## Resources

### Hygiene Systems
- Scheme Hygiene: https://www.scheme.com/tspl4/syntax.html
- Racket Macros: https://docs.racket-lang.org/guide/macros.html
- CL Macros: http://www.lispworks.com/documentation/HyperSpec/Body/03_a.htm
- "Macros That Work" paper: https://www.cs.indiana.edu/~dyb/pubs/macros-that-work.pdf
- Syntactic Closures: https://people.csail.mit.edu/jhbrown/scheme/macros.html
