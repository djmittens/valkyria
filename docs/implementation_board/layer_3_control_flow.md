# Layer 3: Control Flow

**Status**: if/do, recursion, continuations complete; TCO requires compilation

**Timeline**: ~3-6 weeks

---

## Current State

### Complete ✓
- [x] `if` / `do` builtins
- [x] Recursion (works, no optimization)
- [x] Continuations (`LVAL_CONT` type)
- [x] `shift` / `reset` (delimited continuations)
- [x] Async/await patterns (using continuations)
- [x] Error handling (`LVAL_ERR` type)

### Remaining Work
- [ ] TCO (Tail Call Optimization) - **See Layer 6: Compilation**
- [ ] Common Lisp-style Conditions (M - 1-2 weeks)
- [ ] Restarts (L - 2-4 weeks)

**Note**: TCO is blocked on either:
1. Stack machine implementation (not pursued), OR
2. Valk IR → LLVM compilation (Layer 6, Phase 4)

The compilation approach provides TCO via LLVM's `musttail` attribute.

---

## Feature 1: Common Lisp Conditions (M - 1-2 weeks)

**Unlocks**: Advanced error handling, restartable exceptions

**Background**: CL conditions separate error signaling from error handling. Unlike exceptions, conditions allow handling errors without unwinding the stack.

**Use case**: Server encounters error but continues running, file I/O fails but prompts for different file, etc.

### Tasks

- [ ] **3.1: Design Condition System** (2-3 days)
  - Research CL condition system: `signal`, `handler-bind`, `handler-case`
  - Design Valk API:
    ```lisp
    (define-condition error-type (parent-type) (slot1 slot2 ...))
    (signal condition-object)
    (handler-bind ((condition-type handler-fn)) body)
    (handler-case body (condition-type (var) recovery-form))
    ```
  - **Decision**: Use struct/record for condition objects?
  - **Document**: Write design doc with examples
  - **Test**: Create example use cases

- [ ] **3.2: Implement Condition Type** (1-2 days)
  - File: `src/parser.h`
  - Add to `valk_ltype_e`: `LVAL_CONDITION`
  - Condition structure:
    ```c
    typedef struct {
      char* type_name;           // Condition type
      valk_lval_t* parent_type;  // Inheritance
      valk_lval_t* slots;        // Key-value data
      char* message;             // Human-readable
    } valk_condition_t;
    ```
  - **Test**: Create condition object

- [ ] **3.3: Implement define-condition** (2-3 days)
  - File: `src/parser.c` (builtins or macros)
  - Macro: `(define-condition name (parent) slots)`
  - Creates condition type with inheritance
  - Example:
    ```lisp
    (define-condition network-error (error)
      (host port message))
    ```
  - **Test**: Define condition types, verify inheritance

- [ ] **3.4: Implement Signal** (2-3 days)
  - File: `src/parser.c`
  - `(signal condition)` - trigger condition
  - Does NOT unwind stack (unlike `throw`)
  - Searches for handler in dynamic environment
  - If no handler: converts to error
  - **Algorithm**: Walk handler stack, call matching handler
  - **Test**: Signal condition, handler catches it

- [ ] **3.5: Implement handler-bind** (3-4 days)
  - `(handler-bind ((condition-type handler-fn)) body)`
  - Registers handler in dynamic scope
  - Handler is called with condition object
  - Handler can:
    - Handle it (return value)
    - Decline (return :decline, search continues)
    - Re-signal (call signal again)
  - **Implementation**: Handler stack (like dynamic bindings)
  - **Test**: Nested handlers, handler selection

- [ ] **3.6: Implement handler-case** (2-3 days)
  - `(handler-case body (condition-type (var) recovery-form))`
  - Like `try/catch`, but more powerful
  - Unwinds stack to handler
  - **Implementation**: Use continuations for unwinding
  - **Test**: Condition signaled, stack unwound to handler

- [ ] **3.7: Condition Hierarchy** (1-2 days)
  - Standard condition types:
    - `condition` (root)
    - `warning` (non-fatal)
    - `error` (fatal)
    - `type-error`, `arithmetic-error`, `file-error`, etc.
  - **Implementation**: Define in prelude or C
  - **Test**: Signal specific errors, generic handlers catch them

- [ ] **3.8: Integration with LVAL_ERR** (1-2 days)
  - Current errors (`LVAL_ERR`) should signal conditions
  - Convert existing error returns to `signal`
  - Backward compatibility: uncaught conditions → `LVAL_ERR`
  - **Test**: Old error-handling code still works

- [ ] **3.9: Condition Tests** (2-3 days)
  - File: `test/test_conditions.valk`
  - Test: Signal and handle various conditions
  - Test: Handler inheritance (subtype handlers)
  - Test: Multiple handlers (dynamic scoping)
  - Test: Uncaught conditions become errors
  - Test: handler-case vs handler-bind behavior
  - **Run**: Add to `make test`

---

## Feature 2: Restarts (L - 2-4 weeks)

**Unlocks**: Interactive error recovery, debugger integration

**Background**: Restarts allow code to offer multiple ways to recover from errors. Condition handlers can invoke restarts to continue execution.

**Example**:
```lisp
(defun read-file (path)
  (restart-case
    (open-file path)  ; Might fail
    (use-default ()
      :report "Use default config"
      (open-file "/etc/default.conf"))
    (retry ()
      :report "Retry with different path"
      (read-file (prompt-for-path)))
    (abort ()
      :report "Abort operation"
      nil)))

; Handler can invoke restart:
(handler-bind ((file-error
                (lambda (c)
                  (invoke-restart 'use-default))))
  (read-file "/missing.conf"))  ; Uses default instead of failing
```

### Tasks

- [ ] **3.10: Design Restart System** (2-3 days)
  - Research CL restarts: `restart-case`, `restart-bind`, `invoke-restart`
  - Design Valk API
  - **Key insight**: Restarts are escape continuations with names
  - **Document**: Design doc with examples
  - **Test**: Write example use cases

- [ ] **3.11: Implement Restart Type** (1-2 days)
  - File: `src/parser.h`
  - Restart structure:
    ```c
    typedef struct {
      char* name;              // Restart identifier
      valk_lval_t* continuation;  // Where to jump
      valk_lval_t* test_fn;    // Applicability test
      char* report;            // Human description
    } valk_restart_t;
    ```
  - **Test**: Create restart object

- [ ] **3.12: Implement restart-case** (3-4 days)
  - File: `src/parser.c`
  - Macro: `(restart-case protected-form (name params body) ...)`
  - Captures continuation at restart points
  - Registers restarts in dynamic environment
  - Example:
    ```lisp
    (restart-case (/ x y)
      (return-zero () 0)
      (return-value (v) v))
    ```
  - **Implementation**: Use `shift`/`reset` or continuations
  - **Test**: Define restarts, verify registered

- [ ] **3.13: Implement invoke-restart** (2-3 days)
  - `(invoke-restart restart-name arg1 arg2 ...)`
  - Searches dynamic environment for named restart
  - Invokes restart continuation with arguments
  - Does not return (non-local exit)
  - **Test**: Invoke restart from nested function

- [ ] **3.14: Implement find-restart** (1-2 days)
  - `(find-restart name)` - return restart object or nil
  - `(compute-restarts)` - list all active restarts
  - Used by debugger/REPL to show available options
  - **Test**: List restarts in current context

- [ ] **3.15: Interactive Restart Selection** (2-3 days)
  - In REPL: When error occurs, show available restarts
  - Prompt user to select restart
  - Example output:
    ```
    Error: Division by zero
    Restarts:
      0: [RETURN-ZERO] Return 0
      1: [RETURN-VALUE] Return a specific value
      2: [ABORT] Abort computation
    Select restart [0-2]: _
    ```
  - **Integration**: Update REPL error handling
  - **Test**: Interactive restart selection in REPL

- [ ] **3.16: Restart Tests** (2-3 days)
  - File: `test/test_restarts.valk`
  - Test: Define and invoke restarts
  - Test: Multiple restarts available
  - Test: Restart with arguments
  - Test: Nested restart-cases
  - Test: compute-restarts returns all active
  - **Run**: Add to `make test`

- [ ] **3.17: Integration with Conditions** (2-3 days)
  - Handlers can invoke restarts
  - Standard pattern: signal condition, handler chooses restart
  - Example:
    ```lisp
    (handler-bind ((file-error
                    (lambda (c)
                      (if (available-p 'use-default)
                        (invoke-restart 'use-default)))))
      (read-config))
    ```
  - **Test**: Condition + restart integration

- [ ] **3.18: Debugger Integration** (3-4 days)
  - When uncaught error: enter debugger
  - Debugger shows:
    - Error message
    - Stack trace
    - Available restarts
  - User can invoke restart interactively
  - **Challenge**: Stack inspection without VM
  - **Test**: Debugger catches error, offers restarts

---

## Progress Tracking

### Velocity
- **Week 1**: ___ tasks completed
- **Week 2**: ___ tasks completed
- **Week 3**: ___ tasks completed

### Current Status
- **Feature**: ___
- **Task**: ___
- **Blocker**: ___

### Notes
- Session notes here

---

## Resources

### Common Lisp Condition System
- CLtL2 Chapter 29: https://www.cs.cmu.edu/Groups/AI/html/cltl/clm/node312.html
- "Condition Handling in Common Lisp": http://www.nhplace.com/kent/Papers/Condition-Handling-2001.html
- Practical Common Lisp Chapter 19: https://gigamonkeys.com/book/beyond-exception-handling-conditions-and-restarts.html

### Implementation References
- SBCL condition system: https://github.com/sbcl/sbcl/blob/master/src/code/condition.lisp
- Clasp (Common Lisp on LLVM): https://github.com/clasp-developers/clasp

### Tail Call Optimization
- See Layer 6: Compilation for TCO implementation via LLVM
- "Tail Call Optimization" article: https://www.cs.tufts.edu/~nr/cs257/archive/luc-maranget/jr-tailcall.pdf
