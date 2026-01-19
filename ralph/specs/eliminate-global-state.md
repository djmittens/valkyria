# Eliminate Global Mutable State

## Problem

The Valk codebase relies on global mutable state via `def`, which creates concurrency issues:

1. **Main thread** runs initial script setup
2. **Event loop thread** runs callbacks (HTTP handlers, timers, async continuations)
3. **`valk_lenv_put`** has no synchronization - direct array mutation
4. **Data races** occur when both threads access the same environment

Current mitigations are incomplete:
- HTTP handlers use sandboxed envs that block `def` - but only for handlers
- Async tests use atoms - but only for counters
- Most code still uses `def` for globals

## Principle

**No globals should be a strict rule.** Pass state explicitly or use closures.

## Scope

### Phase 1: Test Framework (modules/test.valk)

The test framework is the worst offender with 11 global variables:

```lisp
; Sync test globals
(def {*test-registry*} {})
(def {*test-passed*} 0)
(def {*test-failed*} 0)
(def {*test-skipped*} 0)
(def {*test-suite-name*} "Valkyria Test Suite")
(def {*test-skip-suite*} 0)
(def {*test-skip-reason*} "")
(def {*test-debug*} 0)
(def {*test-expected-exit*} 0)

; Async test globals
(def {*test-async-registry*} {})
(def {*test-async-pending-atom*} (atom 0))  ; OK - atoms are thread-safe
(def {*test-async-passed-atom*} (atom 0))   ; OK
(def {*test-async-failed-atom*} (atom 0))   ; OK
```

**Refactor to:**
- Create test context struct passed through all functions
- Use builder pattern for test suite configuration
- Atoms only for truly cross-thread state (async pending count)

### Phase 2: Audit All .valk Files

Scan for `(def {*` pattern and refactor each instance.

### Phase 3: Runtime Enforcement

Consider adding runtime warning/error when `def` is used to mutate existing bindings (not just in sandboxed handlers).

## Implementation Plan

### Task 1: Refactor test/run (sync tests)

Current:
```lisp
(fun {test/run & args} {
  do
    (def {*test-passed*} 0)  ; MUTATION
    ...
})
```

New:
```lisp
(fun {test/run & args} {
  (= {ctx} (test/context-new))
  (fold test/run-one ctx *test-registry*)
  (test/print-results ctx)
  (test/exit-with-code ctx)
})

(fun {test/context-new} {
  {passed 0 failed 0 skipped 0 suite-name "Valkyria Test Suite"}
})

(fun {test/run-one ctx test} {
  ; Returns updated ctx with incremented counters
  ...
})
```

### Task 2: Refactor test/run-async (async tests)

Current approach with atoms is mostly correct, but context should still be explicit:

```lisp
(fun {test/run-async aio & args} {
  (= {ctx} (test/async-context-new))
  ...
})

(fun {test/async-context-new} {
  {pending (atom 0) passed (atom 0) failed (atom 0)}
})
```

### Task 3: Refactor test registration

Current:
```lisp
(fun {test/define name body} {
  (def {*test-registry*} (join *test-registry* ...))  ; MUTATION
})
```

New approach - return test list, don't mutate global:
```lisp
; Tests are defined inline, not registered to global
(test/run (list
  (test "name1" {body1})
  (test "name2" {body2})))
```

Or use a builder:
```lisp
(-> (test/suite "My Suite")
    (test/add "test1" {body1})
    (test/add "test2" {body2})
    (test/run))
```

### Task 4: Audit other .valk files

Files to check:
- src/prelude.valk - `nil`, `true`, `false` are OK (constants)
- src/async_monadic.valk - aliases OK
- src/async_handles.valk - check for mutable state
- src/http_api.valk - check for mutable state
- All test/*.valk files

### Task 5: Add lint rule

Create a script that fails CI if `(def {*` pattern appears outside of:
- Constant definitions (immutable after init)
- Atom creation

## Acceptance Criteria

- [ ] `modules/test.valk` has no mutable globals (only atoms for async)
- [ ] All test files work with refactored framework
- [ ] No `(def {*...*} ...)` mutations in src/*.valk (except atom creation)
- [ ] CI lint check for global mutation pattern
- [x] Document threading model in AGENTS.md or similar - Added docs/THREADING.md

## Notes

- This is a breaking change to the test framework API
- Existing tests will need migration
- Consider backwards compatibility shim during transition
