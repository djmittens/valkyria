# Eliminate Global Mutable State

## Overview

Remove global mutable state from the Valk codebase to eliminate data races between the main thread and event loop thread. The current reliance on `def` for global variables creates concurrency issues since `valk_lenv_put` has no synchronization. Refactoring to explicit state passing and closures improves thread safety and code clarity.

## Requirements

### Problem Analysis

The codebase has two threads accessing shared state:

| Thread | Role | State Access |
|--------|------|--------------|
| Main thread | Runs initial script setup | Writes globals via `def` |
| Event loop thread | Runs callbacks (HTTP handlers, timers, async) | Reads/writes globals |

`valk_lenv_put` performs direct array mutation without locks, causing data races.

### Current Mitigations (Incomplete)

- HTTP handlers use sandboxed envs that block `def` - but only for handlers
- Async tests use atoms - but only for counters
- Most code still uses `def` for globals

### Design Principle

**No globals should be a strict rule.** Pass state explicitly or use closures. Atoms are acceptable only for truly cross-thread state (e.g., async pending count).

### Test Framework Globals (Worst Offender)

`src/modules/test.valk` has 11 global variables:

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

### Refactored Design: Test Context

Replace globals with explicit context struct:

```lisp
(fun {test/context-new} {
  {passed 0 failed 0 skipped 0 suite-name "Valkyria Test Suite"}
})

(fun {test/run-one ctx test} {
  ; Returns updated ctx with incremented counters
  ...
})

(fun {test/run & args} {
  (= {ctx} (test/context-new))
  (fold test/run-one ctx *test-registry*)
  (test/print-results ctx)
  (test/exit-with-code ctx)
})
```

### Refactored Design: Async Context

```lisp
(fun {test/async-context-new} {
  {pending (atom 0) passed (atom 0) failed (atom 0)}
})

(fun {test/run-async aio & args} {
  (= {ctx} (test/async-context-new))
  ...
})
```

### Refactored Design: Test Registration

Replace mutable registry with inline test lists:

**Current (mutable):**
```lisp
(fun {test/define name body} {
  (def {*test-registry*} (join *test-registry* ...))  ; MUTATION
})
```

**New (immutable):**
```lisp
; Option 1: Inline list
(test/run (list
  (test "name1" {body1})
  (test "name2" {body2})))

; Option 2: Builder pattern
(-> (test/suite "My Suite")
    (test/add "test1" {body1})
    (test/add "test2" {body2})
    (test/run))
```

### Files to Audit

| File | Status | Notes |
|------|--------|-------|
| `src/modules/test.valk` | Needs refactor | 11 globals |
| `src/prelude.valk` | OK | `nil`, `true`, `false` are constants |
| `src/async_monadic.valk` | OK | Aliases only |
| `src/async_handles.valk` | Audit | Check for mutable state |
| `src/http_api.valk` | Audit | Check for mutable state |
| `test/*.valk` | Audit | May use test framework globals |

### CI Lint Rule

Add script that fails CI if `(def {*` pattern appears outside of:
- Constant definitions (immutable after init)
- Atom creation

## Acceptance Criteria

- [ ] `src/modules/test.valk` has no mutable globals (only atoms for cross-thread async counters)
- [ ] `grep -c "def {\*" src/modules/test.valk` returns count matching only atom creations
- [ ] All existing test files work with refactored framework (`make test` passes)
- [ ] No `(def {*...*} ...)` mutations in `src/*.valk` (except atom creation)
- [ ] CI lint check script exists and detects global mutation pattern
- [ ] `docs/THREADING.md` documents the threading model and no-globals rule
- [ ] Backwards compatibility: Old test API works during transition period (optional shim)
