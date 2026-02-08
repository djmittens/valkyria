# Test Framework Mutable State Options

## Problem

The async test framework in `src/modules/test.valk` (lines 390-430) has a closure state sharing problem:

```lisp
(= {test-completed} 0)
(= {test-result} false)
(= {done-fn} (\ {passed} { (= {test-completed} 1) (= {test-result} passed) }))
(= {poll-fn} (\ {} { (if (== test-completed 1) ...) }))
```

When `done-fn` executes `(= {test-completed} 1)`, it creates a NEW local binding in done-fn's environment, NOT modifying the outer `test-completed`. The `poll-fn` captures the ORIGINAL value (0), not a reference.

## Options Investigated

### 1. Atom Builtins (NOT AVAILABLE)

- **Location:** `src/parser.c` lines 4044-4105
- **Functions:** `valk_builtin_atom`, `valk_builtin_atom_get`, `valk_builtin_atom_set`, `valk_builtin_atom_add`, `valk_builtin_atom_sub`
- **Status:** Functions exist but are NOT REGISTERED in `valk_lenv_builtins()` (lines 5160-5332)
- All marked `__attribute__((unused))` with deprecation warning: "use aio/semaphore or aio/then chains"
- **Verdict:** Cannot use without modifying C code to re-register

### 2. plist/set Mutation (DOES NOT WORK)

- **Location:** `src/prelude.valk` lines 225-231
- **Behavior:** `plist/set` returns a NEW plist, does NOT mutate in place
- Functional/immutable style - sharing a plist reference between closures won't allow one closure's changes to be visible to another
- **Verdict:** Cannot use for mutable shared state

### 3. aio/semaphore (REMOVED)

- Was removed per commit fdcde37
- **Verdict:** Not available

## Recommended Approach: Test Body Returns Handle Directly

Instead of test body calling a `done` callback, have it return a handle directly:

```lisp
; Current broken API:
(test-async "test" (\ {done} {
  (aio/then (some-op) (\ {r} { (done (== r :ok)) }))
}))

; New working API:
(test-async "test" (\ {aio} {
  (aio/then (some-op aio) (\ {r} { (aio/pure (== r :ok)) }))
}))
```

**Implementation in `*test-run-async-one*`:**

```lisp
; OLD: create done-fn, poll-fn, start polling
; NEW: call test body, get handle, use aio/then

(= {result-handle} (test-body aio))
(= {timeout-handle} (aio/within result-handle timeout-ms))
(aio/then timeout-handle
  (\ {passed} { {:status (if passed {:pass} {:fail})} })
  (\ {err} { {:status :timeout} }))
```

**Benefits:**
1. No mutable state needed - fully functional
2. Aligns with aio/then chains pattern (mentioned in atom deprecation)
3. No C code changes required
4. Makes tests composable with aio/all, aio/race, etc.

**Impact:** All 27 test files using `test/run-async` need minor updates to return handles instead of calling `done`.

## Alternative: Quick Fix with aio/wait

If changing 27 files is too invasive, could use `aio/wait` to synchronously wait:

```lisp
; In poll-fn, after test-body sets up its async operations:
(aio/wait some-handle)  ; blocks until handle completes
```

But this requires knowing which handle to wait on, which brings us back to the state sharing problem.

## Decision

**Use the handle-returning pattern.** The test framework should be updated to:
1. Pass only `aio` to test body (not a done callback)
2. Expect test body to return a handle that resolves to true/false
3. Use `aio/within` for timeout
4. Use `aio/then`/`aio/catch` to process result
