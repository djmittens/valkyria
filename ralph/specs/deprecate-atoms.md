# Deprecate Atom Builtins and Clean Up Async API

## Overview

Remove the `atom` primitive and `aio/deferred` to enforce a clean monadic async API. The root cause of atom usage is **callback-based APIs** that force coordination via shared state. The fix is making all async APIs monadic (return handles), then using `aio/all` for result collection and `aio/race` for timeouts.

**Key insight:** Atoms exist because callbacks can't compose. Fix the APIs, and atoms become unnecessary. No new primitives like `aio/semaphore` are needed.

## Requirements

### Remove `aio/deferred`

`aio/deferred` returns `{handle complete-fn fail-fn}`, exposing handle completion to Lisp code. This is an anti-pattern - C runtime should own handle completion. All C APIs should return handles directly; Lisp code should never need to manually complete a handle.

**Remove:** `aio/deferred`, `aio/deferred-complete!`, `aio/deferred-fail!` from `aio_combinators.c`

### Add Missing Combinators

The async API is missing common patterns from Finagle/Twitter Futures:

| Combinator | Signature | Description |
|------------|-----------|-------------|
| `aio/within` | `(aio/within handle timeout-ms)` | Fail with timeout error if handle doesn't complete in time |
| `aio/all-settled` | `(aio/all-settled handles)` | Like `aio/all` but doesn't fail-fast; collects all results/errors |
| `aio/retry` | `(aio/retry aio fn opts)` | Retry async operation with backoff policy |
| `aio/never` | `(aio/never aio)` | Returns handle that never completes |
| `aio/traverse` | `(aio/traverse list fn)` | Map fn over list, then collect results (sugar for `aio/all` + `map`) |

#### `aio/within`

Currently timeout requires verbose `aio/race`:
```lisp
(aio/race (list
  handle
  (aio/then (aio/sleep aio 5000) (\ {_} {(error "timeout")}))))
```

With `aio/within`:
```lisp
(aio/within handle 5000)  ; fails with timeout error if > 5s
```

#### `aio/all-settled`

`aio/all` fails fast - if any handle fails, it cancels the rest and returns the first error. Sometimes you want all results regardless of individual failures:

```lisp
(aio/then (aio/all-settled handles)
  (\ {results} {
    ; results is list of {:status :ok :value v} or {:status :error :error e}
    ...}))
```

#### `aio/retry`

Common pattern for network operations:
```lisp
(aio/retry aio
  (\ {} {(http2/client-request aio host port path)})
  {:max-attempts 3 :backoff :exponential :base-ms 100})
```

#### `aio/never`

Returns a handle that never completes. Useful for `aio/race` patterns where you want "wait forever unless X happens":
```lisp
(aio/race (list
  (aio/never aio)      ; wait forever...
  (stream/closed s)))  ; ...unless stream closes
```

#### `aio/traverse`

Sugar for the common pattern of mapping an async function over a list and collecting results:
```lisp
; Instead of:
(aio/all (map (\ {url} {(fetch url)}) urls))

; Write:
(aio/traverse urls fetch)
```

### Fix `aio/interval` to Return Handle

The SSE stress tests use atoms because `aio/interval` returns a number (interval ID), not a handle:

```lisp
; Current broken pattern - interval returns number, can't be cancelled externally
(stream/on-close stream (\ {} {(atom/set! closed true)}))
(aio/interval sys 50 (\ {}
  {(if (atom/get closed) :stop ...)}))
```

**The fix:** `aio/interval` should return a handle that:
1. Can be passed to `aio/cancel` to stop the interval
2. Can be raced with other handles via `aio/race`

```lisp
; New pattern - interval returns handle, cancel on stream close
(= {interval} (aio/interval sys 50 (\ {} {...})))
(stream/on-close stream (\ {} {(aio/cancel interval)}))
```

### Remove Atoms

| File | Atom Count | Usage |
|------|------------|-------|
| `src/modules/test.valk` | 4 | Async test tracking |
| `test/stress/test_sse_concurrency_short.valk` | 6 | Metrics counters + stream close detection |
| `test/stress/test_sse_concurrency.valk` | 6 | Same |
| `test/test_atom_builtins.valk` | N/A | Tests atom API itself |

### Replacement Patterns

| Atom Usage | Replacement |
|------------|-------------|
| Counters | `aio/all` + reduce results |
| Cancellation flags | `aio/race` or `aio/cancel` |
| Stream close detection | `aio/cancel` interval on close |
| Callback coordination | Handle-returning APIs |
| Timeout coordination | `aio/within` |

### Refactored Test Framework

**Current (imperative with atoms):**
```lisp
(def {*test-async-pending-atom*} (atom 0))
(def {*test-async-passed-atom*} (atom 0))
...
(atom/add! *test-async-passed-atom* 1)
```

**New (monadic):**
```lisp
(fun {test/run-async aio tests opts} {
  (aio/then
    (aio/all (map (\ {t} {(test/run-one-async aio opts t)}) tests))
    (\ {results} {(test/summarize-results results)}))})
```

### Refactored Timeout Handling

**Current:**
```lisp
(= {timed-out} (atom 0))
(aio/schedule aio timeout-ms (\ {} {(atom/set! timed-out 1) ...}))
```

**New:**
```lisp
(aio/within (run-test test) timeout-ms)
```

### Files to Modify

| File | Change |
|------|--------|
| `src/aio/aio_combinators.c` | Remove `aio/deferred*`, add `aio/within`, `aio/all-settled`, `aio/retry` |
| `src/aio/aio_combinators.c` | Refactor `aio/interval` to return handle |
| `src/parser.c` | Remove atom builtins |
| `src/modules/test.valk` | Refactor to use `aio/all` and `aio/within` |
| `test/stress/test_sse_concurrency*.valk` | Use `aio/cancel` instead of atom |
| `test/test_atom_builtins.valk` | Delete |

### Phased Rollout

| Phase | Description | Breaking? |
|-------|-------------|-----------|
| 1 | Remove `aio/deferred*` | **Yes** (but unused) |
| 2 | Add `aio/within`, `aio/all-settled`, `aio/retry` | No |
| 3 | Refactor `aio/interval` to return cancellable handle | **Yes** (return type changes) |
| 4 | Refactor test framework to use `aio/all` + `aio/within` | No |
| 5 | Refactor SSE stress tests to use `aio/cancel` | No |
| 6 | Remove atom builtins | **Yes** |

## Acceptance Criteria

### Phase 1: Remove aio/deferred
- [x] `aio/deferred`, `aio/deferred-complete!`, `aio/deferred-fail!` removed
- [x] `make build` succeeds
- [x] `make test` passes

### Phase 2: Add Combinators
- [x] `aio/within handle timeout-ms` returns handle that fails on timeout
- [x] `aio/all-settled handles` collects all results without fail-fast
- [x] `aio/retry aio fn opts` retries with configurable backoff
- [x] `aio/never aio` returns handle that never completes
- [x] `aio/traverse list fn` maps and collects
- [x] Tests exist for each new combinator
- [ ] `make test` passes

### Phase 3: Refactor aio/interval
- [x] `aio/interval` returns a handle instead of a number
- [x] `aio/cancel` on interval handle stops the interval
- [x] Interval handle completes when stopped (via `:stop` return or cancel)
- [x] Existing `:stop` return pattern still works
- [ ] `make test` passes

### Phase 4: Test Framework Refactor
- [x] `src/modules/test.valk` uses `aio/all` instead of atoms
- [x] `src/modules/test.valk` uses `aio/within` for timeout handling
- [x] `grep -c "atom" src/modules/test.valk` returns 0
- [ ] All existing async test files pass without modification

### Phase 5: SSE Stress Test Refactor
- [x] `test/stress/test_sse_concurrency*.valk` use `aio/cancel` for stream close
- [x] `grep -c "atom" test/stress/test_sse_concurrency_short.valk` returns 0
- [x] `grep -c "atom" test/stress/test_sse_concurrency.valk` returns 0
- [ ] All stress tests pass

### Phase 6: Remove Atoms
- [ ] `valk_atom_t` struct removed from `src/parser.c`
- [ ] All `valk_builtin_atom*` functions removed
- [ ] `test/test_atom_builtins.valk` deleted
- [ ] `build/valk -e '(atom 1)'` returns error "Unknown function 'atom'"
- [ ] `make test` passes
