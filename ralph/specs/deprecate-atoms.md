# Deprecate Atom Builtins

## Overview

Remove the `atom` primitive from Valk to eliminate mutable shared state that circumvents the monadic async API. The root cause of atom usage is **callback-based APIs** that force coordination via shared state. The fix is making all async APIs monadic (return handles), then using `aio/all` for result collection and `aio/race` for timeouts.

**Key insight:** Atoms exist because callbacks can't compose. Fix the APIs, and atoms become unnecessary. No new primitives like `aio/semaphore` are needed - rate limiting belongs in filters/middleware, not as a low-level builtin.

## Requirements

### Current Implementation

```c
// parser.c:4003-4063
typedef struct { _Atomic long value; } valk_atom_t;

// Builtins: atom, atom/get, atom/set!, atom/add!, atom/sub!
```

### Files Using Atoms

| File | Atom Count | Usage |
|------|------------|-------|
| `src/modules/test.valk` | 4 | Async test tracking |
| `test/test_sse_concurrency_short.valk` | 6 | Metrics counters |
| `test/stress/test_sse_concurrency_short.valk` | 6 | Metrics counters |
| `test/stress/test_sse_concurrency.valk` | 6 | Metrics counters |
| `test/test_atom_builtins.valk` | N/A | Tests atom API itself |

### Design Principle: Monadic APIs Only

**All async APIs must be monadic (return handles/futures), not callback-based.**

Callback-based APIs like `stream/on-close` force the use of atoms for coordination because:
1. Two independent callbacks (done + timeout) need to know about each other
2. Results from multiple callbacks must be aggregated somewhere
3. There's no way to "wait" for a callback - you need shared state to signal completion

The monadic pattern requires every async operation to return a handle that can be:
- Passed to `aio/then` for sequencing
- Collected with `aio/all` for parallel completion
- Raced with `aio/race` for timeout/cancellation

### Why NOT `aio/semaphore`

The spec previously proposed `aio/semaphore` for rate limiting. This is wrong for several reasons:

1. **Manual resource management** - `acquire`/`release` pairs are error-prone (what if you forget to release? what if an error occurs?)

2. **Wrong abstraction layer** - In Finagle, rate limiting is a filter that wraps a service:
   ```scala
   val rateLimited = new RateLimitFilter(10).andThen(myService)
   ```
   The filter handles acquire/release internally. Users don't touch semaphores.

3. **Doesn't fix the real problem** - Atoms exist because of callback-based APIs. Adding semaphores just adds another imperative primitive without fixing the underlying issue.

4. **Already implemented, should be removed** - The existing `aio/semaphore` implementation in `aio_combinators.c` should be deleted.

### Replacement Patterns

| Atom Usage | Replacement |
|------------|-------------|
| Counters | `aio/all` + reduce results |
| Cancellation flags | `aio/race` with timeout |
| Per-stream state | Return values from handle chains |
| Callback coordination | Handle-returning APIs (not callbacks) |
| Rate limiting | Filter/middleware (future work, not needed for atom removal) |

### New Builtin: `stream/closed`

**File:** `src/aio/http2/stream/aio_stream_builtins.c`

| Function | Signature | Description |
|----------|-----------|-------------|
| `stream/closed` | `stream` -> handle | Returns future that completes with `:closed` when stream closes |

This replaces the callback-based `stream/on-close`. Instead of:
```lisp
(stream/on-close stream (\ {} {(atom/set! closed true)}))
```

Use:
```lisp
(aio/race (list
  (stream/closed stream)
  (do-work-handle)))
```

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

Each test returns `{:status :pass}` or `{:status :fail :error msg}`.

### Refactored Timeout Handling

**Current:**
```lisp
(= {timed-out} (atom 0))
(aio/schedule aio timeout-ms (\ {} {(atom/set! timed-out 1) ...}))
```

**New:**
```lisp
(aio/race (list
  (aio/then (aio/sleep aio timeout-ms) (\ {_} {{:status :timeout}}))
  (aio/then (run-test test) (\ {r} {{:status :pass :result r}}))))
```

### Refactored Stress Tests

**Current (atoms for counters and coordination):**
```lisp
(def {connections-opened} (atom 0))
(def {active-connections} (atom 0))
...
(atom/add! connections-opened 1)
```

**New (collect results with aio/all):**
```lisp
; Each connection returns its metrics
(fun {run-connection aio id} {
  (aio/then (http2/client-request aio host port path)
    (\ {resp} {
      {:id id :events (count-events resp) :status :ok}}))})

; Collect all results
(aio/then
  (aio/all (map (\ {i} {(run-connection aio i)}) (range n)))
  (\ {results} {
    (def {total-events} (reduce + 0 (map :events results)))
    (def {total-conns} (len results))
    {:connections total-conns :events total-events}}))
```

For rate limiting (max N concurrent), use chunked execution rather than semaphores:
```lisp
; Run in batches of MAX_ACTIVE
(fun {run-batch aio batch} {
  (aio/all (map (\ {id} {(run-connection aio id)}) batch))})

(aio/then
  (aio/all (map (\ {batch} {(run-batch aio batch)}) (chunk ids MAX_ACTIVE)))
  aggregate-results)
```

### Deprecation Warning

Add to each atom builtin in `src/parser.c`:
```c
static valk_lval_t* valk_builtin_atom(valk_lenv_t* e, valk_lval_t* a) {
  VALK_WARN("atom is deprecated: use aio/all and aio/race instead");
  // ... existing implementation
}
```

### Files to Modify

| File | Change |
|------|--------|
| `src/aio/aio_combinators.c` | Remove `aio/semaphore*` builtins |
| `src/parser.c` | Remove atom builtins (Phase 5), update deprecation message |
| `src/modules/test.valk` | Refactor to use `aio/all` and `aio/race` |
| `test/test_sse_concurrency_short.valk` | Refactor to collect results via `aio/all` |
| `test/stress/test_sse_concurrency*.valk` | Same refactor |
| `test/test_aio_semaphore.valk` | Delete |
| `test/test_atom_builtins.valk` | Delete (Phase 5) |

### Phased Rollout

| Phase | Description | Breaking? |
|-------|-------------|-----------|
| 1 | Add `stream/closed`, remove `aio/semaphore*` | No |
| 2 | Refactor test framework to use `aio/all` + `aio/race` | No |
| 3 | Refactor stress tests | No |
| 4 | Add deprecation warnings to atoms | No (warnings only) |
| 5 | Remove atom builtins | **Yes** |

## Acceptance Criteria

### Phase 1: API Cleanup
- [ ] `stream/closed stream` returns future that completes when stream closes
- [ ] `aio/semaphore*` builtins removed from `aio_combinators.c`
- [ ] `test/test_aio_semaphore.valk` deleted
- [ ] `make build` succeeds
- [ ] `make test` passes

### Phase 2: Test Framework Refactor
- [ ] `src/modules/test.valk` uses `aio/all` instead of atoms for result collection
- [ ] `src/modules/test.valk` uses `aio/race` for timeout handling
- [ ] `grep -c "atom" src/modules/test.valk` returns 0
- [ ] All existing async test files pass without modification

### Phase 3: Stress Test Refactor
- [ ] `test/test_sse_concurrency_short.valk` uses `aio/all` for result collection
- [ ] `grep -c "atom" test/test_sse_concurrency_short.valk` returns 0
- [ ] `grep -c "atom" test/stress/test_sse_concurrency_short.valk` returns 0
- [ ] `grep -c "atom" test/stress/test_sse_concurrency.valk` returns 0
- [ ] All stress tests still validate concurrency (connections > 0, events > 0)

### Phase 4: Deprecation
- [ ] `build/valk -e '(atom 1)'` prints deprecation warning to stderr
- [ ] Deprecation warning does not break tests (warning only, not error)
- [ ] `make test` passes with warnings

### Phase 5: Removal
- [ ] `valk_atom_t` struct removed from `src/parser.c`
- [ ] All `valk_builtin_atom*` functions removed from `src/parser.c`
- [ ] Atom registrations removed from `valk_lenv_put_builtins`
- [ ] `test/test_atom_builtins.valk` deleted
- [ ] Atom error tests removed from `test/test_parser_errors.c`
- [ ] `build/valk -e '(atom 1)'` returns error "Unknown function 'atom'"
- [ ] `grep -r "atom" src/*.valk test/*.valk | grep -v "atomic" | wc -l` returns 0
- [ ] `make test` passes
