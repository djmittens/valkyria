# Deprecate Atom Builtins

## Overview

Remove the `atom` primitive from Valk to eliminate mutable shared state that circumvents the monadic async API. Every current atom usage can be replaced with proper functional patterns: `aio/all` for result collection, `aio/semaphore` for rate limiting, `aio/race` for cancellation, and recursive `aio/then` chains for per-stream state. This improves code clarity and enforces the Finagle-style monadic programming model.

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

Callback-based APIs like `http2/client-request` (which returns `nil` and invokes a callback) cannot be composed with `aio/all`, `aio/race`, or `aio/then`. The monadic pattern requires every async operation to return a handle that can be:
- Passed to `aio/then` for sequencing
- Collected with `aio/all` for parallel completion
- Raced with `aio/race` for timeout/cancellation

Existing callback-based APIs should be deprecated in favor of handle-returning equivalents.

### Replacement Patterns

| Atom Usage | Replacement |
|------------|-------------|
| Counters | `aio/all` + reduce results |
| Rate limiting | `aio/semaphore` (new builtin) |
| Cancellation flags | `aio/race` with timeout |
| Per-stream state | Recursive `aio/then` chains |
| Callback coordination | Handle-returning APIs (not callbacks) |

### New Builtin: `aio/semaphore`

**File:** `src/aio/aio_combinators.c`

| Function | Signature | Description |
|----------|-----------|-------------|
| `aio/semaphore` | `aio n` → handle | Create semaphore with n permits |
| `aio/semaphore-acquire` | `sem` → future | Returns future that completes when permit acquired |
| `aio/semaphore-release` | `sem` → nil | Release permit |

**Implementation:**
```c
typedef struct {
  valk_aio_system_t *sys;
  int max_permits;
  int available;
  // Queue of waiting handles
} valk_semaphore_t;
```

### New Builtin: `stream/closed`

**File:** `src/aio/http2/stream/aio_stream_builtins.c`

| Function | Signature | Description |
|----------|-----------|-------------|
| `stream/closed` | `stream` → handle | Returns future that completes with `:closed` when stream closes |

This enables `aio/race` instead of callback + atom coordination.

### Refactor: `http2/client-request` to Return Handle

**File:** `src/aio/http2/aio_http2_client.c`

| Function | Old Signature | New Signature |
|----------|---------------|---------------|
| `http2/client-request` | `aio host port path callback` → nil | `aio host port path` → handle |
| `http2/client-request-with-headers` | `aio host port path headers callback` → nil | `aio host port path headers` → handle |

**Rationale:** Callback-based APIs cannot be composed with `aio/all`, `aio/race`, or `aio/then`. The callback parameter is removed; instead the function returns a handle that completes with the response.

```lisp
; Old (callback-based, incompatible with aio/all):
(http2/client-request aio host port path (\ {resp} {...}))

; New (monadic, composable):
(aio/then (http2/client-request aio host port path)
  (\ {resp} {...}))

; Collect results from multiple concurrent requests:
(aio/then
  (aio/all (map (\ {url} {(http2/client-request aio host port url)}) urls))
  (\ {responses} {(process-responses responses)}))
```

**Implementation:** Return the async handle instead of nil:

```c
valk_lval_t *valk_builtin_http2_client_request(valk_lenv_t *e, valk_lval_t *a) {
  // ... validation (no callback parameter) ...
  valk_async_handle_t *handle = valk_async_handle_new(sys, e);
  // Connect and send request, complete handle with response
  return valk_lval_handle(handle);
}
```

### Refactored Test Framework

**Current (imperative):**
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

### Deprecation Warning

Add to each atom builtin in `src/parser.c`:
```c
static valk_lval_t* valk_builtin_atom(valk_lenv_t* e, valk_lval_t* a) {
  VALK_WARN("atom is deprecated: use aio/semaphore or aio/then chains");
  // ... existing implementation
}
```

### Files to Remove (Phase 5)

| File | Content |
|------|---------|
| `src/parser.c` lines ~4003-4063 | `valk_atom_t` struct and all atom builtins |
| `src/parser.c` lines ~5177-5181 | Builtin registrations |
| `test/test_atom_builtins.valk` | Entire file |
| `test/test_parser_errors.c` lines ~1195-1215 | Atom error tests |

### Phased Rollout

| Phase | Description | Breaking? |
|-------|-------------|-----------|
| 1 | Add `aio/semaphore` and `stream/closed` | No |
| 2 | Refactor test framework | No |
| 3 | Refactor stress tests | No |
| 4 | Add deprecation warnings | No (warnings only) |
| 5 | Remove atom builtins | **Yes** |

## Acceptance Criteria

### Phase 1: New Abstractions
- [ ] `aio/semaphore aio n` creates semaphore with n permits
- [ ] `aio/semaphore-acquire sem` returns future that completes when permit acquired
- [ ] `aio/semaphore-release sem` releases permit and returns nil
- [ ] `stream/closed stream` returns future that completes when stream closes
- [ ] `http2/client-request aio host port path` returns handle (remove callback param)
- [ ] `http2/client-request-with-headers aio host port path headers` returns handle
- [ ] `test/test_aio_semaphore.valk` exists with tests for acquire/release/blocking
- [ ] `test/test_sse_builtins.valk` has tests for `stream/closed`
- [ ] All existing `http2/client-request` callers updated to use `aio/then`
- [ ] `make build` succeeds
- [ ] `make test` passes

### Phase 2: Test Framework Refactor
- [ ] `src/modules/test.valk` uses `aio/all` instead of atoms for result collection
- [ ] `src/modules/test.valk` uses `aio/race` for timeout handling
- [ ] `grep -c "atom" src/modules/test.valk` returns 0
- [ ] All existing async test files pass without modification

### Phase 3: Stress Test Refactor
- [ ] `test/test_sse_concurrency_short.valk` uses `aio/semaphore` for rate limiting
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
