# Deprecate Atom Builtins

## Problem

The `atom` primitive provides mutable shared state that circumvents the monadic async API. Every current usage can be replaced with proper functional patterns:

| Atom Usage | Proper Alternative |
|------------|-------------------|
| Counters | `aio/all` + reduce results |
| Rate limiting | `aio/semaphore` (new) |
| Cancellation flags | `aio/race` with timeout |
| Per-stream state | Recursive `aio/then` chains |
| Callback coordination | Future-returning APIs |

Atoms encourage imperative patterns that are harder to reason about. In a Finagle-style monadic world, they are unnecessary.

## Current State

```c
// parser.c:4003-4063
typedef struct { _Atomic long value; } valk_atom_t;

// Builtins: atom, atom/get, atom/set!, atom/add!, atom/sub!
```

**Files using atoms:**
- `src/modules/test.valk` - 4 atoms for async test tracking
- `test/test_sse_concurrency_short.valk` - 6 atoms for metrics
- `test/stress/test_sse_concurrency_short.valk` - 6 atoms (duplicate)
- `test/stress/test_sse_concurrency.valk` - 6 atoms (duplicate)
- `test/test_atom_builtins.valk` - tests for atom API itself

---

## Phase 1: Add Missing Abstractions

Before removing atoms, provide alternatives that make them unnecessary.

### Task 1.1: Implement `aio/semaphore` builtins

**File:** `src/aio/aio_combinators.c`

Add three new builtins for async rate limiting:
- `aio/semaphore aio n` - create semaphore with n permits, returns handle
- `aio/semaphore-acquire sem` - returns future that completes when permit acquired
- `aio/semaphore-release sem` - release permit, returns nil

Implementation:
```c
typedef struct {
  valk_aio_system_t *sys;
  int max_permits;
  int available;
  // Queue of waiting handles
} valk_semaphore_t;
```

**Accept:**
- `make build` succeeds
- `make test` passes
- New test file `test/test_aio_semaphore.valk` with:
  - Basic acquire/release works
  - Acquiring when none available blocks until release
  - `aio/bracket` pattern works for auto-release

---

### Task 1.2: Implement `stream/closed` future

**File:** `src/aio/http2/stream/aio_stream_builtins.c`

Add builtin that returns a future completing when stream closes:
- `stream/closed stream` - returns handle that completes with `:closed` when stream closes

This enables `aio/race` instead of callback + atom coordination.

**Accept:**
- `make build` succeeds
- `make test` passes
- New test in `test/test_sse_builtins.valk`:
  - `stream/closed` returns handle
  - Handle completes when stream closes
  - Can race with other futures via `aio/race`

---

## Phase 2: Refactor Test Framework

Replace atoms in `src/modules/test.valk` with monadic patterns.

### Task 2.1: Refactor `test/run-async` to use `aio/all`

**File:** `src/modules/test.valk`

Current (imperative with atoms):
```lisp
(def {*test-async-pending-atom*} (atom 0))
(def {*test-async-passed-atom*} (atom 0))
...
(atom/add! *test-async-passed-atom* 1)
```

New (monadic):
```lisp
(fun {test/run-async aio tests opts} {
  (aio/then
    (aio/all (map (\ {t} {(test/run-one-async aio opts t)}) tests))
    (\ {results} {(test/summarize-results results)}))})
```

Each test returns `{:status :pass}` or `{:status :fail :error msg}`.

**Accept:**
- `make build` succeeds
- `make test` passes
- `grep -c "atom" src/modules/test.valk` returns 0
- All existing async test files still pass

---

### Task 2.2: Refactor per-test timeout handling

**File:** `src/modules/test.valk`

Current uses atom for timeout coordination:
```lisp
(= {timed-out} (atom 0))
(aio/schedule aio timeout-ms (\ {} {(atom/set! timed-out 1) ...}))
```

New uses `aio/race`:
```lisp
(aio/race (list
  (aio/then (aio/sleep aio timeout-ms) (\ {_} {{:status :timeout}}))
  (aio/then (run-test test) (\ {r} {{:status :pass :result r}}))))
```

**Accept:**
- `make build` succeeds
- `make test` passes  
- Test timeout still works (verify with `test/test_sse_async_timeout.valk`)
- No atom usage for timeout tracking

---

## Phase 3: Refactor Stress Tests

Replace atoms in SSE concurrency tests with result collection.

### Task 3.1: Refactor `test/test_sse_concurrency_short.valk`

**File:** `test/test_sse_concurrency_short.valk`

Current tracks 6 atoms: `connections-opened`, `connections-closed`, `events-received`, `errors-count`, `test-running`, `active-connections`.

New approach:
1. Use `aio/semaphore` for `active-connections` rate limiting
2. Use `aio/race` with timeout for `test-running` cancellation  
3. Collect request results via `aio/all`, compute metrics from list
4. Use recursive `aio/then` for per-stream `events-sent` counter

**Accept:**
- `make build` succeeds
- `make test` passes
- `grep -c "atom" test/test_sse_concurrency_short.valk` returns 0
- Test still validates SSE concurrency (connections opened > 0, events received > 0)

---

### Task 3.2: Refactor `test/stress/test_sse_concurrency_short.valk`

**File:** `test/stress/test_sse_concurrency_short.valk`

Same refactoring as Task 3.1.

**Accept:**
- `make build` succeeds
- `make test` passes
- `grep -c "atom" test/stress/test_sse_concurrency_short.valk` returns 0

---

### Task 3.3: Refactor `test/stress/test_sse_concurrency.valk`

**File:** `test/stress/test_sse_concurrency.valk`

Same refactoring as Task 3.1.

**Accept:**
- `make build` succeeds
- `make test` passes
- `grep -c "atom" test/stress/test_sse_concurrency.valk` returns 0

---

## Phase 4: Deprecation Period

Add warnings before removal.

### Task 4.1: Add deprecation warnings to atom builtins

**File:** `src/parser.c`

Add `VALK_WARN` to each atom builtin:
```c
static valk_lval_t* valk_builtin_atom(valk_lenv_t* e, valk_lval_t* a) {
  VALK_WARN("atom is deprecated: use aio/semaphore or aio/then chains");
  // ... existing implementation
}
```

**Accept:**
- `make build` succeeds
- `make test` passes (warnings don't break tests)
- Running `build/valk -e '(atom 1)'` prints deprecation warning to stderr

---

## Phase 5: Remove Atoms

After deprecation period, remove the implementation.

### Task 5.1: Remove atom builtins from parser.c

**File:** `src/parser.c`

Remove:
- `valk_atom_t` struct (line ~4003)
- `valk_builtin_atom` (line ~4007)
- `valk_builtin_atom_get` (line ~4016)
- `valk_builtin_atom_set` (line ~4026)
- `valk_builtin_atom_add` (line ~4039)
- `valk_builtin_atom_sub` (line ~4052)
- Registrations in `valk_lenv_put_builtins` (lines ~5177-5181)

**Accept:**
- `make build` succeeds
- `make test` passes
- `grep -c "atom" src/parser.c` returns 0 (excluding unrelated uses like "atomic")
- `build/valk -e '(atom 1)'` returns error "Unknown function 'atom'"

---

### Task 5.2: Remove atom test file

**File:** `test/test_atom_builtins.valk`

Delete the file entirely.

**Accept:**
- `make build` succeeds
- `make test` passes
- File does not exist

---

### Task 5.3: Remove atom error tests from parser_errors.c

**File:** `test/test_parser_errors.c`

Remove test functions:
- `test_atom_set_wrong_type` (line ~1195)
- `test_atom_add_wrong_type` (line ~1205)
- `test_atom_sub_wrong_type` (line ~1215)

**Accept:**
- `make build` succeeds
- `make test` passes
- `grep -c "atom" test/test_parser_errors.c` returns 0

---

## Acceptance Criteria (Full Spec)

### Phase 1 Complete
- [ ] `aio/semaphore`, `aio/semaphore-acquire`, `aio/semaphore-release` work
- [ ] `stream/closed` returns future
- [ ] Tests exist for new builtins

### Phase 2 Complete  
- [ ] `src/modules/test.valk` has zero atom usage
- [ ] All async test files still pass

### Phase 3 Complete
- [ ] All `test/*sse_concurrency*.valk` files have zero atom usage
- [ ] Stress tests still validate concurrency behavior

### Phase 4 Complete
- [ ] Deprecation warnings emitted when atoms used

### Phase 5 Complete
- [ ] Atom builtins removed from `parser.c`
- [ ] `test/test_atom_builtins.valk` deleted
- [ ] `test/test_parser_errors.c` atom tests removed
- [ ] `make test` passes with zero atom usage anywhere

---

## Verification Commands

```bash
# Count atom usage across codebase (should reach 0 by Phase 5)
grep -r "atom" src/*.valk test/*.valk test/stress/*.valk | grep -v "atomic" | wc -l

# Verify no atom builtins registered
grep "atom" src/parser.c | grep -v "atomic"

# Run full test suite
make test

# Run specific stress test
build/valk test/test_sse_concurrency_short.valk
```

---

## Notes

- **Ordering matters**: Phase 1 must complete before Phase 2-3 (need alternatives first)
- **Breaking change**: User code using atoms will break after Phase 5
- **Deprecation period**: Ship Phase 4 in one release before Phase 5
- The `atom/set` alias (without `!`) used in test code is also deprecated
