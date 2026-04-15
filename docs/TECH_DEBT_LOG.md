# Tech Debt Log

Issues identified during the 2026-04-14 debugging session. Ordered by isolation
(top = most isolated, easiest to ship safely). Each entry has enough context to
pick up cold.

Status legend: `[ ]` open, `[x]` done, `[~]` in progress.

---

## [ ] 1. Error propagation at call boundary

**Symptom:** functions that recurse on list-shaped input (e.g. `sel/build-nested-walk`)
infinite-loop when passed an error value. `(nil? error)` returns false,
`(tail error)` returns another error, so termination never fires. Scratch arena
fills with garbage from the loop; observed as "GC thrashing" but actually just
a runaway evaluator.

**Desired fix:** in the argument-evaluation path (before invoking a function),
if any evaluated arg is `LVAL_ERR`, return that error immediately — do not
call the function.

**Attempt 1 (reverted):** Added `LVAL_FLAG_ACCEPTS_ERR` + short-circuit for
all functions at call site. Broke 43 tests — pervasive code flows errors
through print/str/=/def as values.

**Attempt 2 (reverted — efd62bb/086ab19):** Narrower short-circuit only
for user-defined lambdas (`fun.builtin == NULL`), C builtins untouched.
Still broke 72 tests. The problem: `parse "(unclosed"` returns a **list
containing an error as an element** (not an error itself). Code that walks
ASTs (e.g. `ref/walk-exprs`) recurses into list elements and the embedded
error hits user lambdas, which now return the error instead of their
graceful fallback. Existing tests expect `nil` in those cases.

**Why intuitive approaches keep failing:** "error as value" is deeply baked
into how AST walks propagate — errors live inside lists and get processed
recursively. Any short-circuit at the call site changes the contract for
helper lambdas.

**Refined approach for next attempt:**
- Don't short-circuit at call site. Instead, make the specific *looping
  primitives* (`tail`, `head`, `nil?`, `len`) return an error when given
  an error arg. Then the USER lambda that calls `(tail err)` gets back
  an error, but:
  - `(nil? err)` returns err → `(if err {then} {else})` propagates err
    (since if already short-circuits on err condition — verified in
    CONT_IF_BRANCH)
  - Loop terminates via if propagation
- Alternative: make `nil?` return truthy for error (1). Then `(if (nil?
  err) {base} {recurse})` takes the base branch, loop terminates with
  the function's graceful fallback value.

The `nil?` option is more compatible — the existing user code expects nil
on error inputs, and a truthy `nil?` triggers that path.

But `nil?` is user-defined in prelude (`(fun {nil? x} {== x nil})`). To
change its behavior for errors, either:
- Convert to C builtin that returns 1 for errors
- Change `==` to return truthy when comparing error and nil

Either change is small but needs careful test-passing verification.

**Files:** `src/lval.c` (`valk_lval_eq`) or new C `nil?` builtin in
`src/builtins_io.c` or similar.

**Risk:** medium. Either change touches widely-used operators.

**Effort:** ~15 LOC + test run.

**Blocks:** nothing.

---

## [x] 2. AST parse cache (6929143)

**Symptom:** every valk subprocess re-parses the entire prelude + stdlib +
whatever files it loads. `valk-check.valk` over the project (168 files) takes
~45s — most of that is re-parsing files already seen. Test runner spawns ~123
Valk child processes, each paying the same startup cost.

**Fix:** in `src/builtins_io.c` (or wherever `valk_parse_file` lives), add an
LRU-bounded cache keyed by `realpath + st_mtime`. Store the raw parsed AST
(before macro expansion / FQN rewrite). On retrieval, `valk_lval_copy` the
cached AST so callers can mutate freely. Register the cache as a GC root
visitor so cached ASTs survive collections.

**Fix shipped (6929143):** LRU cache of 256 entries, mtime invalidation,
GC root visitor. The gotcha from the earlier attempt was solved by deep-
cloning (not `valk_lval_copy`-shallow) on retrieval — previous approach
shared CONS-cell children with the cached original, so `valk_lval_pop`
and in-place rewrites from one load corrupted subsequent loads. Loader
now goes `load` → `realpath` → `parse_file_cached` → deep-clone → mutate
freely.

compile/process (used by valk-check) still parses fresh — it takes text,
not a path, so path-keyed cache doesn't apply. Separate optimization
opportunity if/when needed.

Baseline: 4102 pass / 18 pre-existing fail / 15.9s.

---

## [ ] 3. `make check` dominates `make test` wall time

**Symptom:** `make test` runs `make check` (valk-check lint over whole tree)
before the actual test runner. Currently ~45s of the 67s total.

**Fix:** likely falls out of (2) — valk-check reparses everything. Once the
parse cache is in place, measure again. If still slow, look at valk-check's
own file-iteration pattern — maybe it's doing a full type-check per file with
no shared state.

**Files:** `scripts/valk-check.valk`, `stdlib/diag/*.valk`.

**Depends on:** (2) probably.

**Effort:** unknown until (2) lands.

---

## [ ] 4. Pre-existing test failures (2 suites, 18 tests)

**Symptom:** `test/lang/test_json.valk` — 2 assertions fail
(`encode-option-some-unwraps`, `is-option-some-too-many-args`). No stdout/stderr
output — test framework captures empty on assertion failure.
`test/lsp/test_lsp_helpers.valk` — 16 assertions fail (make-lsp-diag,
ref-to-lsp-location, symkind-to-completion-kind, several snippet / completion
helpers).

**Verified pre-existing:** these fail on `e87dab5` (pre-session HEAD) too. Not
caused by recent work.

**Fix:** read each failing test, compare expected vs actual, fix either the
test or the code being tested. These are isolated to specific tests — no
shared infrastructure risk.

**Files:** `test/lang/test_json.valk`, `test/lsp/test_lsp_helpers.valk`, plus
whatever they call into.

**Risk:** low.

**Effort:** unknown, likely 1–4 hours per suite.

---

## [ ] 5. Async exec / worker thread exhaustion

**Symptom:** `valk_builtin_exec` is synchronous — `poll(fds, 2, -1)` and
`waitpid` block the worker thread until the child produces output and exits.
With 12 aio workers, 12 blocked in exec means zero throughput. Steady-state
CPU during `run-tests.valk` hits ~2–3 cores of 12 despite having 189 tasks to
dispatch. Shell-forked parallel test binaries complete in 28ms; same 12 via
the runner take ~1.3s each — suggests VM-level lock contention during output
collection (GC/alloc serialization on `valk_lval_str`).

**Fix options:**
- (a) `uv_spawn` + `uv_read_start` — proper async through libuv. Worker
      returns immediately after dispatch, callback completes the task. Big
      refactor, integrates with aio combinator infrastructure.
- (b) Quick win: run `waitpid` / `poll` in a detached pthread, return a
      pending handle, let aio mechanism poll. Less invasive but still
      blocks a kernel thread per exec.

**Files:** `src/builtins_file.c` (the `exec` builtin).

**Risk:** medium-high — threading + subprocess + GC interaction.

**Effort:** option (a) ~1 day, option (b) a few hours.

---

## [ ] 6. Module system simplification

**Symptom:** `src/module.c`, `valk_module_rewrite`, pre-registration pass,
module cache keyed on tree — all working together to implement auto-prefixing
of symbol names. The 2026-04-14 session's `sel/find-ranges` hang was caused
by an interaction: cache hit skipped child-module creation but the FQN
rewriter had pre-registered an empty child, which then shadowed the real
module during name resolution.

**Root design question:** the user wants this reimplemented as a macro — the
loader sets a per-file `*module-prefix*` var, the `fun`/`def` macros consume
it. C side becomes trivial.

**Gotcha hit in earlier attempt:** internal refs within a file require either
(a) the rewriter knowing all defs in the file, or (b) a file-scoped local env
so `(fun {foo ...})` creates both a local `foo` binding (for internal calls)
and a global `prefix/foo` binding. Pure C simplification (keep rewriter, drop
tree) broke `test_lsp_integration` — a C test that exec's a child valk LSP
server — didn't finish diagnosing.

**Prerequisites before touching this again:**
1. Read every file that uses `valk_module_t`, `valk_mod_*`, `valk_module_rewrite`,
   `resolve_qualified`, `compile/process`. End-to-end data-flow trace.
2. Understand why `test_lsp_integration`'s child hangs when load semantics
   change. This is probably a stdin-blocking issue for the LSP server's main
   loop, but needs verification.
3. Write a spec doc covering the semantic model: local vs global, nested
   prefixes (lsp/nav vs lsp + nav), what `(type ...)`, `(sig ...)`, `(macro ...)`
   each expand to, how unqualified refs resolve.

**Depends on:** (1) would prevent the old bug class from mattering during
migration — errors from unresolved symbols would propagate cleanly instead of
infinite-looping.

**Risk:** high. Big blast radius, many consumers.

**Effort:** 1–2 days focused.

---

## [ ] 7. Test runner throughput / first-batch 4.8s wall times

**Symptom:** under `run-tests.valk`, the first batch of 12 C tests all report
~4.8s wall time despite completing in milliseconds when run directly. Likely
VM-level lock contention on `valk_lval_str` or similar during output
collection — 12 workers allocating simultaneously hit the same lock.

**Fix:** profile where the lock is held. Candidates: GC pause coordination,
heap allocator lock, macro env lookup during `exec` builtin result
construction. If it's GC coordination, the fix is probably to run `exec` with
a scratch arena instead of the heap.

**Depends on:** useful tooling / profile data. Not currently blocking
progress but is the real answer to "why aren't tests faster."

**Risk:** investigation first, then depends on what we find.

---

## Session context (delete when no longer useful)

Current branch: `lang/llvm-backend`
HEAD: `5cf0118` — fixes `sel/find-ranges` double-load module bug + zombie
subprocess on parent death.

Working test baseline:
- `make test` — 67s wall (45s valk-check + 16s test runner + other overhead)
- 4102 tests pass, 18 fail (all pre-existing — 2 in test_json, 16 in test_lsp_helpers)

Don't touch before reading: `src/module.c`, `src/macro.c` (rewriter),
`src/builtins_io.c` (`load_eval_file`), `src/aio/aio_comb_pmap.c`.
