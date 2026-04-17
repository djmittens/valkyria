# Tech Debt Log

Issues identified during the 2026-04-14 debugging session. Ordered by isolation
(top = most isolated, easiest to ship safely). Each entry has enough context to
pick up cold.

Status legend: `[ ]` open, `[x]` done, `[~]` in progress.

---

## [x] 1. Error propagation at call boundary (a144182)

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

**Attempt 3 (reverted, not committed):** Made `nil?` a C builtin that
returns 1 for LVAL_ERR in addition to LVAL_NIL, so user lambdas with
`(if (nil? l) {base} {... (tail l) ...})` terminate when handed an error.
Passed the repro test. Broke `test_lsp_integration`: LSP code uses
`(if (nil? doc) {send-no-doc} {process doc})` and now errors route to
the "no-doc" path instead of being surfaced by downstream processing.
Same test passed on 5cf0118 (pre-change baseline).

**Attempt 4 (reverted):** Pure BYOL semantics — unconditional
short-circuit in `CONT_COLLECT_ARG`, no opt-outs. This IS the correct
design per Build Your Own Lisp:

```c
/* Error propagation: if any child is an error, return it */
for (int i = 0; i < v->count; i++) {
    if (v->cell[i]->type == LVAL_ERR) { return lval_take(v, i); }
}
```

The user pointed this out — BYOL was always the answer, the scope of
regressions is the size of the bug surface, not a reason to back off.

**Scope of required migration:**
1. Test framework (stdlib/test/test.valk) — `foldl *test-run-one-ctx*
   ctx tests` needs to explicitly catch errors from each test case so a
   single failure doesn't abort the foldl chain. Maybe 10 LOC.
2. LSP code (scripts/lsp/*.valk) — `lsp/get-text-pos`,
   `lsp/get-word-ctx`, and other walkers assume `parse` returns
   something list-shaped they can iterate. `parse` of invalid input
   actually returns `(Error: ...)` nested in a list. Under BYOL, as
   soon as such an error element propagates to a user lambda through
   `(head ast)`/`(tail ast)`, the whole call chain fails. Each site
   needs `(if (error? x) {handle} {continue})` guards. Maybe 30–50
   sites.
3. Type transform / macro expansion — needs to handle errors
   surfacing from `parse` gracefully.
4. Various small test files that rely on errors flowing through
   `print` etc.

**In the meantime:** the specific `sel/find-ranges` / `sel/build-nested-walk`
infinite-loop case is already prevented by the module-load fix in
5cf0118 (the errors that used to flow in as inputs come from a
now-fixed code path). So the original symptom is gone; the class of
bug remains latent.

**Ready-to-apply diff** (when the migration is scheduled) — just
uncomment in `src/eval.c` `CONT_COLLECT_ARG`:
```c
if (LVAL_TYPE(value) == LVAL_ERR) {
  free(frame.collect_arg.args);
  goto apply_cont;  // propagate
}
```

**Effort for full migration:** 1–2 days dedicated.

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

## [x] 3. `make check` dominates `make test` wall time — PARALLELIZED

**Symptom:** `make test` runs `make check` (valk-check lint over whole tree)
before the actual test runner. Was ~32s (pre-optimization), now ~4.7s.

**Status (2026-04-17):** Shipped option (a) — parallelize validation via
`aio/pmap`. Phase 2 (validation) now runs 4 workers over all files; each
worker has its own scratch arena so per-thread GC pressure is 1/4 of the
single-threaded case. DB is read once in the master thread into preloaded
caches (`known-set`, `symdb-type-keys`, `arity-cache`) passed as closure
captures — workers do zero sqlite IO, sidestepping the single-threaded
sqlite handle constraint.

**Result:** `time make check` = 4.7s wall / 11.6s user @ 248% CPU (from 32s).
7× faster; full test suite still at 190 suites / 4143 tests / 0 failures.

**Key pieces:**
- `stdlib/diag/validate-walk.valk` — added `vd/validate-preloaded` taking
  caches as args instead of looking up in DB.
- `scripts/valk-check.valk` — added `check/validate-file-parallel` (worker),
  `check/aggregate-results` (serial reducer), `check/validate-all-parallel`
  (pmap orchestrator). Main starts aio system with 4 threads.

---

## [x] 4. Pre-existing test failures — fully fixed (be41392, 1ac18f7, 499bc3d)

All 18 original pre-BYOL failures resolved. Net at the BYOL ship-point:
14 more passes than at the start. (Subsequent BYOL migration introduced
a new class of failures; see #8.)

---

## [x] 8. BYOL migration — fully resolved (all 189 suites pass)

After BYOL shipped (#1), the call-boundary short-circuit surfaced ~85
tests that depended on errors silently flowing through builtin/user
function calls. Each failure points at a real bug in user code that was
masked by the old behavior. The pattern is always one of:

- `(if (cond-fn x) {then} {else})` where `cond-fn` returns an error and
  pre-BYOL flowed through to `if`'s false branch; under BYOL the error
  reaches `if`'s condition check and short-circuits the whole if.
- `(some-fn (maybe-erroring-call x))` where `some-fn` is a user lambda
  that doesn't check for error and uses the value as if valid.
- AST-walking code that recurses on `(head x)`/`(tail x)` where x can
  contain errors as elements.

**Final state:** All 189 suites pass, 4138 tests, 0 failures.

The last two failures were in `test_lsp_hints`:
- `field-access-hint-from-ctor` and `field-access-from-function-return-type`
- Root cause: two mismatched bracket sequences in `scripts/lsp/hints-fields.valk`
  introduced when adding field-access hint support. An extra `}` in
  `hint/vt-scan-binding` (offset 6849) and a swapped `})` vs `)}` in
  `hint/fa-try-binding` (offset 13817) caused those functions and all
  subsequent definitions to silently fail to load. Fixed by correcting
  the closing sequences on lines 208 and 416.

**Effort:** ~1 hour per suite, 9 suites = ~1 day total.

**Blocks:** nothing — failures are isolated.

**Original symptoms:**
- `test/lang/test_json.valk` — 2 `Option::Some`-unwrap tests. **Fixed by
  be41392** (type transform was over-eagerly rewriting fully-qualified
  {Type::Ctor ...} qexprs into the internal tagged form, producing a
  double-wrapped structure).
- `test/lsp/test_lsp_helpers.valk` — 16 calls to helpers by short name.
  **12 fixed by 1ac18f7** (added (def) aliases from short names to the
  module-prefixed bindings).

**Remaining 4 failures in test_lsp_helpers:**
- `symkind-to-completion-kind`
- `make-sym-completion-item-with-sig`
- `sig-extract-name`
- `sig-extract-name-empty`

The shared cause: `sig/extract-name` lives at top level (its name contains
`/` so the module rewriter leaves it alone), but its body calls
`scan-word-end` unqualified. `scan-word-end` was defined in symdb.valk and
got prefixed to `lsp/symdb/scan-word-end`. The cross-module reference
fails at call time. This is a general module-system issue — the rewriter
only qualifies refs that the *same file* defined.

**To finish this:** fix the cross-module reference resolution so a
function in one file can call a function in a sibling module without
writing the full path. Could be done by:
- Walking up the module tree at lookup time (what the old
  `resolve_qualified` did — but we ripped that out? actually still there)
- Or having the rewriter consult a global symbol table.

**Files:** `src/macro.c` (rewriter), `src/module.c`.

**Risk:** medium. Touches module system.

**Effort:** 2–4 hours focused.

---

## [x] 5. Async exec / worker thread exhaustion — `aio/exec` shipped

**Was:** `valk_builtin_exec` is synchronous — `poll(fds, 2, -1)` and `waitpid`
block the worker thread until the child produces output and exits. With 12
aio workers, 12 blocked in exec means zero throughput.

**Fix:** Added `aio/exec` builtin in `src/builtins_file.c` — `uv_spawn` +
`uv_read_start` on loop 0. Returns an async handle immediately; subprocess
output is accumulated by libuv read callbacks, and the handle completes when
the process exits AND both pipes hit EOF. Five test cases (simple echo,
non-zero exit, stderr capture, spawn failure, 10-way parallel) in
`test/aio/test_aio_exec.valk`, all pass.

**Subtle bugs squashed:**
- `LVAL_ASSERT_TYPE` macro expands with an internal `for (u64 i = 0; ...)`
  that shadows the caller's `i`. Re-evaluating `valk_lval_list_nth(a, i)`
  inside the macro fetches element 0 of arg list. Fix: extract arg to a
  local var before the macro call. Applies wherever a caller uses `i` at
  the macro call site and passes an index-dependent expression.
- `uv_spawn` failure path leaves the `uv_process_t` handle *initialized and
  registered in the loop* even though spawn didn't succeed. Must close the
  process handle alongside the pipes, otherwise loop shutdown walks a stale
  handle whose `data` points to freed memory → SEGV in `__aio_uv_walk_close`
  when a later test stresses the same loop.

**Note:** the original sync `exec` is unchanged — existing users keep the
blocking semantics. The call site in the parallel test runner can be
migrated to `aio/exec` separately.

---

## [~] 6. Module system simplification — **prereqs done; implementation deferred**

**Symptom:** `src/module.c`, `valk_module_rewrite`, pre-registration pass,
module cache keyed on tree — all working together to implement auto-prefixing
of symbol names. The 2026-04-14 session's `sel/find-ranges` hang was caused
by an interaction: cache hit skipped child-module creation but the FQN
rewriter had pre-registered an empty child, which then shadowed the real
module during name resolution.

**Prereq status (2026-04-17):** all three prereqs from the original entry
are now complete; spec lives at `docs/MODULE_SYSTEM_REFACTOR.md`. Key
findings:

- **Hang hypothesis (stdin-blocking) REFUTED.** Actual mechanism is
  *silent handler failure*: when rewrite misses a prefix, the handler
  symbol is unbound, LSP reader callback returns `LVAL_ERR`, error is
  logged to stderr but never propagated as a JSON-RPC response. Parent's
  `MSG_TIMEOUT_MS = 5000` fires. Fix is independent of the refactor — a
  ~5-line change in `src/builtins_pipe.c` around line 341 to emit a
  `window/logMessage` notification would make failures loud during
  development.

- **Pure-macro approach hits two HIGH-risk walls:**
  1. **Sibling resolution.** `scripts/lsp/nav.valk` calls
     `(analysis/line-col->offset …)`. Today the rewriter walks up the module
     tree from `lsp/nav` → `lsp` → finds child `analysis`. Without the tree,
     a `*module-prefix*` var alone cannot resolve siblings. Options: force
     full-qualification everywhere (breaking ~30 sites), or keep a flat
     path→prefix map at the Valk level (rebuilding half the system).
  2. **Macro scope isolation.** Macros evaluate in the global macro env
     (`src/builtins_io.c:195-198`), *before* module rewrite. `fun` in
     prelude generates `def` forms without access to `*module-prefix*`.
     Threading the prefix through the macro env means either a special
     evaluator mode or a post-expansion rewrite pass — at which point the
     C simplification vanishes.

**Options from spec doc:**
- A. Breaking change: require full-qualification at every cross-file
  reference. Ship a codemod for `scripts/lsp/*.valk`.
- B. Flat path→prefix registry + macro-accessible. Reduces C code
  modestly but not trivially.
- C. Defer the refactor; ship only the LSP error-propagation fix.

**Recommendation:** Option C. The module system works today (all 190
suites pass); this refactor is architectural, not correctness. Attempting
it without a chosen path (A or B) risks the same class of regression that
derailed the 2026-04-14 attempt.

**Risk:** high. Big blast radius, many consumers.

**Effort:** 1–2 days focused — once Option A/B is decided.

---

## [x] 7. Test runner throughput — scratch-arena refactor applied

**Was:** first batch of 12 C tests all reported ~4.8s wall despite
completing in milliseconds when run directly.

**Now:** first batch shows some tests at 0.0s, ~4 at 1.1s, one at 4.5s
(test_llvm_codegen — genuinely heavy). The uniform 4.8s cluster is gone
but a smaller clustering remains. Parse cache (#2) didn't help child
subprocesses (caches are per-process) but apparently helped the runner
itself.

**What shipped:** exec builtin's result-building phase now explicitly wraps
lval allocation in `VALK_WITH_ALLOC((void*)scratch)` and evacuates the
returned qlist to heap. Also switched to `valk_lval_str_n` so subprocess
output containing embedded NULs is preserved (was previously truncated by
`valk_lval_str`'s internal strlen). Removed the now-redundant null-
termination of the read buffers.

**Measured impact:** 16.1s test-suite wall time — same as baseline. In the
aio pmap path, exec was already running under scratch (via
`aio_task_queue.c`'s `__run_task_in_scratch`), so the refactor is
effectively a no-op on the hot path. It's defensive correctness: ensures
exec's return is heap-allocated regardless of caller, and handles binary
subprocess output correctly.

**Remaining throughput ceiling:** workers still block in `poll(fds, 2, -1)`
and `waitpid` — that's item #5 (uv_spawn), the real fix for parallel
throughput.

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
