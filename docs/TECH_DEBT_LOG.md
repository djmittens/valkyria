# Tech Debt Log

Issues identified during the 2026-04-14 debugging session. Ordered by isolation
(top = most isolated, easiest to ship safely). Each entry has enough context to
pick up cold.

Status legend: `[ ]` open, `[x]` done, `[~]` in progress.

---

## [~] 1. Error propagation at call boundary — DEFERRED after 4 attempts

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

## [~] 3. `make check` dominates `make test` wall time — PARTIAL via #2

**Symptom:** `make test` runs `make check` (valk-check lint over whole tree)
before the actual test runner. Currently ~45s of the 67s total.

**Status:** parse cache (#2) took this from ~45s to 33–42s (variable). More
is possible but diminishing returns:
- `compile/process` (valk-check's per-file workhorse) takes `text + prefix`,
  not a path, so path-keyed cache doesn't apply. Would need a separate
  `compile/process-file` that caches fully-processed ASTs by `(path,
  mtime, prefix)`. ~30 LOC + change in valk-check.valk.
- The actual cost after parsing is macro-expand + module-rewrite. Both
  are linear in file size. Not obvious where to shave without caching
  post-processed ASTs too.

**Files if resumed:** `src/builtins_io.c` (new builtin),
`scripts/valk-check.valk` (call site).

**Effort:** ~1 hour.

**Blocks:** nothing.

---

## [~] 4. Pre-existing test failures — 14/18 fixed (be41392, 1ac18f7)

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

## [~] 7. Test runner throughput — partially improved via #2

**Was:** first batch of 12 C tests all reported ~4.8s wall despite
completing in milliseconds when run directly.

**Now:** first batch shows some tests at 0.0s, ~4 at 1.1s, one at 4.5s
(test_llvm_codegen — genuinely heavy). The uniform 4.8s cluster is gone
but a smaller clustering remains. Parse cache (#2) didn't help child
subprocesses (caches are per-process) but apparently helped the runner
itself.

**Remaining cost (~1s per test in the first batch):** still likely VM lock
contention during `exec` output collection. `valk_lval_str` allocates
through the GC heap (src/lval.c:73 intern-table lock, src/gc_heap.c
page-list lock). 12 workers reading pipes and allocating strings
concurrently hit these.

**Fix path:** run `exec` under the scratch arena allocator rather than
the heap — `VALK_WITH_ALLOC(scratch) { ... exec body ... }` around the
poll/read loop and `valk_lval_str` calls. Scratch is per-thread, lock-
free. Then evacuate the result lvals to heap only at return. ~20 LOC.

**Files:** `src/builtins_file.c` (exec builtin).

**Risk:** low-medium — scratch-to-heap evacuation is well-tested in the
codebase for similar patterns.

**Effort:** 1–2 hours + measure.

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
