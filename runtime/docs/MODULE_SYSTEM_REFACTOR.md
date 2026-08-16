# Module System Refactor — Spec & Risk Analysis

Status: **design draft**, not yet scheduled for implementation.
Prereqs for item #6 in `TECH_DEBT_LOG.md`.

Note: this analyses a narrower "pure macro" proposal. The broader target model
(file-as-`do`, explicit resolution order, nesting) is in
[MODULE_REFACTOR_INTENT.md](MODULE_REFACTOR_INTENT.md).

## Goal

Replace the current C-side auto-prefixing module implementation with a simpler
model that leans on macros + a lexically-scoped `*module-prefix*` variable.
C side should shrink; behavior should remain identical for all existing LSP,
prelude, and test code paths.

## Current system (summary)

Three-pass load in `eval_loaded_ast()` (`runtime/src/builtins_io.c:186-279`):

1. **Pass 1 — macro expansion.** Every `(macro NAME BODY)` in the file
   evaluates in the macro env. Other forms get expanded if they match a
   known macro. This is global, not module-scoped (`runtime/src/builtins_io.c:195-204`).
2. **Pass 1.5 — child pre-registration.** Walks the AST for nested
   `(load "path")` forms and pre-creates child modules so the rewriter can
   see them. Honors the module cache to avoid shadowing ready modules
   (`runtime/src/builtins_io.c:228-230`, fix from 5cf0118).
3. **Pass 2 — FQN rewrite.** `valk_module_rewrite` (`runtime/src/macro.c:289-312`)
   walks the AST and qualifies unqualified defs + call sites:
   - `(def {foo} …)` → `(def {pkg/foo} …)` if the file's module owns `foo`.
   - Unqualified reference `foo` → `pkg/foo` if `valk_mod_get(cur, "foo")`.
   - Qualified reference `analysis/foo` → canonicalized via `resolve_qualified`
     (`runtime/src/macro.c:162-185`), which walks up the module tree to find the
     first ancestor with a child named `analysis`.

Data structures (`runtime/src/module.h:8-19`): a global tree of `valk_module_t`,
each with a list of `def_names` and `def_vals`. Current module is TLS
(`g_current_mod`, `runtime/src/module.c:7-8`).

## Proposed system

- Load sets a dynamic variable `*module-prefix*` on entry, restores on exit.
- `fun` / `def` macros consume `*module-prefix*` to produce qualified names
  at expansion time.
- No pre-registration pass, no module tree, no FQN rewrite.

## What this simplification can handle

- **Local defs.** `(fun {foo x} …)` in `pkg.valk` expands to
  `(def {pkg/foo} (\ {x} …))`. Symbol goes into root env under `pkg/foo`.
- **Already-qualified references.** `(pkg/foo x)` needs no rewrite at all.
  Evaluator walks root env chain, finds binding if loaded in correct order.

## Where the simplification breaks (from data-flow trace)

### HIGH-risk: Sibling resolution (Risk #5)

`lsp/nav.valk` calls `(analysis/line-col->offset …)`. Today the
rewriter walks up from `lsp/nav` to `lsp`, finds child `analysis`, produces
`lsp/analysis/line-col->offset`. Without the module tree, the macro layer
has no way to know that "analysis" in this file's lexical scope should
resolve to a sibling `lsp/analysis`. Options:

- (a) Require every cross-module reference to be fully qualified
  (`lsp/analysis/line-col->offset`). Works, but verbose and a breaking
  change for ~30 call sites in `lsp/*.valk`.
- (b) Keep a lightweight directory map (path → prefix) and have a *macro*
  do the sibling lookup. The macro still needs enough static info to walk
  siblings — essentially a shadow of the module tree, but Valk-level.
- (c) Hybrid: strip pre-registration, keep `resolve_qualified` as a stand-alone
  helper over a flat map rather than a tree. Simpler than today but not as
  simple as "pure macro".

### HIGH-risk: Macro scope isolation (Risk #1)

`(macro ...)` forms evaluate in the global macro env (`runtime/src/builtins_io.c:195-198`),
*before* rewrite. That env has no access to `*module-prefix*` unless we
thread it through the macro evaluator explicitly. Prelude's `fun` macro
(`stdlib/prelude.valk:6-7`) is the critical case: it generates `def` forms.
If `fun` expansion happens before `*module-prefix*` is bound, generated
defs stay unqualified. Fix: either (i) make `*module-prefix*` visible from
macro env, or (ii) post-process macro output through a second rewrite
pass — at which point we've rebuilt half the current system.

### MEDIUM-risk: Nested loads (Risk #2)

Pass 1.5 exists specifically so the rewriter can see children that haven't
been loaded yet. If a parent file references a not-yet-loaded child's
symbol, today's rewriter pre-creates the child stub. Without it, the
symbol is unqualified at expansion time — and if `*module-prefix*` is only
the *current* file's prefix, child references won't get rewritten.
Workaround: enforce that children are always loaded before parents
reference them (most LSP files already do this), but it's a silent contract.

### MEDIUM-risk: `sig`/`type` qualification (Risk #4)

`(sig 'foo {-> Num Str})` in `analysis.valk` currently gets rewritten to
`(sig 'lsp/analysis/foo …)` by Pass 2, then consumed by `type_transform`.
Without the rewrite pass, `sig` needs to know its own module at macro-
expansion time. Doable via the same `*module-prefix*` channel, but adds a
new macro that has to be loaded before any sig-using file.

### MEDIUM-risk: Shadow variable handling (Risk #3)

The current rewriter tracks shadow vars (`let`, `\` params) to avoid
qualifying them (`runtime/src/macro.c:139-146, 202-208`). If qualification moves
to macro-expansion time, macros generating `\` forms need to manage the
same shadow set. Fragile.

## The hang mode (from LSP test investigation)

When a previous attempt dropped the module tree and kept only the FQN
rewriter, the symptom was `test_lsp_integration` timing out at 10s. Root
cause is **silent handler failure**, not stdin blocking:

1. Refactored code leaves `lsp/workspace/handle-did-open` unresolved at
   eval time (rewriter produced a qualified name for a stub module).
2. LSP reader callback at `runtime/src/builtins_pipe.c:340` invokes the dispatch;
   handler returns `LVAL_ERR`.
3. Error is logged to stderr (line 342) but **not** propagated as a JSON-RPC
   error response. Callback returns normally; event loop continues.
4. Parent test waits `MSG_TIMEOUT_MS = 5000` for a response that never
   comes (`lsp/test/test_lsp_integration.c:15`).

**Implication for any refactor attempt:** before changing module semantics,
add a defensive branch in the LSP reader callback — if the handler returns
LVAL_ERR, emit a JSON-RPC error response so the test fails loudly instead
of hanging. That's a ~5-line change in `__lsp_reader_try_parse` and would
already reduce debug time dramatically.

## Recommended instrumentation before attempting

1. In `runtime/src/builtins_pipe.c:340`, if `LVAL_TYPE(result) == LVAL_ERR`, emit a
   JSON-RPC error with the error message to stdout. Fails loudly.
2. In `lsp/lsp.valk:192` (`lsp/on-message`) and :79
   (`lsp/dispatch-request`), add `stderr/write` of method name.
3. Provide a standalone repro without the C harness:
   `./build/valk lsp/main.valk <<<$(printf 'Content-Length: 79\\r\\n\\r\\n{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}')`

## Recommendation

The "pure macro" approach as stated in `TECH_DEBT_LOG.md` does not cover
Risk #5 (sibling resolution) without either a breaking syntactic change or
a shadow of the module tree at the Valk level. I recommend **not** starting
implementation until one of these is decided:

- **Option A**: accept the breaking change — require every cross-file
  reference to be fully qualified from the file root. Ship a codemod that
  rewrites `lsp/*.valk`. Risks: third-party code, if any.
- **Option B**: keep a path-based module registry (flat map, not a tree),
  accessible from macros. C side shrinks modestly but not to "trivial".
- **Option C**: ship the instrumentation above, defer the full refactor,
  close item #6 as "deferred — unreasonable risk/reward without breaking
  changes." The system works today; the improvement is architectural, not
  correctness.

My default recommendation, given where the branch is right now (~95% of
the plan done, uncommitted work from multiple sessions), is **Option C**:
ship the LSP error instrumentation, mark #6 as deferred, commit everything,
merge the branch.
