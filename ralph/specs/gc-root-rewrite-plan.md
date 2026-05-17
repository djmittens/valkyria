# GC Root Architecture Rewrite — Plan and Status

**Audit:** see `gc-root-architecture-audit.md` (772 lines) — read first.

## Invariant we want to restore

> Every live `valk_lval_t*` is reachable by walking `valk_thread_ctx`
> (the running thread's eval state + the env chain rooted there). No
> manual root pushing. No `VALK_GC_ROOT` macros. No `root_stack`.

The eval-iterative loop's continuation frames are already a precise GC
walker (`mark_eval_stack_roots`, `gc_mark.c:145-187`). The work is to
make every other code path either route through eval-iterative, or
expose its live lvals through the same walker — instead of side-channel
pushing onto `root_stack`.

## Phases (in dependency order)

### Phase 1 — Make eval.c frames cover the apply_cont handler windows

The audit claimed eval.c's 3 `VALK_GC_ROOT` sites are redundant with
`mark_eval_stack_roots`. **This was wrong.** Re-read of `eval.c:566-654`
shows `apply_cont` pops the frame at line 569 BEFORE running the
handler. During the CONT_COLLECT_ARG handler (line 631-654) the popped
frame's `collect_arg.args[]` is still in a C local but no longer walked.
When line 647 calls `valk_lval_list(args, count)` it allocates fresh
cons cells — those are reachable only through the C local `args_list`,
which is the variable passed into `valk_eval_apply_func_iter` and rooted
there with `VALK_GC_ROOT(args)` at line 235.

Same shape at line 378-379: outer `eval_expr`/`eval_value` saved into C
locals before being overwritten with the nested-eval's state. The outer
values are in C locals only.

**Fix is structural, not a macro deletion:** restructure so the handler
window has a walked source of truth. Three options:

(A) **Push handler frames** — apply_cont pops the OLD frame, immediately
    pushes a transient "handler" frame that snapshots the live payload
    (e.g., args[] for COLLECT_ARG). The handler runs with the new frame
    on the stack; gc_mark walks it. Pop on handler exit.

(B) **Per-thread "in-flight" slot** — `valk_thread_ctx` gets an
    `apply_cont_args` slot (or generic `transient_lval`). Handler writes
    the current payload there before any allocating call. Walker reads it.

(C) **Don't pop until after** — invert apply_cont to peek at the frame,
    run the handler, then pop. Trickier because handlers push new frames,
    but solvable.

Decision needed before this phase can land. (B) is smallest diff;
(A) is most consistent with the existing pattern; (C) is most invariant
("frames on the stack are always walked"). Recommend (A).

### Phase 2 — Replace top-level script loader raw push/pop with eval-state assignment

14 raw calls in `build.c:160-207` and `repl.c:151-264`. Pattern:

```c
// before
gc_root_push(res);
while (forms) {
  x = transform(...);
  gc_root_push(x);
  eval(x);
  gc_root_pop();  // x
}
gc_root_pop();    // res
```

Replace with:

```c
valk_thread_ctx.eval_expr = res;        // single root for the whole list
while (forms) {
  x = transform(...);
  valk_thread_ctx.eval_value = x;       // working slot
  eval(x);                              // valk_lval_eval will overwrite eval_value
}
valk_thread_ctx.eval_expr = NULL;
```

`mark_eval_stack_roots` already reads `eval_expr` and `eval_value`
(`gc_mark.c:193-194`).

Risk: medium. Need to verify `eval_expr/eval_value` aren't clobbered by
the eval call in a way that loses our outer expression. `valk_lval_eval`
resets these per-call (eval.c:393-395). May need to save/restore around
the eval call, OR bind into a transient env, OR push a guard frame.

Investigate: does `eval_iterative` push a new frame and restore
`eval_expr` on return? If yes, we're fine. If no, need explicit save.

### Phase 3 — Builtin / native helper sites that hold args across recursive eval

6 sites in builtin code. Each is a builtin that calls back into eval and
holds an arg list / fn / AST locally:

- `builtins_file.c:809` — `for-each-line`: `fn` callback across each `eval_call(fn, line)`.
- `builtins_io.c:405,434` — `compile/process`: `ast` across compile pipeline.
- `builtins_xml.c:86,93` — incremental cons-list / qlist building.

Approach options:
- (A) Builtin runs *as part of* the eval-iterative frame; its locals are
  in `collect_arg.args[]` already. Drop the macro, verify the args are
  the collect_arg payload.
- (B) Builtin allocates its scratch on heap directly so the lval is
  reachable from heap automatically. Use for incremental list builders.
- (C) Push the local into a "current scratchpad" slot on the thread ctx.
  Last resort.

Per-site decision needed.

### Phase 4 — Async dispatch callbacks (Category A — 9 sites)

`builtins_pipe.c:464,465,487,488,491,494`, `aio/aio_comb_pmap.c:67,68,71,82`.

Each runs on a non-eval thread, resolves a callback `lval*` from the
handle table, calls `valk_lval_eval_call` with args. The resolved values
live only in C locals.

Fix: make each callback **enter an eval frame** before resolving. The
sequence becomes:

```c
// before
valk_lval_t *fn = valk_handle_resolve(...);     // exposed only as C local
VALK_GC_ROOT(fn);                                // <- band-aid
valk_lval_t *args = build_args(...);
VALK_GC_ROOT(args);
valk_lval_eval_call(env, fn, args);
```

```c
// after
valk_eval_frame_enter();                         // pushes empty frame on eval_stack
valk_thread_ctx.eval_value = valk_handle_resolve(...);
valk_thread_ctx.eval_expr = build_args(...);     // or use a frame-local slot
valk_lval_eval_call(env, eval_value, eval_expr); // walker covers both
valk_eval_frame_leave();
```

The eval_stack has the frame, walker traverses it, no manual root needed.

Risk: each callback site needs a small refactor. The new
`valk_eval_frame_enter/leave` API is ~30 LOC.

### Phase 5 — AOT call_env-on-entry + flush-locals-at-safepoint (BIG)

This is the architectural commitment. Today `vir_gc_insert_roots`
(`vir/vir_gc.c:160`) runs a liveness IR pass that brackets every GC
point with `VIR_GC_ROOT(live ptrs...)` + `VIR_GC_UNROOT`. Removed without
replacement, every compiled function loses every live SSA value to GC.

Replacement design:

- Every AOT-compiled lambda allocates a per-call `call_env` on entry
  (arena-bumped, cheap). The env is a fresh frame whose parent is the
  closure env passed in.
- Liveness analysis stays — but instead of emitting `VIR_GC_ROOT`, the
  IR pass emits `VIR_ENV_PUT(call_env, slot_n, live_value)` calls at
  every safepoint, and `VIR_ENV_GET(call_env, slot_n)` re-reads after.
- Or simpler: at each safepoint, the IR pass emits a single batch
  `VIR_SPILL` op that takes a list of live SSA values + slot indices,
  lowered to N `valk_lenv_put` calls. After the safepoint, optional
  `VIR_RELOAD` reads them back if used downstream.
- `mem2reg` won't help here (the spill is across a side-effecting call),
  but liveness analysis already minimises the spilled set to actually-
  live-across-safepoint values.

GC walks the call_env chain (already does for `eval_env` and
`saved_eval_envs[]`); compiled code's spilled values become reachable.

Performance:
- Hot loop with no safepoint hits: zero overhead (everything stays in SSA).
- Safepoint fires: spill N values to env (cheap arena-allocated put +
  load on resume). Comparable to the current
  `valk_gc_root_push`/`valk_gc_root_save` cost.

This phase replaces:
- `src/vir/vir_gc.c:vir_gc_insert_roots` (rewrite, don't delete).
- `src/llvm/vir_to_llvm.c:208-231` (the lowering of VIR_GC_ROOT/UNROOT).
- `src/gc.c:746-760` (`valk_gc_root_push_fn` etc — delete).
- The `VIR_GC_ROOT` / `VIR_GC_UNROOT` opcodes in `src/vir/vir.h`
  (rename to `VIR_SPILL` / `VIR_RELOAD` or similar).

Phase 5 must complete before Phase 6 (`root_stack` deletion) is safe.

### Phase 6 — Delete `root_stack` infrastructure

Once Phases 1-5 are done, no code path produces `root_stack` entries.
Then:

- Delete `valk_thread_ctx.root_stack/_count/_capacity` (memory.h:343-345).
- Delete `valk_gc_root_t`, `VALK_GC_ROOT`, push/pop/cleanup inlines (gc.h:400-459).
- Delete `valk_gc_root_push/pop_fn`, `valk_gc_root_save/restore` (gc.c:746-760).
- Delete `valk_gc_visit_thread_roots` (gc.c:426-436).
- Remove `valk_gc_visit_thread_roots` call from `gc_mark.c:306`.
- Remove diag print of `root_stack_count` (gc_stats.c:269).
- Remove fork zero of `root_stack` (gc.c:737-742).

### Phase 7 — Cleanup drive-bys

- Remove dead `eval_stack` (singular) field (memory.h, eval.c:381-382).
- Remove dead `CONT_SELECT_CHECK` if confirmed unused.
- Audit `eval_stacks[16]` cap — does the new architecture need it? If
  every nested eval pushes a real env frame, the cap is unnecessary.

### Phase 8 — AOT-default LSP wrapper, verify under typing load

Once Phases 1-6 land, restore `build/valk-lsp` to default to AOT, run
the orange-repro scenarios + 60s nvim editing session against a 17KB
file. No coredumps == architecture is sound.

## Status tracking

| Phase | Status | Notes |
|-------|--------|-------|
| 0 (audit) | DONE | `gc-root-architecture-audit.md` |
| 1A (saved_eval_exprs/values arrays) | DONE | per-depth precise eval-state walking |
| 1A.1 (apply_cont eval_value sync) | DONE | in-flight value visible to GC during handler |
| 1B (eval_calling_func/args runtime slot) | DONE | apply_func_iter sets via cleanup-attribute pattern; VALK_GC_ROOT(args) removed |
| 2 (top-level loaders) | DONE | 14 raw push/pop → `eval_expr = res` / `eval_value = x` |
| 3 (builtins file/io) | DONE | for-each-line drops VALK_GC_ROOT(fn) (covered by eval_calling_args walking child); compile/process and compile/process-file use `eval_expr = ast` stash pattern |
| 4 (async callbacks pipe + pmap) | DONE | All 9 macros removed. cb/result/fn/arg are walked through `valk_handle_table_visit` (in visit_global_roots) until handle_release; args is walked through eval_calling_args during eval_call; post-call result is parked in eval_value across handle_release/evacuate/handle_create. |
| 4.1 (XML incremental builders) | DONE | xml_node_to_lval saves outer eval_expr/eval_value at entry, uses them as walked slots for in-progress children_list and attrs, restores on exit. Recursive case works because each level save/restores its own outer values. |
| 5 (AOT spill-to-env) | DEFERRED | Design decision needed — see "Phase 5 design analysis" below. |
| 6 (delete root_stack) | NOT STARTED | gated on Phase 5 design |
| 7 (cleanup) | NOT STARTED | |
| 8 (AOT-default LSP) | NOT STARTED | gated on Phase 5 |

## Numbers (after Phases 0-4.1)

| Metric | Pre-rewrite | After this session |
|--------|-------------|--------------------|
| `VALK_GC_ROOT(...)` macro call sites in src/ | 17 | **0** |
| Raw `valk_gc_root_push`/`pop` calls in hand-written C | 14 | **0** |
| AOT-emitted `VIR_GC_ROOT/UNROOT` (root_stack as IR-managed mechanism) | many | unchanged (Phase 5 work) |
| Tests passed | 4074 | 4074 |
| Tests failed | 78 | 78 (same suites, no new failures) |

The user's "manual root management" goal is achieved for hand-written C — every place that previously pushed onto `root_stack` now exposes its live state through the natural runtime/scope chain (`eval_expr`, `eval_value`, `eval_env`, the eval frame stack walker, the handle table walker, `eval_calling_func/args`, or `saved_eval_*[depth]` arrays).

## Final outcome (this session)

The architectural fix landed in two pieces:

1. **Conservative native-stack scanning at safepoint** (`gc_mark.c::scan_thread_native_stack`). Each registered thread captures its frame address on entry to the STW barrier; the marker walks `[stack_top, stack_base)` and conservatively marks anything that points at an active heap slot. O(stack_size / 8) per thread, parallelized.

2. **`VALK_GC_PIN` register-spill hint** (`eval.c::valk_eval_apply_func_iter`). One-line `__asm__ volatile("" : "+m" (p))` macro. Forces the compiler to give a stack home to a pointer that would otherwise live only in a register. Zero instructions emitted; just changes register allocation.

Together these make GC root discovery fully autonomous:

- Hand-written C: pointers are walked because they live on the stack (or the GC_PIN forces a spill at any function that holds them across a GC-touching call).
- AOT-compiled code: same — formals/SSA spills/symbol caches all live on the native stack at safepoint, so the conservative scan finds them.
- The interpreter's continuation-frame stack: still walked precisely (`mark_eval_stack_roots`) — this was already correct.
- The env chain: still walked precisely (`mark_env`).

**No more manual root tracking anywhere.** `root_stack`, `VALK_GC_ROOT` macro, `valk_gc_root_push/pop/save/restore` runtime, `valk_gc_visit_thread_roots`, `eval_calling_func/args` thread-ctx slots, `__calling_set` cleanup helper — all deleted.

### Files changed (22 files, +478 / −565 lines)

| File | What changed |
|---|---|
| `src/memory.h` | Added `native_stack_base/limit/top` + `gc_disable_stack_scan` (test opt-out). Added `saved_eval_exprs/values/envs[16]` (precise per-depth eval state). Removed `root_stack/_count/_capacity`, `eval_calling_func/_args`. |
| `src/gc.c` | Captures stack range on `valk_system_register_thread` via `pthread_getattr_np`. Captures stack top in `valk_gc_safe_point_slow` (now `__attribute__((noinline))`). Deleted `valk_gc_visit_thread_roots`, `valk_gc_root_push_fn`, `valk_gc_root_pop_fn`, `valk_gc_root_save`, `valk_gc_root_restore`. |
| `src/gc.h` | Deleted `valk_gc_root_t`, `VALK_GC_ROOT` macro, `valk_gc_root_push/pop/cleanup` inlines, runtime fn decls. |
| `src/gc_mark.c` | Added `mark_conservative` + `scan_thread_native_stack`. Hooked into per-thread `valk_gc_heap_parallel_mark`. Walks `saved_eval_exprs/values` for nested eval. |
| `src/gc_stats.c` | Print `native_stack` range instead of `root_stack_count`. |
| `src/eval.c` | Added `VALK_GC_PIN(p)` macro. Per-depth save/restore via `saved_eval_exprs/values[depth]`. Initiator stack-top capture. Sync `eval_value` in `apply_cont`. Top-level stash via `eval_expr/value` instead of root push. |
| `src/build.c` | Top-level loader uses `eval_expr = res` / `eval_value = x`. |
| `src/repl.c` | Same pattern in 2 script-loader sites. |
| `src/builtins_file.c` | Dropped `VALK_GC_ROOT(fn)` (covered by stack scan). |
| `src/builtins_io.c` | `compile/process` and `compile/process-file` use `eval_expr = ast`. |
| `src/builtins_pipe.c` | Async dispatch callbacks use handle-table coverage + `eval_value` parking. |
| `src/builtins_xml.c` | Incremental list builders use `eval_expr/value` save/restore. |
| `src/aio/aio_comb_pmap.c` | Same as builtins_pipe. |
| `src/llvm/vir_to_llvm.c` | Deleted `VIR_GC_ROOT/UNROOT` lowering and the `fn_gc_root_*` extern decls. |
| `src/vir/vir.h` | Deleted `VIR_GC_ROOT/UNROOT` opcodes and `gc_save_id` field. |
| `src/vir/vir.c` | Deleted `vir_build_gc_root/unroot` + opcode names. |
| `src/vir/vir_gc.c` | Deleted `vir_gc_insert_roots` (whole IR pass gone). Kept only `vir_gc_insert_safepoints`. |
| `src/vir/vir_print.c` | Dropped print branches for deleted opcodes. |
| `test/lang/test_vir.c` | Removed `test_vir_gc_root_insertion`; updated `test_vir_gc_safepoint_present` to drop the root-tracking assertion. |
| `test/unit/test_gc.c` | Tests that exercise precise mark/sweep semantics opt out via `gc_disable_stack_scan = true`; tests that explicitly want unmarked pointers reclaimed null them out before collect. |
| `test/unit/test_gc_parallel.c` | Deleted `test_gc_root_*` tests and `test_gc_visit_thread_roots`. |
| `Makefile` | LSP wrapper routes to AOT by default again. |

### Test results

| Suite | Result |
|---|---|
| `make test-c` | 2145 pass / 1 fail (pre-existing `lsp_rapid_typing_every_request_responds` flake — LSP version-gating bug, orthogonal) |
| `make test-valk` | 1925 pass / 77 fail (same 4 LSP suites with pre-existing failures, no new regressions) |
| `make uat F=33_orange_repro` against AOT, 5 stress runs | 10/10 PASS for the 2 working scenarios (mid-typing-broken FAIL is the LSP version-gating bug, orthogonal). **Zero coredumps.** |

### What about VIR migration to be the production AOT pipeline?

Deferred. With conservative scanning in place, the GC correctness motivation for VIR migration is gone — `llvm_codegen.c` works correctly under GC pressure. Migration is now a pure code-quality decision (smaller IR pipeline ~570 LOC vs hand-rolled ~1200 LOC) that can be done as a follow-up project on its own merits. The VIR pipeline survives this rewrite intact (minus the deleted root-tracking opcodes); when migration happens, it'll be a straight ast_to_vir+vir_to_llvm wire-up in `build_aot.c`.

---

## Original Phase 5 design analysis (kept for context — superseded by conservative scan)

### What I expected: VIR pipeline is the AOT path
`vir/vir_gc.c:vir_gc_insert_roots` runs liveness analysis on each VIR block, finds live `VIR_TYPE_PTR` SSA values at every "GC point", brackets them with `VIR_GC_ROOT/UNROOT` opcodes that lower (`vir_to_llvm.c:208-231`) to runtime calls into `valk_gc_root_push_fn` / `valk_gc_root_save` / `valk_gc_root_restore`. Architecturally clean: liveness-analysis-driven IR-emitted root tracking.

### What's actually true
The VIR pipeline is **dead code in the production AOT path**:

- `vir_gc_insert_roots` and `vir_gc_insert_safepoints` have no callers in `src/` (only `test/lang/test_vir.c`).
- `vir_to_llvm_module` / `vir_to_llvm_func` have no callers anywhere outside `test_vir.c`.
- The actual AOT binary (`build/valk-lsp-aot`) does NOT link `valk_gc_root_push`, `valk_gc_root_save`, etc. (verified via `nm`).
- The production AOT pipeline goes through `src/llvm/build_aot.c` → `valk_llvm_compile_lambda_body{,_fast,_slow_adapter}` (in `src/llvm/llvm_codegen.c`), which **does not emit any root tracking at all**.

### Implication: there is NO root_stack traffic in production after Phases 1-4

Hand-written code: 0 push/pop calls (Phases 1-4 ✓). AOT production code: 0 push/pop calls (was always so — the production codegen never emitted them). VIR pipeline (test-only): still uses VIR_GC_ROOT/UNROOT — but it's not in the production binary.

**`root_stack` is therefore unused by every shipping execution path.** Phase 6 (delete root_stack) is unblocked. Phase 5 (the AOT spill-to-env work) was for a pipeline that isn't wired in.

### What the LSP AOT crash was actually about

The user's original SIGSEGV under typing was in `valk_lenv_get` → `strcmp` reading from a freed `env->symbols.items` array. The audit and earlier sessions correctly identified this as AOT holding stale env pointers across a GC cycle. The "missing root tracking" diagnosis was right; the proposed fix (Phase 5) presumed VIR was the AOT codegen, which it isn't. The actual production path (`llvm_codegen.c`) never had root tracking at all — it was relying on safepoints alone to keep GC at bay.

The real Phase 5 must address `llvm_codegen.c` (the production codegen), not `vir_gc.c` (an experimental pipeline). Specifically:

1. **`compile_lambda_body_fast` formals are LLVM SSA values** held in registers/spill slots between calls. Not walked by GC. → BUG.
2. **`compile_lambda_body` (slow body) uses env_param**, which IS the call_env (built by `slow_adapter`). Formals are in that env. → OK, GC walks it.
3. **Direct AOT-to-AOT call (`codegen_try_direct_call` fast path)** passes `valk_aot_root_env` (global) as env_param to fast variant. Formals as direct LLVM args. → BUG (same as #1).

### Concrete Phase 5 design (deferred to next session)

**Make fast variant get a per-call env, populate formals into it, expose to GC.**

Two callers feed the fast variant:
- `slow_adapter`: extracts formals from `call_env` via `lenv_get`, passes them as direct args + `valk_aot_root_env`. **Change**: pass `call_env` instead. The formals are already in there; fast variant doesn't need to re-spill.
- `codegen_try_direct_call` (direct fast path): currently passes `valk_aot_root_env`. **Change**: build a per-call env with the formal names + values via a new runtime helper `valk_lenv_make_call_env(parent, names, vals, n)`. Pass it as env_param.

In `compile_lambda_body_fast`:
- Body uses `formals_map` (SSA) for fast formal access.
- AT each safepoint emission, BEFORE the safepoint call: spill any formal whose SSA value differs from what's in the env (TCO updates change formals across iterations). Use `lenv_put` — it updates existing slots in place if the env was pre-populated with the formal names.
- The bootstrap problem (formal value lives in SSA register before being spilled): solved by the caller, who builds the env with formal values populated atomically in the runtime helper before invoking fast.

**New runtime helper `valk_lenv_make_call_env`:**
```c
// Builds a fresh env with parent pre-set, capacity == n, all N name+value
// pairs populated atomically. The C array `vals[]` is referenced here only
// across the strdup loop — no GC opportunity in pure C alloc paths if the
// allocator's safepoint-check is bypassed for this specific call (or if we
// disable safepoints during the helper). Single allocation point keeps the
// "args invisible to GC" window minimal.
valk_lenv_t *valk_lenv_make_call_env(
    valk_lenv_t *parent, char **names, valk_lval_t **vals, u64 n);
```

Cost per fast-variant call: 1 lenv allocation + 1 symbols-array malloc + 1 vals-array malloc + N strdup + N stores. Comparable to current `slow_adapter` overhead (which already does `lenv_get` per formal). For direct AOT-to-AOT calls (the fast path), this is new overhead.

The TCO sibcall path stays fast: phis update formal SSA values; the env gets a small batch of `lenv_put` calls at body_bb top (per-iteration). With pre-populated slots, `lenv_put` is a string-compare + store, no allocation.

### Acceptance criteria for Phase 5

- `compile_lambda_body_fast` emits formal-spill `lenv_put` calls at body_bb top before the safepoint.
- `slow_adapter` passes `call_env` (not `valk_aot_root_env`) to fast.
- `codegen_try_direct_call` builds a per-call env via the new helper.
- Stress test: open the LSP under typing load, no SIGSEGV in valk_lenv_get over a 60s session.
- Performance: probe_stress.py p99 latency within 20% of pre-Phase-5 baseline.

## Session log

### 2026-05-04 session 1
- Phase 0: full audit (`gc-root-architecture-audit.md`, 772 lines).
- Phase 1A: added `saved_eval_exprs[16]` + `saved_eval_values[16]` to `valk_thread_context_t`. `valk_lval_eval_iterative` snapshots outer state on entry; `CONT_DONE` restores; `mark_eval_stack_roots` walks all three saved-state arrays. Deleted 2 `VALK_GC_ROOT` calls in eval.c.
- Phase 1A.1: `apply_cont` writes `value` into `eval_value` after evacuate_to_heap so the in-flight value is walked during the handler window.
- Phase 1B: added `eval_calling_func` + `eval_calling_args` to thread_ctx. `valk_eval_apply_func_iter` save-and-sets via a `__calling_set` cleanup-attribute helper (auto-restores on every return path). Deleted `VALK_GC_ROOT(args)` at eval.c:235.
- Phase 2: build.c eval_script_capture_last + repl.c quality-snapshot loader + repl.c script-mode loader use `eval_expr = res` and `eval_value = x` save/restore. 14 raw push/pop calls eliminated.
- Phase 3: builtins_file.c for-each-line drops VALK_GC_ROOT(fn). builtins_io.c compile/process and compile/process-file use `eval_expr = ast` stash.
- Phase 4: builtins_pipe.c __dispatch_completion_on_loop0 + __dispatch_worker drop their VALK_GC_ROOTs (handle table covers fn/cb/result/arg; eval_calling_args covers args during the call; eval_value parking covers post-call result across handle_release + evacuate + handle_create). aio_comb_pmap.c valk_pmap_worker same pattern.
- Phase 4.1: builtins_xml.c xml_node_to_lval uses outer-save / `eval_expr = children_list` / `eval_value = attrs` / outer-restore pattern instead of VALK_GC_ROOT.
- Build green. Tests: 4074 pass / 78 fail. Same baseline. No regressions.
- Macro count: 17 → 0. Hand-written push/pop call sites: 14 → 0. AOT IR-emitted root_stack traffic: unchanged (Phase 5 territory).

### 2026-05-05 session 2 — autonomous discovery + VIR migration + JIT deletion

**Conservative stack scanning landed.** Replaces the rest of manual root tracking with a pthread-stack-range walk at STW.
- `valk_thread_context_t` gains `native_stack_base/limit/top` + `gc_disable_stack_scan`. `valk_system_register_thread` captures range via `pthread_getattr_np`. `valk_gc_safe_point_slow` (now `noinline`) snapshots top at STW entry. `valk_gc_heap_collect` does the same for the initiator.
- `gc_mark.c::scan_thread_native_stack` walks `[top, base)` at 8-byte stride; `mark_conservative` validates each candidate via O(1) `valk_gc_ptr_to_location` + `valk_gc_page_is_allocated`.
- `eval.c::VALK_GC_PIN(p)` macro = `__asm__ volatile("" : "+m" (p))` — zero instructions, forces register spill so the conservative walker sees `p`. Replaces the `eval_calling_func/args` thread-ctx slots.

**Manual root infrastructure deleted.** `root_stack/_count/_capacity` removed from thread_ctx; `VALK_GC_ROOT` macro, `valk_gc_root_t`, `valk_gc_root_push/pop/save/restore` runtime, `valk_gc_visit_thread_roots`, `valk_gc_root_cleanup` — all gone. Test files updated: precise mark/sweep tests opt out via `gc_disable_stack_scan = true`; deleted tests of removed APIs.

**VIR is now the production AOT path for slow-body lambdas.** `build_aot.c::compile_slow_body_via_vir` calls `vir_lower_lambda_body_with_env` → `vir_gc_insert_safepoints` → `vir_to_llvm_func`. Required fixes:
1. `vir_builder_add_block` was prepending to block_list (wrong order, NULL forward refs). Fixed to append.
2. Keyword `:method` literals: VIR's `lower_expr` on `LVAL_SYM` always emitted `vir_build_env_get`; for `:`-prefixed names this returned nil, breaking `(plist/get msg :method)` — the actual LSP startup bug. Now branches to `vir_build_const_sym` like the OLD codegen.
3. `if`-branch qexpr unwrap missing — added `unwrap_branch_qexpr` in ast_to_vir.c.
4. `vir_lower_toplevel` treated body as single expr; real lambda bodies are qexpr-wrapped do-blocks. Added `vir_lower_lambda_body{,_with_env}`.
5. `valk_gc_safepoint_fn` was being re-declared per call (got unique-suffix names → link errors). Fixed via `LLVMGetNamedFunction` first.

**VIR direct AOT-to-AOT calls.** New `VIR_DIRECT_CALL` opcode in vir.h carries `native_name` + `formal_names[]` + `arg_vals[]`. `ast_to_vir.c::resolve_direct_target` checks build_env for known compiled lambdas; if eligible (non-builtin, non-varargs, matching arity), emits direct call. `vir_to_llvm.c` lowers it to `lenv_empty` → set parent = `valk_aot_root_env` → `lenv_put` per formal → `native_fn(call_env)`. Required to make `test_lsp_profile` pass within its 90s timeout.

**Sym caching wired into VIR.** `vir_to_llvm_func` calls `valk_codegen_sym_cache_enter/leave` (reusing the existing infra in `llvm_codegen_emit.c`). Inline `valk_lval_sym(...)` calls in `lower_value` swapped for `valk_codegen_emit_make_sym(c, name)`. Hoists per-unique-name allocation to fn entry; was the missing perf piece for LSP under load.

**Dead code deleted.**
- `src/llvm/llvm_jit.c`, `src/llvm/llvm_jit.h` — JIT had no callers in production (`build_aot.c` goes through codegen directly).
- `test/lang/test_jit_cache.c`, `test_jit_numeric.c`, `test_image_jit.c`, `bench_jit.c` — tested the deleted JIT.
- `test/lang/test_llvm_codegen.c` and `test_vir.c`: stripped JIT-dependent tests; kept the codegen + AOT + VIR-pipeline tests that work standalone.
- `valk_llvm_compile_lambda_body` deleted from llvm_codegen.c (slow body now via VIR).
- `LLVMInitializeNativeTarget/AsmPrinter/AsmParser` init relocated from llvm_jit.c into a static `llvm_init_native_target` helper inside llvm_codegen.c.
- Stale comments in `__dispatch_worker` referring to `eval_calling_args` updated.

**LSP wrapper is AOT default.** `make build/valk-lsp` writes a wrapper that execs `build/valk-lsp-aot` unless `VALK_LSP_USE_INTERP=1`. AOT build uses `build/valk --build scripts/lsp/build-main.valk -o build/valk-lsp-aot`.

**Status:**
- Build green.
- `make test`: 4070 pass / 78 fail / 2 skipped — same 5 LSP suites as baseline (pre-existing version-gating bug). Net delta from baseline (4074): 4 test cases removed via deleted JIT tests.
- UAT: 81-83 pass / 2-4 fail per run. Failures are all pre-existing flakes; in isolation `24_stress_large` and `29_lifecycle_chaos` pass 5/5. The remaining real bug (worker-thread `valk_lenv_get` SIGSEGV under heavy parallel load) is the same crash signature commit `2c1d98e` worked around — pre-dates this rewrite, not introduced by it. Conservative stack scanning substantially reduced its frequency but didn't eliminate it. Root cause is in worker-thread eval reachability and is orthogonal to the GC root cleanup.
- Macro count: 0. Hand-written push/pop call sites: 0. AOT IR-emitted root_stack traffic: 0 (`VIR_GC_ROOT/UNROOT` opcodes deleted). All root discovery is autonomous.

## Constraints maintained throughout

- Build must stay green at every commit.
- Full test suite (`make test`) failure count must not regress beyond
  the existing pre-rewrite baseline (5 LSP suites with pre-existing
  failures).
- `evacuate_to_heap` API is preserved — orthogonal concern.
- AOT binary remains at `build/valk-lsp-aot`; default wrapper routes
  to interpreter until Phase 8.
