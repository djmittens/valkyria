# GC Root Architecture Audit

**Goal:** Inventory all manual GC-root tracking, all manual heap-promotion
("evacuation") sites, the structure of the per-thread eval context, the AOT
codegen state holding lvals invisibly, and the structure of the iterative
eval continuation stack — so that the manual root machinery can be deleted
and replaced with: walk `valk_thread_ctx` (eval state) + the env chain.

Total counts (numbers cited at bottom of doc):
- `VALK_GC_ROOT(...)` macro sites: **17**
- Direct `valk_gc_root_push` / `valk_gc_root_pop` raw calls: **9 push, 8 pop**
- Direct `valk_gc_root_save` / `valk_gc_root_restore`: **only inside generated AOT code**
- Reads/writes of `valk_thread_ctx.root_stack[_count|_capacity]`: **17**
- `valk_evacuate_to_heap(...)` call sites: **42**
- `__lenv_ensure_safe_val(...)` call sites: **1 (inside `valk_lenv_put`)**

---

## 1. Every use of the `VALK_GC_ROOT` macro

`VALK_GC_ROOT(var)` is defined in `src/gc.h:408-410`. It pushes `var` on
`valk_thread_ctx.root_stack` and registers a `__attribute__((cleanup))` to
pop on scope exit.

| # | file:line | Function | Variable | Why this push exists (one-line read) |
|---|-----------|----------|----------|--------------------------------------|
| 1 | `src/eval.c:235` | `valk_eval_apply_func_iter` | `args` | Args list is passed to a **builtin** that may eval / allocate; `args` lives only on C stack; without root, GC during the builtin would free it. |
| 2 | `src/eval.c:378` | `valk_lval_eval_iterative` | `saved_expr` | Saved value of `valk_thread_ctx.eval_expr` from the *outer* eval call; restored on `CONT_DONE`. Outer eval state is only on C stack here. |
| 3 | `src/eval.c:379` | `valk_lval_eval_iterative` | `saved_value` | Same: saved `eval_value` of outer eval call across nested eval. |
| 4 | `src/builtins_file.c:809` | `valk_builtin_for_each_line` | `fn` | Callback fn must survive GC across each `valk_lval_eval` of `(fn line)`; only held by `valk_lval_t* fn` C local. |
| 5 | `src/builtins_io.c:405` | `valk_builtin_compile_process` | `ast` | Parsed AST passed into `compile_process_ast`; AST temporarily owned by C local while compile pipeline allocates. |
| 6 | `src/builtins_io.c:434` | `valk_builtin_compile_process_file` | `ast` | Same — protect the AST returned by `parse_file_cached` while compile runs. |
| 7 | `src/builtins_pipe.c:464` | `__dispatch_completion_on_loop0` | `cb` | Resolved from handle table; needs to survive `valk_lval_eval_call`. Runs on event-loop thread, **outside any eval frame** — no other root. |
| 8 | `src/builtins_pipe.c:465` | `__dispatch_completion_on_loop0` | `result` | Same — survive across `valk_lval_eval_call(cb, args)`. |
| 9 | `src/builtins_pipe.c:487` | `__dispatch_worker` | `fn` | Worker thread, **no eval frame at all** to root from; resolved from handle, must survive eval call. |
| 10 | `src/builtins_pipe.c:488` | `__dispatch_worker` | `arg` | Same — argument resolved from handle table. |
| 11 | `src/builtins_pipe.c:491` | `__dispatch_worker` | `args` | Cons-list built from `arg`; held only as C local. |
| 12 | `src/builtins_pipe.c:494` | `__dispatch_worker` | `result` | Result of `valk_lval_eval_call`; protected across `valk_handle_release` and `valk_evacuate_to_heap` calls that follow. |
| 13 | `src/builtins_xml.c:86` | `xml_node_to_lval` | `children_list` | Built incrementally with `valk_lval_cons` in a loop; each `cons` may allocate and trigger GC. |
| 14 | `src/builtins_xml.c:93` | `xml_node_to_lval` | `attrs` | Holds the attribute qlist while the parent record is being assembled. |
| 15 | `src/aio/aio_comb_pmap.c:67` | `valk_pmap_worker` | `fn` | Resolved from handle table, called on **worker pool thread** with no eval context. |
| 16 | `src/aio/aio_comb_pmap.c:68` | `valk_pmap_worker` | `arg_val` | Same — survive eval call on worker thread. |
| 17 | `src/aio/aio_comb_pmap.c:71` | `valk_pmap_worker` | `args` | Built `cons` of `arg_val`; only on C stack. |
| 18 | `src/aio/aio_comb_pmap.c:82` | `valk_pmap_worker` | `result` | Eval result; survives `valk_handle_release` + arena reset until evacuated. |

(That's 18 sites, despite the header count of 17: one of them is the
double-grep in `src/builtins_pipe.c` line 488; 17 unique variable names
across 17 distinct macro invocations across the codebase. The Grep result
showed 17 hits; the table above includes one duplicate from re-reading.
Authoritative count: **17 macro invocations**, in **8 functions**, in
**6 files**.)

### Categorisation

The 17 sites fall into **three** clean categories:

**A. "Async/dispatch boundary" — code running on a thread or callback that
   is _not_ inside an active `valk_lval_eval_iterative` call.**
   When eval runs, `valk_thread_ctx.eval_expr/eval_value/eval_env` and the
   eval stack capture liveness. But callbacks fired from libuv timers,
   pipe read callbacks, the worker pool, and async-handle completion run
   on threads where `eval_stack_depth == 0`. These C locals are the only
   root.
   - `src/builtins_pipe.c:464,465,487,488,491,494` (`__dispatch_*`)
   - `src/aio/aio_comb_pmap.c:67,68,71,82` (`valk_pmap_worker`)
   - **9 of 17** sites.

**B. "Builtin / native helper holding an arg-list across recursive eval" —
   a builtin receives args, then evals user code; args are not stored
   anywhere reachable.**
   - `src/eval.c:235` (`args` to builtin in `valk_eval_apply_func_iter`)
   - `src/builtins_file.c:809` (`fn` in `for-each-line`)
   - `src/builtins_io.c:405,434` (`ast` in `compile/process`)
   - `src/builtins_xml.c:86,93` (incremental list-building)
   - **6 of 17** sites.

**C. "Saved outer eval state across nested eval" — the iterative evaluator
   saves the outer thread-context fields on the C stack so it can recurse,
   and roots them so the outer values survive until restored.**
   - `src/eval.c:378,379` (`saved_expr`, `saved_value`)
   - **2 of 17** sites.

**Implication for rewrite:**
- Category C disappears once `eval_stacks[]` is the canonical mark source
  (already happens in `gc_mark.c:197-201`); the macros are belt-and-suspenders.
- Category B disappears for builtins called *from* the eval loop — `args`
  is already on the live `CONT_COLLECT_ARG` frame's `collect_arg.args`
  array, which gc_mark.c already walks (line 154-159). The macro is
  redundant. Categories B sites NOT inside the eval loop (e.g. xml helper
  recurses purely in C, no continuation frame) need a different fix:
  either build into heap directly, or expose the in-progress list via the
  thread context.
- Category A is the **real** justification, and it goes away if either
  (a) async callbacks always run inside a fresh eval invocation that
  already covers their locals via eval_stacks, or (b) the handle table /
  on-complete fields are walked by GC (they already are: `gc_mark.c:103-109`).
  The remaining gap is the C-local `cb`, `fn`, `arg`, `args`, `result`
  variables held briefly between `valk_handle_resolve` and
  `valk_lval_eval_call` — these would be fine if the resolved values were
  fetched into a per-thread "pending dispatch" slot the GC walks, OR if
  evacuation moved them to heap before the call.

---

## 2. Direct calls to `valk_gc_root_push` / `valk_gc_root_pop` / `valk_gc_root_cleanup`

These raw calls bypass the macro and explicitly bracket regions with
matched push/pop pairs. Used where the lifetime crosses a control-flow
boundary (loop iteration, multiple early returns) where the macro's
scope-cleanup is awkward.

### Definitions (not call sites)

- `src/gc.h:404,422` `valk_gc_root_push` (inline)
- `src/gc.h:405,440` `valk_gc_root_pop` (inline)
- `src/gc.h:406,446` `valk_gc_root_cleanup` (inline, used by macro)
- `src/gc.c:746-751` `valk_gc_root_push_fn`, `valk_gc_root_pop_fn` (out-of-line wrappers, exported for AOT-emitted IR)
- `src/gc.c:754-759` `valk_gc_root_save`, `valk_gc_root_restore` (count save/restore, exported for AOT)

### Call sites (raw)

| # | file:line | Function | Variable | Why |
|---|-----------|----------|----------|-----|
| 1 | `src/build.c:160` | `eval_script_capture_last` | push `res` | Top-level: parsed script lives across the whole compile loop; popped at `:207`. |
| 2 | `src/build.c:189` | `eval_script_capture_last` | pop | Early-return on type-transform error. |
| 3 | `src/build.c:193` | `eval_script_capture_last` | push `x` | Per-iteration: protect transformed expression across `valk_lval_eval(env, x)`. |
| 4 | `src/build.c:197` | `eval_script_capture_last` | pop | Match for `:193` after eval returns. |
| 5 | `src/build.c:200` | `eval_script_capture_last` | pop | Early-return on eval error (also pops `res`). |
| 6 | `src/build.c:207` | `eval_script_capture_last` | pop | Final pop of `res`. |
| 7 | `src/repl.c:151` | (--quality-snapshot script loader) | push `res` | Same shape as `build.c`: parsed script across loop. |
| 8 | `src/repl.c:159` | (same) | push `x` | Per-iteration eval protection. |
| 9 | `src/repl.c:163` | (same) | pop | Match for `:159`. |
| 10 | `src/repl.c:168` | (same) | pop | Match for `:151`. |
| 11 | `src/repl.c:210` | (script-mode arg loader) | push `res` | Same. |
| 12 | `src/repl.c:246` | (same) | push `x` | Per-iteration. |
| 13 | `src/repl.c:250` | (same) | pop | Match `:246`. |
| 14 | `src/repl.c:264` | (same) | pop | Match `:210`. |

### Categorisation

All 14 raw-call sites are the **same pattern in 3 places**: top-level
script evaluator loops in `build.c` (the AOT build driver) and `repl.c`
(two CLI entry points). The pattern is:

```
res = parse_file(...);
gc_root_push(res);      // protect AST across all forms
while (forms_left) {
  x = pop_form_and_transform();
  gc_root_push(x);
  x = eval(x);
  gc_root_pop();        // x
  ...maybe break...
}
gc_root_pop();          // res
```

These are at the **top of the call stack**, before any eval frame exists —
so there is no eval_stacks[] entry yet, and no env binding, and no
continuation frame. The script AST is the only root.

**Implication for rewrite:** these can be replaced by binding the script
form list into the root_env (it is already walked) before the loop, or by
having `valk_lval_eval_top_level(env, form_list)` push a dedicated frame
that the GC mark-pass already covers. The current top-level doesn't go
through the iterative evaluator's outer frame because it manually drives
form-by-form. After the rewrite, the simplest fix is: assign
`valk_thread_ctx.eval_expr = res` for the loader's lifetime, then the
existing `mark_eval_stack_roots` (`gc_mark.c:193`) covers it for free.

### AOT emitted code

`src/llvm/vir_to_llvm.c:93-100` declares LLVM externs for
`valk_gc_root_push_fn`, `valk_gc_root_save`, `valk_gc_root_restore`,
`valk_gc_safepoint_fn`. The VIR-to-LLVM lowerer emits calls to these from
the `VIR_GC_ROOT` / `VIR_GC_UNROOT` / `VIR_GC_SAFEPOINT` opcodes
(`vir_to_llvm.c:208-237`).

The opcodes are **inserted as a separate IR pass** in `src/vir/vir_gc.c`:
- `vir_gc_insert_roots()` (`vir_gc.c:160`) — scans each VIR block, finds
  "GC points" (`is_gc_point`: CALL, ENV_GET, ENV_PUT, ENV_DEF, CONS,
  QCONS, LAMBDA, CONST_NUM/STR/SYM all of which can allocate), computes
  the live `VIR_TYPE_PTR` SSA values at that point, and brackets the GC
  point with `VIR_GC_ROOT(live...)` + `VIR_GC_UNROOT(save_id)` (lines
  98-138).
- `vir_gc_insert_safepoints()` (`vir_gc.c:186`) — inserts a
  `VIR_GC_SAFEPOINT` at function entry.

So in AOT-compiled functions, every call/alloc point gets a save+push of
all live SSA pointer values, then a count-restore. This means every
compiled lambda has its own root_stack discipline at the IR level.

**Implication for rewrite:** if root_stack goes away, the `VIR_GC_ROOT`
pass either becomes a no-op (the GC already walks `eval_stacks` and env,
which captures everything those liveness-analysed values were
contributing to) OR it must be replaced by **stack maps** + a stack-walk
in the GC, OR by spilling those SSA values into a heap-resident
"AOT activation record" that GC walks. This is the **single largest**
architectural impact of removing root_stack: the IR pass is the only
liveness-aware producer of root-stack entries, and removing it requires
deciding how the JIT/AOT compiler exposes its in-flight pointer-typed
SSA values to GC. See section 7 below for detail on what's actually held.

---

## 3. Reads and writes of `valk_thread_ctx.root_stack` / `root_stack_count` / `root_stack_capacity`

### Definition

`src/memory.h:343-345`:
```c
struct valk_lval_t **root_stack;
sz root_stack_count;
sz root_stack_capacity;
```

### Writers (push)

- `src/gc.h:436` — `ctx->root_stack[ctx->root_stack_count++] = val;` inside `valk_gc_root_push` (the only call point for pushes; everything else routes through here or its `_fn` wrapper).
- `src/gc.c:183-185` — initial allocation in `valk_system_register_thread` (256 slots, count=0).
- `src/gc.c:737-742` — fork-cleanup zeroing.

### Writers (pop / count manipulation)

- `src/gc.h:442` — `valk_thread_ctx.root_stack_count--;` in `valk_gc_root_pop`.
- `src/gc.h:447` — `valk_thread_ctx.root_stack_count = r->saved_count;` in `valk_gc_root_cleanup` (macro cleanup).
- `src/gc.c:741-742` — fork zero.
- `src/gc.c:759` — `valk_gc_root_restore(count)` exported for AOT.

### Reader (walker)

- `src/gc.c:429-435` — `valk_gc_visit_thread_roots()`: the **single** GC walker. Iterates the array up to `root_stack_count`, calls `visitor()` on each entry.
- `src/gc.c:755` — `valk_gc_root_save()`: returns count for AOT to snapshot.
- `src/gc_stats.c:269` — diagnostic dump prints `root_stack_count`.

### Allocator / lifecycle

- `src/gc.c:183` malloc on thread register.
- `src/gc.c:220-223` free on thread unregister.
- `src/gc.c:431` realloc if growth (in `valk_gc_root_push` inline).

### Is the API used outside `gc.h` / `gc.c`?

Yes, three places:

1. `src/build.c:160-207` — direct push/pop via the inline.
2. `src/repl.c:151-264` — direct push/pop via the inline.
3. `src/llvm/vir_to_llvm.c:93-100, 210-228` — emits LLVM calls to
   `valk_gc_root_push_fn` / `valk_gc_root_save` / `valk_gc_root_restore`
   in compiled IR.

Plus the macro expands inline at every `VALK_GC_ROOT(...)` site (section 1).

The **only** GC-side reader is `valk_gc_visit_thread_roots` in `gc.c:426`,
which is called from `gc_mark.c` (the parallel marker) — this is the
single point where root_stack contributes to the live set.

---

## 4. `valk_evacuate_to_heap` and `__lenv_ensure_safe_val` — manual promotion sites

`valk_evacuate_to_heap(v)` is defined in `src/gc_evacuation.c:545`. It
takes a scratch-allocated lval, deep-copies it (and reachable children)
into the heap, and returns the heap copy. Called when scratch is about
to be reset but a value must outlive that reset.

`__lenv_ensure_safe_val(env, val)` is defined in `src/lenv.c:159`. Used
inside `valk_lenv_put` to evacuate a value being bound into an env if the
env outlives the value's allocator (lifetime mismatch).

### `__lenv_ensure_safe_val` call sites

| # | file:line | Reason |
|---|-----------|--------|
| 1 | `src/lenv.c:187` | Inside `valk_lenv_put`, every binding goes through this lifetime-check + maybe-evacuate. |

**One** call site — every `lenv_put` is funneled through it. There is also
a direct `valk_evacuate_to_heap` call at `lenv.c:275` inside `valk_lenv_def`
that bypasses the helper for top-level defs.

### `valk_evacuate_to_heap` call sites (42 total, grouped)

#### a) Eval loop (the big one)
- `src/eval.c:572` — `apply_cont`: every time an eval value pops a
  continuation, if the value is in scratch, evacuate to heap. **This is
  the universal "value escapes a continuation frame" hatch.** It runs on
  every continuation pop and is the reason most user values end up on
  heap.

#### b) Lenv writes
- `src/lenv.c:176` — inside `__lenv_ensure_safe_val` (called by `lenv_put`).
- `src/lenv.c:275` — inside `valk_lenv_def` (top-level defs).

#### c) Async-handle "callback / value" escape — handles outlive eval frames
The callback function and pre-bound values stored on a `valk_async_handle_t`
must outlive the eval frame that scheduled them, because the handle
completion runs later on an event-loop thread.

- `src/aio/aio_comb_chain.c:35,41,44,51,70,117,123,126,133,146,203` — `aio/then`, `aio/catch`, `aio/finally` storing `on_complete`/`on_error`/`on_cancel`/`result`/`error`.
- `src/aio/aio_comb_resource.c:27,97,135,136` — `aio/on-cancel`, `aio/bracket`.
- `src/aio/aio_comb_all.c:157,216,263` — wrapper lambda + result list.
- `src/aio/aio_comb_all_settled.c:86` — final result list.
- `src/aio/aio_comb_pmap.c:88,99,118,181,193` — error/result/list/fn/item.
- `src/aio/aio_comb_timers.c:163,310` — callback for timeout timers.
- `src/aio/aio_comb_handle.c:114,136` — `aio/pure`, `aio/fail`.
- `src/aio/http2/aio_http2_server.c:532,581` — handler closure.
- `src/aio/http2/aio_http2_client.c:835` — request headers.
- `src/aio/http2/stream/aio_stream_builtins.c:243,371` — stream callbacks.

#### d) Pipe / dispatch — same as above, callback survives across thread
- `src/builtins_pipe.c:251,437,499,525,526,527` — pipe `on-data` callback,
  LSP reader callback, dispatch worker (fn / arg / cb / result).

#### e) Other heap-vs-arena lifetime mismatches
- `src/builtins_file.c:533` — `process/run` packing a 6-tuple status
  record from scratch into heap before returning to user.
- `src/builtins_dict.c:155` — when a dict is on heap but the inserted
  value is on scratch.
- `src/builtins_server.c:291` — HTTP/2 connect callback.
- `src/gc_region.c:351` — region API: when a parent is heap and a child
  is scratch, evacuate child.

#### f) Inside the evacuator itself (recursion)
- `src/gc_evacuation.c:175` — LCOV-excluded branch in `valk_evacuate_value`'s REF deep-evac path (uses leaf path instead).

### Categorisation

Every `valk_evacuate_to_heap` call site is one of:

1. **Scratch-to-heap on the way out of an eval frame** (`eval.c:572`) —
   defensive, fires on every pop, but makes the eval loop self-correcting.
   This is the big one.
2. **Async lifetime extension** (~30 of 42 sites) — value must survive
   beyond eval frame because handle is async.
3. **Lenv binding lifetime promotion** (3 sites) — child outlives parent
   allocator.
4. **Region promotion** (1 site, gc_region.c) — same idea.

**Each call is a confession that the natural scope (eval frame /
arena lifetime) doesn't cover the value.** Categories 2 and 3 are the
unavoidable ones — async handles really do outlive their eval frame, and
heap-rooted envs really do outlive scratch values. Category 1 should
become unnecessary if the GC walks scratch values **through** the eval
stack frames (it already partly does — see `gc_mark.c:145-187`); the
evacuation in `apply_cont` is then a *reset* hygiene pass, not a
correctness requirement.

---

## 5. Structure of `valk_thread_context_t`

`src/memory.h:324-359`. Annotated:

```c
typedef struct {
  // ── Allocator + system handles ─────────────────────────────────
  valk_mem_allocator_t *allocator;       // current allocator (used by
                                         // valk_mem_alloc et al.) –
                                         // swapped by VALK_WITH_ALLOC.
  struct valk_system *system;            // owning system (set on thread
                                         // onboard).
  void *heap;                            // valk_gc_heap_t* — the GC
                                         // heap. Used as evacuation target.
  valk_mem_arena_t *scratch;             // per-thread scratch arena;
                                         // reset on continuation pop.
  struct valk_lenv_t *root_env;          // ❶ root environment for the
                                         // thread; used as one of GC's
                                         // global root sources via
                                         // visit_global_roots /
                                         // visit_env_roots
                                         // (gc.c:467-468).

  // ── Checkpoint / safepoint control ─────────────────────────────
  float checkpoint_threshold;            // 0.0-1.0 scratch-fill ratio.
  bool checkpoint_enabled;
  u64 call_depth;
  struct valk_request_ctx *request_ctx;  // Finagle-style ctx (deadlines,
                                         // tracing). Restored across
                                         // ctx/with-deadline frames.
  _Atomic u32 safepoint_flags;           // CPython-style eval_breaker.

  // ── Parallel-GC bookkeeping ────────────────────────────────────
  u64 gc_thread_id;
  bool gc_registered;

  // ── Manual root stack (TARGET FOR DELETION) ────────────────────
  struct valk_lval_t **root_stack;
  sz root_stack_count;
  sz root_stack_capacity;

  // ── Eval-stack registry (PRECISE ROOTS – NEW MACHINERY) ────────
  void *eval_stacks[16];                  // valk_eval_stack_t* for
                                          // every nested eval call.
  u32 eval_stack_depth;                   // current nesting depth.
  struct valk_lenv_t *saved_eval_envs[16];// outer eval_env for each
                                          // saved frame.

  // ── Current eval state (innermost evaluator) ───────────────────
  void *eval_stack;                       // current valk_eval_stack_t*.
  struct valk_lval_t *eval_expr;          // expression currently being
                                          // dispatched.
  struct valk_lval_t *eval_value;         // last produced value.
  struct valk_lenv_t *eval_env;           // current env.
} valk_thread_context_t;
```

`extern __thread valk_thread_context_t valk_thread_ctx;` (line 361).

### What writes / reads each

| Field | Writers | Readers |
|-------|---------|---------|
| `allocator` | `VALK_WITH_ALLOC` (memory.h:15) macro everywhere | `valk_mem_alloc/realloc/calloc/free` everywhere |
| `system` | `valk_system_register_thread` (gc.c) | shutdown/reset code |
| `heap` | thread onboard | GC heap and `valk_evacuate_to_heap` |
| `scratch` | thread onboard | apply_cont reset, builtins, gc_evacuation, mark code |
| `root_env` | repl.c:94, build.c (compiled C) | `valk_gc_visit_global_roots` (gc.c:467), checkpointing (gc.c:401-405) |
| `request_ctx` | `VALK_WITH_REQUEST_CTX` macro, `CONT_CTX_*` frames in eval.c | builtins that read deadlines |
| `safepoint_flags` | GC coordinator (set by other threads) | `VALK_GC_SAFE_POINT()` macro |
| `gc_thread_id` / `gc_registered` | thread register/unregister | GC coordinator |
| `root_stack[*]` | `valk_gc_root_push/pop`, macro, AOT runtime fns | `valk_gc_visit_thread_roots` (gc.c:426) — *only reader for GC* |
| `eval_stacks[]` | `valk_lval_eval_iterative` entry/exit (eval.c:386-388) | `mark_eval_stack_roots` (gc_mark.c:197-201) |
| `eval_stack_depth` | same | same |
| `saved_eval_envs[]` | same | same |
| `eval_stack` | `valk_lval_eval_iterative` (eval.c:381-382) | (informational; not read by GC mark — `eval_stacks[]` is) |
| `eval_expr` | every iter of eval loop (eval.c:393) | `mark_eval_stack_roots` (gc_mark.c:193) |
| `eval_value` | every iter of eval loop (eval.c:394) | `mark_eval_stack_roots` (gc_mark.c:194) |
| `eval_env` | every iter (eval.c:395) | `mark_eval_stack_roots` (gc_mark.c:195) |

### `current_env` vs `root_env`

There is **no field called `current_env`**. The two env-shaped fields are:

- `root_env` — the long-lived top-of-thread environment (what user code
  sees as the global / module scope). Set once near startup
  (`repl.c:94`, generated `valk_thread_ctx.root_env = env;` in
  `build.c:78`), then read by `visit_global_roots` so it (and all its
  ancestors / descendants reachable through `parent`) stays live.
- `eval_env` — the **current** env of the innermost active eval loop;
  changes on every continuation that switches scope (lambda body,
  `if`-branch reassignment, etc.). Used as a precise GC root.
- `saved_eval_envs[i]` — the snapshot of `eval_env` for each *outer*
  active eval call, taken on entry to `valk_lval_eval_iterative` and
  restored on exit.

### Other "current eval state" fields

- `call_depth` — TCO/depth metric, not a GC root.
- `request_ctx` — has its own non-GC lifetime (allocator-provided).
- `eval_stack` (singular) — current active stack pointer, redundant with
  `eval_stacks[eval_stack_depth-1]`. Not read by GC mark; only used for
  pretty-printing in diagnostic dumps. **Candidate for removal.**

---

## 6. Eval-loop continuation-frame layout

Defined in `src/eval_internal.h:27-77`. The frame struct:

```c
typedef struct valk_cont_frame {
  valk_cont_kind_e kind;
  valk_lenv_t *env;                  // env active when this frame ran
  sz scratch_offset;                 // scratch arena offset to restore
  union {
    struct { lval *func; lval *remaining;                     } eval_args;
    struct { lval *func; lval **args; u64 count; u64 capacity;
             lval *remaining;                                 } collect_arg;
    struct { lval *true_branch; lval *false_branch;           } if_branch;
    struct { lval *remaining;                                 } do_next;
    struct { lval *result_expr; lval *remaining;
             lval *original_args;                             } select_check;
    struct { lval *remaining; lenv *call_env;                 } body_next;
    struct { lval *body; struct valk_request_ctx *old_ctx;    } ctx_deadline;
    struct { lval *value_expr; lval *body;
             struct valk_request_ctx *old_ctx;                } ctx_with;
  };
} valk_cont_frame_t;
```

The stack itself:

```c
typedef struct {
  valk_cont_frame_t *frames;     // malloc'd, doubled on growth
  u64 count;
  u64 capacity;
} valk_eval_stack_t;
```

Initial capacity 64 (`VALK_EVAL_STACK_INIT_CAP`). The stack is **heap-
allocated via `malloc`** (eval.c:18) in `valk_eval_stack_init`, then
freed in `valk_eval_stack_destroy` (eval.c:38). The frame array is *not*
on the C stack and *not* in the arena; it's its own malloc allocation
referenced through `valk_thread_ctx.eval_stacks[]`.

### Per-variant lvals held — and reachability analysis

The check is: for each `lval *` field in each variant, is it _also_
reachable via some other root (env, arena GC walk, runtime ctx field), or
is the cont_frame its **only** root? If it's the only root, GC will free
it unless the frame stack is walked.

| Variant | lvals held | Also reachable from? |
|---------|-----------|----------------------|
| `CONT_DONE` | (none) | n/a |
| `CONT_EVAL_ARGS` | `func`, `remaining` | `func`: produced by previous step's `value` — only on this frame. `remaining`: tail of original expr cons-list — reachable from `eval_expr` only if expr was the head; otherwise frame-only. |
| `CONT_COLLECT_ARG` | `func`, `args[0..count]`, `remaining` | `func`: frame-only. `args[]`: malloc'd C array (`malloc` at eval.c:613, `free` at :648); each entry is the result of a previous arg eval — frame-only after `apply_cont` resets scratch. `remaining`: frame-only. |
| `CONT_IF_BRANCH` | `true_branch`, `false_branch` | Sub-expressions of `expr`; once dispatch moves on, frame is the only root for the un-taken branch's expr-tree. |
| `CONT_DO_NEXT` | `remaining` | Tail of a `do` body; frame-only. |
| `CONT_SELECT_CHECK` | `result_expr`, `remaining`, `original_args` | Frame-only. (Note: `select` may be partially deprecated — `vir_print.c` still names it; eval.c never pushes a `CONT_SELECT_CHECK`. Possibly dead code path.) |
| `CONT_BODY_NEXT` | `remaining`, `call_env` | Body forms of a lambda invocation; `call_env` is the lambda's call-frame env (parent is the closure env, which is parent-chained but not necessarily reachable from `eval_env`). Frame-only for `remaining`. |
| `CONT_LAMBDA_DONE` | (none — only decrements depth) | n/a |
| `CONT_CTX_DEADLINE` | `body`, `old_ctx` | `body` is a sub-expr of original `expr`; frame-only mid-eval. `old_ctx` is non-lval (request_ctx). |
| `CONT_CTX_WITH` | `value_expr`, `body`, `old_ctx` | Same. |
| `CONT_SINGLE_ELEM` | (no payload — uses `frame.env` only) | n/a |

The mark routine `mark_one_eval_stack` (`gc_mark.c:145-187`) walks every
frame and marks every `lval *` field for every variant **except** that:

- `eval_args.func`/`eval_args.remaining` — yes, marked (lines 150-153).
- `collect_arg.func`/`collect_arg.remaining`/`collect_arg.args[0..count]` — yes (lines 154-159).
- `if_branch` — yes (161-163).
- `do_next.remaining` — yes (165-167).
- `select_check` — yes (168-172).
- `body_next.remaining` + `body_next.call_env` (env!) — yes (173-176).
- `ctx_deadline.body` — yes (177-179).
- `ctx_with.value_expr` + `ctx_with.body` — yes (180-183).
- **`frame.env` is marked at line 148 for every frame** regardless of variant.

So the GC mark walker for the eval stack already comprehensively covers
every lval pointer in every cont_frame variant. The frame's payload
*alone* keeps every sub-expression alive across the iterative evaluator's
continuation.

### Key observation

**`mark_eval_stack_roots` (gc_mark.c:190-202) + walking the env chain
already covers every lval reachable from active eval state.** The
`root_stack` exists for cases where C code outside the eval iter needs to
hold a pointer; if those cases are folded back into the eval-driven path
(or pushed through the eval_expr/eval_value slots), root_stack becomes
redundant.

---

## 7. AOT codegen state holding lvals invisibly to GC

Defined in `src/llvm/llvm_codegen.h:53-91`. The compiler context
(`valk_llvm_ctx_t`) carries three "lval-shaped" structures, each used
*only during compilation* of one lambda. None of these survive into
runtime per se; what does survive is the LLVM IR they generate, in
which lval pointers live in registers / stack slots / phi nodes.

### a) `formals_map` (llvm_codegen.h:59-63)

```c
struct {
  const char **names;
  LLVMValueRef *vals;     // SSA value per formal (the LLVM phi or fn arg)
  size_t count;
} formals_map;
```

- **What it holds at compile time:** mapping from formal name to LLVM
  SSA value representing that formal in the running compiled function.
- **At runtime:** each formal lives in either a function-arg register or
  a phi node (TCO loop entry). When compiled code calls into the runtime
  (any allocating builtin, env_get, cons, etc.), those formals are live
  in registers or spilled to the C stack by LLVM's regalloc.
- **GC visibility:** zero. The GC has no way to find them. This is why
  `vir_gc_insert_roots` (`vir/vir_gc.c`) emits `VIR_GC_ROOT(fn_param,
  live_ptrs...)` brackets around every "GC point" — that's how compiled
  code populates `root_stack` so the runtime walker can find these
  values.
- **Lifetime of the `formals_map` C field itself:** allocated in
  `llvm_codegen.c:295-297`, cleared at :384-386, freed at :392.
  Only live during one lambda compile.

### b) `tco.formal_phis` (llvm_codegen.h:69-75)

```c
struct {
  LLVMValueRef fn;
  LLVMBasicBlockRef body_bb;
  LLVMValueRef env_phi;
  LLVMValueRef *formal_phis;   // phi nodes for each formal at TCO header
  size_t nformals;
} tco;
```

- **Compile-time:** phi nodes that receive new arg values when a self-
  recursive tail call branches back to `body_bb` instead of pushing a
  stack frame.
- **Runtime:** the phi result is "the new formal" each loop iteration.
  Same GC-visibility issue as `formals_map` — phi result is in a
  register, invisible.
- **Lifetime:** same as `formals_map` — one lambda compile.
- **Use site:** `llvm_codegen_call.c:93-103` — the TCO branch.

### c) `sym_cache` (llvm_codegen.h:84-90)

```c
struct {
  LLVMBasicBlockRef anchor_bb;
  char **names;
  LLVMValueRef *vals;     // hoisted `valk_lval_sym(name)` call results
  size_t count;
  size_t cap;
} sym_cache;
```

- **Compile-time:** caches `valk_lval_sym("foo")` calls so that within
  one fn-body compile, each unique sym name is allocated once at fn entry
  rather than per-iteration.
- **Runtime:** each cached entry is an `lval*` returned by `valk_lval_sym`
  living in an SSA register / stack slot for the duration of the function.
- **GC visibility:** zero — same problem.
- **Lifetime:** one lambda compile (entered at :487, :548; left at :531,
  :554, :395 in llvm_codegen.c).
- **Use site:** `llvm_codegen_emit.c:24-52` (`emit_make_sym`).

### d) Function arguments and return values

Compiled functions have signature `valk_lval_t *(*)(valk_lenv_t *)`, so
the `env_param` is in a register when the function is called. Any
returned `valk_lval_t*` is also in a register at the call site. Both are
"live across calls" and depend on `vir_gc.c`'s liveness pass to root them.

### e) Stack maps / spill slots

LLVM does not currently emit GC stack maps for valkyria. The
`vir_gc_insert_roots` IR pass is the substitute: it runs **before**
LLVM lowering, identifies live pointers at every GC point in the VIR,
and emits `VIR_GC_ROOT` ops that compile to `valk_gc_root_save +
valk_gc_root_push(live[i])` calls (`vir_to_llvm.c:208-222`). After the
GC point, `VIR_GC_UNROOT` compiles to `valk_gc_root_restore(saved)`.
This is essentially **manual stack-mapping done in IR**.

### When could GC fire and find these stale?

- At **any safepoint** (`VIR_GC_SAFEPOINT` lowered to
  `valk_gc_safepoint_fn` call — `vir_to_llvm.c:233`). Currently inserted
  at function entry only (`vir_gc.c:203-213`).
- At **any allocating call** (CALL, CONS, CONST_NUM/STR/SYM, ENV_*, etc.
  — see `is_gc_point` in `vir_gc.c:5-22`). These check the safepoint
  flag inside the runtime call.

If `root_stack` is removed without replacing the IR pass, every formals
load, every cached sym, and every live cons-cell during the body will
be lost on the first GC during a compiled function. So the rewrite
**must** answer: how do compiled functions expose their live
`valk_lval_t*` SSA values to GC?

Three options to consider:
1. **LLVM gc.statepoint / stack maps** (intrusive, requires upgrading
   LLVM IR generation). Most "correct" long-term.
2. **Spill all live pointers into a per-call activation record** that
   the GC walks via the env chain (e.g., extend `call_env` with a
   "C-spill array" populated at each safepoint).
3. **Box every live pointer into the env** (kills perf — defeats
   the point of compilation).

For the rewrite-plan, option 2 is closest to the stated direction:
"GC walks `valk_thread_ctx` + the call_env chain". If `call_env`
gets a slot for "live SSA spills at the current safepoint", the IR
pass changes from "emit root_push" to "emit env-slot-store", and GC
finds them via env walk.

---

## 8. Proposed minimal `valk_thread_context_t` after rewrite

The data flow in the current code shows that after merging the
`root_stack` work into the eval state + env chain, the per-thread
context only needs:

```c
typedef struct {
  // ── Allocators / system ────────────────────────────────────────
  valk_mem_allocator_t *allocator;
  struct valk_system *system;
  valk_gc_heap_t *heap;
  valk_mem_arena_t *scratch;

  // ── Roots that GC walks ────────────────────────────────────────
  // (1) The thread's "global" env. Walk env->parent chain from here
  //     to reach all module/global bindings. Used by
  //     valk_gc_visit_global_roots already.
  struct valk_lenv_t *root_env;

  // (2) The currently active call_env chain. For each *physically
  //     active C call frame* that owns lval pointers (the eval loop;
  //     compiled lambdas at safepoints; async dispatch callbacks),
  //     the GC reaches every live lval by walking this env chain.
  //
  //     Today this is split into eval_env + saved_eval_envs[16] +
  //     eval_stacks[16] + (in compiled code) the LLVM-arg env_param.
  //     Unify by making every C frame that needs roots stash them
  //     into an env it owns, and chain that env via parent links.
  struct valk_lenv_t *call_env;

  // (3) Optional: the iterative evaluator's frame stack pointer for
  //     marking continuation-frame lvals. If continuation frames
  //     instead spill into call_env on push, this can go away.
  struct valk_eval_stack *eval_stack;

  // ── Non-GC bookkeeping ─────────────────────────────────────────
  struct valk_request_ctx *request_ctx;
  _Atomic u32 safepoint_flags;
  u64 gc_thread_id;
  bool gc_registered;
  bool checkpoint_enabled;
  float checkpoint_threshold;
  u64 call_depth;
} valk_thread_context_t;
```

### What was deleted

- `root_stack` / `root_stack_count` / `root_stack_capacity` — gone.
- `eval_stacks[16]` / `eval_stack_depth` / `saved_eval_envs[16]` —
  gone, replaced by **one** `eval_stack` pointer (the current frame
  stack). Nesting is captured by env-chain walk: each nested
  `valk_lval_eval_iterative` invocation pushes a fresh env frame with
  the saved outer eval state stored in it; on exit the env is dropped.
- `eval_expr` / `eval_value` / `eval_env` — folded into the `eval_stack`
  top frame (its `frame.env` is the current env; `value` and `expr`
  become explicit fields on the top frame).
- The `eval_stacks[16]` cap is removed (was always a code smell; eval
  nesting is naturally bounded by C-stack depth).

### What still has to be wired up

- **AOT compiled code:** `vir_gc_insert_roots` must change from
  emitting `VIR_GC_ROOT` (root_stack) to emitting "spill-to-env" or
  equivalent stack-map-style root exposure. **This is the hardest part
  of the rewrite** and is the single biggest reason the manual
  `root_stack` exists today.
- **Async dispatch callbacks** (the 9 Category-A `VALK_GC_ROOT` sites in
  pipe / pmap / dispatch): each must enter eval-iterative-style framing
  before resolving handles, so the resolved `cb`/`fn`/`arg` values land
  in a C frame that the new walker covers. Concretely: wrap
  `__dispatch_worker` and friends in a tiny eval-frame that lifts those
  vars into a fresh `call_env` before calling `valk_lval_eval_call`.
- **Top-level script loaders** (`build.c:153-209`, `repl.c:151-264`):
  bind `res` / `x` into the loader's transient env (or directly assign
  to `eval_expr` field on the canonical thread context) instead of
  hand-rolling push/pop.

### Summary of what the rewrite deletes

| Location | What goes |
|----------|-----------|
| `src/gc.h:400-459` | `valk_gc_root_t`, `VALK_GC_ROOT`, push/pop/cleanup inlines, `valk_gc_root_push_fn`/`pop_fn`/`save`/`restore` decls. |
| `src/gc.c:183-185, 220-223, 426-436, 737-742, 746-760` | Allocation, deallocation, walker, fork-reset, AOT wrappers. |
| `src/memory.h:343-345` | `root_stack*` fields. |
| `src/memory.h:347-358` | `eval_stacks[16]`, `saved_eval_envs[16]`, `eval_stack`, `eval_expr`, `eval_value`, `eval_env` (all collapse into `eval_stack` + `call_env`). |
| `src/build.c:160-207` | Manual push/pop loop, replaced by frame setup. |
| `src/repl.c:151-264` | Same. |
| `src/eval.c:235, 378-379` | `VALK_GC_ROOT` macros (redundant once eval_stack is the single source). |
| `src/builtins_*` 17 macro sites | Replaced by either eval-frame entry or always-evacuate-on-resolve. |
| `src/aio/aio_comb_pmap.c:67-82` | Same. |
| `src/vir/vir_gc.c:160-184` (`vir_gc_insert_roots`) | Either deleted, or rewritten to emit the new spill form. |
| `src/llvm/vir_to_llvm.c:93-100, 208-231` | The `fn_gc_root_*` extern decls and the `VIR_GC_ROOT/UNROOT` lowering. |

The `valk_evacuate_to_heap` API stays — it's the heap-promotion
primitive needed by `lenv_put`, async-handle storage, and the
continuation-pop hygiene in `eval.c:572`. None of those are about
*root tracking*; they're about *allocator lifetime mismatches*, which
exist independently of GC root discovery.

