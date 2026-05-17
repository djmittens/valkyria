# JIT for Script Execution — Shipping State & Path to Default-On

## Goal

`valk script.valk` should JIT-compile the script's lambdas using the
**same compilation pipeline as `valk --build`** and execute them
in-process via LLVM ORC LLJIT — bypassing the tree-walking interpreter
for hot code without requiring a separate build step.

## Current shipping state (this session)

Infrastructure complete, opt-in via env var:

```
VALK_JIT=1 build/valk script.valk     # ~10x speedup on numeric/recursive code
build/valk script.valk                # default: tree-walking interpreter
```

Verified speedup: `fact(15)` in a 50000-iter `sumloop` runs in
**0.82s with JIT vs 8.04s interpreted** — same output. Compile cost
(~75ms for stdlib) amortizes after the first non-trivial top-level
expression.

`make test` baseline preserved: 4070 pass / 78 fail (same 5 pre-existing
LSP suites). UAT: 82 pass / 3 fail (same flakes).

## Architecture

Single AOT compilation pipeline serves both `--build` and JIT:

```
                       parse + interp eval defs (populates env)
                                      |
                                      v
                    valk_aot_compile_env(env, &count)   (build_aot.c)
                          phases 1-5: candidate scan,
                          slow body via VIR, fast variant +
                          slow_adapter, verify, optimize
                                      |
                          +-----------+-----------+
                          |                       |
              --build:                   JIT (VALK_JIT=1):
              valk_aot_emit_object       valk_jit_compile_env (llvm_jit.c)
              + write_dispatch_c         hands ctx->module to ORC LLJIT,
              + image dump + link        looks up each native_name via
              -> standalone binary       dlsym, populates v->fun.native_fn
                                         -> in-process execution
```

JIT trigger point in `repl.c` script mode: between pass 1 (defs) and
pass 3, just before the FIRST non-def-like form runs. By that point env
has stdlib + every top-level def from the script; subsequent calls
dispatch via `eval.c:348`'s `func->fun.native_fn`. Heuristic: defs
include `(def ...)`, `(sig ...)`, `(load ...)`. Anything else triggers
JIT.

## Why opt-in (not default-on yet)

The user explicitly asked for default-on, but enabling by default broke
8 test suites and made `make check` segfault. Three classes of
codegen bugs are exposed when JIT covers arbitrary user code (which
`--build` of the LSP doesn't trigger):

### 1. Reachability bug under heavy parallel load (pre-existing)

Same crash signature as commit `2c1d98e` from before the GC root cleanup:

```
#0  libc + 0x177f2f                    ; strcmp on freed string
#1  valk_lenv_get
#2  valk_aot_NNN                       ; JIT'd or AOT'd Lisp lambda
```

A worker thread calls a JIT'd lambda that does `lenv_get`; the env's
`keys[i]->str` has been swept. Conservative stack scanning
(`gc_mark.c::scan_thread_native_stack`) substantially reduced
frequency but didn't eliminate. Manifests in:
- `make check` (segfaults during validation phase 2)
- UAT `24_stress_large` and `29_lifecycle_chaos` (under parallel load)
- Various aio/http tests when many handlers run concurrently

Root cause is upstream of JIT — same bug affects `valk-lsp-aot` under
typing load. JIT just exposes it on more code paths because more user
lambdas now run as native code.

### 2. Async/threading interactions (likely codegen)

Several aio/threading tests fail under JIT but pass interpreted:
- `aio/test_aio_traverse` (traverse with transformation)
- `aio/test_aio_debug`
- `aio/test_async_monadic_suite`
- `lang/test_chm` (chm-thread-stress)
- `stress/test_pmap_heavy_alloc`

Likely candidates: TLS access in compiled code, env capture across
worker threads, or safepoint coordination with concurrently-running
JIT'd code. Needs investigation per failure.

### 3. HTTP integration tests

- `http/test_http_minimal`
- `http/test_http_integration`
- `lang/test_debug_handler`

Similar shape — async handlers running compiled lambdas.

## Codegen bugs already fixed in this session

Two were caught and fixed before opt-in flip:

### A. `body_is_fast_safe` mis-classified single-sexpr bodies

A body shaped `{\ {n} {+ start n}}` (qexpr containing one form whose
head is a SYM) was iterated as a do-block of three forms (the sym `\`,
the qexpr `{n}`, the qexpr `{body}`), missing that the body IS a `\`
form. Result: closure-returning lambdas wrongly flagged fast-safe and
their inner closures captured `valk_aot_root_env` instead of the call
env.

Fix in `llvm_codegen.c::valk_llvm_body_is_fast_safe`: when first
unwrapped element is a sym, treat the cons as a single sexpr and check
its head (matches `eval.c:355` and `vir_lower_lambda_body_with_env`'s
shape convention).

### B. Closures and macros AOT'd when they shouldn't be

`is_aot_candidate` accepted any non-builtin LVAL_FUN with a body. Two
classes shouldn't be:
- **Closures** — captured non-trivial env. AOT codegen discards env
  capture (fast variant uses `valk_aot_root_env`; slow uses caller's
  call_env). Detection: `v->fun.env != build_env`.
- **Macros** — bodies typically use `(quasiquote ...)` and
  `(unquote ...)`, neither of which VIR lowers as special forms; they
  fall through to `valk_lval_eval_call` against env where neither is
  bound, returning Error. Macros run only at expansion time anyway —
  `--build` mode never calls them at runtime, but JIT does (via
  `(eval {macro-using-form})`). Detection: `v->flags & LVAL_FLAG_MACRO`.

Both fixed in `build_aot.c::is_aot_candidate`.

## Path to default-on

1. **Fix the reachability bug.** Same fix unlocks AOT-LSP under load
   (commit `2c1d98e`'s workaround can then be removed). Likely
   investigation: what makes a worker-thread-held env's `keys[i]->str`
   unreachable to conservative scan? Candidates:
   - The string buffer behind `keys[i]` is allocated separately from
     the keys array; if the array is on the C stack but the strings
     are heap-allocated and not referenced elsewhere, sweep frees
     them.
   - Check `valk_lenv_t` allocation path — are `symbols.items[i]->str`
     and the items themselves separately allocated?

2. **Fix the async/threading codegen bugs.** Each failing test is a
   minimal repro waiting to be reduced. Likely common cause is
   single-threaded vs multi-threaded codegen assumptions (e.g., a
   mutable global the codegen relied on being the calling thread's,
   or env capture across thread boundaries).

3. **Verify `make test` clean with default-on.**
4. **Flip the default**: change `jit_should_compile()` in
   `repl.c:55` to default-on, rename env var to `VALK_NO_JIT`, update
   docs.
5. **Stretch goal — tier-up.** Currently JIT compiles every eligible
   lambda upfront (~75ms for stdlib). For very small scripts this is
   net-negative. Tier-up would interpret first, profile call counts,
   JIT only hot lambdas. Out of scope for v1.

## Files in this feature

- `src/llvm/build_aot.h`, `build_aot.c` — split out `valk_aot_compile_env`
  as the shared compile-to-module entry point. `valk_build_emit_aot`
  (used by `--build`) becomes a thin wrapper. Tightened
  `is_aot_candidate` to exclude closures and macros.
- `src/llvm/llvm_codegen.c` — fixed `valk_llvm_body_is_fast_safe`
  shape convention.
- `src/llvm/llvm_jit.h`, `llvm_jit.c` — new ORC LLJIT layer:
  `valk_jit_compile_env`, `valk_jit_free`, `valk_jit_compiled_count`.
  Adopts the codegen ctx's module (steals it before ctx_free), creates
  a JITDylib with `LLVMOrcCreateDynamicLibrarySearchGeneratorForProcess`
  for runtime symbol resolution, walks env to populate `v->fun.native_fn`
  via `LLVMOrcLLJITLookup`. Sets `valk_aot_root_env = env`.
- `src/repl.c` — JIT trigger point in script-mode pass 3 before first
  non-def form. Weak-extern `valk_jit_compile_env` (so non-LLVM build
  wouldn't break). Process-lifetime `g_script_jit` handle (intentionally
  leaked at exit).
- `CMakeLists.txt` — added `src/llvm/llvm_jit.c` to `valk_llvm` lib;
  added `-Wl,-u,valk_jit_compile_env` to force the static archive
  pull-in.

## Smoke test (kept handy in /tmp)

`/tmp/jit_bench.valk`:
```
(fun {fact n}
  {if (== n 0) {1} {* n (fact (- n 1))}})
(fun {sumloop n acc}
  {if (== n 0) {acc} {sumloop (- n 1) (+ acc (fact 15))}})
(println "fact(15) = %d" (fact 15))
(println "sumloop(50000, 0) = %d" (sumloop 50000 0))
```

Time JIT vs interp:
```
time build/valk /tmp/jit_bench.valk           # ~8s interp
time VALK_JIT=1 build/valk /tmp/jit_bench.valk # ~0.8s JIT
```
