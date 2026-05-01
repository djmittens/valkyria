# AOT-Compiled Code Missing GC Safe Points Around Symbol Lookup

## Overview

`valk_lval_eval_call` invoked from AOT-compiled code (`valk_aot_NNN`)
calls `valk_lenv_get`, which walks `env->symbols.items[]` and does
`strcmp(key->str, items[i])`. Under typing load on the LSP, this
`strcmp` segfaults because the copying GC has relocated the symbols
array — the local pointer in `lenv_get`'s frame is now pointing at
unmapped or freed memory.

Reproduction: open a sizable `.valk` file in nvim, edit two lines, the
LSP crashes with SIGSEGV. Backtrace consistently shows
`__strcmp_avx2 → valk_lenv_get → valk_aot_NNN`. coredumpctl history
has 8+ instances over the past day, all the same signature, all in
AOT-compiled function call frames. Interpreted-mode LSP
(`build/valk-lsp` wrapper running `valk scripts/lsp/main.valk`) does
NOT crash on the same workload — strongly implicating a code-gen gap
specific to AOT.

The current workaround (committed alongside this spec) is to default
`build/valk-lsp` to interpreted mode. AOT binary remains at
`build/valk-lsp-aot` for reproduction. This spec covers the actual fix.

## Why It Crashes

valk's GC is a copying collector (`valk_evacuate_to_heap`,
`valk_evacuate_leaf`). When GC fires:

1. STW: all threads must reach a safe point (`VALK_GC_SAFE_POINT()`)
   so GC knows where their roots are.
2. Mark: walk roots, mark live objects.
3. Evacuate: relocate live objects to fresh pages, free old pages.
4. Update: rewrite root pointers to new locations.

Tree-walking interpreter inserts safe points at every function
call/loop iteration. AOT-compiled code in `src/aot_codegen.c` (or
wherever the AOT pipeline is) currently doesn't insert safe points
around `valk_lenv_get` call sites. The compiled function holds a
pointer to `env` (or env's symbols.items) in a register or stack slot
across the call. If GC runs between the AOT function loading the env
pointer and `lenv_get` dereferencing it, the pointer is stale.

The interpreter avoids this because every `valk_lval_eval_iterative`
call is wrapped with safe point checks that pause the thread before
touching env memory.

## Requirements

### AOT Safe-Point Insertion

Identify every call site in AOT-generated code that invokes a function
which can transitively touch env memory:
- `valk_lval_eval_call`
- `valk_lenv_get`
- `valk_lval_eval_iterative`
- Any builtin marked GC-touching

Before each such call, emit a `VALK_GC_SAFE_POINT()` equivalent in the
generated code. The macro polls `valk_thread_ctx.safepoint_flags` and
parks the thread at the GC barrier when a STW is requested.

### GC Root Reporting From AOT Frames

When AOT code holds GC-tracked pointers in registers or stack slots
across a call, those pointers must be reported as roots when GC pauses
the thread. Two acceptable strategies:

1. **Conservative stack scan**: GC walks the AOT thread's stack and
   treats anything that looks like a heap pointer as a root. Simpler
   but pins extra objects.
2. **Stack maps / GC descriptors**: AOT codegen emits a side table
   describing which stack slots and registers hold pointers at each
   safe point. Precise but more codegen work.

Either is acceptable. Document which one is implemented.

### `valk_lenv_get` Fast-Path Hardening

Independent of AOT: even with safe points, a misbehaving caller (or
future bug) could walk a stale env pointer. Make `lenv_get` defensive:

- Validate `env->symbols.items != NULL` before dereferencing
  (already partially done at lenv.c:190 but only in `lenv_put`)
- Bound-check `i < env->symbols.count` reading symbols.count once into
  a local variable to avoid race-induced over-read

These don't fix the root cause but turn silent SEGV into a clean error
when the bug recurs.

## Reproduction Steps

```bash
# 1. Switch to AOT binary (workaround removed)
VALK_LSP_USE_AOT=1 build/valk-lsp < /dev/null  # quick sanity check

# 2. In nvim, open scripts/lsp/lsp.valk (large file)
# 3. Edit two lines (any change)
# 4. coredumpctl list valk-lsp-aot  ← should show new SIGSEGV
# 5. coredumpctl info <pid>  ← backtrace should show
#    valk_aot_NNN -> valk_lenv_get -> __strcmp_avx2
```

## Verification Strategy

Once safe points are inserted:

```bash
# Build AOT binary
make build/valk-lsp-aot

# Stress test: 200 didChange + 50 sem requests, 10 iterations
# (this saturates GC pressure; user reports got 1 GB GC reclaims in 9s)
for i in $(seq 1 10); do
  python3 /tmp/probe_stress.py /home/nik/src/valkyria/build/valk-lsp-aot
done

# No new core dumps:
test "$(coredumpctl list valk-lsp-aot --since='10 minutes ago' 2>&1 | grep -c SIGSEGV)" -eq 0
```

## Acceptance Criteria

- [ ] AOT codegen emits safe-point check before every `valk_lval_eval_call` invocation: `grep -c 'safepoint\|gc_safe_point' src/aot_codegen.c` returns > 0 (matches the call-site emission count)
- [ ] AOT codegen emits safe-point check before every `valk_lenv_get` invocation: same grep > 0 for that emission site
- [ ] GC root reporting strategy documented in `src/aot_codegen.c` header comment: `grep -c 'GC root\|stack scan\|stack map' src/aot_codegen.c` returns >= 1
- [ ] `lenv_get` snapshots `symbols.count` into a local before the loop: `grep -c 'count.*=.*env->symbols.count' src/lenv.c` returns >= 1 in `valk_lenv_get`
- [ ] Stress probe against AOT binary produces zero crashes over 10 runs: `for i in $(seq 1 10); do python3 /tmp/probe_stress.py build/valk-lsp-aot >/dev/null 2>&1; done && coredumpctl list valk-lsp-aot --since='10 minutes ago' 2>&1 | grep -c SIGSEGV` returns 0
- [ ] AOT binary survives a 60-second nvim editing session against `scripts/lsp/lsp.valk`: manual repro per the steps above, no core dumps generated
- [ ] Workaround removed: `build/valk-lsp` is the AOT binary directly (delete the wrapper script logic in Makefile that routes to interpreted mode)

## Non-Requirements

- This spec does NOT change the GC algorithm (still copying)
- Does NOT change the interpreter — the interpreter already works
- Does NOT touch `lenv_put`'s array-grow logic — runtime mutation of
  the global env is also potentially unsafe but not the cause of the
  observed crashes (verified: traced lenv_put calls, all global-env
  mutations happen on one thread during init, never at runtime)

## Dependencies

None. This is a runtime correctness fix that stands on its own.

## Files Likely Affected

- `src/aot_codegen.c` (or equivalent — the AOT compilation pipeline)
- `src/lenv.c` (defensive snapshot of count)
- `src/gc.h` / `src/gc.c` (if root reporting needs new public API)
- `Makefile` (remove wrapper logic once AOT is safe)
- `test/test_aot_safepoints.c` (new test exercising GC under AOT load)
