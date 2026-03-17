# Scratch Arena Stack Discipline

## Overview

Replace the current "fill scratch → panic-evacuate all roots → reset" model
with stack-discipline checkpointing at eval boundaries. Each continuation
frame saves the scratch offset on push. When the frame is consumed (sub-
expression reduces to a result), only the result value is promoted to heap
and the scratch offset is restored — instantly freeing all intermediates.

This eliminates scratch overflow as a normal-case event, removes the
expensive root-env walk from checkpoints, and keeps heap pressure to the
minimum: only values that escape an expression boundary hit the heap.

## Dependencies

- Requires `scratch-00-dict-value-type.md` — dicts must be a first-class
  type with structural evacuation so the result promotion at eval boundaries
  can deep-copy dict results correctly. Without this, dict values stored in
  scratch would not be properly promoted.

## Architecture

```
    eval (+ (f 1) (f 2))

    push CONT_EVAL_ARGS          save scratch_offset = S0
    ├─ eval `+`  → builtin       promote result, restore to S0
    │
    push CONT_COLLECT_ARG        save scratch_offset = S1
    ├─ eval `(f 1)` → R1         promote R1 to heap, restore to S1
    │   └─ all intermediates from (f 1) instantly freed
    │
    push CONT_COLLECT_ARG        save scratch_offset = S2
    ├─ eval `(f 2)` → R2         promote R2 to heap, restore to S2
    │   └─ all intermediates from (f 2) instantly freed
    │
    apply + with R1, R2          result promoted by parent frame
```

Scratch usage is bounded by ONE sub-expression's intermediates at a time,
regardless of total program size. The 128 MB arena should never fill.

## Requirements

### Scratch Offset in Continuation Frame

Add `sz scratch_offset` to `valk_cont_frame_t` in `src/eval_internal.h`,
outside the union (next to `kind` and `env`):

```c
typedef struct valk_cont_frame {
  valk_cont_kind_e kind;
  valk_lenv_t *env;
  sz scratch_offset;
  union { ... };
} valk_cont_frame_t;
```

### Save Offset on Frame Push

At every `valk_eval_stack_push` call site in `src/eval.c`, capture the
current scratch arena offset into the frame:

```c
valk_mem_arena_t *scratch = valk_thread_ctx.scratch;
sz offset = scratch ? scratch->offset : 0;
```

Set `.scratch_offset = offset` in the frame initializer. There are
approximately 12 push sites (CONT_EVAL_ARGS, CONT_COLLECT_ARG,
CONT_IF_BRANCH, CONT_DO_NEXT, CONT_SELECT_CHECK, CONT_BODY_NEXT,
CONT_SINGLE_ELEM, CONT_LAMBDA_DONE, CONT_CTX_DEADLINE, CONT_CTX_WITH,
and the initial CONT_DONE).

To avoid repetition, the save can be done inside `valk_eval_stack_push`
itself (reads `valk_thread_ctx.scratch->offset` and stores it in the
frame before pushing).

### Promote Result and Restore on Frame Pop

At `apply_cont` in `src/eval.c`, after `valk_eval_stack_pop(&stack)` (line
523) and before the `switch (frame.kind)` dispatch (line 525), insert:

```c
if (value != NULL && LVAL_ALLOC(value) == LVAL_ALLOC_SCRATCH) {
  value = valk_evacuate_to_heap(value);
}
valk_mem_arena_t *scratch = valk_thread_ctx.scratch;
if (scratch && frame.scratch_offset < scratch->offset) {
  scratch->offset = frame.scratch_offset;
}
```

This promotes the result value (and its transitive closure) to the heap,
then restores scratch to the saved offset — instantly freeing all
intermediate allocations from the sub-expression that just completed.

The `frame.scratch_offset < scratch->offset` guard prevents restoring
to a stale offset if scratch was already restored by a deeper frame.

**CONT_DONE special case**: When `CONT_DONE` is popped, the result is
the final value of the entire eval call. It should be promoted but scratch
should NOT be restored — the caller manages scratch lifetime. The initial
CONT_DONE frame's `scratch_offset` should be set to the current offset at
eval entry (so the guard prevents restoration).

### Simplify Checkpoint

With eval-boundary promotion, the current `valk_checkpoint` in
`src/gc_checkpoint.c` does far less work:

1. **Remove root env walk** (lines 119-121). Environment values are already
   safe — `valk_lenv_put` has a write barrier (`__lenv_ensure_safe_val`)
   that promotes scratch values when stored into heap environments.

2. **Remove eval stack walk** (lines 75-87). The eval loop now promotes
   results at frame boundaries. There should be no surviving scratch
   values in continuation frames.

3. **Keep the scratch reset** (line 154). If a checkpoint fires (e.g.,
   during STW GC coordination), it should still reset scratch. But the
   evacuation work should be minimal because most values were already
   promoted by the eval loop.

The checkpoint function becomes a simple "reset scratch if any allocations
happened" with optional stats tracking. The heavy root-walking logic can
be removed or gated behind a debug flag.

### Overflow Path as Safety Net

Keep the existing scratch overflow path in `memory.c` (lines 210-225)
including the warning log we just added. With stack-discipline
checkpointing, overflow should never trigger in normal operation. If it
does, the warning makes it immediately visible.

The overflow counter can be checked in tests to verify the new system
works: after running the test suite, `scratch->stats.overflow_fallbacks`
should be 0 (or near-zero).

### VALK_GC_SAFE_POINT Adjustment

The `VALK_GC_SAFE_POINT()` slow path in `src/gc.c` currently triggers
checkpoint evacuation when `VALK_SP_STW` is set. With the simplified
checkpoint, this path should:

1. Still reset scratch (to ensure arena doesn't hold stale data during STW)
2. Still participate in STW barriers
3. No longer need to walk root env or eval stacks for evacuation

The threshold-based checkpoint check (`valk_should_checkpoint`) is no
longer needed — scratch stays small due to per-frame restoration. It
can be removed or kept as a defensive assertion ("if scratch exceeds
75%, something is wrong — log a warning").

## Non-Requirements

- No changes to the aio/pmap worker evacuation path (workers already
  evacuate results and reset their own scratch correctly)
- No changes to dict internal layout (handled by spec 00)
- No changes to the GC mark-sweep collector itself
- No changes to environment allocation (already heap-allocated)
- No changes to AST parsing (already uses heap allocator)

## Error Handling

| Condition | Response |
|-----------|----------|
| `valk_evacuate_to_heap` returns NULL | Propagate the original value (defensive — should not happen if heap has space) |
| `scratch` is NULL at push/pop time | Skip offset save/restore (no scratch arena in this thread) |
| Scratch offset goes backwards | Guard: only restore if `frame.scratch_offset < scratch->offset` |

## Acceptance Criteria

- [ ] `scratch_offset` field in frame struct: `grep -c 'scratch_offset' src/eval_internal.h` returns >= 1
- [ ] Offset saved on push: `grep -c 'scratch_offset' src/eval.c` returns >= 5
- [ ] Result promotion at apply_cont: `grep -c 'valk_evacuate_to_heap' src/eval.c` returns >= 1
- [ ] Root env walk removed from checkpoint: `grep -c 'valk_evacuate_env.*root_env' src/gc_checkpoint.c` returns 0
- [ ] `make build` succeeds
- [ ] `make test` passes
- [ ] `make lint` passes
- [ ] Coverage script completes without scratch overflow: `VALK_HEAP_HARD_LIMIT=1073741824 make coverage 2>&1 | grep -c '\[scratch\] overflow'` returns 0
- [ ] No GC death spiral during coverage: `VALK_HEAP_HARD_LIMIT=1073741824 make coverage 2>&1 | grep -c '\[gc\] slow cycle'` returns <= 2
