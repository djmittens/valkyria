# Dict as First-Class Value Type (LVAL_DICT)

## Overview

Move dict from `LVAL_REF` wrapper to a dedicated `LVAL_DICT` type so dicts
participate in structural GC traversal and scratch arena evacuation without
custom callbacks. This enables proper write barriers and is a prerequisite
for eval-boundary scratch checkpointing (see `scratch-01-eval-checkpointing.md`).

Currently dict is the ONLY `LVAL_REF` user with custom `mark` and `evacuate`
callbacks. All other `LVAL_REF` users (file handles, HTTP connections, SQLite,
metrics, etc.) are true external resources that correctly use the ref abstraction.
Dict is a value — its contents are lvals that must be walkable by the GC and
evacuator structurally.

## Requirements

### LVAL_DICT Type Constant

Add `LVAL_DICT = 10` to `valk_ltype_e` in `src/parser.h` (after `LVAL_HANDLE = 9`).

Add a union member to `valk_lval_t`:

```c
struct {
  valk_dict_t *data;
} dict;
```

This is 8 bytes — fits within the existing 48-byte union.

Move `valk_dict_t` and `valk_dict_cell_t` struct definitions from
`builtins_dict.c` to a new header `src/dict.h` so the evacuator and
mark phase can access the layout. The dict helper functions (dict_buckets,
dict_cells, dict_strings, dict_block_size, dict_hash) should also be in
`src/dict.h` as static inlines.

### Dict Constructor

Replace `dict_make_ref` in `builtins_dict.c` with a constructor:

```c
valk_lval_t* valk_lval_dict(valk_dict_t *data);
```

In `src/lval.c`. Sets `flags = LVAL_DICT | alloc_flags`, `dict.data = data`.
No `ref.*` callbacks — structural traversal replaces them.

Update `dict/new`, `dict/from-keys`, and any other dict-creating builtins
to call `valk_lval_dict` instead of `dict_make_ref`.

### Structural GC Mark

In `src/gc_mark.c`, add `case LVAL_DICT:` that does exactly what the current
`dict_mark_fn` callback does:

1. `valk_gc_heap_mark_raw(ctx, obj->dict.data)` — mark the contiguous block
2. Walk all bucket chains, call `valk_gc_heap_mark_object(ctx, cell.value)`
   for each non-null value

Remove `dict_mark_fn` from `builtins_dict.c`.

### Structural Evacuation

In `src/gc_evacuation.c`, handle `LVAL_DICT` in two places:

**In `valk_evacuate_value`** (the value copy): After copying the lval struct,
if the dict data block is in scratch, allocate a new block on heap with
`dict_block_size`, `memcpy` the entire block, update `new_val->dict.data`.

**In `valk_evacuate_children`** (transitive walk): Walk all bucket chains,
call `valk_evacuate_value` on each `cell.value`, update the pointer if changed.

This replaces `dict_evacuate_fn` in `builtins_dict.c`.

### GC Sweep

In `src/gc_heap_sweep.c`, add `case LVAL_DICT:` that frees the dict data
block (equivalent to the current `dict_free_fn` which is actually a no-op
since the block is GC-managed). If the block was allocated on the GC heap,
it will be swept independently. If it was allocated via malloc (shouldn't
happen), free it.

### Dict Write Barrier

Add a write barrier to `dict_set` in `builtins_dict.c`. Before storing a
value into the dict, check:

```c
if (dict_is_on_heap(d) && val != NULL && LVAL_ALLOC(val) == LVAL_ALLOC_SCRATCH) {
  val = valk_evacuate_to_heap(val);
}
cells[ci].value = val;
```

Where `dict_is_on_heap` checks `!valk_thread_ctx.scratch || !valk_ptr_in_arena(valk_thread_ctx.scratch, d)` — the same pattern `dict_grow` already uses.

This prevents scratch pointers from being stored into heap dicts, which
currently creates dangling pointers after scratch reset.

### Type Name and Display

Update `valk_ltype_name` (or equivalent) to return `"Dict"` for `LVAL_DICT`.

Update `valk_lval_print` / `valk_lval_println` to handle `LVAL_DICT` —
print `{dict N entries}` or delegate to the existing dict print logic.

### Dict Accessor Builtins

Update all dict builtins in `builtins_dict.c` to check `LVAL_TYPE(v) == LVAL_DICT`
and access `v->dict.data` instead of `v->ref.ptr`:

- `dict/get`, `dict/set!`, `dict/put!`, `dict/delete!`
- `dict/keys`, `dict/values`, `dict/count`, `dict/contains?`
- `dict/merge`, `dict/new`, `dict/from-keys`

The `LVAL_ASSERT_TYPE` calls should assert `LVAL_DICT` instead of `LVAL_REF`.

## Non-Requirements

- No changes to other `LVAL_REF` users (file handles, connections, etc.)
- No changes to the `LVAL_REF` type itself — it remains for external resources
- No changes to the eval loop or scratch arena lifecycle (that's spec 01)
- Dict internal layout (buckets, cells, string pool) is unchanged

## Acceptance Criteria

- [ ] `LVAL_DICT` defined in parser.h: `grep -c 'LVAL_DICT' src/parser.h` returns >= 1
- [ ] Dict union member exists: `grep -c 'dict\.data' src/parser.h` returns >= 1
- [ ] Dict struct definitions in dict.h: `test -f src/dict.h`
- [ ] No dict mark/evacuate callbacks remain: `grep -c 'dict_mark_fn\|dict_evacuate_fn' src/builtins_dict.c` returns 0
- [ ] Structural mark exists: `grep -c 'LVAL_DICT' src/gc_mark.c` returns >= 1
- [ ] Structural evacuation exists: `grep -c 'LVAL_DICT' src/gc_evacuation.c` returns >= 1
- [ ] Write barrier in dict_set: `grep -c 'LVAL_ALLOC_SCRATCH' src/builtins_dict.c` returns >= 1
- [ ] `make build` succeeds
- [ ] `make test` passes (all existing dict tests validate behavior is preserved)
- [ ] `make lint` passes
