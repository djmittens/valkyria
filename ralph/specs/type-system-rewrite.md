# Type System Rewrite: Unified Inference-Driven Transform

## Overview

Replace the two-scope bridge architecture (HM scope + string-based transform scope + `track_binding`/`track_fun_params`) with a single system where `transform_expr` queries the HM inference results directly. After macro expansion, all code is standard AST forms (`=`, `\`, `def`, `if`, `do`, constructor calls). The type system should handle these uniformly with zero special-case detection for macro expansion patterns.

## Non-Requirements

- Changes to the runtime representation (still dynamically typed at runtime)
- Changes to the parser or macro system
- Removing `sig` declarations (they remain optional hints)
- Full dependent types or linear types

## Requirements

### Remove the String-Based Transform Scope

Delete `valk_type_scope_t` usage from `type_env.c`. Delete `track_binding`, `track_fun_params`, `scope_add`, `scope_find_type`, `scope_cleanup`, `g_ti_ctx`, `ti_lookup_type_str`. The transform currently maintains `valk_type_scope_t` (a `{var, type_name}` string array) as a parallel scope. This is redundant with the HM scope.

Instead, `transform_expr` calls `valk_ti_lookup_type_name(ctx, var_name)` directly when resolving field access. The `ctx` is passed through the transform functions.

### Pass TI Context Through Transform

Change `transform_expr` signature from:

```c
static valk_lval_t *transform_expr(valk_type_env_t *env, valk_type_scope_t *scope, valk_lval_t *expr);
```

to:

```c
static valk_lval_t *transform_expr(valk_type_env_t *env, valk_ti_ctx_t *ti, valk_lval_t *expr);
```

Field access resolution (`resolve_field_access`) queries `valk_ti_lookup_type_name(ti, var_name)` instead of `scope_find_type(scope, var_name)`. Chained field access stores intermediate types in the TI context via a temporary binding (e.g., `__chain__`).

### Unified Lambda Handling in Inference

`infer_binding` detects when the RHS is a lambda (any CONS with head `\` or resolved `\` builtin). When it is, it calls `infer_lambda` with `fname = binding_name`. `infer_lambda` looks up `fname` in scope for an existing sig and pre-seeds param types from the sig BEFORE processing the body.

This replaces the separate `fun` handler, the `def`+`\` detection, and the FUN-builtin-pointer comparison. Post-macro-expansion, `fun` doesn't exist — only `def`+`\` and `=`+`\`. Both go through `infer_binding`.

The existing `fun` handler (line ~860) becomes dead code and is removed.

### Sig Variable Sharing Across Params

`valk_ti_import_new` must use a single `ti_var_map_t` across all param type strings and the return type string for each sig. Currently each `valk_ti_parse_sig_str` call creates a fresh var map, so `(sig 'head {-> (List a) a})` produces two unrelated type variables instead of one shared variable.

### Empty Formals Handling

The `\` handler in `infer_expr` must accept `LVAL_NIL` formals (empty `{}`). Currently `is_qexpr_node({})` returns false because empty `{}` parses as `LVAL_NIL`, not a quoted CONS. The fix: check for NIL explicitly and pass `nullptr` formals to `infer_lambda`.

### Prelude List Sigs

Add sigs to `stdlib/prelude.valk` for builtin list operations: `head`, `tail`, `cons`, `init`, `join`, `nth`, `map`, `foldl`, `foldr`. These are currently only in `stdlib/builtins.valk` which is never loaded at runtime.

### Memory: Dual-Lifetime Arena

The TI context uses two allocation pools:

| Pool | Lifetime | Contents |
|------|----------|----------|
| Page-chain (permanent) | Until `valk_ti_destroy` | base_scope entries, imported sigs/constructors, promoted bindings, primitive types |
| Expression buffer (transient) | Until next `valk_ti_reset` | Per-expression type nodes, fresh vars, child scopes, all_bindings |

`ti_alloc` checks `ctx->use_expr`: if true, allocates from the expression buffer; if false, from the page chain. `import_new` and `promote_to_base` set `use_expr = false` to allocate permanently. `valk_ti_reset` clears the expression buffer and sets `use_expr = true`.

### Split type_env.c

`type_env.c` exceeds the 1000-line limit. Extract `transform_expr` and all transform helpers to `type_transform.c` / `type_transform.h`. The type_env module retains type/sig/constructor registration and the `valk_type_env_t` data structure.

## Acceptance Criteria

- [ ] `grep -c 'track_binding\|track_fun_params\|scope_find_type\|valk_type_scope_t' src/type_env.c src/type_transform.c` returns 0
- [ ] `grep -c 'g_ti_ctx' src/type_env.c src/type_transform.c` returns 0
- [ ] Field access works inside function bodies: `build/valk -c '...'` test prints correct values (see test_types.valk)
- [ ] `make test-valk F=test_types` passes (all 71 tests)
- [ ] `make test-c` passes (all 66 suites including test_lsp_integration)
- [ ] `wc -l src/type_env.c src/type_transform.c` both under 1000 lines
- [ ] `make lint` passes
- [ ] `make test-c-asan` passes
