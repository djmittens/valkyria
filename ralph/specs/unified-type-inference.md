# Unified Type Inference (Hindley-Milner)

## Overview

Replace the three separate, incomplete type systems (C type_env, Valk validator, symdb) with a single Hindley-Milner type inference engine in C. The engine infers types for all expressions — including lambdas, closures, and higher-order function arguments — without requiring explicit annotations. `sig` declarations become optional hints that seed the inference, not the only source of type information.

## Non-Requirements

- Full dependent types or linear types
- Runtime type checking (inference is compile-time/analysis-time only)
- Changes to the runtime representation of values (still dynamically typed at runtime)
- Removing `sig` declarations (they become optional constraints, not mandatory)

## Requirements

### Type Representation

Define `valk_type_t` in `src/type_infer.h`:

| Variant | Fields | Example |
|---------|--------|---------|
| `TYPE_VAR` | `id: u32` | Fresh unification variable `?0`, `?1` |
| `TYPE_CON` | `name: char*, args: valk_type_t*[], arity: u32` | `Num`, `Str`, `(List Num)`, `(-> Num Str)` |
| `TYPE_FUN` | `params: valk_type_t*[], param_count: u32, ret: valk_type_t*` | `(-> Num Str Bool)` — sugar for nested TYPE_CON `->` |

All type nodes are allocated from an arena per inference context (not GC heap). `TYPE_VAR` nodes carry a `link` pointer for union-find unification.

### Unification

`valk_type_t *valk_type_unify(valk_type_infer_t *ctx, valk_type_t *a, valk_type_t *b)`

Standard union-find unification:
- `VAR` vs anything: link the var to the other type (occurs check)
- `CON` vs `CON`: names must match, arity must match, unify each arg pairwise
- `FUN` vs `FUN`: param counts must match, unify each param + return
- Failure: return `NULL`, record error with source position in `ctx->errors[]`

### Inference Context

`valk_type_infer_t` holds:
- Arena allocator for type nodes
- Fresh variable counter
- Error list (position + message)
- Type environment: `name → type_scheme` mapping (let-polymorphism)
- Constructor environment: imported from existing `valk_type_env_t`
- Sig environment: imported from existing `valk_type_sig_t` entries

`valk_type_infer_t *valk_type_infer_create(valk_type_env_t *type_env)`
`void valk_type_infer_destroy(valk_type_infer_t *ctx)`

### Core Inference

`valk_type_t *valk_type_infer_expr(valk_type_infer_t *ctx, valk_type_scope_t *scope, valk_lval_t *expr)`

Walks the AST (using `cons.head`/`cons.tail` directly — no evaluation) and returns the inferred type:

| Form | Inference rule |
|------|---------------|
| Number literal | `Num` |
| String literal | `Str` |
| Symbol `x` | Lookup in scope, instantiate scheme if polymorphic |
| `(\ {params} body)` | Fresh vars for each param, infer body, return `(-> p1 p2 ... ret)` |
| `(fun {name params} body)` | Same as lambda, also bind `name` in scope |
| `(f arg1 arg2 ...)` | Infer `f` as `tf`, infer each arg as `ta1 ta2 ...`, fresh var `tr`, unify `tf` with `(-> ta1 ta2 ... tr)`, return `tr` |
| `(= {x} rhs)` | Infer `rhs`, generalize (let-polymorphism), bind `x` in scope |
| `(if c t f)` | Infer `c` (unify with `Num`), infer `t` and `f`, unify them, return |
| `(do e1 e2 ... en)` | Infer each, return type of `en` |
| `(sig 'name {type})` | Parse type, bind `name` in scope with that type (no generalization) |
| Constructor `(Ctor args)` | Lookup constructor, instantiate field types with fresh vars, unify args with field types, return parent type |
| Field access `x:field` | Lookup `x`'s type, find field in constructor, return field type |
| `(match val clauses)` | Infer `val`, for each clause: bind pattern vars from constructor fields, infer body, unify all clause bodies |

### Integration with Existing Transform

The type inference pass runs BEFORE `transform_expr`. It populates the `valk_type_scope_t` with inferred types. Then `transform_expr` reads the scope to resolve field accesses, match destructuring, etc.

Modify the pipeline in `repl.c` and `builtins_io.c`:
```
parse → macro-expand → module-rewrite → type-infer → type-transform → eval
```

`valk_type_infer_expr` walks the full AST and builds the scope. Then `transform_expr` uses that scope (instead of building its own via `track_binding`).

### LSP / Validator Unification

The Valk validator (`validate-checks.valk`, `validate-walk.valk`) currently reimplements type checking in Valk. Replace its type-related checks with queries to the C inference engine:

Add C builtin `type/infer-file`:
```
(sig 'type/infer-file {-> List Str List})
; Takes (ast text), returns list of type errors as plists {:line :col :message}
```

The validator calls `type/infer-file` instead of `vd/infer-expr-type`, `vd/infer-arg-call-type`, `vd/check-arg-types`, `vd/types-compatible`, `vd/flag-untyped-params`, `vd/check-one-binding-str`. These Valk functions are removed.

### Symdb Type Storage

The symdb currently stores sig strings. Extend to store inferred types:

Add column `inferred_type TEXT` to `symbols` table. After inference, store the principal type for each top-level definition. This enables cross-file type information without re-inferring.

The `valk_type_infer_create` constructor loads existing inferred types from the symdb as seed constraints, so cross-file calls have type info even before the called file is fully inferred.

### Remove `track_binding` Special Cases

`type_env.c:track_binding()` has hardcoded special cases for `head`, `tail`, `filter`, `reverse`, `with`, constructor calls, etc. These are unnecessary with proper inference — unification handles them all generically:

- `(= {x} (head xs))` where `xs : (List Person)` → unify `head : (-> (List a) a)` with `(List Person)` → `a = Person` → `x : Person`
- `(= {x} (filter pred xs))` → `filter : (-> (-> a Bool) (List a) (List a))` → return type is same `(List a)`

Delete `track_binding` and all its special cases.

## Acceptance Criteria

- [ ] `valk_type_t` and `valk_type_unify` exist: `grep -c 'valk_type_unify' src/type_infer.c` >= 1
- [ ] Lambda types are inferred: `build/valk -c '(= {f} (\ {x} {+ x 1})) (println (type/infer f))'` prints `(-> Num Num)`
- [ ] Field access works without sig: `build/valk -c '(type {P} {:x Num}) (fun {get-x p} {p:x}) (println (get-x (P 42)))'` prints `42`
- [ ] Higher-order functions propagate types: `build/valk -c '(type {P} {:x Num}) (fun {apply f p} {f p}) (println (apply (\ {p} {p:x}) (P 42)))'` prints `42`
- [ ] Cross-file inference via symdb: `build/valk scripts/valk-check.valk` still reports all clear
- [ ] `track_binding` removed: `grep -c 'track_binding' src/type_env.c` returns 0
- [ ] `vd/infer-expr-type` removed: `grep -c 'vd/infer-expr-type' stdlib/diag/validate-checks.valk` returns 0
- [ ] Type errors from inference replace validator type errors: `build/valk -c '(sig "add" {-> Num Num Num}) (add "hello" 1)'` produces type error mentioning Str vs Num
- [ ] All existing tests pass: `make test` passes
- [ ] LSP diagnostics use inference: no "Type could not be resolved" for functions with inferable types
