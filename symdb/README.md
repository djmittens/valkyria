# symdb

The code-intelligence core: a sqlite-backed symbol database plus static
validation for Valk workspaces. Shared foundation for the LSP server (`lsp/`),
workspace diagnostics (`check/`), and quality snapshots (`quality/`).

## Layout

| File | Purpose |
|---|---|
| `symdb.valk` | Schema and indexing: syncs workspace files into the DB via the runtime's `lsp/index-ast` builtin |
| `symdb-query.valk` | Query layer: definitions, references, load graph, dead symbols |
| `symdb-types.valk` | Type/sig row handling |
| `validate.valk` | Entry point for static validation (loads the two below) |
| `validate-checks.valk` | Checks: undefined symbols, arity, sig conformance, ... |
| `validate-walk.valk` | AST walking for validation |

## Usage

```lisp
(load "symdb/symdb.valk")
(load "symdb/validate.valk")
```

Consumers open a workspace-local cache at `.valk/symdb.sqlite`.

## Runtime support

Indexing depends on two builtin groups that stay compiled into the runtime:
`lsp/index-ast` (`runtime/src/lsp_index*.c`) and `sqlite/*`
(`runtime/src/builtins_sqlite.c`, vendored sqlite3).
