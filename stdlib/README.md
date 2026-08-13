# stdlib

The Valk standard library. Shipped with the runtime; `prelude.valk` and
`aio/handles.valk` are loaded automatically by `build/valk` at startup.

## Layout

| File | Purpose | Loaded |
|---|---|---|
| `prelude.valk` | Core macros (`fun`, `module`), Option/Result/Pair, list utilities | auto |
| `builtins.valk` | `sig` type declarations + docs for every C builtin (feeds LSP hover and static checks) | auto (via prelude) |
| `aio/handles.valk` | Async handle helpers | auto |
| `aio/monadic.valk` | `aio/do` and monadic combinator sugar | on demand |
| `aio/sse.valk` | Server-sent events helpers | on demand |
| `aio/debug.valk`, `aio/debug-broadcaster.valk`, `aio/metrics-stream.valk` | Debug dashboard server + metrics streaming | on demand |
| `http/api.valk` | High-level HTTP convenience API | on demand |
| `ast/walk.valk` | AST walking helper | on demand |

## Conventions

- Everything here ships in every binary: no global mutable state
  (enforced by `check/check-no-globals.valk`), no test-only helpers.
- Covered by the Valk coverage gate (`coverage/check-coverage.valk`).
- The test framework lives in `testing/`, the code-intel library in `symdb/` —
  they are separate projects, not part of the standard library.
