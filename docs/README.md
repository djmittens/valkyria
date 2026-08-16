# Valkyria Documentation

Cross-cutting documentation. Project-specific docs live inside each project
(`runtime/docs/`, `testing/docs/`, `coverage/docs/`, and each project's README).

## Start Here

- **[CONTRIBUTING.md](CONTRIBUTING.md)** - Build setup, code style, testing
- **[ROADMAP.md](ROADMAP.md)** - Tech tree and feature status
- **[../runtime/docs/LANGUAGE.md](../runtime/docs/LANGUAGE.md)** - Language reference: syntax, core forms, builtins, prelude

## Runtime (`runtime/docs/`)

- **[MEMORY_MANAGEMENT.md](../runtime/docs/MEMORY_MANAGEMENT.md)** - Scratch arena, GC heap, evacuation, handles
- **[GC_MARKING_ALGORITHM.md](../runtime/docs/GC_MARKING_ALGORITHM.md)** - Parallel mark queue and work stealing
- **[THREADING.md](../runtime/docs/THREADING.md)** - Two-thread model and GC coordination
- **[ASYNC_IO.md](../runtime/docs/ASYNC_IO.md)** - Async handles, combinators, `aio/do` and `aio/let`
- **[ASYNC_CLOSURES.md](../runtime/docs/ASYNC_CLOSURES.md)** - How async callbacks capture environments
- **[METRICS.md](../runtime/docs/METRICS.md)** - Metrics, export formats, debug endpoints
- **[HTTP_API.md](../runtime/docs/HTTP_API.md)** - HTTP/2 client and server API
- **[HTTP_API_QUICK_REFERENCE.md](../runtime/docs/HTTP_API_QUICK_REFERENCE.md)** - Cheat sheet
- **[CAPACITY_PLANNING.md](../runtime/docs/CAPACITY_PLANNING.md)** - Tuning for throughput and latency

## Testing & Coverage

- **[testing/docs/TESTING.md](../testing/docs/TESTING.md)** - Running and writing tests
- **[coverage/docs/COVERAGE_REQUIREMENTS.md](../coverage/docs/COVERAGE_REQUIREMENTS.md)** - Coverage tiers and enforcement

## Design Drafts (not yet implemented)

- **[TYPE_SYSTEM_DESIGN.md](../runtime/docs/TYPE_SYSTEM_DESIGN.md)** - Algebraic data types with erasure
- **[MODULE_REFACTOR_INTENT.md](../runtime/docs/MODULE_REFACTOR_INTENT.md)** - Target module model (design intent)
- **[MODULE_SYSTEM_REFACTOR.md](../runtime/docs/MODULE_SYSTEM_REFACTOR.md)** - Risk analysis of the narrower macro-prefix proposal

## Open Work

- **[TECH_DEBT_LOG.md](TECH_DEBT_LOG.md)** - Known debt, ordered by isolation

## Project Layout

| Path | Contents |
|---|---|
| `runtime/` | C runtime: `src/` (parser, eval, memory, gc, aio, llvm/vir), `vendor/`, `test/`, `CMakeLists.txt` |
| `stdlib/` | Valk standard library (`prelude.valk` auto-loads at startup) |
| `testing/` | Test framework (`test.valk`, `property.valk`), C harness (`c/`), unified runner (`run-tests.valk`) |
| `symdb/` | Symbol database + static validation (shared by lsp, check, quality) |
| `lsp/` | LSP server and its tests (`lsp/test/`, UAT in `lsp/test/uat/`) |
| `coverage/` | Coverage report and gate tooling |
| `quality/` | Quality snapshot and diff |
| `check/` | Workspace diagnostics and globals lint |
| `scripts/` | Misc: benchmarks, profiling helpers |
