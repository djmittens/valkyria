# Valkyria Documentation

## Start Here

- **[LANGUAGE.md](LANGUAGE.md)** - Language reference: syntax, core forms, builtins, prelude
- **[CONTRIBUTING.md](CONTRIBUTING.md)** - Build setup, code style, testing
- **[ROADMAP.md](ROADMAP.md)** - Tech tree and feature status

## Subsystems

- **[MEMORY_MANAGEMENT.md](MEMORY_MANAGEMENT.md)** - Scratch arena, GC heap, evacuation, handles
- **[GC_MARKING_ALGORITHM.md](GC_MARKING_ALGORITHM.md)** - Parallel mark queue and work stealing
- **[THREADING.md](THREADING.md)** - Two-thread model and GC coordination
- **[ASYNC_IO.md](ASYNC_IO.md)** - Async handles, combinators, `aio/do` and `aio/let`
- **[ASYNC_CLOSURES.md](ASYNC_CLOSURES.md)** - How async callbacks capture environments
- **[METRICS.md](METRICS.md)** - Metrics, export formats, debug endpoints

## HTTP/2

- **[HTTP_API.md](HTTP_API.md)** - HTTP/2 client and server API
- **[HTTP_API_QUICK_REFERENCE.md](HTTP_API_QUICK_REFERENCE.md)** - Cheat sheet
- **[CAPACITY_PLANNING.md](CAPACITY_PLANNING.md)** - Tuning for throughput and latency

## Testing

- **[TESTING.md](TESTING.md)** - Running and writing tests
- **[COVERAGE_REQUIREMENTS.md](COVERAGE_REQUIREMENTS.md)** - Coverage tiers and enforcement

## Design Drafts (not yet implemented)

- **[TYPE_SYSTEM_DESIGN.md](TYPE_SYSTEM_DESIGN.md)** - Algebraic data types with erasure
- **[MODULE_REFACTOR_INTENT.md](MODULE_REFACTOR_INTENT.md)** - Target module model (design intent)
- **[MODULE_SYSTEM_REFACTOR.md](MODULE_SYSTEM_REFACTOR.md)** - Risk analysis of the narrower macro-prefix proposal

## Open Work

- **[TECH_DEBT_LOG.md](TECH_DEBT_LOG.md)** - Known debt, ordered by isolation

## Source Layout

| Path | Contents |
|---|---|
| `src/` | C runtime (`parser.c`, `eval.c`, `memory.c`, `gc*.c`) |
| `src/aio/` | Async I/O, HTTP/2, TLS |
| `src/llvm/`, `src/vir/` | AOT/JIT compilation |
| `stdlib/prelude.valk` | Standard library (auto-loaded at startup) |
| `stdlib/http/api.valk` | High-level HTTP API |
| `stdlib/aio/` | Async handles, monadic combinators, SSE |
| `stdlib/test/test.valk` | Test framework |
| `test/<area>/` | C and Valk tests by area |
