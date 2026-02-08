# Valkyria Documentation

## Core Documentation

- **[LANGUAGE.md](LANGUAGE.md)** - Language reference: syntax, semantics, builtins
- **[ROADMAP.md](ROADMAP.md)** - Tech tree and feature status
- **[CONTRIBUTING.md](CONTRIBUTING.md)** - Development setup, code style, testing

## Feature Documentation

Detailed documentation for implemented features:

- **[features/](features/)** - Feature documentation index
  - [Memory Management](features/MEMORY_MANAGEMENT.md) - Three-tier allocation, GC, checkpoint system
  - [Async I/O](features/ASYNC_IO.md) - libuv backend, handles, HTTP/2
  - [Concurrency](features/CONCURRENCY.md) - Thread pool, futures, promises
  - [Metrics](features/METRICS.md) - Observability and Prometheus export

## API Reference

- **[HTTP_API.md](HTTP_API.md)** - High-level HTTP client/server API
- **[HTTP_API_QUICK_REFERENCE.md](HTTP_API_QUICK_REFERENCE.md)** - HTTP API cheat sheet

## Implementation Planning

- **[implementation_board/](implementation_board/)** - Detailed task breakdown by layer
- **[ASYNC_API_PLAN.md](ASYNC_API_PLAN.md)** - Current async API design (in progress)

## Source Files

- `src/prelude.valk` - Standard library
- `src/http_api.valk` - HTTP API implementation
- `src/async_handles.valk` - Async handle utilities
- `src/modules/test.valk` - Test framework

## Archive

Historical planning documents are in `archive/`.
