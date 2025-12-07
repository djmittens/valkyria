# Implemented Features

Documentation for features that are fully implemented and production-ready.

## Core Features

| Feature | Description | Documentation |
|---------|-------------|---------------|
| [Memory Management](MEMORY_MANAGEMENT.md) | Three-tier allocation with checkpoint-based GC | Complete |
| [Async I/O](ASYNC_IO.md) | libuv-based async with handles and continuations | Complete |
| [Concurrency](CONCURRENCY.md) | Thread pool, futures, promises | Complete |
| [Metrics](METRICS.md) | GC, interpreter, and AIO metrics | Complete |

## Language Features

See [LANGUAGE.md](../LANGUAGE.md) for:
- S-expressions and Q-expressions
- Lambda functions and closures
- Lexical scoping with dynamic fallback
- Pattern matching with `select` and `case`
- Quasiquote with `,` and `,@`
- Delimited continuations (shift/reset)

## API Documentation

- [HTTP_API.md](../HTTP_API.md) - High-level HTTP client/server API
- [HTTP_API_QUICK_REFERENCE.md](../HTTP_API_QUICK_REFERENCE.md) - Quick reference

## Standard Library

The prelude (`src/prelude.valk`) provides 40+ functions:

**List Operations:** `head`, `tail`, `nth`, `take`, `drop`, `map`, `filter`, `foldl`, `exists`

**Higher-Order:** `curry`, `uncurry`, `flip`, `comp`, `id`

**Control Flow:** `select`, `case`, `let`, `not`, `or`, `and`

**Property Lists:** `plist/get`, `plist/set`, `plist/has?`, `plist/keys`, `plist/vals`
