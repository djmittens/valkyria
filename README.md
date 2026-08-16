# Valkyria

A Lisp interpreter written in C23 with async I/O, HTTP/2 networking, a parallel
garbage collector, and an optional LLVM AOT/JIT backend.

## Quick Start

```bash
# Build
make build

# Run REPL
./build/valk

# Run a script
./build/valk script.valk

# Run tests
make test
```

## Features

- **S-expression syntax** with Q-expressions for quoting
- **Lexical scoping** with closures
- **Async I/O** on libuv with composable handles and combinators
- **HTTP/2 client and server** with TLS
- **Parallel stop-the-world GC** with scratch-arena bump allocation
- **Macros and modules**
- **LLVM AOT/JIT** compilation (optional)
- **Language server** for editor integration
- **Metrics and a debug dashboard** (Prometheus + SSE)
- **Interactive REPL** with history

## Example

The prelude is loaded automatically at startup.

```lisp
(fun {factorial n}
  {if (<= n 1)
    {1}
    {(* n (factorial (- n 1)))}})

(print (factorial 5))  ; 120
```

An HTTP/2 round trip:

```lisp
(def {aio} (aio/await (aio/start)))

(def {srv} (http2/server-listen aio 0 (\ {req} {
  `{:status "200" :body "Hello"}
})))

(aio/then (http2/client-request aio "127.0.0.1" (http2/server-port srv) "/") (\ {r} {
  (do
    (print (http2/response-status r))   ; "200"
    (print (http2/response-body r))     ; "Hello"
    (http2/server-stop srv)
    (aio/stop aio))
}))

(aio/run aio)
```

## Projects

The repository is a monorepo of root-level projects:

| Project | What it is |
|---------|------------|
| [`runtime/`](runtime/README.md) | The C23 interpreter/runtime: parser, eval, GC, async I/O, HTTP/2, LLVM backend |
| [`stdlib/`](stdlib/README.md) | Valk standard library (`prelude.valk` auto-loads) |
| [`testing/`](testing/README.md) | Test framework (C harness + Valk framework) and the unified test runner |
| [`symdb/`](symdb/README.md) | Symbol database + static validation (shared code-intel core) |
| [`lsp/`](lsp/README.md) | Language server (LSP) and its test suites |
| [`coverage/`](coverage/README.md) | Aggregated C+Valk coverage reports and CI gates |
| [`quality/`](quality/README.md) | Structural quality snapshots and diffing |
| [`check/`](check/README.md) | Workspace diagnostics and lints |

## Documentation

- **[Documentation Index](docs/README.md)** - All docs
- **[Language Reference](runtime/docs/LANGUAGE.md)** - Syntax, features, semantics
- **[HTTP API](runtime/docs/HTTP_API.md)** - HTTP/2 client and server
- **[Async I/O](runtime/docs/ASYNC_IO.md)** - Handles and combinators
- **[Project Roadmap](docs/ROADMAP.md)** - Development plans
- **[Contributing](docs/CONTRIBUTING.md)** - Development setup and guidelines

## Project Status

**Experimental** - not production validated.

| Component | Status |
|-----------|--------|
| Parser / Evaluator | Working |
| Garbage collection (parallel STW) | Working |
| Async I/O | Working |
| HTTP/2 client | Working |
| HTTP/2 server | Working |
| Macros / modules | Working |
| LSP server | Working |
| Metrics / dashboard | Working |
| LLVM AOT / JIT | Partial |
| Type system | Not implemented ([design](runtime/docs/TYPE_SYSTEM_DESIGN.md)) |
| Tail call optimization | Not implemented |

## Building

### Dependencies

- Clang (C23 support)
- CMake, Ninja, pkg-config
- OpenSSL, libuv, libedit, expat
- libbacktrace (optional, for better stack traces)
- LLVM (optional, for the AOT/JIT backend)

nghttp2 and sqlite3 are vendored.

### Commands

```bash
make configure    # First-time setup
make build        # Build everything
make test         # Run C + Valk tests
make test-all     # Comprehensive: all tests with and without ASAN
make repl         # Start REPL
make debug        # REPL under debugger
make lint         # Run clang-tidy
make coverage     # Coverage report
make clean        # Clean build
```

See [CONTRIBUTING.md](docs/CONTRIBUTING.md) for the full workflow.

## License

MIT
