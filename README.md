# Valkyria

A Lisp interpreter written in C23 with built-in concurrency, async I/O, and HTTP/2 networking.

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
- **Delimited continuations** (shift/reset)
- **HTTP/2 client** with TLS support
- **Garbage collection** (mark & sweep)
- **Interactive REPL** with history

## Example

```lisp
; Load standard library
(load "src/prelude.valk")

; Define a function
(fun {factorial n}
  {if (<= n 1)
    {1}
    {(* n (factorial (- n 1)))}})

(print (factorial 5))  ; 120

; HTTP request
(load "src/http_api.valk")
(def {resp} (fetch-sync "example.com"))
(print (response-body resp))
```

## Documentation

- **[Language Reference](docs/LANGUAGE.md)** - Syntax, features, semantics
- **[Project Roadmap](docs/ROADMAP.md)** - Development plans
- **[Contributing](docs/CONTRIBUTING.md)** - Development setup and guidelines
- **[HTTP API](docs/HTTP_API.md)** - Networking documentation

## Project Status

**Experimental** - Core interpreter works, not production validated.

| Component | Status |
|-----------|--------|
| Parser/Evaluator | Working |
| Garbage Collection | Working |
| Continuations | Working |
| HTTP/2 Client | Working |
| HTTP/2 Server | Not implemented |
| Type System | Not implemented |
| TCO | Not implemented (requires LLVM backend) |

## Building

### Dependencies

- Clang (C23 support)
- CMake, Ninja
- OpenSSL, libuv, libbacktrace

### Commands

```bash
make configure    # First-time setup (builds editline)
make build        # Build everything
make test         # Run all tests
make repl         # Start REPL
make debug        # REPL under debugger
make lint         # Run linters
make clean        # Clean build
```

## License

MIT
