# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Valkyria is a Lisp interpreter written in C23 with built-in concurrency primitives, asynchronous I/O, and HTTP/2 networking support. The language features a REPL, garbage collection, and an arena-based memory management system.

## Common Development Commands

### Building and Testing
```bash
# Initial build (generates TLS test certificates in build/)
make build

# Run all tests (ALWAYS use 'make test', NOT direct binary execution)
# Note: Leak detection is enabled. The GC properly cleans up auxiliary data
# (environment arrays, strings) when destroying the heap or sweeping during GC.
make test

# Run REPL with prelude
make repl

# Run with AddressSanitizer (for debugging)
make asan
```

### Linting and Analysis
```bash
# Run clang-tidy over codebase
make lint

# Run cppcheck static analysis
make cppcheck

# Run infer analysis (requires Docker)
make infer
```

### Debugging
```bash
# Launch REPL under lldb
make debug

# Find TODOs for current branch
make todo

# Create test Lisp files for debugging
# IMPORTANT: Use test/ folder (NOT /tmp) for test files
# Example:
cat > test/debug_issue.valk << 'EOF'
(print "test code here")
EOF
./build/valk test/debug_issue.valk
```

### Clean Build
```bash
make clean
```

### First-Time Setup
```bash
# Install editline dependency (requires autotools)
make configure
```

## Architecture Overview

### Core Components

**Parser & VM (src/parser.{c,h}, src/vm.{c,h})**
- Lisp S-expression parser with support for numbers, symbols, strings, quoted expressions, and S-expressions
- Value types defined in `valk_ltype_e`: LVAL_NUM, LVAL_SYM, LVAL_STR, LVAL_FUN, LVAL_REF, LVAL_QEXPR, LVAL_SEXPR, LVAL_ERR, LVAL_ENV
- `valk_lval_t` represents all Lisp values using tagged union pattern with flags field (lower 8 bits for type, upper bits for flags like GC marking)
- VM uses stack frames for evaluation (`valk_vm_frame_t`) with escape analysis to promote stack values to heap when needed
- Environments (`valk_lenv_t`) store symbol bindings with parent-pointer for lexical scoping

**Memory Management (src/memory.{c,h})**
- Thread-local allocator context (`valk_thread_ctx.allocator`) supports multiple allocation strategies
- **Arena allocator** (`valk_mem_arena_t`): Bump-pointer allocation for temporary/ephemeral values, reset between REPL iterations
- **Slab allocator** (`valk_mem_slab_t`): Fixed-size block allocation with optional Treiber stack for lock-free freelist, used for futures/promises
- **Malloc fallback**: Standard libc malloc/free for general allocation
- **Reference counting**: Custom ARC-style reference counting with `valk_retain`/`valk_release` macros, atomic `valk_arc_retain`/`valk_arc_release` for concurrent access
- **Allocator switching**: `VALK_WITH_ALLOC(allocator)` macro temporarily swaps thread-local allocator (crucial for ensuring scratch arena usage during evaluation, global arena for persistent structures)
- Debug support: `VALK_ARC_DEBUG` enables full reference counting trace capture with backtraces

**Concurrency (src/concurrency.{c,h})**
- Futures/promises model for async operations (`valk_future`, `valk_promise`)
- Work queue with pthread-based worker pool (default 4 workers via `VALK_NUM_WORKERS`)
- `valk_arc_box` provides atomic reference-counted containers for passing data between threads
- Futures support chaining via `andThen` callbacks
- Thread-safe allocators required for concurrent operations (checked via `__assert_thread_safe_allocator()`)

**Async I/O (src/aio.h, src/aio_uv.c, src/aio_ssl.c)**
- Pluggable I/O backend architecture (currently libuv-based via `aio_uv.c`, with placeholders for epoll and io_uring)
- HTTP/2 client and server support using nghttp2 library with TLS (OpenSSL)
- Connection types: `valk_aio_http_server`, `valk_aio_http2_client`, `valk_aio_http_conn`
- Request/response model with `valk_http2_request_t` and `valk_http2_response_t`
- All async operations return futures: `valk_aio_read_file`, `valk_aio_http2_listen`, `valk_aio_http2_connect`, `valk_aio_http2_request_send`

### REPL (src/repl.c)

- Two-arena model:
  - **Global arena** (16 MiB): Persistent structures (environments, global definitions)
  - **Scratch arena** (4 MiB): Temporary values during parsing/evaluation, reset after each expression
- Loads `src/prelude.valk` on startup for standard library (list functions, control flow, etc.)
- Modes: `--script` for non-interactive execution, REPL mode by default
- AIO system initialized automatically unless `VALK_DISABLE_AIO` environment variable is set
- Uses editline library for readline-style input with history

### Testing Structure

Each test file in `test/` links against the `valkyria` library and uses `test/testing.{c,h}` framework:
- `test_std.c`: Standard library and parser tests
- `test_memory.c`: Memory allocator tests (arena, slab, reference counting)
- `test_concurrency.c`: Futures, promises, work queue tests
- `test_networking.c`: Low-level HTTP/2 networking tests
- `test_networking_lisp.c`: Lisp-level networking integration tests

## Important Patterns

### Allocator Context Management
Always use `VALK_WITH_ALLOC(allocator)` when you need to control which allocator is used:
```c
VALK_WITH_ALLOC((void *)scratch) {
    expr = valk_lval_read(&pos, input);
    expr = valk_lval_eval(env, expr);
}
```

### Reference Counting
- Use `valk_retain(ref)` for single-threaded increment
- Use `valk_arc_retain(ref)` for atomic increment (concurrent contexts)
- Use `valk_release(ref)` for single-threaded decrement
- Use `valk_arc_release(ref)` for atomic decrement (concurrent contexts)
- Custom free functions can be set via `ref->free` field

### Value Construction
Values are created via constructors like `valk_lval_num()`, `valk_lval_sym()`, `valk_lval_str()`, etc. Use `valk_intern(env, val)` to deep-copy a value into an environment's allocator for persistence beyond stack scope.

## Platform-Specific Notes

- **macOS**: Set `HOMEBREW_CLANG=on` (handled automatically by Makefile), uses `dsymutil` for debug symbols, ASAN enabled by default
- **Linux**: Uses system clang, requires `_XOPEN_SOURCE=700` and `_GNU_SOURCE` for pthread/libuv headers, ASAN disabled by default
- Both platforms require: pkg-config, OpenSSL, libuv, libedit (editline), libbacktrace

## Dependencies

- **nghttp2**: HTTP/2 protocol implementation (vendor/nghttp2, built as subproject)
- **libuv**: Cross-platform async I/O (system dependency)
- **OpenSSL**: TLS/SSL support (system dependency)
- **libedit**: Readline-like library for REPL (vendor/editline, requires autotools build via `make configure`)
- **libbacktrace**: Stack trace support (system dependency)

## Code Style

- Language: C23 with extensions (`-std=c23`, allows GNU zero-variadic-macro-arguments)
- Naming: `snake_case` for functions/variables, `UPPER_SNAKE` for macros, `*_t` suffix for types, `*_e` suffix for enums
- Indentation: 2 spaces
- Prefix: All public symbols prefixed with `valk_`
- Headers: Local includes use `"header.h"`, system includes use `<header.h>`
- Macros: Extensive use of statement expressions `({ })` and for-loop-based RAII patterns

## TODO Comments

The project uses branch-specific TODO comments. Use `make todo` to find TODOs tagged with the current branch name:
```bash
# Example: TODO(networking): comment about networking work
make todo  # on networking branch finds all TODO(networking) items
```

## Future Improvements

### Test Runner Tool
Plan to create a test runner utility that allows:
- Running specific tests by name or pattern (e.g., `./test_runner test_std::test_parser_numbers`)
- Filtering tests by category or tag
- Parallel test execution
- Better test output formatting and filtering
- Integration with the existing test framework in `test/testing.{c,h}`

This will complement the existing Makefile targets and provide more granular control over test execution.
