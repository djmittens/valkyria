# CLAUDE.md

Claude Code notes for this repository.

**`AGENTS.md` is the authoritative agent guide** — build/test commands, file-size
limits, debugging workflows, async patterns, code style, and workflow rules all
live there. Read it first. This file only adds an architecture orientation and
the testing philosophy.

## Project Overview

Valkyria is a Lisp interpreter in C23. See [docs/](docs/README.md) for full documentation:
- [LANGUAGE.md](runtime/docs/LANGUAGE.md) - Language reference
- [ROADMAP.md](docs/ROADMAP.md) - Project roadmap
- [CONTRIBUTING.md](docs/CONTRIBUTING.md) - Development guide

## Quick Commands

```bash
make build          # Build everything
make test           # Run C + Valk tests (no ASAN)
make test-all       # Comprehensive: all tests with and without ASAN
make repl           # Start REPL with prelude
make debug          # REPL under debugger (lldb on macOS, gdb on Linux)
make todo           # Find TODOs for current branch
```

## Key Architecture

### Core Files
- `runtime/src/parser.{c,h}` - Parser, value types, builtins
- `runtime/src/eval.c` - Evaluator
- `runtime/src/memory.{c,h}` - Allocators (arena, slab)
- `runtime/src/gc.{c,h}`, `runtime/src/gc_mark.c`, `runtime/src/gc_evacuation.c` - Parallel GC
- `runtime/src/aio/` - Async I/O; `runtime/src/aio/aio_uv.c` is the libuv backend
- `runtime/src/aio/http2/` - HTTP/2 client, server, sessions, TLS
- `runtime/src/llvm/`, `runtime/src/vir/` - AOT/JIT backend
- `repl/main.c` - Entry point and bootstrap (the `valk` CLI)
- `stdlib/` - Valk standard library (`prelude.valk` auto-loads)

### Value Types
`valk_ltype_e` (`runtime/src/parser.h:91`): LVAL_UNDEFINED, LVAL_NUM, LVAL_SYM,
LVAL_STR, LVAL_FUN, LVAL_REF, LVAL_NIL, LVAL_CONS, LVAL_ERR, LVAL_HANDLE,
LVAL_DICT.

`LVAL_QEXPR` is a deprecated alias for `LVAL_CONS` — quoting is a flag
(`LVAL_FLAG_QUOTED`), not a distinct type. There is no `LVAL_ENV` or `LVAL_CONT`.

### Memory Model
- **Scratch arena**: Bump allocator for temporaries; overflow falls back to the heap
- **GC heap**: Parallel stop-the-world mark-sweep for persistent values
- **Slab allocators**: Fixed-size blocks (lval, lenv, AIO structures)

Use `VALK_WITH_ALLOC(allocator)` to switch allocators temporarily.
Use `valk_evacuate_to_heap(val)` to move a scratch value to the GC heap — this
happens at lifetime escape points. There is no `valk_intern` and no separate
checkpoint pass. See [MEMORY_MANAGEMENT.md](runtime/docs/MEMORY_MANAGEMENT.md).

### Testing
- C tests: `runtime/test/<area>/test_*.c` using the harness in `testing/c/testing.{c,h}`
- Valk tests: `runtime/test/<area>/test_*.valk` using `testing/test.valk`
- Areas: `aio`, `gc`, `http`, `lang`, `metrics`, `parser`, `unit`, `stress`; LSP tests live in `lsp/test/`
- Always run `make test`, not individual binaries

### Testing Philosophy (IMPORTANT)
**Use test doubles (fakes), NEVER mocking frameworks.**

- **Fakes**: Real implementations with simplified behavior (e.g., `io_tcp_ops_test.c`)
- Fakes record data for inspection: `valk_test_tcp_get_sent()`
- Fakes allow injecting data: `valk_test_tcp_inject_data()`
- NO mock frameworks, NO expectation setup, NO "expect X calls" patterns
- Tests verify state/output, not interaction counts

Example pattern:
```c
// GOOD: Use fake that records sent data
valk_test_tcp_inject_data(&tcp, request_bytes, len);
process_request(&conn);
size_t sent = valk_test_tcp_get_sent(&tcp, buf, sizeof(buf));
ASSERT(memcmp(buf, expected_response, sent) == 0);

// BAD: Mock with expectations (DO NOT USE)
// EXPECT_CALL(tcp, write).Times(1).With(expected_data);
```

## TODO Comments

Use branch-specific tags: `TODO(networking):`, `TODO(llvm):`, `TODO(main):`

Find with: `make todo`

## Everything Else

Code style, the file-size limit, required workflow, quality snapshots, debugging
(core dumps, rr, sanitizers, async completion hangs), and the "what NOT to do"
rules are all in **[AGENTS.md](AGENTS.md)**. Not duplicated here — that file is
the single source of truth.

Two additions specific to this file:

- Don't suggest mocking frameworks - use fakes/test doubles only
- Don't use "mock" terminology - say "fake" or "test double"
