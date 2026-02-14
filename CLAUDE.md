# CLAUDE.md

Instructions for Claude Code when working with this repository.

## Project Overview

Valkyria is a Lisp interpreter in C23. See [docs/](docs/) for full documentation:
- [LANGUAGE.md](docs/LANGUAGE.md) - Language reference
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
- `src/parser.{c,h}` - Parser, evaluator, builtins
- `src/memory.{c,h}` - Memory allocators
- `src/gc.{c,h}` - Garbage collector
- `src/aio_uv.c` - Async I/O (libuv)
- `src/repl.c` - REPL entry point

### Value Types
`valk_ltype_e`: LVAL_NUM, LVAL_SYM, LVAL_STR, LVAL_FUN, LVAL_REF, LVAL_NIL, LVAL_CONS, LVAL_QEXPR, LVAL_ERR, LVAL_ENV, LVAL_CONT

### Memory Model
- **GC Heap**: Mark-and-sweep for persistent values
- **Scratch Arena**: Bump allocator for temporaries (reset per REPL expression)
- **Slab Allocator**: Fixed-size blocks for specific structures

Use `VALK_WITH_ALLOC(allocator)` to switch allocators temporarily.
Use `valk_intern(env, val)` to copy values to GC heap.

### Testing
- C tests: `test/test_*.c` using `testing.{c,h}`
- Lisp tests: `test/test_*.valk` using `src/modules/test.valk`
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

## Code Style

- C23 with GNU extensions, 2-space indent
- `snake_case` functions/vars, `UPPER_SNAKE` macros
- `*_t` suffix for types, `*_e` for enums
- All public symbols prefixed `valk_`

## TODO Comments

Use branch-specific tags: `TODO(networking):`, `TODO(llvm):`, `TODO(main):`

Find with: `make todo`

## Required Workflow (CRITICAL - MUST FOLLOW)

### Before ANY Code Change
1. READ the file(s) you intend to modify - NEVER edit without reading first
2. Understand the existing code conventions and patterns
3. Verify any libraries/utilities exist before using them

### After ANY Code Change
1. Run `make build` to verify compilation succeeds
2. Run `make test` to verify all tests pass
3. If ANYTHING fails, fix it immediately and re-run
4. ONLY report completion after build AND tests pass

### Task Completion Rules
- NEVER mark a task complete if tests are failing
- NEVER mark a task complete if build is broken
- NEVER mark a task complete if implementation is partial
- NEVER stop mid-task - continue until fully done or user stops you
- NEVER claim a task is "too large" - break it down and complete it

## Communication Style
- Be concise and direct - no fluff
- Don't add preamble like "I'll help you with that" - just do it
- Don't use sycophantic phrases like "Great question!"
- Prioritize accuracy over validation

## What NOT To Do
- Don't make changes without reading code first
- Don't skip running tests after changes
- Don't add comments unless explicitly asked
- Don't commit unless explicitly asked
- Don't add unnecessary abstractions
- Don't create documentation files unless asked
- Don't suggest mocking frameworks - use fakes/test doubles only
- Don't use "mock" terminology - say "fake" or "test double"
