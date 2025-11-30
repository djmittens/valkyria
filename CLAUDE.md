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
make test           # Run all tests (ALWAYS use this, not direct binary)
make repl           # Start REPL with prelude
make debug          # REPL under lldb
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

## Code Style

- C23 with GNU extensions, 2-space indent
- `snake_case` functions/vars, `UPPER_SNAKE` macros
- `*_t` suffix for types, `*_e` for enums
- All public symbols prefixed `valk_`

## TODO Comments

Use branch-specific tags: `TODO(networking):`, `TODO(llvm):`, `TODO(main):`

Find with: `make todo`

## Known Limitations

- **No TCO**: Tree-walking interpreter uses C stack. TCO requires stack machine or LLVM backend.
- **No HTTP/2 server**: Only client implemented.
- **No type system**: Dynamically typed for now.

## Creating Test Files

Use `test/` folder, not `/tmp`:
```bash
cat > test/debug_issue.valk << 'EOF'
(load "src/prelude.valk")
(print "test")
EOF
./build/valk test/debug_issue.valk
```
