# AGENTS.md - Valkyria Lisp Interpreter (C23)

## Build & Test Commands
- `make build` - Build into `build/` (CMake+Ninja)
- `make test` - Run all C and Valk tests
- `make lint` - Run clang-tidy (must pass before committing)
- Single C test: `build/test_memory` (binary name matches `test/*.c`)
- Single Valk test: `build/valk test/test_prelude.valk`
- ASAN tests: `make test-c-asan`, `make test-valk-asan`

## Code Style
- C23 with GNU extensions, 2-space indent, no comments unless essential
- `snake_case` for functions/variables, `UPPER_SNAKE` for macros
- `*_t` suffix for types, `*_e` for enums, `valk_` prefix for public symbols
- Headers mirror sources: `memory.c` -> `memory.h`
- DO NOT ADD COMMENTS to code unless explicitly asked

## Project Layout
- `src/` - C runtime + `.valk` stdlib; core: `parser.c`, `memory.c`, `gc.c`
- `test/` - `test_*.c` (C) and `test_*.valk` (Lisp); `stress/` for long tests
- `build/` - Generated; never commit

## Error Handling
- Return `valk_lval_err()` for recoverable errors in builtins
- Use `VALK_ASSERT()` for invariant violations

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
