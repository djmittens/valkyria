# AGENTS.md - Valkyria Lisp Interpreter (C23)

## Build & Test Commands
- `make build` - Build into `build/` (CMake+Ninja)
- `make test` - Run all C and Valk tests
- `make lint` - Run clang-tidy (must pass before committing)
- `make coverage` - Generate aggregated C+Valk coverage (HTML: `coverage-report/index.html`)
- `python3 scripts/find-uncovered-branches.py <file.c>` - Find specific uncovered branches
- Single C test: `build/test_memory` (binary name matches `test/*.c`)
- Single Valk test: `build/valk test/test_prelude.valk`
- ASAN tests: `make test-c-asan`, `make test-valk-asan`
- TSAN tests: `make test-c-tsan`, `make test-valk-tsan`

## Sanitizer Output (CRITICAL)
Sanitizer output can flood context. **Always redirect to file, then summarize.**

```bash
# TSAN - redirect and summarize
TSAN_OPTIONS="log_path=build/tsan.log" make test-c-tsan
echo "TSAN: $(grep -c 'WARNING: ThreadSanitizer' build/tsan.log 2>/dev/null || echo 0) races"
grep -A2 "WARNING: ThreadSanitizer" build/tsan.log | grep "#0" | sort -u | head -5

# ASAN - redirect and summarize  
ASAN_OPTIONS="log_path=build/asan.log" make test-c-asan
grep -c "ERROR: AddressSanitizer" build/asan.log 2>/dev/null || echo "0 errors"
```

**NEVER** run sanitizer tests without redirecting output - it will flood your context.

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

## Defensive Code Principles

### Validate at API Boundaries, Trust Internally
- Type checking happens via `LVAL_ASSERT_TYPE` in builtins (parser.c)
- Internal functions trust these guarantees - no redundant type/null checks
- Don't re-validate what the API boundary already guarantees

### Don't Sanity-Check Other Subsystems
- If GC is broken, fix GC - don't scatter forward-pointer checks everywhere
- If memory is corrupted, fix the corruption source - don't add magic number validation
- Each subsystem is responsible for its own correctness

### LCOV Exclusions - Only for Truly Untestable Code
Use `// LCOV_EXCL_START` / `// LCOV_EXCL_STOP` ONLY for:
- OOM paths (malloc/aligned_alloc failures)
- Platform API failures that essentially never fail (e.g., uv_timer_init)
- Impossible branches required by API contracts

DO NOT exclude:
- Error handling that can be triggered by bad input
- Callback paths that just need integration tests
- Code that's "hard to test" but not impossible

### Anti-Patterns to Remove
When refactoring, eliminate these patterns:
- **Magic number validation**: `if (x->magic != EXPECTED_MAGIC)` - unreliable, masks real bugs
- **Forward pointer chasing**: `while (val->forward) val = val->forward` - GC's job, not caller's
- **Redundant null/type checks**: Already validated at API boundary
- **Atomic loads/stores**: Unnecessary with stop-the-world GC
- **Debug fprintf/tracing**: Remove or gate behind compile-time flag

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
