# Coverage Improvement

## Overview

Achieve comprehensive test coverage across the Valk codebase to ensure reliability and catch regressions early. The target is 90% line coverage and 85% branch coverage for all source files. This improves confidence in the codebase and makes refactoring safer.

## Requirements

### Coverage Targets

| Metric | Target | Scope |
|--------|--------|-------|
| Line coverage | ≥90% | All files in `src/` |
| Branch coverage | ≥85% | All files in `src/` |

### Tooling

Coverage is measured using:
- `make coverage` - Generates HTML coverage report
- `python3 scripts/find-uncovered-branches.py <file.c>` - Lists uncovered branches in a file

### Coverage Report Location

Reports are generated to `coverage-report/` directory. Open `coverage-report/index.html` to view.

### Strategy

1. **Identify gaps**: Run `make coverage` and identify files below targets
2. **Find uncovered branches**: Use `find-uncovered-branches.py` to locate specific untested code paths
3. **Analyze conditions**: Read source code at uncovered lines to understand what condition is not being hit
4. **Write targeted tests**: Create tests that specifically exercise the UNTESTED branch
5. **Verify improvement**: Re-run `make coverage` to confirm branch coverage increased

### Priority Order

Focus on files in this order:
1. Core parser (`src/parser.c`) - Most critical, highest impact
2. AIO subsystem (`src/aio/*.c`) - Critical for async correctness
3. Memory management (`src/gc/*.c`, `src/arena.c`) - Critical for stability
4. HTTP/SSE handlers (`src/aio/http2/*.c`) - Important for server functionality
5. Utility files - Lower priority

### Test File Conventions

New tests should be added to:
- `test/test_<module>_coverage.c` for C unit tests targeting specific branches
- `test/test_<module>_edge_cases.valk` for Valk integration tests

### Exclusions

The following are excluded from coverage requirements:
- `vendor/` directory (third-party code)
- Debug-only code guarded by `#ifdef DEBUG`
- Platform-specific code not compiled on CI platform

## Acceptance Criteria

- [ ] `make coverage` reports ≥90% line coverage for all `src/` files
- [ ] `make coverage` reports ≥85% branch coverage for all `src/` files
- [ ] No files in `src/` are marked as "failing" in coverage report
- [ ] All new tests pass (`make test` succeeds)
- [ ] Coverage report generates without errors
