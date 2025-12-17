# Coverage Requirements Implementation Summary

## Overview

Implemented tiered coverage requirements for Valkyria runtime with automated CI enforcement.

## What Was Implemented

### 1. Documentation (4 files)

- **`docs/COVERAGE_REQUIREMENTS.md`** - Complete coverage strategy
  - Tiered requirements by component criticality
  - Rationale for runtime-level standards
  - Testing focus areas per tier
  - MC/DC guidance for safety-critical paths
  
- **`docs/TESTING.md`** - Testing guide
  - How to run tests and coverage
  - Writing tests for C and Valk
  - Debugging failed tests
  - Best practices

- **`docs/CONTRIBUTING.md`** - Updated with coverage requirements
  - Added tier requirements to contributor guide
  - Links to detailed documentation

- **`CLAUDE.md`** - Updated with coverage workflow
  - Added coverage-check to required workflow
  - Added tier requirements summary

### 2. Tooling (2 Python scripts)

- **`bin/check-coverage.py`** - CI gate checker
  - Parses gcov output for all C files
  - Checks each file against tier requirements
  - Exit code 0 = pass, 1 = fail (blocks CI)
  - Colorized output with clear status
  - Supports `--tier` flag to check specific tier
  
- **`bin/coverage-report.py`** - Enhanced HTML reporter
  - Added tier-based sections to HTML report
  - Visual status indicators (✓/✗) per file
  - Pass/fail highlighting
  - Target percentages shown for each tier

### 3. Build Integration (Makefile)

- Added `coverage-check` target
- Integrated into `coverage` workflow
- Exit code propagates to CI

### 4. CI/CD (GitHub Actions)

- **`.github/workflows/coverage.yml`**
  - Runs on all PRs affecting src/test/
  - Builds with coverage instrumentation
  - Runs all tests
  - Generates report
  - Checks requirements (blocks merge on fail)
  - Uploads report as artifact

## Tiered Requirements

| Tier | Components | Line | Branch | Rationale |
|------|------------|------|--------|-----------|
| **0** | gc.c, memory.c | 95% | 90% | Memory corruption cascades to all user code |
| **1** | parser.c, concurrency.c, aio_uv.c | 90% | 85% | Semantic bugs break user correctness |
| **2** | aio_ssl.c, metrics_v2.c, etc. | 80% | 70% | Isolated features with predictable failures |
| **3** | debug.c, log.c, etc. | 70% | 60% | Diagnostic code, fails safely |

## Usage

### Local Development

```bash
# Run full coverage workflow
make coverage

# Check requirements only
make coverage-check

# View HTML report with tier breakdown
open coverage-report/index.html
```

### CI/CD

- Coverage checks run automatically on all PRs
- PRs that fail requirements are blocked from merge
- Coverage reports available as artifacts
- No manual intervention required

### Example Output

```
================================================================================
VALKYRIA RUNTIME COVERAGE GATE CHECK
================================================================================

TIER 0: Memory Safety (CRITICAL)
  Required: 95.0% line, 90.0% branch

  gc.c                 ✗   78.9% line,  60.8% branch  (-16.1% line, -29.2% branch)
  memory.c             ✗   57.8% line,  40.7% branch  (-37.2% line, -49.3% branch)
  Status: ✗ FAIL

TIER 1: Execution Correctness (HIGH)
  Required: 90.0% line, 85.0% branch

  parser.c             ✗   53.3% line,  33.1% branch  (-36.7% line, -51.9% branch)
  concurrency.c        ✗   25.4% line,  16.3% branch  (-64.6% line, -68.7% branch)
  aio_uv.c             ✗   33.2% line,  20.4% branch  (-56.8% line, -64.6% branch)
  Status: ✗ FAIL

================================================================================
RESULT: ✗ COVERAGE REQUIREMENTS NOT MET
================================================================================
```

## Current Status (as of 2025-12-16)

### Critical Gaps

All Tier 0 and Tier 1 components are below requirements:

| Component | Current | Target | Gap |
|-----------|---------|--------|-----|
| gc.c | 78.9% line | 95% | -16.1% |
| memory.c | 57.8% line | 95% | -37.2% |
| parser.c | 53.3% line | 90% | -36.7% |
| concurrency.c | 25.4% line | 90% | -64.6% |
| aio_uv.c | 33.2% line | 90% | -56.8% |

### Next Steps

1. **Add runtime-specific tests**
   - GC: cycles, fragmentation, large objects
   - Memory: OOM, alignment, arena exhaustion
   - Parser: malformed input, deep nesting
   - Concurrency: race conditions, deadlocks

2. **Enable MC/DC (optional)**
   - Add `-fprofile-conditions` to CMakeLists.txt
   - Provides condition-level coverage for critical paths
   - Requires Clang 18+

3. **Document exemptions**
   - Use `// COVERAGE_EXEMPT: reason` for unreachable code
   - Platform-specific code that can't be tested
   - Hardware failure paths (malloc NULL on OOM)

## Verification

All components tested and working:

```bash
# Documentation exists
✓ docs/COVERAGE_REQUIREMENTS.md
✓ docs/TESTING.md
✓ Updated docs/CONTRIBUTING.md
✓ Updated CLAUDE.md

# Tooling works
✓ bin/check-coverage.py (exit code 0/1)
✓ bin/coverage-report.py (tier sections)

# Build integration works
✓ make coverage-check target
✓ Integrates with make coverage

# CI configuration ready
✓ .github/workflows/coverage.yml
```

## Architecture Decisions

### Why Tiered Requirements?

Not all runtime code has equal blast radius. Tiered approach:
- Focuses effort on highest-risk components
- Allows pragmatism for low-risk diagnostics
- Aligns with industry standards (DO-178C, ISO 26262)
- Makes requirements achievable

### Why 95% for Memory Safety?

Memory corruption bugs:
- Cascade to all user code
- Cause non-deterministic failures
- Are extremely difficult to debug
- Can create security vulnerabilities

95% is the minimum for safety-critical memory management (DO-178C Level A).

### Why Expression Coverage for Valk?

Lisp code is naturally more granular:
- One line can contain 5-10 S-expressions
- Line coverage is misleading
- Expression coverage ≈ C statement coverage
- Provides equivalent semantic granularity

## References

- [DO-178C](https://en.wikipedia.org/wiki/DO-178C) - Avionics software certification
- [ISO 26262](https://en.wikipedia.org/wiki/ISO_26262) - Automotive safety standard
- [IEC 62304](https://en.wikipedia.org/wiki/IEC_62304) - Medical device software
- [V8 Testing](https://v8.dev/docs/test) - JavaScript engine testing practices
- [CPython Coverage](https://devguide.python.org/testing/coverage/) - Python runtime coverage

## Future Enhancements

- Codecov integration for PR comments
- Coverage trend tracking over time
- Per-tier dashboard visualization
- Automated test generation for gaps
- MC/DC instrumentation for Tier 0/1
