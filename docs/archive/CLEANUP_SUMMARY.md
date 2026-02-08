# Test Directory Cleanup - Summary

## What Was Done

### 1. Created Regression Test Suites

Created 2 new comprehensive test suites to preserve critical bug fixes:

- **test/test_crash_regressions.valk** (5 tests)
  - Tests for do blocks in test/define that previously crashed
  - Ensures do works correctly as a compiler special form
  
- **test/test_do_suite.valk** (14 tests)
  - Comprehensive tests for do block functionality
  - Critical because do was recently changed from builtin to special form
  - Tests: return values, assignments, scoping, TCO preservation, edge cases

### 2. Cleaned Up Test Directory

**Before:**
- 315 files in test/ directory
- 250+ debug_*.valk files from debugging sessions
- 14 files in `make test`
- Unclear which files mattered

**After:**
- 16 test files (clean and organized)
- All debug files removed (245 deleted)
- 2 new regression test suites added to `make test`
- Critical regression sources archived in test/regression_sources/

**Files Removed:**
- 245 debug_*.valk files (temporary debugging files)
- 21 temporary test files (test_at_*.valk, test_one_*.valk, etc.)
- All debug_*.c files

**Files Archived:**
- 5 crash regression sources → test/regression_sources/crash/
- 15 do block regression sources → test/regression_sources/do_blocks/

### 3. Organized Documentation

**Root Directory MD Files:**
- Kept: CLAUDE.md, README.md, ROADMAP.md, HTTP_API.md, HTTP_API_QUICK_REFERENCE.md
- Archived to docs/archive/: 14 old implementation/status documents

### 4. Updated Build System

**Makefile Changes:**
- Added test_crash_regressions.valk to test suite
- Added test_do_suite.valk to test suite
- New "Regression Tests" section in make test

## Test Suite Status

**Current Test Files (16):**
1. test_async_suite.valk
2. test_bytecode_suite.valk
3. test_continuations_suite.valk
4. test_crash_regressions.valk ✨ NEW
5. test_do_suite.valk ✨ NEW
6. test_gc_stress.valk
7. test_gc_suite.valk
8. test_http_minimal.valk
9. test_namespace.valk
10. test_networking_stress.valk
11. test_prelude.valk
12. test_recursion_25k.valk
13. test_recursion_50k.valk
14. test_recursion_stress.valk
15. test_tco_suite.valk
16. test_varargs.valk

**All Tests Passing:**
- 23 + 1 + 2 + 3 + 4 + 7 + 9 + 5 + 5 + 14 + 8 + 8 + 1 + 1 + 6 + 11 = **108 total tests**
- ✨ All tests pass in ~10 seconds

## Impact

- **84% reduction** in test directory clutter (315 → 16 files)
- **New regression coverage** for crash bugs and do block edge cases
- **Clean organization** with archived sources for future reference
- **No functionality lost** - all critical test cases preserved
