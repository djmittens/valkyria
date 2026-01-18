# Warning Remediation Plan

**Total Warnings: 366**
**Date: December 28, 2025**

## Summary by Category

| Category | Count | Risk Level | Description |
|----------|-------|------------|-------------|
| Format String Mismatch | 233 | **HIGH** | `%lu` used for `uint64_t` instead of `%llu` - undefined behavior on some platforms |
| Unused Functions | 54 | LOW | Dead code - static functions never called |
| Unused Variables | 32 | LOW | Variables declared but never used |
| Incompatible Pointer Types | 21 | **HIGH** | Type mismatches in pointer assignments/parameters - potential memory corruption |
| String Comparison | 9 | MEDIUM | Using `==` instead of `strcmp()` for string comparison |
| Unused Parameters | 6 | LOW | Function parameters not used |
| Missing Switch Cases | 4 | MEDIUM | Enum values not handled in switch statements |
| Unused-but-set Variables | 3 | LOW | Variables assigned but never read |
| Function Type Cast Mismatch | 2 | **HIGH** | Casting between incompatible function pointer types |
| Discarded Qualifiers | 1 | MEDIUM | Dropping const qualifier |
| Empty Translation Unit | 1 | LOW | Source file has no declarations when conditionally compiled out |

## Warnings by File (Top Offenders)

| File | Warnings | Primary Issues |
|------|----------|----------------|
| `src/aio/aio_metrics.c` | 114 | Format strings, incompatible pointers |
| `src/aio/aio_sse_diagnostics.c` | 106 | Format strings, incompatible pointers |
| `test/testing.c` | 43 | String comparison, unused |
| `src/metrics_delta.c` | 20 | Format strings |
| `test/test_memory.c` | 12 | Unused |
| `src/parser.c` | 8 | Switch cases, incompatible pointers |
| `src/metrics_v2.c` | 6 | Format strings |

## Remediation Plan

### Phase 1: Critical - Type Safety Issues (Priority: HIGH)

**Target: 0 warnings from incompatible pointer types and format strings**

#### 1.1 Format String Fixes (233 warnings)

**Problem:** Using `%lu` format specifier for `uint64_t` values. On ARM64 macOS, `uint64_t` is `unsigned long long`, not `unsigned long`.

**Solution:** Use portable format macros from `<inttypes.h>`:
```c
#include <inttypes.h>
printf("value: %" PRIu64 "\n", my_uint64);
```

**Files to fix:**
- [ ] `src/aio/aio_metrics.c` (114 instances)
- [ ] `src/aio/aio_sse_diagnostics.c` (~80 instances)
- [ ] `src/metrics_delta.c` (20 instances)
- [ ] `src/metrics_v2.c` (6 instances)
- [ ] `src/aio/aio_sse.c` (2 instances)
- [ ] Various test files

**Estimated effort:** 2-3 hours (mostly mechanical replacement)

#### 1.2 Incompatible Pointer Types (21 warnings)

**Problem:** Forward declarations using `struct foo_t*` don't match typedefs like `typedef struct bar foo_t`.

**Root cause:** Headers declare `struct valk_gc_malloc_heap_t*` but the actual typedef is:
```c
typedef struct valk_gc_heap2 valk_gc_malloc_heap_t;
```

**Solution:** Fix the forward declarations to match actual types, or use consistent naming.

**Files to fix:**
- [ ] `src/aio/aio_metrics.h` - fix forward declarations
- [ ] `src/aio/aio_system.c` - fix assignments
- [ ] `src/parser.c` - fix function calls
- [ ] `src/aio/aio_sse_diagnostics.c` - fix pointer types

**Estimated effort:** 1-2 hours (requires understanding type relationships)

#### 1.3 Function Type Cast Mismatch (2 warnings)

**Problem:** In `src/aio/http2/http2_ops_nghttp2.c`, casting callback function pointers between incompatible signatures.

**Solution:** Create proper wrapper functions that match the expected signature.

**Estimated effort:** 30 minutes

### Phase 2: Medium Priority - Logic Issues

#### 2.1 String Comparison (9 warnings)

**Problem:** Using `==` to compare strings (compares pointers, not content).

**Location:** `test/testing.c`

**Solution:** Replace with `strcmp()` calls.

**Estimated effort:** 15 minutes

#### 2.2 Missing Switch Cases (4 warnings)

**Problem:** `LVAL_HANDLE` not handled in switch statements in `src/parser.c`.

**Solution:** Add explicit `case LVAL_HANDLE:` with appropriate handling or `default:` fallthrough.

**Estimated effort:** 30 minutes

### Phase 3: Low Priority - Code Cleanliness

#### 3.1 Unused Functions (54 warnings)

**Files affected:**
- `test/testing.c` - test helper functions
- `test/test_aio_uv_coverage.c` - disabled tests
- `src/aio/aio_http2_conn.c` - vtable functions
- `src/aio/aio_pressure.c` - utility function
- `src/gc.c` - debug function

**Options:**
1. Delete if truly dead code
2. Add `__attribute__((unused))` if intentionally kept for future use
3. Wrap in `#ifdef` if conditionally needed

**Estimated effort:** 1 hour

#### 3.2 Unused Variables (32 warnings)

**Solution:** Delete or comment out, or use `(void)var;` if intentionally unused.

**Estimated effort:** 30 minutes

#### 3.3 Unused Parameters (6 warnings)

**Solution:** Add `(void)param;` at function start, or use `__attribute__((unused))`.

**Estimated effort:** 15 minutes

#### 3.4 Empty Translation Unit (1 warning)

**Location:** `src/source_loc.c` when `VALK_COVERAGE` is not defined.

**Solution:** Add a dummy declaration or restructure the conditional compilation.

**Estimated effort:** 5 minutes

## Implementation Order

1. **Week 1: Phase 1 (Critical)**
   - Day 1-2: Format string fixes (all `%lu` → `PRIu64`)
   - Day 3: Incompatible pointer types
   - Day 4: Function type casts + string comparison

2. **Week 2: Phase 2 & 3 (Medium/Low)**
   - Day 1: Switch case handling
   - Day 2: Unused functions audit
   - Day 3: Unused variables/parameters cleanup

## Testing Strategy

After each fix:
1. Run `make build` - verify no new warnings introduced
2. Run `make test` - verify no regressions
3. Run `make lint` - verify clang-tidy passes

## Success Criteria

- [ ] `make build 2>&1 | grep -c "warning:"` returns 0
- [ ] All tests pass
- [ ] No new memory issues (ASAN tests pass)

## Notes

- The format string warnings are the most numerous but also the most mechanical to fix
- The incompatible pointer type warnings are the most concerning for correctness
- Most unused code is in test files and may be intentional (disabled tests, helper functions)
- Consider adding `-Werror` to CI after warnings are fixed to prevent regressions
