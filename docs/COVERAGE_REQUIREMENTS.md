# Coverage Requirements for Valkyria Runtime

## Overview

Valkyria is a **language runtime system**. All runtime code must meet high coverage standards because bugs cascade to every user application.

## Coverage Requirements

### `src/` - All Runtime Code: **90% line, 85% branch**

**Applies to**: All `.c` files in `src/` directory

**Why**: Every line of runtime code can affect user applications. No exceptions.

**Rationale**:
- Memory bugs cascade system-wide
- Parser bugs affect language semantics  
- Concurrency bugs create race conditions in all user code
- I/O bugs cause silent data corruption
- Even "observability" code can hide critical bugs if it fails

---

### `test/` - Test Code: **No requirement**

**Why**: Test code doesn't ship to production.

---

### `*.valk` - User Code: **70% expression, 60% branch**

**Why**: Application-level Lisp code with standard expectations.

**Note**: Expression coverage for Valk is semantically equivalent to line coverage for C.

---

## Why 90% for ALL Runtime Code?

### No Safe Place to Cut Corners

Every runtime component is critical:

| Component | Why 90% Required |
|-----------|------------------|
| **Memory** | Corruption cascades everywhere |
| **Parser** | Controls program semantics |
| **GC** | Bugs cause non-deterministic failures |
| **Concurrency** | Race conditions affect all async code |
| **I/O (aio_*)** | Silent data corruption, deadlocks |
| **Metrics** | Can hide critical bugs, affect debugging |
| **Debug/Log** | Must work when debugging crashes |
| **SSL/TLS** | Security vulnerabilities |

### What About "Non-Critical" Code?

**There is no non-critical code in a runtime.**

Example: A bug in `log.c` that crashes when logging an error means:
- The actual error is hidden
- Debugging becomes impossible
- User sees wrong error message
- Production crashes are undiagnosable

Example: A bug in `metrics_v2.c` that corrupts memory means:
- Performance monitoring hides real issues
- Memory corruption spreads to user code
- Observability becomes an attack vector

---

## Industry Standards

- **V8 (JavaScript)**: ~90% for all runtime code
- **CPython**: ~85% for all C runtime code
- **Ruby MRI**: ~80% for core
- **DO-178C Level A** (avionics): 100% MC/DC
- **ISO 26262 ASIL D** (automotive): 100% statement + branch

**Valkyria targets 90%** as a pragmatic runtime safety standard across the board.

---

## Coverage Measurement

### C Runtime: Line + Branch Coverage

Use gcov/llvm-cov with standard instrumentation:
```bash
make coverage
```

### Valk/Lisp: Expression + Branch Coverage

Expression-level tracking provides finer granularity than line coverage for Lisp code.

**Equivalence**:
- Valk Expression Coverage ≈ C Statement Coverage
- Both measure atomic units of work

---

## CI/CD Enforcement

### Coverage Gates

CI **blocks** pull requests that:
1. Reduce coverage in `src/` below 90% line, 85% branch
2. Add new `src/` code without meeting requirements

### Per-File Enforcement

```bash
# Check coverage requirements
make coverage-check

# View detailed report
open coverage-report/index.html
```

---

## Enabling MC/DC (Future)

**When**: For memory safety and parser critical paths

**How**: Add `-fprofile-conditions` (requires Clang 18+)

```cmake
if(COVERAGE)
  set(COVERAGE_FLAGS "-fprofile-arcs -ftest-coverage -fprofile-conditions -O0 -g")
endif()
```

**Target**: 100% MC/DC for:
- `gc.c` - collection algorithm
- `memory.c` - allocation/free logic
- `parser.c` - eval loop

---

## Current Status

Run `make coverage` to see current coverage levels.

**Known Gaps** (as of 2025-12-16):
- `src/` runtime: Currently ~40.9% line → need 90%
- Most files below threshold due to insufficient tests

**Priority**: Add tests for ALL runtime components:
- Memory: allocation, free, arena management, OOM
- GC: mark, sweep, cycles, large objects
- Parser: valid/invalid syntax, eval, edge cases
- Concurrency: race conditions, deadlocks, cancellation
- I/O: connection lifecycle, errors, timeouts, backpressure
- SSL: handshake, errors, renegotiation
- Metrics: atomic operations, thread safety
- Logging: error paths, concurrent writes
- Debug: crash handling, backtrace generation

---

## Exceptions and Exemptions

### Acceptable Reasons for Uncovered Code

Document with `// COVERAGE_EXEMPT: reason`:

```c
// COVERAGE_EXEMPT: Platform-specific code (Linux only)
#ifdef __linux__
  munmap(addr, size);
#endif

// COVERAGE_EXEMPT: Hardware failure - malloc NULL on OOM
if (ptr == NULL) {
  return VALK_ERR_OOM;
}

// COVERAGE_EXEMPT: Defensive assertion, mathematically impossible
VALK_ASSERT(refcount >= 0, "Negative refcount impossible");
```

### Review Process

All changes to `src/` must:
1. Include tests achieving 90% line, 85% branch
2. Pass `make coverage-check` in CI
3. Be reviewed by maintainer
4. Document any exemptions with justification

---

## Why Not 100%?

**100% is impractical** for runtime code:
- Platform-specific code paths (Linux vs macOS)
- Hardware failure conditions (OOM, disk full)
- Defensive assertions for "impossible" states
- Error recovery paths that can't be reliably triggered

**90% is achievable** and provides:
- Coverage of all normal execution paths
- Coverage of most error paths
- Coverage of edge cases
- Pragmatic balance with development velocity

**Exemptions must be documented** - if you can't test it, explain why.

---

## Testing Focus

### All Runtime Components Need:

1. **Happy path testing**: Normal operation works correctly
2. **Error path testing**: All error returns are tested
3. **Edge case testing**: Boundary conditions, empty inputs, max values
4. **Concurrency testing**: Thread safety, race conditions
5. **Integration testing**: Components work together correctly
6. **Stress testing**: Behavior under load

### Specific Focus Areas:

**Memory Safety**:
- Arena allocation/deallocation under load
- GC mark-and-sweep correctness
- Object graph cycles
- Large object handling
- Fragmentation scenarios
- OOM handling

**Execution Correctness**:
- Valid syntax parsing
- Malformed input rejection
- Deeply nested expressions
- Tail call optimization
- Stack overflow protection
- Error recovery

**Concurrency**:
- Thread safety
- Lock acquisition/release
- Race condition prevention
- Deadlock avoidance
- Cancellation handling

**I/O & Networking**:
- Connection lifecycle
- Error handling
- Timeouts
- Backpressure
- SSL/TLS handshake
- Large payloads

**Observability**:
- Metrics accuracy
- Concurrent metric updates
- Log correctness under errors
- Debug info during crashes

---

## The Bottom Line

**Every line of runtime code affects user applications.**

There is no "safe" place to skip testing. The runtime must be rock-solid because:
- Users can't work around runtime bugs
- Runtime bugs affect ALL applications
- Runtime bugs are extremely hard to debug
- Runtime bugs can be security vulnerabilities

**90% coverage is the minimum** for production-ready runtime code.

---

## References

- [DO-178C](https://en.wikipedia.org/wiki/DO-178C) - Avionics software certification
- [ISO 26262](https://en.wikipedia.org/wiki/ISO_26262) - Automotive safety standard
- [V8 Testing](https://v8.dev/docs/test) - JavaScript engine testing practices
- [CPython Coverage](https://devguide.python.org/testing/coverage/) - Python runtime coverage
