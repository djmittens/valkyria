# Testing Guide for Valkyria

## Running Tests

```bash
# Run all tests
make test

# Run C tests only
make test-c

# Run Valk tests only
make test-valk

# Run with AddressSanitizer
make test-c-asan
make test-valk-asan

# Single test
./build/test_memory
./build/valk test/test_prelude.valk
```

## Coverage Testing

```bash
# Full coverage workflow
make coverage

# Step by step
make build-coverage      # Build with instrumentation
make coverage-tests      # Run all tests
make coverage-report     # Generate HTML report
make coverage-check      # Check against requirements

# View report
open coverage-report/index.html
```

## Coverage Requirements

See [COVERAGE_REQUIREMENTS.md](COVERAGE_REQUIREMENTS.md) for detailed tier requirements.

**Quick reference:**
- Tier 0 (gc.c, memory.c): 95% line, 90% branch
- Tier 1 (parser.c, concurrency.c, aio_uv.c): 90% line, 85% branch
- Tier 2 (features): 80% line, 70% branch
- Tier 3 (observability): 70% line, 60% branch

## Writing Tests

### C Tests

Located in `test/test_*.c`:

```c
#include "testing.h"

void test_my_feature(void) {
  ASSERT(1 + 1 == 2);
  ASSERT_STR_EQ("hello", "hello");
}

int main(void) {
  RUN_TEST(test_my_feature);
  return TEST_SUMMARY();
}
```

### Valk Tests

Located in `test/test_*.valk`:

```lisp
(load "src/prelude.valk")

(defun test-addition ()
  (assert (= (+ 1 1) 2) "1 + 1 should equal 2")
  (assert (= (+ 2 3) 5) "2 + 3 should equal 5"))

(test-addition)
(print "All tests passed!")
```

## Testing Runtime Components

### Memory Safety (Tier 0)

**gc.c tests should cover:**
- Mark-and-sweep correctness
- Object graph cycles
- Large object handling
- Fragmentation scenarios
- Collection under load
- Edge cases (empty heap, full heap)

**memory.c tests should cover:**
- Arena allocation/deallocation
- Arena exhaustion
- Alignment requirements
- OOM handling
- Slab allocator correctness
- Memory pool management

### Execution Correctness (Tier 1)

**parser.c tests should cover:**
- Valid syntax parsing
- Malformed input rejection
- Deeply nested expressions
- Edge case tokens
- Error recovery
- Large input handling

**concurrency.c tests should cover:**
- Thread safety
- Lock acquisition/release
- Deadlock prevention
- Race condition scenarios
- Work queue correctness

### Feature Correctness (Tier 2)

**aio_*.c tests should cover:**
- Happy path functionality
- Error handling
- Connection lifecycle
- Configuration edge cases
- Load testing

## Stress Testing

Located in `test/stress/`:

```bash
# Run stress tests (not part of regular test suite)
./build/valk test/stress/test_gc_stress.valk
./build/valk test/stress/test_networking_stress.valk
```

## CI/CD

Coverage gates are enforced in CI:

```yaml
# .github/workflows/coverage.yml
- name: Check Runtime Coverage Requirements
  run: |
    python3 bin/check-coverage.py --build-dir build-coverage
```

Pull requests that fail coverage checks will be blocked.

## Debugging Failed Tests

### With GDB

```bash
# C tests
gdb ./build/test_memory
(gdb) run
(gdb) bt

# Valk tests
gdb ./build/valk
(gdb) run test/test_prelude.valk
```

### With LLDB (macOS)

```bash
lldb ./build/test_memory
(lldb) run
(lldb) bt
```

### AddressSanitizer

```bash
make test-c-asan
# ASAN will report memory errors with stack traces
```

## Performance Testing

```bash
# With valgrind (Linux)
valgrind --tool=callgrind ./build/valk script.valk

# With Instruments (macOS)
instruments -t "Time Profiler" ./build/valk script.valk
```

## Best Practices

1. **Test at the right level**: Unit tests for functions, integration tests for subsystems
2. **Test error paths**: Don't just test happy paths
3. **Use property-based testing**: Generate random inputs for parsers, allocators
4. **Measure coverage**: Use `make coverage` regularly
5. **Document test intent**: Comment why you're testing, not what
6. **Keep tests fast**: Slow tests don't get run
7. **Isolate tests**: Each test should be independent

## Common Issues

### Test hangs
- Likely deadlock in concurrency code
- Use timeout: `timeout 10 ./build/test_concurrency`

### Flaky tests
- Race conditions in async code
- Use AddressSanitizer with thread sanitizer

### Low coverage
- Add tests for uncovered branches
- Use `make coverage` to see gaps
- Focus on Tier 0/1 components first
