# Test Status Summary

## Current Situation

**Test files in `test/` directory:** 81 files (77 .valk + 4 .c)
**Tests actually run by `make test`:** 14 tests

## Tests Currently in `make test`

### C Tests (7)
1. ✅ `build/test_std` - Standard library and parser tests
2. ✅ `build/test_memory` - Memory allocator tests
3. ✅ `build/test_freeze` - Freeze/thaw functionality
4. ✅ `build/test_escape` - Escape analysis tests
5. ✅ `build/test_bytecode` - Bytecode tests
6. ✅ `build/test_concurrency` - Futures/promises tests
7. ✅ `build/test_networking` - Low-level HTTP/2 tests

### Lisp Tests (7)
8. ✅ `test/test_prelude.valk` - 23 tests of standard library functions
9. ✅ `test/test_simple.valk` - Minimal sanity check (just prints 42)
10. ✅ `test/test_namespace.valk` - 1 test of namespaced symbols
11. ✅ `test/test_varargs.valk` - 2 tests of variadic functions
12. ✅ `test/test_minimal.valk` - Async/await basic functionality
13. ✅ `test/test_two_async.valk` - Sequential async operations
14. ✅ `test/test_one_async.valk` - Single async operation
15. ✅ `test/test_http_minimal.valk` - 11 HTTP API tests (NEW!)

## Tests NOT in `make test`

### Working Tests (Could Be Added)

#### GC Tests (5 working)
- ✅ `test/test_gc.valk` - GC allocation stress test
- ✅ `test/test_gc_header.valk` - GC header tests
- ✅ `test/test_gc_metrics.valk` - GC metrics tests
- ✅ `test/test_gc_safepoint.valk` - GC safepoint tests
- ✅ `test/test_gc_trigger.valk` - GC trigger tests

#### Continuation Tests (4 working)
- ✅ `test/test_continuations.valk` - Continuation functionality
- ✅ `test/test_cont_simple.valk` - Simple continuation tests
- ✅ `test/test_cont_shift.valk` - Shift/reset tests
- ✅ `test/test_cont_capture.valk` - Continuation capture tests

#### Async Tests (5 working)
- ✅ `test/test_async_comprehensive.valk` - Comprehensive async tests
- ✅ `test/test_async_demo.valk` - Async demos
- ✅ `test/test_async_part1.valk` - Async part 1
- ✅ `test/test_core_monadic.valk` - Core monadic operations
- ✅ `test/test_monadic_simple.valk` - Simple monadic tests

#### Bytecode Tests (2 working)
- ✅ `test/test_bytecode_simple.valk` - Simple bytecode test
- ✅ `test/test_bytecode_countdown.valk` - Bytecode countdown test

#### HTTP/Networking Tests (5 working)
- ✅ `test/http2_error_handling.valk` - HTTP/2 error handling
- ✅ `test/http2_rst_stream.valk` - HTTP/2 RST_STREAM tests
- ✅ `test/http2_server_client.valk` - HTTP/2 client/server
- ✅ `test/test_http_basic.valk` - Basic HTTP API tests
- ✅ `test/test_aio_check.valk` - AIO checks

#### Other Working Tests (10+)
- ✅ `test/test_basic.valk` - Basic sanity check
- ✅ `test/test_await_inside.valk` - Await functionality
- ✅ `test/test_macro_expansion.valk` - Macro expansion
- ✅ `test/test_just_lib.valk` - Library loading
- ✅ `test/test_numeric.valk` - Numeric operations
- And more...

### Failing/Problematic Tests (6)
- ❌ `test/test_async_final.valk` - Memory issues
- ❌ `test/test_async_monadic.valk` - Crashes
- ❌ `test/test_async_simple.valk` - Crashes
- ❌ `test/test_async_working.valk` - Crashes
- ❌ `test/test_http_api.valk` - Memory issues with complex operations
- ❌ `test/test_http_simple.valk` - Memory issues
- ❌ `test/test_cont_basic.valk` - Fails/crashes

### Debug/Development Files (~40)
These are experimental/debug files created during development:
- `test/*_debug.valk` - Debug versions
- `test/*_inline.valk` - Inline test experiments
- `test/*_direct.valk` - Direct test experiments
- `test/test_simple_*.valk` - Simple test variations

## Recommendations

### High Priority - Should Add to `make test`

**GC Tests** (important for memory safety):
```makefile
build/valk test/test_gc.valk &&\
build/valk test/test_gc_metrics.valk &&\
```

**Continuation Tests** (core functionality):
```makefile
build/valk test/test_continuations.valk &&\
build/valk test/test_cont_simple.valk &&\
```

**Bytecode Tests** (if bytecode is used):
```makefile
build/valk test/test_bytecode_simple.valk &&\
```

### Medium Priority - Could Add

**Async Tests** (if they use test framework):
- These should be converted to use `test/define` and `test/run` first
- Then add to `make test`

**HTTP/2 Tests** (if networking is critical):
- `test/http2_error_handling.valk`
- `test/http2_rst_stream.valk`

### Low Priority

**Debug/Development Files**:
- Keep for development but don't add to `make test`
- Consider moving to `test/dev/` or `test/debug/` subdirectory

## Converting Tests to Use Test Framework

Many tests just use `print` statements. They should be converted to use the proper test framework:

### Before:
```lisp
(def {result} (+ 1 2))
(print "Result:" result)
```

### After:
```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/define "addition-works"
  {do
    (def {result} (+ 1 2))
    (test/assert-eq 3 result "1 + 2 should equal 3")
  })

(test/run {})
```

## Test Framework Files

Tests using the proper test framework (6 files):
1. ✅ `test/test_prelude.valk` - 23 tests
2. ✅ `test/test_namespace.valk` - 1 test
3. ✅ `test/test_varargs.valk` - 2 tests
4. ✅ `test/test_http_minimal.valk` - 11 tests
5. ⚠️ `test/test_http_debug.valk` - Debug file
6. ⚠️ `test/test_http_framework.valk` - Debug file

## Suggested New `make test` Target

```makefile
.PHONY: test
test: build
	# C tests
	build/test_std &&\
	build/test_memory &&\
	build/test_freeze &&\
	build/test_escape &&\
	build/test_bytecode &&\
	build/test_concurrency &&\
	build/test_networking &&\
	# Lisp standard library tests
	build/valk test/test_prelude.valk &&\
	build/valk test/test_simple.valk &&\
	build/valk test/test_namespace.valk &&\
	build/valk test/test_varargs.valk &&\
	# Async/continuation tests
	build/valk test/test_minimal.valk &&\
	build/valk test/test_two_async.valk &&\
	build/valk test/test_one_async.valk &&\
	build/valk test/test_continuations.valk &&\
	build/valk test/test_cont_simple.valk &&\
	# GC tests
	build/valk test/test_gc.valk &&\
	build/valk test/test_gc_metrics.valk &&\
	# Bytecode tests
	build/valk test/test_bytecode_simple.valk &&\
	# HTTP API tests
	build/valk test/test_http_minimal.valk
```

This would bring us from **14 tests** to **22 tests** in `make test`.

## Summary Stats

| Category | Total Files | In `make test` | Working | Could Add |
|----------|-------------|----------------|---------|-----------|
| C Tests | 4 | 7 binaries | 7 | 0 |
| Lisp Tests | 77 | 7 | ~40 | ~8 |
| **Total** | **81** | **14** | **~47** | **~8** |

## Next Steps

1. **Immediate**: Add the 8 recommended tests to `make test`
2. **Short-term**: Convert more tests to use `test/define` framework
3. **Medium-term**: Fix the 6 failing tests (memory issues)
4. **Long-term**: Organize test directory into subdirectories:
   - `test/unit/` - Unit tests
   - `test/integration/` - Integration tests
   - `test/dev/` - Development/debug tests
   - `test/benchmarks/` - Performance tests
