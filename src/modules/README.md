# Valkyria Modules

This directory contains loadable Valkyria modules organized by namespace.

## test - Testing Framework

The `test` module provides a simple testing framework for Valkyria code.

### Usage

#### From Command Line

```bash
# Run all tests in test/ directory
valk test

# Run specific test file(s)
valk test test/test_simple.valk

# Via Make
make test-lisp
```

#### From Lisp

```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

; Define a test (body must be quoted!)
(test/define "my-test"
  {(test/assert-eq 2 (+ 1 1) "1 + 1 should equal 2")})

; Run all tests
(test/run {})
```

### API

#### test/define
Register a new test.

```lisp
(test/define "test-name" {body})
```

**Important**: The test body must be a quoted expression (wrapped in `{}`).

#### test/assert
Assert that a condition is true.

```lisp
(test/assert condition "error message if false")
```

#### test/assert-eq
Assert that two values are equal.

```lisp
(test/assert-eq expected actual "error message if not equal")
```

#### test/assert-ne
Assert that two values are not equal.

```lisp
(test/assert-ne value1 value2 "error message if equal")
```

#### test/run
Run all registered tests and print results.

```lisp
(test/run {})
```

**Note**: Must be called with `{}` due to zero-argument function calling limitations.

#### test/suite
Group related tests together (optional).

```lisp
(test/suite "suite-name"
  {(do
    (test/define "test1" {body1})
    (test/define "test2" {body2}))})
```

#### test/run-suite
Run only tests from a specific suite.

```lisp
(test/run-suite "suite-name")
```

#### test/list
List all registered tests.

```lisp
(test/list {})
```

#### test/clear
Clear all registered tests (useful in REPL).

```lisp
(test/clear {})
```

### Example

See `examples/test_example.valk` for a complete example.

### Limitations

- Test bodies must be quoted (wrapped in `{}`  for delayed evaluation)
- Zero-argument functions must be called with `{}` (e.g., `(test/run {})`)
- Error handling in tests is limited - errors will stop test execution
- No async test support yet

### Future Improvements

- Better error reporting (show which assertion failed)
- Test fixtures (setup/teardown)
- Async test support
- Test timeouts
- Test coverage reporting
- Better failure messages
