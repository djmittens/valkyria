# Valkyria Modules

Loadable Valkyria modules.

## test.valk - Testing Framework

```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

; Name the test suite
(test/suite "My Tests")

; Define tests (body must be quoted with {})
(test/define "test-name"
  {do
    (= {result} (my-function 42))
    (== result expected)})

; Run all tests
(test/run {})
```

### API

| Function | Description |
|----------|-------------|
| `(test/suite name)` | Set suite name |
| `(test/skip reason)` | Skip all tests with reason |
| `(test/define name body)` | Register a test |
| `(test/run {})` | Run all tests |
| `(test/debug 1)` | Enable debug output |

### Assertions

Tests pass if their body evaluates to `true` (or any truthy value).

```lisp
(test/define "example"
  {(== (+ 1 1) 2)})  ; Passes if true
```

### Skipping Tests

```lisp
(test/suite "My Tests")
(test/skip "Feature not implemented")
; All tests will be marked as skipped
```
