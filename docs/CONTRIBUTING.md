# Contributing to Valkyria

This document covers development setup, code style, and contribution guidelines.

## Getting Started

### Prerequisites

#### macOS (Homebrew)

```bash
brew install cmake ninja llvm libuv openssl@3
```

Note: libbacktrace is not required on macOS (uses native backtrace support).

#### Linux

- **Compiler**: Clang with C23 support
- **Build tools**: CMake, Ninja, pkg-config
- **Libraries**: OpenSSL, libuv, libbacktrace, libedit
- **Optional**: Docker (for infer analysis)

```bash
# Debian/Ubuntu
sudo apt install clang cmake ninja-build pkg-config \
  libssl-dev libuv1-dev libbacktrace-dev libedit-dev
```

### Build from Source

```bash
# Clone repository
git clone <repo-url>
cd valkyria

# Build
make build

# Run tests
make test

# Run REPL
make repl
```

### Common Commands

```bash
make build          # Build everything
make test           # Run all tests
make repl           # Start REPL with prelude
make debug          # Launch REPL under lldb
make asan           # Build with AddressSanitizer
make lint           # Run clang-tidy
make cppcheck       # Run cppcheck analysis
make infer          # Run Facebook Infer (requires Docker)
make clean          # Clean build artifacts
make todo           # Find TODOs for current branch
```

## Project Structure

```
valkyria/
├── src/
│   ├── parser.{c,h}      # Parser and evaluator
│   ├── memory.{c,h}      # Memory management
│   ├── gc.{c,h}          # Garbage collector
│   ├── concurrency.{c,h} # Futures, promises
│   ├── aio.h             # Async I/O interface
│   ├── aio_uv.c          # libuv implementation
│   ├── aio_ssl.c         # TLS support
│   ├── repl.c            # REPL main entry point
│   ├── prelude.valk      # Standard library
│   ├── http_api.valk     # HTTP high-level API
│   └── modules/          # Loadable modules
├── test/
│   ├── testing.{c,h}     # C test framework
│   ├── test_*.c          # C test files
│   ├── test_*.valk       # Lisp test files
│   └── stress/           # Stress tests
├── vendor/               # Third-party code
│   ├── nghttp2/          # HTTP/2 library
│   └── editline/         # REPL line editing
├── build/                # Build output
└── docs/                 # Documentation
```

## Code Style

### C Code

- **Standard**: C23 with GNU extensions
- **Indentation**: 2 spaces
- **Naming**:
  - Functions/variables: `snake_case`
  - Macros: `UPPER_SNAKE`
  - Types: `snake_case_t`
  - Enums: `snake_case_e`
- **Prefix**: All public symbols use `valk_` prefix
- **Headers**: Local `"header.h"`, system `<header.h>`

```c
// Example style
typedef struct {
  size_t capacity;
  size_t count;
  valk_lval_t** items;
} valk_list_t;

valk_lval_t* valk_lval_num(long x) {
  valk_lval_t* res = valk_mem_alloc(sizeof(valk_lval_t));
  res->flags = LVAL_NUM;
  res->num = x;
  return res;
}
```

### Lisp Code

- **Indentation**: 2 spaces
- **Line length**: ~80 characters preferred
- **Naming**: `kebab-case` for functions and variables

```lisp
; Example style
(fun {calculate-sum items}
  {foldl + 0 items})

(def {result}
  (calculate-sum {1 2 3 4 5}))
```

## Testing

### Testing Philosophy

**Use test doubles (fakes), NOT mocking frameworks.**

This project uses **fakes** - real implementations with simplified/deterministic behavior that can be swapped in via vtables. Fakes allow:
- Injecting test data: `valk_test_tcp_inject_data()`
- Inspecting outputs: `valk_test_tcp_get_sent()`
- Controlling time: `valk_test_timer_fire()`

Do NOT use:
- Mocking frameworks (gmock, cmock, etc.)
- Expectation-based testing ("expect X calls with Y args")
- Interaction verification ("verify method was called N times")

```c
// GOOD: Fake records data, test inspects it
valk_test_tcp_inject_data(&tcp, request, len);
handle_request(&conn);
size_t sent = valk_test_tcp_get_sent(&tcp, response, sizeof(response));
ASSERT(sent > 0);
ASSERT(memcmp(response, expected, sent) == 0);

// BAD: Mock expectations (DO NOT USE)
// mock_expect_call(tcp_write, times(1), with(expected_data));
```

### C Tests

Located in `test/test_*.c`. Use the `testing.{c,h}` framework:

```c
#include "testing.h"

void test_my_feature(void) {
  valk_lval_t* val = valk_lval_num(42);
  ASSERT_EQ(val->num, 42);
}

int main(void) {
  test_my_feature();
  return 0;
}
```

### Lisp Tests

Located in `test/test_*.valk`. Use the test module:

```lisp
(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "My Tests")

(test/define "my-test-name"
  {do
    (= {result} (my-function 42))
    (== result expected-value)})

(test/run {})
```

### Running Tests

```bash
# All tests
make test

# Specific C test
./build/test_std

# Specific Lisp test
./build/valk test/test_prelude.valk
```

### Skipping Tests

For tests that can't pass yet (missing features, known issues):

```lisp
(test/suite "My Tests")
(test/skip "Reason for skipping")
; Tests will be marked as skipped
```

## Memory Management

### Allocator Patterns

```c
// Switch to specific allocator temporarily
VALK_WITH_ALLOC((void*)scratch) {
  expr = valk_lval_read(&pos, input);
}

// Values that escape must be interned to GC heap
val = valk_intern(env, val);
```

### Reference Counting (for specific structures)

```c
valk_retain(ref);           // Single-threaded increment
valk_arc_retain(ref);       // Atomic increment (concurrent)
valk_release(ref);          // Single-threaded decrement
valk_arc_release(ref);      // Atomic decrement (concurrent)
```

### GC Considerations

- Values in scratch arena are temporary
- Use `valk_intern()` to copy to GC heap
- Set `LVAL_FLAG_ESCAPES` on values stored in closures

## TODO Comments

Use branch-specific TODO tags:

```c
// TODO(networking): Implement connection pooling
// TODO(llvm): Tail call optimization
// TODO(main): General improvement
```

Find TODOs for current branch:
```bash
make todo
```

## Pull Request Process

1. Create feature branch from `main`
2. Make changes with tests
3. Ensure `make test` passes
4. Run `make lint` and fix warnings
5. Update documentation if needed
6. Submit PR with clear description

## Architecture Guidelines

### Adding Built-in Functions

1. Add to `valk_lenv_builtins()` in `parser.c`
2. Implement as `static valk_lval_t* valk_builtin_xxx(valk_lenv_t* e, valk_lval_t* a)`
3. Use `LVAL_ASSERT_*` macros for argument validation
4. Add tests

```c
static valk_lval_t* valk_builtin_my_func(valk_lenv_t* e, valk_lval_t* a) {
  LVAL_ASSERT_COUNT_EQ(a, a, 1);
  LVAL_ASSERT_TYPE(a, valk_lval_list_nth(a, 0), LVAL_NUM);

  long x = valk_lval_list_nth(a, 0)->num;
  return valk_lval_num(x * 2);
}

// In valk_lenv_builtins():
valk_lenv_put_builtin(env, "my-func", valk_builtin_my_func);
```

### Adding Value Types

1. Add enum value to `valk_ltype_e` in `parser.h`
2. Add union member to `valk_lval_t` if needed
3. Add case to `valk_ltype_name()`
4. Handle in `valk_lval_copy()`, `valk_lval_eq()`, etc.
5. Handle in GC marking if contains pointers

### Platform Considerations

- **macOS**: 
  - Uses Homebrew LLVM/Clang automatically
  - libbacktrace not required (uses system backtrace support)
  - editline header location: `<editline/readline.h>`
  - Debug symbols generated with dsymutil
- **Linux**: 
  - Uses system clang
  - Requires `_XOPEN_SOURCE=700` and `_GNU_SOURCE` for pthread support
  - Requires libbacktrace for enhanced stack traces
- Test on both platforms before merging

## Resources

- [LANGUAGE.md](LANGUAGE.md) - Language reference
- [ROADMAP.md](ROADMAP.md) - Project roadmap
- `CLAUDE.md` - AI assistant instructions
