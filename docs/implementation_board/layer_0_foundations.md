# Layer 0: Foundations

**Status**: Partially complete (parser, S-expressions, numbers, strings, symbols done)

**Timeline**: ~2-3 months for full completion

---

## Current State

### Complete ✓
- [x] Parser (2,895 LOC)
- [x] S-expressions (lists as code)
- [x] Q-expressions (quoting, lists as data)
- [x] Numbers (long/double)
- [x] Strings (C strings)
- [x] Symbols (identifiers)
- [x] Namespaces (basic `namespace/symbol` parsing - partial)

### Remaining Work
- [ ] Rationals (S - 1-3 days)
- [ ] BigNums (M - 1-2 weeks)
- [ ] Unicode support (M - 1-2 weeks)
- [ ] Regex (M - 1-2 weeks)
- [ ] Module system (M - 1-2 weeks)

---

## Feature 1: Rational Numbers (S - 1-3 days)

**Unlocks**: Exact arithmetic, no floating point errors

### Tasks

- [ ] **0.1: Define Rational Type** (2 hours)
  - File: `src/parser.h`
  - Add to `valk_ltype_e`: `LVAL_RATIONAL`
  - Add to `valk_lval_t` union: `struct { long num; long den; } rat;`
  - **Research**: GCD algorithm for normalization
  - **Test**: Create rationals `1/2`, `3/4`, ensure normalized

- [ ] **0.2: Rational Arithmetic** (4-6 hours)
  - File: `src/parser.c` (builtins section)
  - Implement `valk_builtin_add_rational()`
  - Implement `valk_builtin_mul_rational()`
  - Implement `valk_builtin_div_rational()` - just swap num/den
  - Auto-promote integers to rationals when needed
  - **Algorithm**: `a/b + c/d = (ad + bc)/(bd)`, then normalize with GCD
  - **Test**: `(+ 1/2 1/3)` → `5/6`

- [ ] **0.3: Rational Parser** (3-4 hours)
  - File: `src/parser.c` (parsing section)
  - Extend number parser to recognize `/` in token
  - Parse `123/456` as rational
  - Handle edge cases: `5/0` → error, `6/3` → normalize to `2/1`
  - **Test**: Parse `(+ 1/2 1/4)` correctly

- [ ] **0.4: Rational Printer** (1 hour)
  - File: `src/parser.c` (`valk_lval_print`)
  - Print rationals as `num/den`
  - Special case: `x/1` prints as just `x`
  - **Test**: REPL displays rationals correctly

- [ ] **0.5: Rational Tests** (2 hours)
  - File: `test/test_rational.c`
  - Test: Basic arithmetic `1/2 + 1/3 = 5/6`
  - Test: Normalization `6/8 = 3/4`
  - Test: Division `(/ 1 2)` = `1/2`
  - Test: Mixed int/rational `(+ 1 1/2)` = `3/2`
  - **Run**: Add to `make test`

---

## Feature 2: BigNum Support (M - 1-2 weeks)

**Unlocks**: Arbitrary precision arithmetic

**Dependency**: Consider using GMP (GNU Multiple Precision) library

### Tasks

- [ ] **0.6: Choose BigNum Library** (1 day)
  - Research options: GMP, LibTomMath, mini-gmp
  - **Decision factors**: License (GMP is LGPL), size, performance
  - **Recommendation**: GMP for full features, mini-gmp for minimal
  - Update `Makefile` with library dependency
  - **Test**: Link GMP, call `mpz_add` from C

- [ ] **0.7: Define BigNum Type** (1 day)
  - File: `src/parser.h`
  - Add to `valk_ltype_e`: `LVAL_BIGNUM`
  - Add to `valk_lval_t`: `mpz_t bignum;` (if using GMP)
  - Add allocation flag: bignums must live on heap
  - **Memory**: Bignums need cleanup on GC sweep
  - **Test**: Create bignum, verify mpz_t initialized

- [ ] **0.8: BigNum Arithmetic** (3-4 days)
  - File: `src/parser.c` (builtins)
  - Implement `valk_builtin_add` variant for bignums
  - Auto-promote: `int` → `bignum` when overflow
  - Implement all operators: `+`, `-`, `*`, `/`, `%`, `^` (exponentiation)
  - **GMP functions**: `mpz_add`, `mpz_mul`, `mpz_tdiv_q`
  - **Test**: `(+ 123456789012345678901234567890 1)` works

- [ ] **0.9: BigNum Parser** (2 days)
  - File: `src/parser.c`
  - Parse large integers as bignum type
  - Threshold: If number > LONG_MAX, use bignum
  - Parse hex bignums: `0x...`
  - **GMP functions**: `mpz_set_str`
  - **Test**: Parse `999999999999999999999999999999`

- [ ] **0.10: BigNum Printer** (1 day)
  - File: `src/parser.c`
  - Use `mpz_get_str` to convert to string
  - Add suffix? e.g., `123N` or just print as-is
  - **Test**: REPL displays large numbers

- [ ] **0.11: BigNum GC Integration** (2-3 days)
  - File: `src/gc.c`
  - In sweep phase, call `mpz_clear` before freeing
  - In mark phase, bignums don't have pointers to mark
  - **Memory leak check**: Valgrind should show no leaks
  - **Test**: Allocate 1M bignums, GC, verify memory freed

- [ ] **0.12: BigNum Tests** (1 day)
  - File: `test/test_bignum.c`
  - Test: Factorial of 100 (very large)
  - Test: Fibonacci of 1000
  - Test: GC doesn't leak bignums
  - **Run**: Add to `make test`

---

## Feature 3: Unicode Support (M - 1-2 weeks)

**Unlocks**: International strings, proper string operations

**Dependency**: Use UTF-8 encoding (backward compatible with ASCII)

### Tasks

- [ ] **0.13: UTF-8 String Storage** (1 day)
  - **Decision**: Keep `char*` as UTF-8 bytes (no change needed!)
  - UTF-8 is already compatible with C strings
  - **Research**: UTF-8 byte sequence rules
  - **Test**: Store "Hello 世界" as UTF-8 bytes

- [ ] **0.14: String Length Function** (2-3 days)
  - File: `src/modules/string.valk` or `src/parser.c` (builtin)
  - Implement `(str-length s)` - counts UTF-8 codepoints, not bytes
  - **Algorithm**: Scan string, count UTF-8 sequence starts (bytes not matching `10xxxxxx`)
  - **Library option**: Use utf8proc or utf8.h
  - **Test**: `(str-length "世界")` → `2`, not `6`

- [ ] **0.15: String Indexing** (2-3 days)
  - Implement `(str-ref s index)` - get nth codepoint
  - Implement `(str-set s index char)` - set nth codepoint
  - **Challenge**: UTF-8 is variable width, indexing is O(n)
  - **Alternative**: Provide byte-level and codepoint-level APIs
  - **Test**: `(str-ref "a世b" 1)` → `"世"`

- [ ] **0.16: Case Conversion** (2-3 days)
  - Implement `(str-upcase s)`, `(str-downcase s)`
  - **Library**: Use utf8proc for proper Unicode case mapping
  - **Challenge**: Turkish İ/i problem, locale-aware
  - **Test**: `(str-upcase "hello")` → `"HELLO"`, German ß handling

- [ ] **0.17: Unicode Normalization** (1-2 days)
  - Implement `(str-normalize s form)` - NFC, NFD, NFKC, NFKD
  - **Library**: utf8proc provides normalization
  - **Use case**: String comparison, é vs e+´
  - **Test**: Normalize different forms of "café"

- [ ] **0.18: Character Type Predicates** (1 day)
  - Implement `(char-alphabetic? c)`, `(char-numeric? c)`, etc.
  - **Library**: utf8proc or Unicode data tables
  - **Test**: Chinese characters return true for alphabetic

- [ ] **0.19: Unicode Tests** (1 day)
  - File: `test/test_unicode.c` or `test/test_unicode.valk`
  - Test: All major scripts (Latin, Chinese, Arabic, Emoji)
  - Test: String operations with multibyte chars
  - Test: Edge cases (surrogate pairs, invalid UTF-8)
  - **Run**: Add to `make test`

---

## Feature 4: Regular Expressions (M - 1-2 weeks)

**Unlocks**: Pattern matching, text processing

**Dependency**: Use PCRE2 or RE2 library

### Tasks

- [ ] **0.20: Choose Regex Library** (1 day)
  - Research: PCRE2 (Perl-compatible), RE2 (safe, no backtracking)
  - **Recommendation**: PCRE2 for full features, RE2 for safety
  - Add to `Makefile` dependencies
  - **Test**: Link library, compile simple regex from C

- [ ] **0.21: Regex Type** (1 day)
  - File: `src/parser.h`
  - Add to `valk_ltype_e`: `LVAL_REGEX`
  - Store compiled regex: `void* pcre_code;`
  - **Memory**: Must free on GC sweep with `pcre2_code_free`
  - **Test**: Create regex object

- [ ] **0.22: Regex Compilation** (2 days)
  - File: `src/parser.c`
  - Implement `(regex pattern)` - compile pattern to regex object
  - Handle errors: invalid patterns
  - **PCRE2 API**: `pcre2_compile`
  - **Syntax**: Support flags like `#/pattern/i` for case-insensitive
  - **Test**: `(regex "\\d+")` compiles successfully

- [ ] **0.23: Regex Matching** (2-3 days)
  - Implement `(regex-match pattern string)` - returns match or nil
  - Implement `(regex-match-all pattern string)` - returns all matches
  - Return match object with groups
  - **PCRE2 API**: `pcre2_match`
  - **Test**: `(regex-match "\\d+" "abc123")` → `"123"`

- [ ] **0.24: Regex Groups** (2 days)
  - Return capture groups from match
  - **API**: `(regex-groups match)` → list of captured strings
  - **PCRE2 API**: `pcre2_substring_get_bynumber`
  - **Test**: `(regex-match "(\\w+)@(\\w+)" "user@host")` → groups `["user", "host"]`

- [ ] **0.25: Regex Replacement** (2-3 days)
  - Implement `(regex-replace pattern string replacement)`
  - Support backreferences: `$1`, `$2`, etc.
  - **PCRE2 API**: `pcre2_substitute`
  - **Test**: `(regex-replace "\\d+" "abc123" "X")` → `"abcX"`

- [ ] **0.26: Regex Tests** (1 day)
  - File: `test/test_regex.valk`
  - Test: Email validation pattern
  - Test: Capture groups
  - Test: Unicode in regex
  - Test: Invalid patterns return error
  - **Run**: Add to `make test`

---

## Feature 5: Module System (M - 1-2 weeks)

**Unlocks**: Code organization, namespaces, imports

### Tasks

- [ ] **0.27: Module Design** (2 days)
  - Design module syntax: `(module math ...)` or `(defmodule math ...)`
  - Design import syntax: `(import math)`, `(import (math :only [sqrt]))`, `(import (math :as m))`
  - Design export lists: What's public vs private?
  - **Research**: Check Common Lisp packages, Racket modules, Scheme R6RS
  - **Document**: Write spec before implementing
  - **Test**: Create design doc with examples

- [ ] **0.28: Module Registry** (2 days)
  - File: `src/modules.h`, `src/modules.c`
  - Create global module registry (hash table: name → module)
  - Define `valk_module_t` structure:
    ```c
    typedef struct {
      char* name;
      valk_lenv_t* env;       // Module's private environment
      valk_lval_t* exports;    // List of exported symbols
    } valk_module_t;
    ```
  - **Memory**: Modules live forever (or GC-managed with roots)
  - **Test**: Register module, look up by name

- [ ] **0.29: Module Definition** (2-3 days)
  - File: `src/parser.c` (builtins)
  - Implement `(module name body...)` special form
  - Create new environment for module
  - Evaluate body in module env
  - Register module in global registry
  - **Example**:
    ```lisp
    (module math
      (fun square (x) (* x x))
      (fun cube (x) (* x x x))
      (export square cube))
    ```
  - **Test**: Define module, verify private env created

- [ ] **0.30: Module Import** (3-4 days)
  - Implement `(import module-name)` - import all exports
  - Implement `(import (module :only [sym1 sym2]))` - selective import
  - Implement `(import (module :as prefix))` - prefixed import
  - Copy exported symbols to current environment
  - **Namespace collision**: Error if symbol already defined?
  - **Test**: Import math module, call `square`

- [ ] **0.31: Module Export** (1-2 days)
  - Implement `(export sym1 sym2 ...)` within module
  - Only exported symbols available via `import`
  - **Default**: Nothing exported unless specified
  - **Test**: Import module with exports, verify private symbols hidden

- [ ] **0.32: File-Based Modules** (2-3 days)
  - Implement `(import "path/to/file.valk")`
  - Load file, wrap in implicit module
  - Module name = filename
  - **Search path**: Check relative path, then `VALK_PATH` env var
  - **Caching**: Load each file only once
  - **Test**: Split code across files, import successfully

- [ ] **0.33: Module Tests** (1-2 days)
  - File: `test/test_modules.valk`
  - Test: Define module with exports
  - Test: Import and use exported functions
  - Test: Private symbols are hidden
  - Test: Namespace collisions handled
  - Test: File-based imports
  - **Run**: Add to `make test`

---

## Progress Tracking

### Velocity
- **Week 1**: ___ tasks completed
- **Week 2**: ___ tasks completed
- ...

### Current Status
- **Feature**: ___
- **Task**: ___
- **Blocker**: ___

### Notes
- Session notes here

---

## Resources

### Unicode
- UTF-8 Everywhere: http://utf8everywhere.org/
- utf8proc: https://julialang.org/utf8proc/
- ICU (International Components for Unicode): https://icu.unicode.org/

### Regex
- PCRE2: https://www.pcre.org/
- RE2: https://github.com/google/re2

### BigNum
- GMP: https://gmplib.org/
- LibTomMath: https://www.libtom.net/LibTomMath/

### Modules
- Common Lisp Packages: http://www.lispworks.com/documentation/HyperSpec/Body/11_.htm
- Racket Modules: https://docs.racket-lang.org/guide/module-basics.html
