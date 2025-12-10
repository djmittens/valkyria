# Valk Line-Based Coverage Implementation Plan

## Executive Summary

This document outlines a plan to add **line-based code coverage** for `.valk` files in the Valkyria interpreter. The current coverage system only tracks which files were executed, not which specific lines. This enhancement will provide granular coverage data compatible with standard LCOV tooling.

### Zero Overhead Design (Key Requirement)

**Normal builds have ZERO runtime overhead.** This is achieved through:

| Technique | How It Works |
|-----------|--------------|
| **Compile-time elimination** | All coverage code wrapped in `#ifdef VALK_COVERAGE` |
| **Macro expansion to nothing** | `VALK_COVERAGE_RECORD_LVAL(x)` → `((void)0)` |
| **No struct changes** | Source location fields don't exist in normal builds |
| **No runtime checks** | No `if (coverage_enabled)` in hot paths |
| **Separate build target** | `make build` vs `make build-coverage` |

```c
// In normal builds, this line:
VALK_COVERAGE_RECORD_LVAL(lval);

// Expands to:
((void)0);

// Which the compiler eliminates entirely - zero instructions generated
```

## Current State Analysis

### Existing Coverage Infrastructure

**File:** `src/coverage.c`, `src/coverage.h`

| Feature | Current Implementation |
|---------|------------------------|
| Granularity | File-level only (`filename → eval_count`) |
| Data Structure | Hash table with 512 buckets, chained collision |
| Output Formats | Text (`file:count`) and LCOV (faked single line per file) |
| Activation | `VALK_COVERAGE=1` environment variable |
| Thread Safety | pthread mutex for all operations |
| Integration Point | `valk_parse_file()` calls `valk_coverage_record_file()` |

**Key Limitation:** The LCOV output in `valk_coverage_report_lcov()` currently fakes line data:
```c
fprintf(f, "DA:1,%zu\n", files[i]->eval_count);  // Always reports line 1
```

### Parser & AST Analysis

**Key Finding:** The `valk_lval_t` struct does **NOT** store source location information.

Current parsing flow:
1. `valk_parse_file()` reads file content into string
2. `valk_lval_read()` parses expressions using byte offset (`int *i`)
3. Parsed `valk_lval_t` values have no line/column tracking
4. `valk_lval_eval()` evaluates expressions without source context

### Evaluation Flow

```
valk_lval_eval(env, lval)
  ├── Self-evaluating (NUM, STR, FUN, ERR, NIL, QEXPR) → return as-is
  ├── SYM → valk_lenv_get(env, lval)
  └── CONS (S-expression) → function application
       ├── Evaluate function position
       ├── Evaluate arguments
       └── valk_lval_eval_call(env, func, args)
```

---

## Implementation Plan

### Design Principle: Zero Overhead When Disabled

**Critical Requirement:** Coverage tracking must have **absolutely zero runtime overhead** when not in coverage mode. This is achieved through:

1. **Compile-time elimination:** All coverage code is `#ifdef`'d out in normal builds
2. **Separate coverage build:** Use `-DVALK_COVERAGE=1` CMake flag for coverage builds
3. **No struct bloat:** Source location fields only exist in coverage builds
4. **No function calls:** Coverage recording macros expand to nothing in normal builds

This approach ensures production builds have identical performance to today's code.

---

### Phase 1: Source Location Tracking in AST (Coverage Builds Only)

**Goal:** Store line numbers in parsed `valk_lval_t` values, but ONLY in coverage-enabled builds.

#### 1.1 Extend `valk_lval_t` Structure (Conditional)

```c
// In parser.h, add to valk_lval_t struct:
struct valk_lval_t {
  uint64_t flags;
  void *origin_allocator;
  struct valk_lval_t *gc_next;
  
#ifdef VALK_COVERAGE
  // Source location info - ONLY present in coverage builds (8 bytes)
  uint16_t file_id;   // Index into file table (max 65535 files)
  uint16_t line;      // Line number (max 65535 lines per file)
  uint16_t column;    // Column number (optional, for future use)
  uint16_t _reserved; // Padding for alignment
#endif
  
  union { ... };
};
```

**Key Insight:** By using `#ifdef VALK_COVERAGE`, normal builds have:
- No extra memory per lval (0 bytes overhead)
- Identical struct layout to current code
- No ABI changes for non-coverage builds

#### 1.2 Create File ID Registry (Coverage Builds Only)

```c
// New: src/source_loc.h / src/source_loc.c
// ENTIRE FILE is #ifdef VALK_COVERAGE guarded

#ifdef VALK_COVERAGE

#define MAX_SOURCE_FILES 4096

typedef struct {
  char *filenames[MAX_SOURCE_FILES];
  uint16_t count;
  pthread_mutex_t lock;
} valk_source_registry_t;

uint16_t valk_source_register_file(const char *filename);
const char *valk_source_get_filename(uint16_t file_id);

#endif // VALK_COVERAGE
```

#### 1.3 Modify Parser to Track Line Numbers (Coverage Builds Only)

All parser modifications are wrapped in `#ifdef VALK_COVERAGE`:

```c
#ifdef VALK_COVERAGE
// Add line tracking state to parser - ONLY in coverage builds
typedef struct {
  const char *source;
  int pos;
  int line;       // Current line number (1-based)
  int line_start; // Byte offset of current line start
  uint16_t file_id;
} valk_parse_ctx_t;

// Helper to update line tracking when consuming whitespace
static void parse_skip_whitespace(valk_parse_ctx_t *ctx) {
  while (strchr(" ;\t\v\r\n", ctx->source[ctx->pos]) && ctx->source[ctx->pos] != '\0') {
    if (ctx->source[ctx->pos] == '\n') {
      ctx->line++;
      ctx->line_start = ctx->pos + 1;
    }
    if (ctx->source[ctx->pos] == ';') {
      while (ctx->source[ctx->pos] != '\n' && ctx->source[ctx->pos] != '\0') {
        ctx->pos++;
      }
    } else {
      ctx->pos++;
    }
  }
}

valk_lval_t* valk_lval_read_ctx(valk_parse_ctx_t *ctx);
#endif // VALK_COVERAGE
```

#### 1.4 Macro-Based Source Location Assignment

```c
// In parser.h or common.h

#ifdef VALK_COVERAGE
  #define LVAL_SET_SOURCE_LOC(lval, fid, ln, col) do { \
    (lval)->file_id = (fid); \
    (lval)->line = (ln); \
    (lval)->column = (col); \
  } while(0)
#else
  #define LVAL_SET_SOURCE_LOC(lval, fid, ln, col) ((void)0)
#endif
```

After creating each `valk_lval_t`:
```c
valk_lval_t *result = valk_lval_num(x);
LVAL_SET_SOURCE_LOC(result, ctx->file_id, ctx->line, ctx->pos - ctx->line_start + 1);
return result;
```

In non-coverage builds, `LVAL_SET_SOURCE_LOC` expands to nothing.

---

### Phase 2: Line Coverage Data Structures (Coverage Builds Only)

**Goal:** Efficient storage for line execution counts. All code in this phase is `#ifdef VALK_COVERAGE` guarded.

#### 2.1 Per-File Line Coverage Bitmap

```c
// In coverage.h - ALL coverage data structures are conditional

#ifdef VALK_COVERAGE

typedef struct valk_file_coverage_t {
  const char *filename;
  uint16_t file_id;
  
  // Line coverage data
  uint32_t *line_counts;  // Array: line_counts[line] = execution count
  size_t line_capacity;   // Allocated size
  size_t total_lines;     // Lines in source file (for percentage calc)
  size_t lines_hit;       // Number of distinct lines executed
  
  // For hash table chaining
  struct valk_file_coverage_t *next;
} valk_file_coverage_t;

typedef struct {
  valk_file_coverage_t *buckets[COVERAGE_HASH_SIZE];
  size_t total_files;
  pthread_mutex_t lock;
} valk_line_coverage_t;

#endif // VALK_COVERAGE
```

#### 2.2 Coverage Recording API (Compile-Time Eliminated)

```c
// In coverage.h

#ifdef VALK_COVERAGE
  // Real implementations - only exist in coverage builds
  void valk_coverage_record_line_impl(uint16_t file_id, uint16_t line);
  valk_file_coverage_t *valk_coverage_get_file(uint16_t file_id);
  
  #define VALK_COVERAGE_RECORD_LINE(fid, line) valk_coverage_record_line_impl(fid, line)
#else
  // Compile to nothing in normal builds - ZERO OVERHEAD
  #define VALK_COVERAGE_RECORD_LINE(fid, line) ((void)0)
#endif
```

#### 2.3 Implementation (Coverage Builds Only)

```c
// In coverage.c - wrapped in #ifdef VALK_COVERAGE

#ifdef VALK_COVERAGE

void valk_coverage_record_line_impl(uint16_t file_id, uint16_t line) {
  // No runtime check needed - this function only exists in coverage builds
  
  pthread_mutex_lock(&g_line_coverage.lock);
  
  valk_file_coverage_t *fc = valk_coverage_get_file(file_id);
  if (fc == NULL) {
    pthread_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  // Grow array if needed
  if (line >= fc->line_capacity) {
    size_t new_cap = (line + 1) * 2;
    fc->line_counts = realloc(fc->line_counts, new_cap * sizeof(uint32_t));
    memset(fc->line_counts + fc->line_capacity, 0, 
           (new_cap - fc->line_capacity) * sizeof(uint32_t));
    fc->line_capacity = new_cap;
  }
  
  if (fc->line_counts[line] == 0) {
    fc->lines_hit++;
  }
  fc->line_counts[line]++;
  
  pthread_mutex_unlock(&g_line_coverage.lock);
}

#endif // VALK_COVERAGE
```

---

### Phase 3: Instrument Evaluation (Zero Overhead in Normal Builds)

**Goal:** Record line hits during expression evaluation, with ZERO overhead in non-coverage builds.

#### 3.1 Instrument `valk_lval_eval()` Using Macros

```c
valk_lval_t* valk_lval_eval(valk_lenv_t* env, valk_lval_t* lval) {
  atomic_fetch_add(&g_eval_metrics.evals_total, 1);
  
  // Coverage recording - compiles to NOTHING in normal builds
  VALK_COVERAGE_RECORD_LVAL(lval);
  
  // ... rest of existing evaluation logic (unchanged)
}
```

#### 3.2 Coverage Macro Definition

```c
// In coverage.h

#ifdef VALK_COVERAGE
  #define VALK_COVERAGE_RECORD_LVAL(lval) do { \
    if ((lval) != NULL && (lval)->line > 0) { \
      valk_coverage_record_line_impl((lval)->file_id, (lval)->line); \
    } \
  } while(0)
#else
  // ZERO OVERHEAD: Expands to nothing, compiler eliminates entirely
  #define VALK_COVERAGE_RECORD_LVAL(lval) ((void)0)
#endif
```

#### 3.3 Why This Is Zero Overhead

In non-coverage builds (`-DVALK_COVERAGE` not defined):

1. **`VALK_COVERAGE_RECORD_LVAL(lval)`** expands to `((void)0)` - a no-op
2. **No function call** - `valk_coverage_record_line_impl` doesn't exist
3. **No struct access** - `lval->file_id` and `lval->line` fields don't exist
4. **No branch** - no runtime check for coverage enabled
5. **Compiler optimization** - `((void)0)` is completely eliminated

The generated assembly for `valk_lval_eval()` is **identical** to current code.

#### 3.4 Selective Instrumentation (Optional Enhancement)

For even more targeted coverage, only record at statement boundaries:

```c
#ifdef VALK_COVERAGE
  #define VALK_COVERAGE_RECORD_STMT(lval) do { \
    if ((lval) != NULL && LVAL_TYPE(lval) == LVAL_CONS && (lval)->line > 0) { \
      valk_coverage_record_line_impl((lval)->file_id, (lval)->line); \
    } \
  } while(0)
#else
  #define VALK_COVERAGE_RECORD_STMT(lval) ((void)0)
#endif
```

---

### Phase 4: LCOV Report Generation (Coverage Builds Only)

**Goal:** Generate proper LCOV format with real line data. This code only exists in coverage builds.

#### 4.1 Update `valk_coverage_report_lcov()`

```c
#ifdef VALK_COVERAGE

void valk_coverage_report_lcov(const char *output_file) {
  pthread_mutex_lock(&g_line_coverage.lock);
  
  FILE *f = fopen(output_file, "w");
  if (!f) {
    pthread_mutex_unlock(&g_line_coverage.lock);
    return;
  }
  
  fprintf(f, "TN:\n");  // Test name (empty)
  
  for (int i = 0; i < COVERAGE_HASH_SIZE; i++) {
    valk_file_coverage_t *fc = g_line_coverage.buckets[i];
    while (fc != NULL) {
      fprintf(f, "SF:%s\n", fc->filename);
      
      // Count functions (approximate: count top-level definitions)
      // For now, report 0 functions since we don't track them
      fprintf(f, "FNF:0\n");
      fprintf(f, "FNH:0\n");
      
      // Line coverage data
      size_t lines_found = 0;
      size_t lines_hit = 0;
      
      for (size_t line = 1; line < fc->line_capacity; line++) {
        if (fc->line_counts[line] > 0) {
          fprintf(f, "DA:%zu,%u\n", line, fc->line_counts[line]);
          lines_hit++;
        }
        // Note: We only output lines that were hit
        // For full coverage, we'd need to know all executable lines
      }
      
      // We need total executable lines for accurate percentage
      // For now, use lines_hit as approximation (100% of observed lines)
      fprintf(f, "LF:%zu\n", fc->total_lines > 0 ? fc->total_lines : lines_hit);
      fprintf(f, "LH:%zu\n", lines_hit);
      
      fprintf(f, "end_of_record\n");
      
      fc = fc->next;
    }
  }
  
  fclose(f);
  pthread_mutex_unlock(&g_line_coverage.lock);
}

#endif // VALK_COVERAGE
```

#### 4.2 Determining Executable Lines

To calculate accurate coverage percentage, we need to know which lines are "executable" (contain code vs. comments/blanks).

**Option A: Parse-time tracking**
```c
#ifdef VALK_COVERAGE
// During parsing, record which lines have expressions
void valk_coverage_mark_executable(uint16_t file_id, uint16_t line);
#endif
```

**Option B: Post-hoc source analysis**
```c
#ifdef VALK_COVERAGE
// After test run, scan source files to count non-blank, non-comment lines
size_t valk_coverage_count_source_lines(const char *filename);
#endif
```

**Recommendation:** Option A is more accurate; implement during Phase 1.

---

### Phase 5: Testing & Integration

#### 5.1 New Test File: `test/test_coverage.c`

```c
#include "coverage.h"
#include "testing.h"

void test_coverage_line_recording(void) {
  valk_coverage_init();
  
  // Simulate parsing a file
  uint16_t file_id = valk_source_register_file("test.valk");
  
  // Record some line hits
  valk_coverage_record_line(file_id, 1);
  valk_coverage_record_line(file_id, 3);
  valk_coverage_record_line(file_id, 3);
  valk_coverage_record_line(file_id, 5);
  
  // Verify counts
  valk_file_coverage_t *fc = valk_coverage_get_file(file_id);
  ASSERT_EQ(fc->line_counts[1], 1);
  ASSERT_EQ(fc->line_counts[3], 2);
  ASSERT_EQ(fc->line_counts[5], 1);
  ASSERT_EQ(fc->lines_hit, 3);
  
  valk_coverage_reset();
}
```

#### 5.2 Integration Test: `test/test_line_coverage.valk`

```lisp
; Test that coverage correctly tracks line execution

(load "src/prelude.valk")
(load "src/modules/test.valk")

(test/suite "Line Coverage")

; This test verifies coverage tracking works
; by checking that coverage is being recorded
(test/define "basic-line-tracking"
  {do
    ; Each of these lines should be recorded
    (= {a} 1)
    (= {b} 2)
    (= {c} (+ a b))
    (test/assert-eq 3 c "simple addition")
  })

; Conditional branches
(test/define "branch-coverage"
  {do
    (fun {maybe-double x}
      {if (> x 10)
        {* x 2}
        {x}})
    (test/assert-eq 5 (maybe-double 5) "false branch")
    (test/assert-eq 40 (maybe-double 20) "true branch")
  })

(test/run)
```

#### 5.3 Update Makefile

Add to `run_tests_c`:
```makefile
if [ "$(VALK_METRICS)" = "1" ] && [ -f $(1)/test_coverage ]; then $(1)/test_coverage; fi
```

Add coverage validation target:
```makefile
.PHONY: coverage-validate
coverage-validate: coverage
	@echo "=== Validating Valk line coverage ==="
	@if grep -q "DA:[0-9]*,[0-9]*" build-coverage/coverage-valk.info; then \
		echo "Line coverage data present"; \
		grep "^LH:" build-coverage/coverage-valk.info | head -5; \
	else \
		echo "ERROR: No line coverage data found"; \
		exit 1; \
	fi
```

---

## Performance Considerations

### Zero Overhead Guarantee

**In normal (non-coverage) builds, there is ZERO runtime overhead:**

| Aspect | Normal Build | Coverage Build |
|--------|--------------|----------------|
| Struct size | Original size | +8 bytes/lval |
| Eval overhead | 0 cycles | ~50ns per expression |
| Memory | 0 extra | Coverage data structures |
| Binary size | Original | +~2KB code |

### How Zero Overhead Is Achieved

1. **Compile-time Elimination**
   - All coverage code is inside `#ifdef VALK_COVERAGE` blocks
   - Macros expand to `((void)0)` which compilers optimize away completely
   - No dead code, no unreachable branches

2. **No Runtime Checks**
   - No `if (coverage_enabled)` in hot paths
   - The `g_coverage_enabled` variable doesn't exist in normal builds
   - Function calls are eliminated, not just skipped

3. **No Struct Bloat**
   - `file_id`, `line`, `column` fields don't exist in normal builds
   - `sizeof(valk_lval_t)` is identical to current code
   - No padding changes

4. **Verification**
   ```bash
   # Compare generated assembly - should be identical
   make build
   objdump -d build/valk > normal.asm
   
   make build-coverage  
   objdump -d build-coverage/valk > coverage.asm
   
   # valk_lval_eval should differ (coverage instrumentation)
   # Other hot functions should be identical
   ```

### Coverage Build Optimizations

For coverage builds (where overhead is acceptable):

1. **Per-thread Buffers** (future optimization)
   - Each thread accumulates hits in local buffer
   - Flush to global on buffer full or at checkpoint
   - Reduces lock contention

2. **Lock-free Recording** (future optimization)
   - Use atomic operations for line_counts array
   - `atomic_fetch_add(&fc->line_counts[line], 1)`
   - Eliminates mutex entirely

---

## Build System Integration

### CMake Configuration

```cmake
# In CMakeLists.txt

option(VALK_COVERAGE "Enable Valk line coverage instrumentation" OFF)

if(VALK_COVERAGE)
  add_compile_definitions(VALK_COVERAGE)
  message(STATUS "Valk line coverage: ENABLED")
else()
  message(STATUS "Valk line coverage: DISABLED (zero overhead)")
endif()
```

### Makefile Integration

```makefile
# Coverage build uses -DVALK_COVERAGE=1
.PHONY: build-coverage
build-coverage: build-coverage/.cmake
	$(call do_build,build-coverage)

cmake-coverage build-coverage/.cmake: CMakeLists.txt
	$(CMAKE_BASE) -DCOVERAGE=1 -DVALK_COVERAGE=1 -DASAN=0 -S . -B build-coverage
```

### Build Variants Summary

| Build | Command | VALK_COVERAGE | Overhead |
|-------|---------|---------------|----------|
| Normal | `make build` | OFF | Zero |
| ASAN | `make build-asan` | OFF | Zero (coverage) |
| Coverage | `make build-coverage` | ON | ~5% (acceptable) |

---

## Migration Plan

### Backward Compatibility

- Keep `valk_coverage_record_file()` working for file-level tracking
- New line coverage is additive, doesn't break existing behavior
- Runtime environment variable `VALK_COVERAGE=1` still required to activate
- Compile flag `VALK_COVERAGE` controls whether instrumentation exists

### Two-Level Activation

1. **Compile-time:** `-DVALK_COVERAGE` - includes instrumentation code
2. **Runtime:** `VALK_COVERAGE=1` env var - activates data collection

This allows coverage-instrumented builds to run without collecting data (useful for debugging the coverage system itself).

### Rollout Phases

1. **Phase 1-2:** Parser changes + data structures (no user-visible changes)
2. **Phase 3:** Instrumentation (coverage output changes)
3. **Phase 4:** LCOV generation (full line coverage reports)
4. **Phase 5:** Testing + CI integration

---

## File Changes Summary

| File | Changes | Conditional |
|------|---------|-------------|
| `src/parser.h` | Add source location fields to `valk_lval_t` | `#ifdef VALK_COVERAGE` |
| `src/parser.c` | Track line numbers during parsing, instrument eval | `#ifdef VALK_COVERAGE` |
| `src/coverage.h` | Add line coverage data structures and API macros | `#ifdef VALK_COVERAGE` |
| `src/coverage.c` | Implement line recording and LCOV generation | `#ifdef VALK_COVERAGE` |
| `src/source_loc.c` | **NEW:** File ID registry | Entire file conditional |
| `src/source_loc.h` | **NEW:** File ID registry header | Entire file conditional |
| `CMakeLists.txt` | Add `VALK_COVERAGE` option, new source files | Build system |
| `Makefile` | Add `-DVALK_COVERAGE=1` to coverage build | Build system |
| `test/test_coverage.c` | **NEW:** C unit tests for coverage | `#ifdef VALK_COVERAGE` |
| `test/test_line_coverage.valk` | **NEW:** Valk integration tests | N/A |

### Conditional Compilation Pattern

Every coverage-related code block follows this pattern:

```c
#ifdef VALK_COVERAGE
// Coverage-specific code here
// Only compiled when -DVALK_COVERAGE is set
#endif
```

This ensures:
- Normal builds have zero coverage code
- No performance impact from dead branches
- Clean separation of concerns

---

## Success Criteria

1. **Functional:** `make coverage` generates LCOV with real line data (`DA:line,count` entries)
2. **Accurate:** Coverage percentages reflect actual code execution
3. **Zero Overhead:** Normal builds have identical performance to current code
4. **Measurable:** Coverage builds have < 5% overhead (acceptable for testing)
5. **Compatible:** Works with existing `genhtml` and coverage tooling
6. **Tested:** Both C and Valk tests validate coverage tracking
7. **Verified:** Assembly comparison confirms zero overhead in normal builds

---

## Open Questions

1. **Column tracking:** Include column numbers for IDE integration? (Recommendation: Yes, store but don't require for MVP)

2. **Function coverage:** Track function definitions and calls? (Recommendation: Defer to future phase)

3. **Branch coverage:** Track which branch of `if` was taken? (Recommendation: Defer, requires more AST annotation)

4. **Macro expansion:** How to handle coverage for macro-generated code? (Recommendation: Track original source location, not expanded)

---

## Appendix: LCOV Format Reference

```
TN:<test name>
SF:<source file path>
FN:<line>,<function name>
FNDA:<call count>,<function name>
FNF:<functions found>
FNH:<functions hit>
DA:<line>,<execution count>
LF:<lines found>
LH:<lines hit>
BRF:<branches found>
BRH:<branches hit>
end_of_record
```

Example output:
```
TN:
SF:/home/user/valkyria/src/prelude.valk
FNF:0
FNH:0
DA:6,1
DA:12,3
DA:13,3
DA:14,3
DA:17,2
DA:21,1
LF:6
LH:6
end_of_record
```
