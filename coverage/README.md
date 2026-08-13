# coverage

Aggregated coverage tooling for both sides of the codebase: C (gcov/llvm-cov)
and Valk (the runtime's own line/expression instrumentation).

## Layout

| File | Purpose |
|---|---|
| `coverage_common.valk` | Shared LCOV/gcov parsers, file filters, stats |
| `coverage-report.valk` | HTML + Cobertura XML report over C and Valk data |
| `check-coverage.valk` | CI gate: 90% line / 85% branch (C), 90% expr (Valk), with documented `KNOWN_BLOCKED` exceptions |
| `find-uncovered-branches.valk` | Lists uncovered branches for one file from `coverage-report/coverage.xml` |
| `docs/COVERAGE_REQUIREMENTS.md` | Coverage tiers and rationale |

## Usage

```bash
make coverage         # build-coverage + run tests + generate report
make coverage-check   # enforce the gate
open coverage-report/latest/index.html

# Find what's left in one file:
build/valk coverage/find-uncovered-branches.valk -- runtime/src/gc.c
```

## How it works

- The `build-coverage/` build compiles C with gcov flags (`COVERAGE=1`) and
  enables Valk instrumentation (`VALK_COVERAGE=1` — note: this widens
  `valk_lval_t`, so coverage builds are ABI-incompatible with regular builds).
- Valk coverage is written by the runtime to `build-coverage/coverage-valk.txt`
  (override with `VALK_COVERAGE_OUTPUT`).
- Gated sets: C files under `runtime/src/` (vendor excluded); Valk files in
  `stdlib/`, `symdb/`, `testing/{test,property}.valk` and `quality/quality.valk`.
