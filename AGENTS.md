# Repository Guidelines

## Project Structure & Module Organization
- `src/` — C23 runtime, GC, parser, REPL, plus `.valk` standard library modules (e.g., `prelude.valk`, async libs).
- `test/` — C test suites (`test_*.c`) and Valkyria tests (`test_*.valk`); `stress/` for long‑running cases.
- `docs/`, `examples/` — reference material and runnable examples.
- `vendor/` — third‑party deps (e.g., `editline`).
- `build/` — CMake/Ninja outputs (generated); do not commit.
- Top‑level: `CMakeLists.txt`, `Makefile`, `.clang-tidy`.

## Build, Test, and Development Commands
- `make build` — configure (CMake+Ninja) and compile into `build/`.
- `make test` — run C suites (binaries in `build/`) and Valkyria tests via `build/valk`.
- `make lint` — run clang‑tidy over `src/` and `test/`.
- `make cppcheck` — static analysis pass.
- `make clean` — remove `build/`.
- `make repl` — launch `build/valk` with `src/prelude.valk`.
- `make asan` — run selected tests with ASAN/LSAN enabled.
Notes: On macOS, Makefile enables extra flags; first build auto‑generates a self‑signed TLS cert in `build/`.

## Coding Style & Naming Conventions
- Language: C23 in `src/*.c`/`*.h`; Valkyria modules in `*.valk`.
- Naming: snake_case for files and identifiers; headers mirror C sources (e.g., `memory.c`/`memory.h`).
- Formatting: follow existing style; ensure `make lint` passes. Prefer small, focused functions and clear ownership in memory APIs.

## Testing Guidelines
- Add C tests under `test/` named `test_<area>.c`; add Valkyria tests as `test_<area>.valk`.
- Run all: `make test`. Run a single Valk test: `build/valk test/test_prelude.valk`.
- Keep tests fast; place long scenarios in `test/stress/`.

## Commit & Pull Request Guidelines
- Commits: concise, imperative subject (“Fix GC sweep order”); include brief rationale when non‑obvious.
- Link issues where relevant. Group unrelated changes into separate commits.
- PRs: include summary, motivation, testing notes, and any perf or memory impacts. Ensure `make build`, `make lint`, and `make test` pass locally; exclude `build/` outputs.

## Security & Configuration Tips
- Linux/macOS supported via CMake+Ninja. If vendor deps are missing, run `make configure` inside `vendor/editline` (autotools required). Avoid committing secrets; certificates generated in `build/` are for local testing only.

