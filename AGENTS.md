# Repository Guidelines

## Project Structure & Module Organization
- `src/` — Core C23 sources (`parser.c`, `memory.c`, `concurrency.c`, `aio_uv.c`, `aio_ssl.c`, `vm.c`, `debug.c`).
- `test/` — Plain C tests compiled as separate binaries (`test_*.c`).
- `build/` — CMake/Ninja output; also stores a local self‑signed TLS cert (`server.crt`, `server.key`).
- `bin/`, `vendor/`, `docs/` — Helper scripts, third‑party code (e.g., nghttp2, editline), and documentation.

## Build, Test, and Development Commands
- `make build` — Configure (CMake + Ninja) and compile; generates TLS test certs in `build/`.
- `make test` — Run all test binaries (`test_std`, `test_memory`, `test_concurrency`, `test_networking`).
- `make repl` — Launch the REPL (`build/valk`) with `src/prelude.valk`.
- `make lint` — Run clang‑tidy over the tree using `build/compile_commands.json`.
- `make cppcheck` — Static analysis via cppcheck for `src/` and `test/`.
- `make clean` — Remove `build/`.
- `make configure` — Build/install `vendor/editline` locally if needed (autotools).
- `make asan` — Run selected tests with AddressSanitizer flags.

## Coding Style & Naming Conventions
- Language: C23 (`-std=c23`). Indentation: 2 spaces; no tabs.
- Naming: `snake_case` for functions and variables (e.g., `valk_c_err_format`), `UPPER_SNAKE` for macros, `*_t` for typedefs, `*_e` for enums.
- Headers: prefer local includes for project headers (`"..."`), system headers with `<...>`.
- Linting: adhere to `.clang-tidy`; fix diagnostics or justify with minimal, targeted `NOLINT`.

## Testing Guidelines
- Tests live in `test/` and build to separate binaries; keep filenames `test_<area>.c`.
- Add tests alongside changes; aim to cover error paths and concurrency cases.
- Run locally with `make test`; for focused runs, execute specific binaries in `build/`.

## Commit & Pull Request Guidelines
- Commits: short imperative subject (≤72 chars), optional scope (e.g., `parser:`), body explaining rationale/impact.
- PRs: clear description, link issues, list behavioral changes, include before/after notes or logs when relevant.
- Validation: run `make lint && make cppcheck && make test` before opening; include new/updated tests.

## Security & Configuration Tips
- TLS artifacts in `build/server.crt` and `build/server.key` are for local use only; never commit secrets.
- macOS builds use `HOMEBREW_CLANG=on` automatically; Linux uses system clang. Ensure `pkg-config`, OpenSSL, libuv, and editline are available.

