# runtime

The Valkyria interpreter/runtime: a Lisp implemented in C23 with a parallel
stop-the-world GC, libuv-based async I/O, HTTP/2 networking with TLS, and an
optional LLVM AOT/JIT backend.

## Layout

| Path | Contents |
|---|---|
| `src/` | Core: `parser.c`, `eval.c`, `lval.c`, `lenv.c`, `memory.c`, `gc*.c`, builtins |
| `src/aio/` | Async I/O: event loop, handles, combinators; `system/` lifecycle, `io/` ops layer |
| `src/aio/http2/` | HTTP/2 client/server/sessions, TLS, overload management, streaming |
| `src/llvm/`, `src/vir/` | Optional AOT/JIT backend (IR + LLVM codegen) |
| `vendor/` | Vendored deps: nghttp2, sqlite3, editline, backtrace |
| `test/<area>/` | Tests by area: `aio`, `gc`, `http`, `lang`, `metrics`, `parser`, `unit`; `stress/` long-running; `fixtures/`, `fakes/` |
| `docs/` | Runtime documentation (language, memory, GC, threading, async, HTTP, metrics) |
| `CMakeLists.txt` | The CMake project (library, `valk` binary, all C test executables, benchmarks) |

## Build

Builds are orchestrated from the repository root:

```bash
make build          # cmake -S runtime -B build (Ninja)
make build-asan     # ASAN variant into build-asan/
make build-tsan     # TSAN variant into build-tsan/
make build-coverage # gcov + Valk-coverage variant into build-coverage/
```

Or standalone:

```bash
cmake -G Ninja -S runtime -B build && cmake --build build
```

The binary is `build/valk`. It loads `stdlib/prelude.valk` at startup, resolved
relative to (in order): the loading file's directory, the cwd, each `VALK_PATH`
entry (colon-separated), `<exe_dir>/..`, and `<exe_dir>`.

## AOT builds (`valk --build`)

`valk --build src.valk -o out` compiles a script into a standalone binary:
the evaluated environment is serialized into an image, embedded via an
assembly `.incbin` section, and linked against `libvalkyria` together with
the **precompiled shim** `valk-shim.o` (built from `src/build_shim.c` at
runtime-build time, staged next to the library).

A relocated install needs only four things — no headers, no source tree:

```
bin/valk  bin/libvalkyria.dylib  bin/valk-shim.o  stdlib/
```

The deployment machine needs a C toolchain for assembling the image section
and linking. The compiler defaults to the one that built the runtime
(baked in as `VALK_CC`; override with `$CC`) so sanitizer/coverage runtimes
always match the instrumented library.

## Test

```bash
make test           # everything (C + Valk + LSP UAT), via testing/run-tests.valk
make test-c         # C suites only
make test-valk      # Valk suites only
make test F=gc      # filter by substring
```

C tests live in `test/<area>/test_*.c` and link the harness from
`../testing/c/testing.{c,h}`. Valk tests are `test/<area>/test_*.valk` and load
`testing/test.valk`.

## Docs

See [docs/](docs/) — start with [LANGUAGE.md](docs/LANGUAGE.md) and
[MEMORY_MANAGEMENT.md](docs/MEMORY_MANAGEMENT.md).
