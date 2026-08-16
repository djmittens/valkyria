# repl

The `valk` CLI entry point: process bootstrap, script mode, and the
interactive REPL.

## Layout

| File | Purpose |
|---|---|
| `main.c` | `main()`: system/heap/env bootstrap, prelude + `stdlib/aio/handles.valk` load, CLI flags (`--build`, `--quality-snapshot`, `--repl`), script mode, the editline read-eval-print loop, SIGUSR1 memory stats |

## Build

Compiled into the `valk` executable by `runtime/CMakeLists.txt` (the runtime
provides everything as the `valkyria` static library; this project is the
entry-point glue that links it, editline, and optionally the LLVM backend).

```sh
make build   # produces build/valk
build/valk               # interactive REPL
build/valk script.valk   # script mode
```
