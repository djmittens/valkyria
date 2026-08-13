# profile

Profiling tools, written in Valk. External profilers (`perf`, `nvim`) are
driven via `exec`; all parsing, folding, and rendering is Valk.

## Layout

| File | Purpose |
|---|---|
| `flamegraph.valk` | CPU flame graphs: records with `perf`, folds stacks and renders the SVG itself — no FlameGraph/perl dependency |
| `flame.valk` | The `flame/` module: `perf script` output folding, call-tree building, SVG rendering (integer-millipixel geometry, stable per-function colors) |
| `lsp-profile.valk` | Profiles the `valk-lsp` load path through real headless neovim via `build/lsp_proxy`; prints the full message timeline and per-phase latencies |

## Usage

```sh
# Flame graph of any command (default: prelude test workload)
build/valk profile/flamegraph.valk -- out.svg build/valk check/valk-check.valk -- stdlib

# LSP startup/latency breakdown (needs build/lsp_proxy and build/valk-lsp)
build/valk profile/lsp-profile.valk
```

`lsp-profile.valk` env overrides: `VALK_LSP_FIXTURE`, `VALK_LSP_WAIT_MS`,
`VALK_LSP_PROXY_LOG`.

## Related make targets

Crash analysis lives in the Makefile, not here: `make cores` (list),
`make debug-core` (interactive gdb), `make core-report` (one-shot batch
report: crash frame, full backtrace, registers, all threads).
