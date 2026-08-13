# lsp

The Valkyria language server, written in Valk. Provides diagnostics,
hover, completion, go-to-definition, references, inlay hints and semantic
tokens for `.valk` workspaces.

## Layout

| Path | Purpose |
|---|---|
| `lsp.valk` | Dispatch + main loop |
| `io.valk` | JSON-RPC framing, capabilities |
| `workspace.valk`, `scan.valk` | Workspace state, file scanning, symdb sync (`.valk/symdb.sqlite`) |
| `analysis.valk`, `refs.valk`, `nav.valk`, `features.valk` | Language features |
| `hints.valk`, `hints-fields.valk` | Inlay hints |
| `main.valk` | Interpreted entry point (`build/valk lsp/main.valk`) |
| `build-main.valk` | AOT entry point (compiled to `build/valk-lsp`) |
| `test/` | Valk unit tests (`test_lsp_*.valk`) and C integration/profiling tests |
| `test/uat/` | User-acceptance tests: real Neovim driving `build/valk-lsp` (see `test/uat/README.md`) |

Depends on the `symdb/` project for indexing and validation.

## Build

```bash
make lsp            # AOT-compile to build/valk-lsp (staleness-checked)
make lsp FORCE=1    # rebuild unconditionally
```

## Test

```bash
make test F=lsp     # unit + integration suites
make uat            # UAT scenarios through headless nvim
make uat F=hover    # single scenario
```

## Editor setup

Point your editor's LSP client at `build/valk-lsp` (or
`build/valk lsp/main.valk` for interpreted development). Tree-sitter grammar
and a VS Code extension live in `editors/`.
