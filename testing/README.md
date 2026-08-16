# testing

The Valkyria test framework and unified test runner.

## Layout

| Path | Purpose |
|---|---|
| `c/testing.{c,h}` | C test harness: `VALK_TEST()`, assertions, fixtures, fork-based isolation, JSONL output (`VALK_TEST_JSON=1`) |
| `test.valk` | Valk test framework: `test/case`, `test/assert*`, async tests, timeouts, capture |
| `property.valk` | Property-based testing on top of `test.valk` |
| `run-tests.valk` | The unified runner: discovers C, Valk, example and UAT suites, runs them in parallel, emits JUnit XML |
| `docs/TESTING.md` | Full guide to running and writing tests |

## Usage

All test invocation goes through the root Makefile:

```bash
make test                 # everything
make test F=memory        # filter suites by substring
make test-c / test-valk   # one kind only
make test-c-asan          # sanitizer variants
make uat                  # LSP user-acceptance tests (needs nvim)
```

Direct invocation:

```bash
build/valk testing/run-tests.valk -- --build-dir build [--filter X] [--only c|valk|uat|example]
```

## Discovery

- **C suites**: executables named `test_*` in the build dir (each links `c/testing.c`)
- **Valk suites**: `runtime/test/<area>/test_*.valk` and `lsp/test/test_*.valk`
  (each loads `testing/test.valk`); `runtime/test/stress/` is opt-in
- **Examples**: `examples/*.valk`
- **UAT**: `lsp/test/uat/scenarios/*.lua`, driven through headless Neovim

The runner parses per-test JSONL from suite stdout, writes JUnit XML per suite
under `test-report/<timestamp>/`, and fails on silent-failure/empty suites.

## Runtime support

The Valk framework depends on the `test/capture-start` / `test/capture-stop`
builtins (`runtime/src/builtins_test.c`), which stay in the runtime.
