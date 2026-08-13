# LSP User Acceptance Tests

Scenario-driven LSP tests that drive `valk-lsp` through real neovim
(`nvim --headless`). Catches UX issues that the C/Valk integration
tests miss: latency budgets, response correctness, stability under
typing load.

## Running

UAT has no runner of its own. `testing/run-tests.valk` discovers
`scenarios/*.lua` the same way it discovers C binaries and `test_*.valk`
files, so these share one filter, one JUnit tree and one summary with every
other suite.

```sh
make test                   # C + Valk + UAT, one report
make uat                    # same runner, restricted to --only uat
make uat F=hover            # suites whose name contains `hover` (substring)
make test F=hover           # identical filter semantics across all kinds
```

### Execution model

One scenario **file** is one suite, and each runs in its own nvim process
with its own valk-lsp and its own workspace, so suites cannot interfere.

Suites are scheduled by the runner's `aio/pmap` alongside everything else,
except scenarios marked `_latency = true`, which are tagged `:exclusive` and
run alone after the parallel batch finishes. A p95 measured while the rest of
the suite saturates the box describes the scheduler, not the editor.

Within a process, tests run in sorted order. `pairs()` order over a
string-keyed table varies between runs, and that non-determinism used to turn
any cross-test state dependency into a flaky failure.

Splitting is per scenario **file**, never per test: tests in a file may share
fixtures and a `_setup`.

If `nvim` is not on `PATH`, or `build/valk-lsp` has not been built, UAT
discovery emits a note and contributes zero suites. `VALK_UAT_STRICT=1` turns
that skip into an error (CI use).

## Waiting: use conditions, not sleeps

`vim.wait(N)` as a synchronization device is banned in scenarios. A fixed sleep
must be sized for the worst case, so it is simultaneously slower than necessary
and too short under load — sluggish and flaky from the same line. Removing them
took the suite from 62s to 15s and uncovered two real server bugs that the
sleeps had been masking.

| Need | Use |
|---|---|
| "the server has processed my edit" | `lib.sync(bufnr)` — round trip; notifications and requests share one FIFO queue |
| "the symbol index caught up" | `lib.require_symbol_indexed` / `wait_for_symbol_gone` (same file) |
| a symbol from **another** file | `lib.require_workspace_symbol` — `documentSymbol` only reports the requested document |
| "the workspace scan finished" | `lib.wait_for_workspace_scan` — the server sends `$/progress` `kind="end"` |
| a specific diagnostic | `lib.wait_for_diagnostic_containing` |
| "there should be no errors" | `lib.settle_diagnostics` — waits for the publish the edit provoked, then assert on it |
| "the client went quiet" | `lib.wait_for_quiescence` |
| any other condition | `lib.wait_until` / `lib.require_until` |

Two things are **not** synchronization and are allowed to be a duration:
`lib.keystroke_gap()` (a workload parameter — a latency percentile is
meaningless without a defined input rate) and the poll interval inside
`wait_until`.

Never sleep "to let didChange flush": nvim's `Client:request` calls
`changetracking.flush()` before sending every request, so a queued didChange
always reaches the server ahead of your next request.

## Layout

```
lsp/test/uat/
├── runner.lua              # nvim Lua: workspace, dispatch, JSONL on stdout
├── lib.lua                 # helpers: open_fixture, request, assert_*, etc.
├── scenarios/
│   ├── 01_cold_start.lua   # latency: open → first response < 2s
│   ├── 02_hover.lua        # correctness: hover content
│   ├── 03_completion.lua   # correctness: completion list contains user syms
│   ├── 04_goto_def.lua     # correctness: goto-def jumps to (fun ...)
│   ├── 05_diagnostics.lua  # correctness: bad code flagged, good code silent
│   ├── 06_rapid_typing.lua # stability: tokens valid during 12-keystroke burst
│   └── 07_latency_budget.lua # latency: p95 hover under load
└── fixtures/
    ├── small.valk            # baseline: 3 user fns
    ├── diagnostics_bad.valk  # known-bad: (/ 1 0) + undefined fn
    ├── diagnostics_clean.valk
    └── typing_seed.valk      # rapid-typing scenario seed
```

## Adding a scenario

A scenario is a Lua module under `scenarios/` returning a table whose
function-valued keys are individual tests. Test names beginning with
`_` are reserved (the runner calls `_setup` if present).

```lua
-- lsp/test/uat/scenarios/08_rename.lua
return {
  rename_local_symbol_renames_only_in_scope = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    -- ... make request, assert ...
  end,
}
```

Helpers in `lib.lua`:

| Function | Purpose |
|---|---|
| `lib.open_fixture(rel)` | Open a fixture, fresh buffer, LSP attached |
| `lib.open_repo_file(rel)` | Same but for any repo file |
| `lib.wait_for_lsp(bufnr, ms)` | Block until client initialized |
| `lib.request(buf, method, params, ms)` | Sync request → result, elapsed_ms, err |
| `lib.tdp(uri, line, char)` | TextDocumentPositionParams shorthand |
| `lib.find_text(buf, needle)` | (line, col) of first match — column-robust |
| `lib.assert_eq / assert_lt / assert_truthy / assert_contains` | The usual |
| `lib.percentile(arr, p)` | Latency stats |

## Failure modes the suite catches

| Pain | Scenario |
|---|---|
| "First hover takes forever" | `cold_start::cold_start_to_first_hover_under_2s` |
| "Hover doesn't say anything useful" | `hover::hover_user_function_shows_signature` |
| "Completion shows nothing for my own functions" | `completion::completion_after_open_paren_has_user_fns` |
| "Goto-def jumps to the wrong line" | `goto_def::goto_def_local_function` |
| "Cross-file goto-def is broken" | `goto_def::goto_def_cross_file_stdlib` |
| "Errors don't show up" | `diagnostics::diagnostics_flag_known_bad_code` |
| "Errors show on working code" | `diagnostics::diagnostics_silent_on_clean_code` |
| "LSP locks up while I type" | `rapid_typing::rapid_typing_tokens_stay_valid` |
| "Tokens flicker / point at whitespace" | `rapid_typing` (token-fits-in-buffer assertion) |
| "Hover lags after a while" | `latency_budget::hover_p95_under_load` |

## Output

`runner.lua` writes one JSON line per test to **stdout**, in the same
`{"test","status","us","suite"}` schema `testing/c/testing.c` and
`testing/test.valk` emit. That is the whole integration: `run-tests.valk`
parses it with the same `parse-jsonl-tests` it uses for every other suite, and
writes JUnit into the run's `test-report/<timestamp>/` directory.

Human-readable progress goes to **stderr**, which `run-tests.valk` prints only
for suites that failed — including the grouped failure block at the end of the
scenario's output. Keep stdout free of anything but JSONL.

`runner.lua` exit codes (they become the suite's exit code):

- `0` — every test in the scenario passed
- `1` — at least one test failed
- `2` — environment broken (no `VALK_LSP_BIN`, unseedable workspace, no such
  scenario), or the parent runner died and the watchdog took us down

## Adding a latency scenario

Set `_latency = true` in the returned table if the scenario asserts a
wall-clock budget or a percentile. That moves it into the serial phase. Also
make sure the percentile has enough samples to mean something — at n=12, "p95"
is just the maximum, which is typically a cold-cache outlier rather than the
steady state you meant to measure.

## Why scenarios are not unit tests

Existing `lsp/test/test_lsp_*.c` and `*.valk` files exercise the LSP's
code paths — they prove "the function returns successfully" but not
"the function returns the right answer in <Xms when invoked the way
nvim does it". UAT plugs that gap by running everything through real
client-server JSON-RPC over real pipes with real client-side timing.

If a UAT fails but every other test passes, the bug is in the
**user-facing behavior** layer — exactly where smoke tests are blind.
