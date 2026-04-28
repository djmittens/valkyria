# LSP User Acceptance Tests

Scenario-driven LSP tests that drive `valk-lsp` through real neovim
(`nvim --headless`). Catches UX issues that the C/Valk integration
tests miss: latency budgets, response correctness, stability under
typing load.

## Running

```sh
make uat                # all scenarios
make uat F=hover        # only scenarios matching `hover`
make test               # also runs UAT (skips silently if nvim missing)

# Direct:
test/lsp/uat/run.sh
test/lsp/uat/run.sh hover                 # filter by lua pattern
VALK_UAT_STRICT=1 test/lsp/uat/run.sh     # fail if nvim missing (CI use)
NVIM=/path/to/nvim test/lsp/uat/run.sh    # override nvim binary
VALK_LSP_BIN=/path/to/lsp test/lsp/uat/run.sh
```

The runner reuses **one nvim session** across all scenarios for speed
(~12s for 13 scenarios). Each scenario opens its own buffer (`bwipeout!`
+ `edit!`) so unsaved-edit state from a prior test cannot leak.

## Layout

```
test/lsp/uat/
├── run.sh                  # bash entry: spawn nvim, parse results, set exit
├── runner.lua              # nvim Lua: scenario discovery + dispatch
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
-- test/lsp/uat/scenarios/08_rename.lua
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

Each test emits one JSON line to `$VALK_UAT_RESULTS` (set by the
wrapper). The bash wrapper parses for `"status":"fail"` and sets the
exit code accordingly:

- `0` — all passed, or skipped (no nvim and `VALK_UAT_STRICT` unset)
- `1` — at least one scenario failed
- `2` — environment broken (no LSP binary, no results file produced)

## Why scenarios are not unit tests

Existing `test/lsp/test_lsp_*.c` and `*.valk` files exercise the LSP's
code paths — they prove "the function returns successfully" but not
"the function returns the right answer in <Xms when invoked the way
nvim does it". UAT plugs that gap by running everything through real
client-server JSON-RPC over real pipes with real client-side timing.

If a UAT fails but every other test passes, the bug is in the
**user-facing behavior** layer — exactly where smoke tests are blind.
