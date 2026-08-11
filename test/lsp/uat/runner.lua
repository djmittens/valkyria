-- UAT scenario runner. One nvim process runs ONE scenario file:
--
--     nvim --headless -l <abs>/test/lsp/uat/runner.lua
--
-- It is not invoked by hand. scripts/run-tests.valk discovers
-- scenarios/*.lua and schedules each as a suite (kind "uat") alongside the
-- C and Valk suites, so UAT shares one discovery pass, one filter, one
-- JUnit tree and one summary with everything else. There is no separate
-- UAT orchestrator: parallelism comes from the runner's aio/pmap, and
-- latency scenarios are marked exclusive so they run alone (see
-- discover-uat-tests).
--
-- Contract with scripts/run-tests.valk (run-one-suite / parse-jsonl-tests):
--   stdout    one JSON object per line, {"test","status","us","suite"} —
--             the same schema test/testing.c and stdlib/test/test.valk emit
--   stderr    human-readable progress; surfaced only for failing suites
--   exit      0 iff every test passed
--
-- Env:
--   VALK_LSP_BIN     (required) server binary under test
--   VALK_UAT_SCENARIO  scenario file stem, e.g. "02_hover"; empty runs all
--
-- Failure semantics: a scenario signals failure with error(msg); the runner
-- catches it, records the test as failed, and continues with the next one.
-- Buffer state from a failing test is left as-is — tests open their own
-- fixtures via lib.open_fixture.

local script_dir = debug.getinfo(1, "S").source:sub(2):match("(.*/)")
if not script_dir or script_dir:sub(1, 1) ~= "/" then
  io.stderr:write("UAT: runner.lua must be invoked by absolute path\n")
  os.exit(2)
end
package.path = script_dir .. "?.lua;" .. package.path

local server_bin = vim.env.VALK_LSP_BIN
if not server_bin or server_bin == "" then
  io.stderr:write("UAT: VALK_LSP_BIN not set\n")
  os.exit(2)
end
if vim.fn.executable(server_bin) ~= 1 then
  io.stderr:write(("UAT: missing LSP binary at %s\n"):format(server_bin))
  os.exit(2)
end

local scenario_sel = vim.env.VALK_UAT_SCENARIO or ""

-- ---------------------------------------------------------------------------
-- Workspace isolation
-- ---------------------------------------------------------------------------
-- Each process gets a private copy of fixtures/ and points both cwd and the
-- LSP root_dir at it. That keeps the real .valk/symdb.sqlite untouched, holds
-- the server's workspace scan to a small fixed set instead of the 180+ .valk
-- files in the repo, and makes a run reproducible regardless of repo state.
--
-- The directory is carved out of nvim's own temp dir, which nvim removes on
-- exit for us — including the exit paths a trap would miss. This used to be
-- mktemp + a bash cleanup trap + a watchdog process in run.sh.
local workspace = vim.fn.tempname()
vim.fn.mkdir(workspace, "p")
vim.fn.system({ "cp", "-r", script_dir .. "fixtures/.", workspace .. "/" })
if vim.v.shell_error ~= 0 then
  io.stderr:write("UAT: failed to seed workspace from fixtures/\n")
  os.exit(2)
end
vim.env.VALK_UAT_WORKSPACE = workspace
vim.cmd("cd " .. vim.fn.fnameescape(workspace))

-- Parent-death watchdog. An interrupted run (SIGKILL on the test runner,
-- which no trap can catch) used to leave nvim and its valk-lsp child alive,
-- each holding ~1GB of GC heap; enough interrupted runs OOM'd the host.
-- Linux gets this free via PR_SET_PDEATHSIG in valk's exec, macOS does not,
-- so poll for reparenting and take ourselves down. Timers only fire while
-- the loop is pumped, which vim.wait in lib.lua does constantly.
local ppid0 = vim.uv.os_getppid()
local watchdog = vim.uv.new_timer()
watchdog:start(1000, 1000, function()
  if vim.uv.os_getppid() ~= ppid0 then
    vim.schedule(function() vim.cmd("cquit 2") end)
  end
end)

-- ---------------------------------------------------------------------------
-- LSP client setup
-- ---------------------------------------------------------------------------

vim.filetype.add({ extension = { valk = "valk" } })

vim.api.nvim_create_autocmd("FileType", {
  pattern = "valk",
  callback = function(args)
    local ok, err = pcall(vim.lsp.start, {
      name = "valk-lsp",
      cmd = { server_bin },
      root_dir = workspace,
    })
    if not ok then
      io.stderr:write("vim.lsp.start failed: " .. tostring(err) .. "\n")
    end
  end,
})

-- The server reports its startup workspace scan via $/progress with a
-- kind="end" value (scripts/lsp/scan.valk:142-148). Record that so scenarios
-- can wait on "the index is populated" instead of sleeping for a couple of
-- seconds and hoping. Installed before any client starts so no report is
-- missed.
local scan_state = { ended = 0 }
local prev_progress = vim.lsp.handlers["$/progress"]
vim.lsp.handlers["$/progress"] = function(err, result, ctx, cfg)
  local kind = result and result.value and result.value.kind
  if kind == "end" then scan_state.ended = scan_state.ended + 1 end
  if prev_progress then return prev_progress(err, result, ctx, cfg) end
end

-- Count publishDiagnostics per URI. This is what makes "assert no diagnostics"
-- a condition rather than a blind sleep: instead of waiting N ms and hoping
-- nothing shows up, a scenario can wait for the server to publish for that URI
-- at least once after its edit, then assert the payload was empty. Absence of
-- an event is unobservable; arrival of an empty one is not.
local publish_counts = { _total = 0 }
local prev_publish = vim.lsp.handlers["textDocument/publishDiagnostics"]
vim.lsp.handlers["textDocument/publishDiagnostics"] = function(err, result, ctx, cfg)
  if result and result.uri then
    publish_counts[result.uri] = (publish_counts[result.uri] or 0) + 1
    publish_counts._total = publish_counts._total + 1
  end
  if prev_publish then return prev_publish(err, result, ctx, cfg) end
end

local lib = require("lib")
lib._scan_state = scan_state
lib._publish_counts = publish_counts

-- ---------------------------------------------------------------------------
-- Result reporting
-- ---------------------------------------------------------------------------

local function json_escape(s)
  return (tostring(s):gsub('[%c"\\]', function(c)
    if c == '"' then return '\\"' end
    if c == "\\" then return "\\\\" end
    if c == "\n" then return "\\n" end
    if c == "\r" then return "\\r" end
    if c == "\t" then return "\\t" end
    return ("\\u%04x"):format(c:byte())
  end))
end

-- The JSON line is the runner's machine-readable record and must be the only
-- thing this process writes to stdout; everything human goes to stderr.
local function emit_result(scenario, test, status, us)
  io.stdout:write(('{"test":"%s","status":"%s","us":%d,"suite":"%s"}\n')
    :format(json_escape(test), status, math.floor(us), json_escape(scenario)))
  io.stdout:flush()
end

local pass_count = 0
local failures = {}
local total_t0 = vim.uv.hrtime()

local function run_one(scenario_name, test_name, fn)
  local full = scenario_name .. "::" .. test_name
  io.stderr:write(("[uat] %s ... "):format(full))
  io.stderr:flush()

  local t0 = vim.uv.hrtime()
  local ok, err = pcall(fn, lib)
  local elapsed_us = (vim.uv.hrtime() - t0) / 1e3

  if ok then
    pass_count = pass_count + 1
    io.stderr:write(("PASS (%.0f ms)\n"):format(elapsed_us / 1000))
    emit_result(scenario_name, test_name, "pass", elapsed_us)
  else
    -- Keep the detail for the grouped report at the end; the inline
    -- line stays short so a long stack trace doesn't bury the summary.
    table.insert(failures, { name = full, err = tostring(err), elapsed_us = elapsed_us })
    io.stderr:write(("FAIL (%.0f ms)\n"):format(elapsed_us / 1000))
    emit_result(scenario_name, test_name, "fail", elapsed_us)
  end
end

-- ---------------------------------------------------------------------------
-- Scenario selection
-- ---------------------------------------------------------------------------

local files = vim.fn.glob(script_dir .. "scenarios/*.lua", false, true)
table.sort(files)

local work = {}
for _, file in ipairs(files) do
  local name = file:match("([^/]+)%.lua$")
  if scenario_sel == "" or name == scenario_sel then
    table.insert(work, { file = file, name = name })
  end
end

if #work == 0 then
  io.stderr:write(("UAT: no scenario named '%s' under scenarios/\n"):format(scenario_sel))
  vim.cmd("cquit 2")
end

for _, entry in ipairs(work) do
  local mod = dofile(entry.file)
  if type(mod) ~= "table" then
    io.stderr:write(("[uat] %s: invalid scenario (must return table)\n"):format(entry.name))
    table.insert(failures, { name = entry.name, err = "scenario did not return a table", elapsed_us = 0 })
    emit_result(entry.name, entry.name, "fail", 0)
  else
    if type(mod._setup) == "function" then mod._setup(lib) end
    -- Run each exported test function. `pairs` order over a string-keyed
    -- table is an implementation detail of the hash layout, and it DOES
    -- vary between runs — which made any cross-test state dependency
    -- surface as a flaky failure. Sort so a given commit always runs the
    -- same sequence and a failure reproduces.
    local tnames = {}
    for tname, fn in pairs(mod) do
      if type(fn) == "function" and not tname:match("^_") then
        table.insert(tnames, tname)
      end
    end
    table.sort(tnames)
    for _, tname in ipairs(tnames) do
      run_one(entry.name, tname, mod[tname])
    end
  end
end

local total_ms = (vim.uv.hrtime() - total_t0) / 1e6

-- Grouped failure report. Per-test FAIL lines are interleaved with whatever
-- the server wrote to stderr, so repeat every failure here, at the very
-- bottom. run-tests.valk prints this block verbatim for a failing suite.
if #failures > 0 then
  io.stderr:write(("\n%s\n"):format(("="):rep(72)))
  io.stderr:write(("FAILURES (%d)\n"):format(#failures))
  io.stderr:write(("%s\n"):format(("="):rep(72)))
  for i, f in ipairs(failures) do
    io.stderr:write(("\n%d) %s  (%.0f ms)\n"):format(i, f.name, f.elapsed_us / 1000))
    for line in (f.err .. "\n"):gmatch("(.-)\n") do
      io.stderr:write(("   %s\n"):format(line))
    end
  end
  io.stderr:write(("%s\n"):format(("="):rep(72)))
end

io.stderr:write(("\n[uat] %d passed, %d failed in %.0f ms\n"):format(
  pass_count, #failures, total_ms))

if #failures > 0 then vim.cmd("cquit 1") end
vim.cmd("qall!")
