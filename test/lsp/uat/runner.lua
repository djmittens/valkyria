-- UAT runner. Invoked by run.sh as
--     nvim --headless -l test/lsp/uat/runner.lua [scenario_filter]
--
-- Reuses ONE nvim session across all scenarios:
--   - registers .valk filetype
--   - starts valk-lsp once on first .valk buffer (then attaches to subsequent)
--   - executes each scenario module's exported test functions
--   - writes JSON-line results to $VALK_UAT_RESULTS (one line per test)
--   - exits 0 (the bash wrapper inspects the results file for pass/fail)
--
-- Failure semantics:
--   - scenario function calls `error(msg)` on failure
--   - runner catches via pcall, records as fail, continues with next test
--   - stale buffer state from a failing test is left in place; tests are
--     responsible for opening their own fixtures (lib.open_fixture).

local script_dir = debug.getinfo(1, "S").source:sub(2):match("(.*/)")
package.path = script_dir .. "?.lua;" .. package.path

-- The bash wrapper sets up an isolated tmp workspace and points us at
-- it via VALK_UAT_WORKSPACE. cd there + use it as the LSP root_dir so
-- the server's workspace scan only sees our fixtures, not the 180+
-- .valk files in the real repo.
local workspace = vim.env.VALK_UAT_WORKSPACE
if not workspace or workspace == "" then
  io.stderr:write("UAT: VALK_UAT_WORKSPACE not set — run via test/lsp/uat/run.sh\n")
  os.exit(2)
end
vim.cmd("cd " .. vim.fn.fnameescape(workspace))

local server_bin = vim.env.VALK_LSP_BIN
if not server_bin or server_bin == "" then
  io.stderr:write("UAT: VALK_LSP_BIN not set\n")
  os.exit(2)
end
local results_path = vim.env.VALK_UAT_RESULTS
local filter = arg[1]

if vim.fn.executable(server_bin) ~= 1 then
  io.stderr:write(("UAT: missing LSP binary at %s\n"):format(server_bin))
  os.exit(2)
end

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

local lib = require("lib")

-- ---------------------------------------------------------------------------
-- Result reporting
-- ---------------------------------------------------------------------------

local results_fd
if results_path then
  results_fd = io.open(results_path, "w")
end

local function emit_result(rec)
  local line = vim.json.encode(rec)
  if results_fd then results_fd:write(line .. "\n"); results_fd:flush() end
  io.stderr:write(line .. "\n")
end

local pass_count, fail_count = 0, 0
local total_t0 = vim.uv.hrtime()

local function run_one(scenario_name, test_name, fn)
  local full = scenario_name .. "::" .. test_name
  if filter and not full:match(filter) then return end

  io.stderr:write(("[uat] %s ... "):format(full))
  io.stderr:flush()

  local t0 = vim.uv.hrtime()
  local ok, err = pcall(fn, lib)
  local elapsed_ms = (vim.uv.hrtime() - t0) / 1e6

  if ok then
    pass_count = pass_count + 1
    io.stderr:write(("PASS (%.0f ms)\n"):format(elapsed_ms))
    emit_result({
      scenario = scenario_name, test = test_name,
      status = "pass", elapsed_ms = elapsed_ms,
    })
  else
    fail_count = fail_count + 1
    io.stderr:write(("FAIL (%.0f ms): %s\n"):format(elapsed_ms, tostring(err)))
    emit_result({
      scenario = scenario_name, test = test_name,
      status = "fail", elapsed_ms = elapsed_ms,
      error = tostring(err),
    })
  end
end

-- ---------------------------------------------------------------------------
-- Scenario discovery
-- ---------------------------------------------------------------------------

local scenarios_dir = script_dir .. "scenarios"
local files = vim.fn.glob(scenarios_dir .. "/*.lua", false, true)
table.sort(files)

for _, file in ipairs(files) do
  local name = file:match("([^/]+)%.lua$")
  local mod = dofile(file)
  if type(mod) ~= "table" then
    io.stderr:write(("[uat] %s: invalid scenario (must return table)\n"):format(name))
  else
    -- Optional setup function
    if type(mod._setup) == "function" then mod._setup(lib) end
    -- Run each exported test function
    for tname, fn in pairs(mod) do
      if type(fn) == "function" and not tname:match("^_") then
        run_one(name, tname, fn)
      end
    end
  end
end

local total_ms = (vim.uv.hrtime() - total_t0) / 1e6
io.stderr:write(("\n[uat] %d passed, %d failed in %.0f ms\n"):format(
  pass_count, fail_count, total_ms))

if results_fd then results_fd:close() end

-- Always exit 0; bash wrapper interprets the results file for CI exit code.
-- (nvim --headless -l swallows lua errors past pcall, so a script error
-- here would still produce a 0 exit anyway. The wrapper checks for the
-- presence + content of the results file as the canonical signal.)
vim.cmd("qall!")
