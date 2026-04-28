-- Shared helpers for UAT scenarios.
--
-- Each scenario receives `lib` (this module) as its first argument. The
-- runner takes care of setup (LSP client started, valk filetype
-- registered) and result reporting; scenarios just call into helpers
-- here and `error(...)` on failure.

local M = {}

local repo_root = vim.fn.getcwd()

-- ---------------------------------------------------------------------------
-- File / buffer
-- ---------------------------------------------------------------------------

-- nvim --headless -l skips automatic filetype detection on BufRead, so
-- the FileType=valk autocmd that starts the LSP client never fires.
-- The helpers below also wipe any prior buffer for the same path so a
-- previous test's unsaved edits don't leak (`E37: No write since last
-- change` blocks `:edit` otherwise).

local function open_with_fresh_buffer(path)
  -- If a buffer for this path already exists, wipe it. `bwipeout!` is
  -- the only command that fully removes a buffer including its name
  -- mapping, so a subsequent `:edit` re-reads the file from disk.
  local existing = vim.fn.bufnr(path)
  if existing > 0 and vim.api.nvim_buf_is_valid(existing) then
    -- Detach LSP client first to avoid stale didClose ordering.
    pcall(vim.cmd, "bwipeout! " .. existing)
  end
  vim.cmd("edit! " .. vim.fn.fnameescape(path))
  vim.cmd("filetype detect")
  return vim.api.nvim_get_current_buf()
end

-- Open a fixture under test/lsp/uat/fixtures/ in a fresh buffer. Returns
-- the bufnr.
function M.open_fixture(rel)
  return open_with_fresh_buffer(repo_root .. "/test/lsp/uat/fixtures/" .. rel)
end

-- Open an arbitrary path inside the repo (e.g. an existing real .valk
-- file under scripts/lsp/). Useful for exercising the LSP against the
-- same files the user actually edits.
function M.open_repo_file(rel)
  return open_with_fresh_buffer(repo_root .. "/" .. rel)
end

-- Wait until at least one LSP client is attached to `bufnr` AND its
-- initialize handshake has completed (server_capabilities populated).
-- Times out after `timeout_ms` and errors. Returns the client.
function M.wait_for_lsp(bufnr, timeout_ms)
  timeout_ms = timeout_ms or 10000
  local deadline = vim.uv.hrtime() + timeout_ms * 1e6
  while vim.uv.hrtime() < deadline do
    local clients = vim.lsp.get_clients({ bufnr = bufnr })
    for _, c in ipairs(clients) do
      if c.server_capabilities and c.initialized ~= false then
        return c
      end
    end
    vim.wait(20)
  end
  error(("LSP did not attach to buf %d within %dms"):format(bufnr, timeout_ms))
end

-- ---------------------------------------------------------------------------
-- Request / response
-- ---------------------------------------------------------------------------

-- Synchronous LSP request with timing. Returns
--     result, elapsed_ms, err
-- where `result` is the server's response (or nil on timeout/error)
-- and `err` is the LSP error if any. Errors out only on protocol-level
-- failures (e.g., timeout); LSP-level errors are returned for the
-- scenario to inspect.
function M.request(bufnr, method, params, timeout_ms)
  timeout_ms = timeout_ms or 5000
  local t0 = vim.uv.hrtime()
  local responses = vim.lsp.buf_request_sync(bufnr, method, params, timeout_ms)
  local elapsed_ms = (vim.uv.hrtime() - t0) / 1e6
  if not responses then
    return nil, elapsed_ms, "timeout"
  end
  -- buf_request_sync returns a map keyed by client_id. We expect one client.
  for _, r in pairs(responses) do
    return r.result, elapsed_ms, r.error
  end
  return nil, elapsed_ms, "no client responded"
end

-- Position helper: 0-indexed (line, character). Editor users think in
-- 1-indexed lines / 0-indexed cols, but LSP wants both 0-indexed —
-- abstract it to keep scenarios readable.
function M.pos(line0, char0)
  return { line = line0, character = char0 }
end

function M.tdp(uri, line0, char0)
  return {
    textDocument = { uri = uri },
    position = { line = line0, character = char0 },
  }
end

function M.bufuri(bufnr)
  return vim.uri_from_bufnr(bufnr)
end

-- Locate a substring in a buffer and return (line0, col0) of its
-- first byte. Errors if not found. Convenient for "click on this
-- text" style assertions instead of hard-coded coordinates.
function M.find_text(bufnr, needle)
  local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
  for i, line in ipairs(lines) do
    local s = line:find(needle, 1, true)
    if s then return i - 1, s - 1 end
  end
  error(("text not found in buffer: %q"):format(needle))
end

-- ---------------------------------------------------------------------------
-- Assertions
-- ---------------------------------------------------------------------------

function M.assert_eq(actual, expected, msg)
  if actual ~= expected then
    error(("%s: expected %s, got %s"):format(
      msg or "assert_eq",
      vim.inspect(expected), vim.inspect(actual)), 2)
  end
end

function M.assert_lt(actual, bound, msg)
  if not (actual < bound) then
    error(("%s: %s !< %s"):format(msg or "assert_lt",
      tostring(actual), tostring(bound)), 2)
  end
end

function M.assert_truthy(v, msg)
  if not v then
    error((msg or "assert_truthy") .. ": got " .. vim.inspect(v), 2)
  end
end

function M.assert_contains(haystack, needle, msg)
  if type(haystack) == "string" then
    if not haystack:find(needle, 1, true) then
      error(("%s: %q not in %q"):format(msg or "assert_contains",
        needle, haystack), 2)
    end
    return
  end
  if type(haystack) == "table" then
    for _, v in ipairs(haystack) do
      if v == needle then return end
      if type(v) == "table" and v.label == needle then return end
      if type(v) == "table" and v.name == needle then return end
    end
    error(("%s: %s not in list of %d items"):format(
      msg or "assert_contains", vim.inspect(needle), #haystack), 2)
  end
end

-- ---------------------------------------------------------------------------
-- Editing
-- ---------------------------------------------------------------------------

-- Insert `text` at (line0, col0) in `bufnr` and notify the LSP via
-- didChange. Returns the new (line0, col0) at the end of the insertion.
-- Used by the rapid-typing scenario.
function M.insert_at(bufnr, line0, col0, text)
  local lines = vim.split(text, "\n", { plain = true })
  vim.api.nvim_buf_set_text(bufnr, line0, col0, line0, col0, lines)
  -- Recompute end position after insertion
  local end_line, end_col
  if #lines == 1 then
    end_line, end_col = line0, col0 + #lines[1]
  else
    end_line, end_col = line0 + #lines - 1, #lines[#lines]
  end
  -- nvim's LSP integration auto-fires didChange via on_lines callback.
  -- Give the event loop a tick to flush.
  vim.wait(5)
  return end_line, end_col
end

-- ---------------------------------------------------------------------------
-- Stats
-- ---------------------------------------------------------------------------

-- Compute percentile of a sorted-or-unsorted array of numbers.
function M.percentile(arr, p)
  if #arr == 0 then return 0 end
  local sorted = vim.deepcopy(arr)
  table.sort(sorted)
  local idx = math.ceil(#sorted * p / 100)
  if idx < 1 then idx = 1 end
  if idx > #sorted then idx = #sorted end
  return sorted[idx]
end

return M
