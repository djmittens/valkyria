-- Shared helpers for UAT scenarios.
--
-- Each scenario receives `lib` (this module) as its first argument. The
-- runner takes care of setup (LSP client started, valk filetype
-- registered) and result reporting; scenarios just call into helpers
-- here and `error(...)` on failure.

local M = {}

-- The runner sets cwd to the per-run tmp workspace before this file
-- is required. All "fixture" paths resolve relative to that workspace.
local workspace = vim.env.VALK_UAT_WORKSPACE or vim.fn.getcwd()

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

-- Open a fixture in a fresh buffer. Fixture name is relative to the
-- workspace root; the bash wrapper has already copied
-- test/lsp/uat/fixtures/* into the workspace, so e.g.
-- `open_fixture("small.valk")` opens "<workspace>/small.valk".
function M.open_fixture(rel)
  return open_with_fresh_buffer(workspace .. "/" .. rel)
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
-- Temp files and save/close lifecycle
-- ---------------------------------------------------------------------------

-- Write `content` to `<workspace>/<name>` and return the absolute
-- path. The workspace is wiped on runner exit. Use a unique `name`
-- per scenario so concurrent fixtures don't collide.
function M.write_temp(name, content)
  local path = workspace .. "/" .. name
  local f = assert(io.open(path, "w"), "could not open " .. path)
  f:write(content); f:close()
  return path
end

-- Open a path that exists on disk (e.g. the result of write_temp) in
-- a fresh buffer. Same wipe-then-edit pattern as open_fixture.
function M.open_path(path)
  local existing = vim.fn.bufnr(path)
  if existing > 0 and vim.api.nvim_buf_is_valid(existing) then
    pcall(vim.cmd, "bwipeout! " .. existing)
  end
  vim.cmd("edit! " .. vim.fn.fnameescape(path))
  vim.cmd("filetype detect")
  return vim.api.nvim_get_current_buf()
end

-- Save the buffer to disk AND notify the LSP via didSave. nvim's
-- `:write` triggers BufWritePost and the LSP client's auto-attach
-- normally fires didSave for us — but only if the relevant autocmds
-- ran during normal startup, which `nvim --headless -l` skips.
-- Be explicit: write to disk + manually send the notification.
function M.save_buffer(bufnr)
  vim.api.nvim_buf_call(bufnr, function() vim.cmd("write!") end)
  local clients = vim.lsp.get_clients({ bufnr = bufnr })
  if #clients == 0 then
    error("save_buffer: no LSP client attached to buf " .. bufnr)
  end
  local include_text = clients[1].server_capabilities.textDocumentSync
                   and clients[1].server_capabilities.textDocumentSync.save
                   and clients[1].server_capabilities.textDocumentSync.save.includeText
  local params = { textDocument = { uri = M.bufuri(bufnr) } }
  if include_text then
    params.text = table.concat(
      vim.api.nvim_buf_get_lines(bufnr, 0, -1, false), "\n")
  end
  for _, c in ipairs(clients) do
    c:notify("textDocument/didSave", params)
  end
  -- Give the server a beat to process the notification before the
  -- caller fires the next request. Without this, requests can race
  -- the didSave-triggered re-index.
  vim.wait(50)
end

-- Close a buffer (sending didClose). open_path/open_fixture already
-- wipe a stale buffer for the same path, so most scenarios don't
-- need this — but a "close, do other work, reopen" sequence does.
function M.close_buffer(bufnr)
  if vim.api.nvim_buf_is_valid(bufnr) then
    pcall(vim.cmd, "bwipeout! " .. bufnr)
  end
end

-- Append a line at the end of `bufnr`. Used by add-feature scenarios.
-- Returns the 0-indexed line number of the appended content.
function M.append_line(bufnr, text)
  local n = vim.api.nvim_buf_line_count(bufnr)
  vim.api.nvim_buf_set_lines(bufnr, n, n, false, { text })
  vim.wait(50)  -- let didChange flush
  return n  -- caller's appended line is at index n (0-indexed)
end

-- Replace the entire buffer with new content. Useful for "edit a
-- function body" by rewriting the whole file at once.
function M.replace_all(bufnr, new_content)
  local lines = vim.split(new_content, "\n", { plain = true })
  vim.api.nvim_buf_set_lines(bufnr, 0, -1, false, lines)
  vim.wait(50)
end

-- ---------------------------------------------------------------------------
-- Indexing polling
-- ---------------------------------------------------------------------------

-- Poll documentSymbol until the buffer's symdb entry contains at
-- least one symbol matching `name_pattern` (Lua pattern), or timeout.
-- Use after open_fixture / write_temp+open_path before you make
-- assertions that depend on the LSP having indexed the file.
-- Returns true if found, false on timeout. Always returns within
-- timeout_ms; never raises.
function M.wait_for_symbol_indexed(bufnr, name_pattern, timeout_ms)
  timeout_ms = timeout_ms or 3000
  local deadline = vim.uv.hrtime() + timeout_ms * 1e6
  while vim.uv.hrtime() < deadline do
    local res = vim.lsp.buf_request_sync(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = M.bufuri(bufnr) } }, 500)
    if res then
      for _, r in pairs(res) do
        if r.result then
          for _, s in ipairs(r.result) do
            if (s.name or ""):match(name_pattern) then return true end
          end
        end
      end
    end
    vim.wait(50)
  end
  return false
end

-- ---------------------------------------------------------------------------
-- Diagnostics polling
-- ---------------------------------------------------------------------------

-- Poll vim.diagnostic.get(bufnr) until either count is met or timeout.
-- Returns the diagnostics list (possibly empty). When `want_count` is
-- 0, waits the full timeout to be confident none arrived.
function M.wait_for_diagnostics(bufnr, want_count, timeout_ms)
  timeout_ms = timeout_ms or 3000
  local deadline = vim.uv.hrtime() + timeout_ms * 1e6
  local diags = {}
  while vim.uv.hrtime() < deadline do
    diags = vim.diagnostic.get(bufnr)
    if want_count == 0 then
      vim.wait(100)
      diags = vim.diagnostic.get(bufnr)
    elseif #diags >= want_count then
      return diags
    end
    vim.wait(50)
  end
  return diags
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
