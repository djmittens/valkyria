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
  -- `silent` keeps the `"path" NL, NB` file message out of stderr, which
  -- is where the test report lives.
  vim.cmd("silent edit! " .. vim.fn.fnameescape(path))
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
  local ok, client = M.wait_until(function()
    for _, c in ipairs(vim.lsp.get_clients({ bufnr = bufnr })) do
      if c.server_capabilities and c.initialized ~= false then return c end
    end
    return nil
  end, timeout_ms)
  if not ok then
    error(("LSP did not attach to buf %d within %dms"):format(bufnr, timeout_ms))
  end
  return client
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
  vim.cmd("silent edit! " .. vim.fn.fnameescape(path))
  vim.cmd("filetype detect")
  return vim.api.nvim_get_current_buf()
end

-- Save the buffer to disk AND notify the LSP via didSave. nvim's
-- `:write` triggers BufWritePost and the LSP client's auto-attach
-- normally fires didSave for us — but only if the relevant autocmds
-- ran during normal startup, which `nvim --headless -l` skips.
-- Be explicit: write to disk + manually send the notification.
function M.save_buffer(bufnr)
  -- `silent` — the default "N lines, M bytes written" message goes to
  -- stderr under --headless and interleaves with the test report,
  -- corrupting the PASS/FAIL lines it lands in the middle of.
  vim.api.nvim_buf_call(bufnr, function() vim.cmd("silent write!") end)
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
  -- Barrier, not a sleep: the round trip proves the server dequeued the
  -- didSave. (The re-index it *enqueues* runs on lsp/idx-sys and still needs
  -- an outcome poll — see wait_for_symbol_indexed / wait_for_symbol_gone.)
  M.sync(bufnr)
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
  M.sync(bufnr)  -- didChange handled before the caller's next request
  return n  -- caller's appended line is at index n (0-indexed)
end

-- Replace the entire buffer with new content. Useful for "edit a
-- function body" by rewriting the whole file at once.
function M.replace_all(bufnr, new_content)
  local lines = vim.split(new_content, "\n", { plain = true })
  vim.api.nvim_buf_set_lines(bufnr, 0, -1, false, lines)
  M.sync(bufnr)
end

-- ---------------------------------------------------------------------------
-- Synchronization
-- ---------------------------------------------------------------------------
--
-- Two distinct primitives, because the server has two queues:
--
--   M.sync(bufnr)  — round-trip barrier. Notifications (didOpen/didChange/
--     didClose/didSave) and requests share ONE FIFO worker queue in arrival
--     order (scripts/lsp/lsp.valk:116-122), so a request that comes back
--     proves every notification sent before it has been fully handled.
--     This replaces every "vim.wait(N) to let didChange flush" sleep.
--
--   M.wait_until(...) — outcome poll. Notification handlers enqueue indexing
--     and diagnostics onto a SEPARATE system (lsp/idx-sys, lsp.valk:373), and
--     no request round-trips through it. So index/diagnostic effects can only
--     be awaited by polling for the observable result.
--
-- A bare vim.wait(N) is legitimate in exactly one place: as the poll interval
-- inside wait_until. Everywhere else it has to be sized for the worst case,
-- which makes it simultaneously slower than necessary in the common case and
-- too short under load — sluggish AND flaky from the same line of code.
--
-- Three sleeps that look necessary but are not:
--
--   "let nvim flush the pending didChange" — never needed. Client:request
--   calls changetracking.flush() before sending every request
--   (nvim runtime/lua/vim/lsp/client.lua:732), so a queued didChange always
--   reaches the server ahead of the next request. Just make the request.
--
--   "wait for the workspace scan" — the server announces it, via $/progress
--   with kind="end". Use wait_for_workspace_scan.
--
--   "wait to be sure no diagnostic arrives" — absence of an event is not
--   observable, but arrival of an empty publish is. Use settle_diagnostics,
--   which waits for the publish that the edit provoked and then lets you
--   assert on its contents.

-- The barrier request must NOT be document-scoped. Anything that parses the
-- buffer (foldingRange, documentSymbol, semanticTokens, ...) raises on
-- incomplete input, and these scenarios deliberately leave unbalanced parens
-- to simulate mid-typing states, so a document-scoped barrier would turn
-- every mid-edit sync into an error response. (Those errors are at least
-- matchable now — the AOT miscompile that dropped `id` from
-- lsp/request-done-cb and made them come back with a null id is fixed;
-- see test_build.c build_aot_closure_captures_formals.) A barrier that
-- reports failure is still a bad barrier. workspace/symbol only touches
-- the symbol db, cannot fail on buffer text, and still goes through the
-- same FIFO worker queue, so it orders correctly.
local SYNC_METHOD = "workspace/symbol"
local SYNC_PARAMS = { query = "\1uat-barrier" }

-- WORKLOAD parameter, not synchronization. A latency scenario asks "is the
-- editor responsive while I type", and that number only means something at a
-- defined input rate — with no gap at all you measure max-rate queue
-- contention instead, which is a different (harsher, also valid) test.
-- ~25ms/char is roughly 100wpm sustained.
--
-- Never use this to wait for the server to catch up. It is only the simulated
-- gap between two keystrokes, and only in scenarios that report a latency
-- percentile. Correctness-under-burst scenarios type with no gap on purpose.
M.TYPING_CADENCE_MS = 25

function M.keystroke_gap()
  vim.wait(M.TYPING_CADENCE_MS)
end

-- Block until the server has drained every notification sent before now.
-- Returns true if the round trip completed.
function M.sync(bufnr, timeout_ms)
  local clients = vim.lsp.get_clients({ bufnr = bufnr })
  if #clients == 0 then return false end
  local res = vim.lsp.buf_request_sync(bufnr, SYNC_METHOD, SYNC_PARAMS,
    timeout_ms or 5000)
  return res ~= nil
end

-- Poll `predicate` until it returns truthy. Returns (ok, value, elapsed_ms).
-- Polls on a short interval rather than sleeping a fixed budget, so the
-- common case costs one interval and only a genuine failure costs the
-- timeout. `interval_ms` defaults to 10.
function M.wait_until(predicate, timeout_ms, interval_ms)
  timeout_ms = timeout_ms or 5000
  interval_ms = interval_ms or 10
  local t0 = vim.uv.hrtime()
  local deadline = t0 + timeout_ms * 1e6
  while true do
    local ok, value = pcall(predicate)
    if ok and value then
      return true, value, (vim.uv.hrtime() - t0) / 1e6
    end
    if vim.uv.hrtime() >= deadline then
      return false, value, (vim.uv.hrtime() - t0) / 1e6
    end
    vim.wait(interval_ms)
  end
end

-- Same, but errors with `msg` on timeout instead of returning false. Use
-- this when the wait is a precondition for the assertion that follows: a
-- silent timeout turns a "server never indexed the file" bug into a
-- confusing failure several lines later.
function M.require_until(predicate, msg, timeout_ms, interval_ms)
  local ok, value, elapsed = M.wait_until(predicate, timeout_ms, interval_ms)
  if not ok then
    error(("%s (waited %.0f ms)"):format(msg or "require_until timed out", elapsed), 2)
  end
  return value
end

-- Wait until the client has been idle for `window_ms` — no server-initiated
-- diagnostics have arrived in that window.
--
-- This is for the one case a barrier cannot cover: after churning many files,
-- nvim itself has a backlog of inbound notifications, and its handlers run on
-- the same main loop the test runs on. Measuring latency mid-drain times nvim's
-- queue rather than the server.
--
-- A quiescence window is not a guessed sleep: the condition ("nothing has
-- arrived for W ms") is verified, the total wait adapts to real load, and it
-- fails fast when the system is already idle. It only spends the full timeout
-- when the server genuinely will not stop talking.
function M.wait_for_quiescence(window_ms, timeout_ms)
  window_ms = window_ms or 150
  local counts = M._publish_counts
  if not counts then return true end
  local deadline = vim.uv.hrtime() + (timeout_ms or 5000) * 1e6
  while vim.uv.hrtime() < deadline do
    local before = counts._total
    vim.wait(window_ms)
    if counts._total == before then return true end
  end
  return false
end

-- Wait until the server has finished at least one workspace scan, observed
-- via the $/progress kind="end" report the runner records. This is the honest
-- precondition for any cross-file assertion — previously scenarios slept 2-2.5s
-- and hoped. Returns true if a scan completed within the timeout.
--
-- Prefer wait_for_workspace_symbol when you can name the symbol you need; use
-- this when the assertion tolerates a miss (e.g. "must not crash") and you
-- only need the index to be settled.
function M.wait_for_workspace_scan(timeout_ms)
  local state = M._scan_state
  if not state then return false end
  local seen = state.ended
  if seen > 0 then return true end
  return (M.wait_until(function() return state.ended > seen end,
    timeout_ms or 10000, 10))
end

-- ---------------------------------------------------------------------------
-- Indexing polling
-- ---------------------------------------------------------------------------

-- Return the documentSymbol names the server currently reports for `bufnr`.
function M.document_symbols(bufnr)
  local res = vim.lsp.buf_request_sync(bufnr, "textDocument/documentSymbol",
    { textDocument = { uri = M.bufuri(bufnr) } }, 1000)
  local names = {}
  if res then
    for _, r in pairs(res) do
      for _, s in ipairs(r.result or {}) do
        table.insert(names, s.name or "")
      end
    end
  end
  return names
end

local function has_symbol(bufnr, name_pattern)
  for _, n in ipairs(M.document_symbols(bufnr)) do
    if n:match(name_pattern) then return true end
  end
  return false
end

-- Poll documentSymbol until a symbol matching `name_pattern` (Lua pattern)
-- appears. Returns true if found, false on timeout; never raises. Prefer
-- require_symbol_indexed when the symbol's presence is a precondition.
function M.wait_for_symbol_indexed(bufnr, name_pattern, timeout_ms)
  local ok = M.wait_until(function() return has_symbol(bufnr, name_pattern) end,
    timeout_ms or 3000, 20)
  return ok
end

-- Strict variant: fails the test if the symbol never shows up.
function M.require_symbol_indexed(bufnr, name_pattern, timeout_ms)
  if not M.wait_for_symbol_indexed(bufnr, name_pattern, timeout_ms) then
    error(("server never indexed a symbol matching %q; documentSymbol reports: %s")
      :format(name_pattern, vim.inspect(M.document_symbols(bufnr))), 2)
  end
end

-- Inverse: wait until no symbol matches. Needed after deleting a definition,
-- where the interesting state is the absence of a row.
function M.wait_for_symbol_gone(bufnr, name_pattern, timeout_ms)
  return (M.wait_until(function() return not has_symbol(bufnr, name_pattern) end,
    timeout_ms or 3000, 20))
end

-- Wait until the workspace index can resolve `name`, via workspace/symbol
-- rather than the per-file documentSymbol list.
--
-- Use this — NOT wait_for_symbol_indexed — whenever the symbol is defined in
-- a file other than `bufnr`. documentSymbol only reports definitions in the
-- requested document, so polling it for a cross-file symbol can never
-- succeed: it burns the entire timeout and then returns false, which callers
-- routinely ignore. Four such call sites were silently costing 5s each.
function M.wait_for_workspace_symbol(bufnr, name, timeout_ms)
  return (M.wait_until(function()
    local res = vim.lsp.buf_request_sync(bufnr, "workspace/symbol",
      { query = name }, 1000)
    if not res then return false end
    for _, r in pairs(res) do
      for _, s in ipairs(r.result or {}) do
        if (s.name or "") == name then return true end
      end
    end
    return false
  end, timeout_ms or 5000, 20))
end

-- Strict variant: a cross-file precondition that never materializes should
-- fail here, loudly, rather than 20 lines later as a confusing assertion.
function M.require_workspace_symbol(bufnr, name, timeout_ms)
  if not M.wait_for_workspace_symbol(bufnr, name, timeout_ms) then
    error(("workspace index never resolved %q"):format(name), 2)
  end
end

-- ---------------------------------------------------------------------------
-- Diagnostics polling
-- ---------------------------------------------------------------------------

-- Poll vim.diagnostic.get(bufnr) until count is met or timeout.
-- Returns the diagnostics list. Distinguish three modes:
--   want_count > 0: return as soon as len(diags) >= want_count
--   want_count == 0: poll until len(diags) == 0 (clear case);
--                    falls back to a quiescence sample if no clear
--                    arrives within timeout.
--   want_count < 0: alias for "wait the full timeout, return whatever
--                   landed" — useful when you want to assert the
--                   absence of new diags but currently have some.
function M.wait_for_diagnostics(bufnr, want_count, timeout_ms)
  timeout_ms = timeout_ms or 3000
  if want_count >= 0 then
    M.wait_until(function()
      local n = #vim.diagnostic.get(bufnr)
      if want_count > 0 then return n >= want_count end
      return n == 0
    end, timeout_ms, 10)
    return vim.diagnostic.get(bufnr)
  end
  -- want_count < 0: "whatever landed after the server caught up". Not a sleep:
  -- flush + barrier, then wait for the server to actually publish for this URI.
  M.settle_diagnostics(bufnr, timeout_ms)
  return vim.diagnostic.get(bufnr)
end

-- How many times has the server published diagnostics for this buffer's URI?
function M.diagnostic_publishes(bufnr)
  local counts = M._publish_counts
  if not counts then return 0 end
  return counts[M.bufuri(bufnr)] or 0
end

-- Wait for the server to publish diagnostics for `bufnr` at least once from
-- now on. Returns true if a publish arrived.
function M.wait_for_diagnostic_publish(bufnr, timeout_ms)
  local before = M.diagnostic_publishes(bufnr)
  return (M.wait_until(function()
    return M.diagnostic_publishes(bufnr) > before
  end, timeout_ms or 3000, 10))
end

-- Bring diagnostics for `bufnr` to a known-settled state, for assertions of
-- the form "there should be no (more) errors here".
--
-- The absence of a notification is not observable, so this does not try to
-- observe it. Instead:
--   1. sync() forces the client to flush pending didChange (nvim flushes
--      changetracking before every request) and proves the server dequeued it,
--   2. then wait for the resulting publish for this URI to actually arrive.
-- After that the diagnostic set reflects the edit, and asserting on it is
-- deterministic rather than a race against a fixed sleep.
--
-- Returns true if a publish was observed. False means the server chose not to
-- republish, in which case the current set is already the settled one.
function M.settle_diagnostics(bufnr, timeout_ms)
  local before = M.diagnostic_publishes(bufnr)
  M.sync(bufnr)
  return (M.wait_until(function()
    return M.diagnostic_publishes(bufnr) > before
  end, timeout_ms or 3000, 10))
end

-- Wait until diagnostics for `bufnr` satisfy `pred(diags)`. Preferred over
-- wait_for_diagnostics when the assertion is about content rather than count:
-- it returns the moment the expected message lands instead of waiting for an
-- arbitrary count that may never be reached.
function M.wait_for_diagnostic_matching(bufnr, pred, timeout_ms)
  M.wait_until(function() return pred(vim.diagnostic.get(bufnr)) end,
    timeout_ms or 3000, 10)
  return vim.diagnostic.get(bufnr)
end

-- Convenience: any diagnostic whose message contains `needle`.
function M.wait_for_diagnostic_containing(bufnr, needle, timeout_ms)
  return M.wait_for_diagnostic_matching(bufnr, function(diags)
    for _, d in ipairs(diags) do
      if (d.message or ""):find(needle, 1, true) then return true end
    end
    return false
  end, timeout_ms)
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
  -- No wait here, deliberately. This simulates a keystroke in a burst, so a
  -- round-trip barrier would serialize every keystroke against a response and
  -- stop testing the thing under test. And no bare tick is needed either:
  -- nvim's Client:request calls changetracking.flush() before sending
  -- (runtime/lua/vim/lsp/client.lua:732), so the pending didChange is
  -- guaranteed to reach the server ahead of whatever request the caller makes
  -- next. Sleeping to "let didChange flush" was always a no-op guess.
  return end_line, end_col
end

-- ---------------------------------------------------------------------------
-- Async / concurrent requests
-- ---------------------------------------------------------------------------

-- Fire a request without blocking; returns a "ticket" object you can
-- pass to wait_for_response or cancel_request. The ticket records when
-- the request was sent so callers can measure latency, and stores the
-- response in `ticket.response` / error in `ticket.err` when it lands.
--
-- Use this when you need to overlap requests in time or want to fire-
-- and-forget. Pair with M.drain_responses(tickets, timeout_ms) to wait
-- for a batch.
function M.request_async(bufnr, method, params)
  local ticket = {
    method = method,
    sent_ns = vim.uv.hrtime(),
    done = false,
    response = nil,
    err = nil,
  }
  local clients = vim.lsp.get_clients({ bufnr = bufnr })
  if #clients == 0 then
    ticket.done = true; ticket.err = "no client"
    return ticket
  end
  local _, request_id = clients[1]:request(method, params, function(err, result)
    ticket.done = true
    ticket.response = result
    ticket.err = err
    ticket.recv_ns = vim.uv.hrtime()
  end, bufnr)
  ticket.request_id = request_id
  ticket.client = clients[1]
  return ticket
end

-- Wait for all tickets to land (or timeout). Returns the count that
-- completed. Tickets that didn't complete remain `done = false`.
function M.drain_responses(tickets, timeout_ms)
  timeout_ms = timeout_ms or 5000
  local deadline = vim.uv.hrtime() + timeout_ms * 1e6
  while vim.uv.hrtime() < deadline do
    local pending = 0
    for _, t in ipairs(tickets) do
      if not t.done then pending = pending + 1 end
    end
    if pending == 0 then break end
    vim.wait(5)
  end
  local done = 0
  for _, t in ipairs(tickets) do
    if t.done then done = done + 1 end
  end
  return done
end

-- Cancel an in-flight ticket. The LSP spec lets the server respond
-- normally OR with a Cancelled error after $/cancelRequest. Either is
-- acceptable; the test we care about is "the server doesn't deadlock
-- or crash". Returns true if the cancel was sent.
function M.cancel_request(ticket)
  if not ticket.client or not ticket.request_id then return false end
  return ticket.client:cancel_request(ticket.request_id)
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
