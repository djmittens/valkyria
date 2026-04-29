-- Rapid-typing stability: simulate a user typing 30 characters into
-- a file one keystroke at a time. After each keystroke, request
-- semantic tokens. Verify:
--   1. No request times out / errors.
--   2. Every returned token's offsets fit inside the current buffer
--      (no token whose `(line, col + len)` lands past EOL).
--   3. p95 response latency is reasonable.
--
-- This is the regression test for the "tokens flicker / land in
-- whitespace mid-edit" UX bug that the cache-on-clean-parse fix
-- targeted. A mishandled cache would either time out, return offsets
-- off the end of the buffer, or take >1s under typing load.

local function token_fits(data, lines)
  -- LSP semantic tokens are 5-tuples [dl, dc, len, type, mod] with
  -- relative coordinates. Walk the array, accumulate (line, col),
  -- check each span fits.
  local line, col = 0, 0
  for i = 1, #data, 5 do
    local dl, dc, len = data[i], data[i + 1], data[i + 2]
    if dl > 0 then line = line + dl; col = dc
    else col = col + dc end
    if line < 0 or line >= #lines then
      return false, ("token line %d out of range [0,%d)"):format(line, #lines)
    end
    if col < 0 or col + len > #(lines[line + 1] or "") then
      return false, ("token (line %d, col %d, len %d) past EOL %d")
        :format(line, col, len, #(lines[line + 1] or ""))
    end
  end
  return true
end

return {
  rapid_typing_tokens_stay_valid = function(lib)
    local bufnr = lib.open_fixture("typing_seed.valk")
    lib.wait_for_lsp(bufnr)
    -- Prime the AST cache with a clean parse first.
    lib.request(bufnr, "textDocument/semanticTokens/full",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    -- Find the blank line between (fun ...) and (def ...). Hard-coded
    -- line numbers are brittle; locate the blank line by scanning so
    -- the test survives whitespace edits to the fixture.
    local insert_text = "(let {x 1 y "
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local insert_line = nil
    local saw_fun = false
    for i, line in ipairs(lines) do
      if line:find("(fun ", 1, true) then saw_fun = true
      elseif saw_fun and line:match("^%s*$") then
        insert_line = i - 1; break
      end
    end
    if not insert_line then
      error("typing_seed.valk has no blank line after the (fun ...) form")
    end

    local latencies = {}
    local errors = {}
    for i = 1, #insert_text do
      local ch = insert_text:sub(i, i)
      vim.api.nvim_buf_set_text(bufnr, insert_line, i - 1, insert_line, i - 1, { ch })
      -- Wait long enough for nvim's deferred LSP didChange to flush
      -- through the client's outgoing pipe. The default change-tracking
      -- debounce is ~150ms; without this the server hasn't yet seen
      -- the edit when our sem-tokens request arrives, and serializes
      -- the request behind the impending didChange notification.
      vim.wait(50)
      local res, elapsed, err = lib.request(bufnr, "textDocument/semanticTokens/full",
        { textDocument = { uri = lib.bufuri(bufnr) } }, 3000)
      table.insert(latencies, elapsed)
      if err then table.insert(errors, ("step %d: %s"):format(i, tostring(err))) end
      if res and res.data then
        local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
        local ok, why = token_fits(res.data, lines)
        if not ok then
          error(("step %d (after inserting %q): %s"):format(i, ch, why))
        end
      end
    end

    lib.assert_eq(#errors, 0,
      "rapid-typing produced LSP errors: " .. vim.inspect(errors))
    local p95 = lib.percentile(latencies, 95)
    -- Generous bound — the validator + symdb are heavy. Tighten later.
    lib.assert_lt(p95, 300,
      ("p95 token latency %d ms exceeds budget"):format(p95))
    io.stderr:write(("[uat] rapid-typing: median %d ms, p95 %d ms across %d edits\n")
      :format(lib.percentile(latencies, 50), p95, #latencies))
  end,

  -- The real "editing experience" workload: type a sequence of
  -- characters, between each one fire a hover at the cursor.
  -- Records latency for each hover. p99 should stay sub-second.
  --
  -- Lives in 06_ rather than later because suite-cumulative state
  -- (deep async-task queues from 70+ scenarios worth of didChanges)
  -- masks the actual editor-vs-LSP perf characteristic. By running
  -- early, we measure the LSP at the load shape a real user sees:
  -- one buffer, one editor session, modest history.
  hover_during_typing_keeps_p99_under_budget = function(lib)
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(500)

    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local target = nil
    for i = 30, #lines do
      if lines[i]:match("^%s*$") then target = i - 1; break end
    end
    if not target then error("no blank line in medium.valk after line 30") end

    local sample = "(def {scratch} (+ 1 2 3))"
    local latencies = {}
    for i = 1, #sample do
      local ch = sample:sub(i, i)
      vim.api.nvim_buf_set_text(bufnr, target, i - 1, target, i - 1, { ch })
      vim.wait(10)
      local _, elapsed = lib.request(bufnr, "textDocument/hover",
        lib.tdp(lib.bufuri(bufnr), target, math.max(0, i - 1)), 3000)
      table.insert(latencies, elapsed)
    end

    local p50 = lib.percentile(latencies, 50)
    local p95 = lib.percentile(latencies, 95)
    local p99 = lib.percentile(latencies, 99)
    io.stderr:write(("[uat] hover-during-typing: p50=%dms p95=%dms p99=%dms n=%d\n")
      :format(p50, p95, p99, #latencies))
    lib.assert_lt(p99, 1000,
      ("hover-during-typing p99 %dms exceeds 1000ms budget"):format(p99))
  end,
}
