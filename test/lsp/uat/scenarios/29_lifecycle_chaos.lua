-- Lifecycle chaos: didOpen / didChange / didClose / didSave races.
-- Real editor sessions invariably hit these patterns:
--   - close a tab while a request is still pending
--   - rapid open-close-open of the same file (jumping definitions)
--   - save while text is mid-edit (auto-save plugins)
--   - external file replace + nvim refresh
-- The LSP must never crash, deadlock, or send a response for a
-- buffer that's been closed.
--
-- Timeouts are intentionally generous (15s) — these tests run late in
-- the suite where async-task queues are cumulatively deep, and the
-- pass criterion is "the LSP eventually responds, doesn't crash, and
-- gives a correct answer". A real user who closes/reopens/saves
-- aggressively may see a brief lag, but they SHOULD see correct
-- responses come through. Tightening these would just be flake-
-- chasing the suite-load amplification rather than measuring real
-- behavior.

return {
  close_during_pending_request_does_not_crash = function(lib)
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(300)

    -- Fire a heavy-ish request, immediately wipe the buffer.
    local doc = { textDocument = { uri = lib.bufuri(bufnr) } }
    local t = lib.request_async(bufnr, "textDocument/semanticTokens/full", doc)
    lib.close_buffer(bufnr)

    -- Open a different buffer and verify the LSP is still healthy.
    local other = lib.open_fixture("small.valk")
    lib.wait_for_lsp(other)
    local res = lib.request(other, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(other) } }, 15000)
    lib.assert_truthy(res, "LSP unresponsive after close-during-pending-request")
    -- Drain the original ticket — the response may be a Cancelled
    -- error or nil or a real result depending on timing. We just
    -- verify it lands (no zombie waiting forever).
    lib.drain_responses({ t }, 10000)
  end,

  rapid_open_close_open_same_file = function(lib)
    -- Jump-to-definition-style flow: user opens file, looks, closes,
    -- opens again. Each open/close fires didOpen/didClose; the LSP
    -- must reset its per-doc state so the second open's content is
    -- authoritative.
    for i = 1, 5 do
      local bufnr = lib.open_fixture("small.valk")
      lib.wait_for_lsp(bufnr)
      vim.wait(50)
      lib.close_buffer(bufnr)
      vim.wait(50)
    end

    -- After the cycle, the symbol table for small.valk should still
    -- be queryable.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 5000)
    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 15000)
    lib.assert_truthy(res and #res >= 1,
      "documentSymbol after open/close cycles returned empty/nil")
  end,

  save_during_pending_edit_does_not_lose_changes = function(lib)
    -- Edit, save, edit, save in rapid succession — each save fires
    -- didSave; the LSP must reflect the latest text in subsequent
    -- requests.
    local path = lib.write_temp("save_race.valk", "(def {x} 1)\n")
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    vim.wait(200)

    lib.append_line(bufnr, "(def {y} 2)")
    lib.save_buffer(bufnr)
    lib.append_line(bufnr, "(def {z} 3)")
    lib.save_buffer(bufnr)
    vim.wait(300)

    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 15000)
    lib.assert_truthy(res, "documentSymbol after rapid save returned nil")
    local names = {}
    for _, s in ipairs(res or {}) do names[s.name] = true end
    lib.assert_truthy(names["x"] and names["y"] and names["z"],
      ("rapid-save lost symbols: have x=%s y=%s z=%s")
        :format(tostring(names["x"]), tostring(names["y"]), tostring(names["z"])))
  end,

  did_open_then_did_change_before_request_is_consistent = function(lib)
    -- Open with seed content, fire didChange, then a request — make
    -- sure the request sees the post-change text.
    local path = lib.write_temp("open_change.valk", "(def {original} 1)\n")
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    vim.wait(150)

    -- Append a uniquely-named def via didChange (no save).
    lib.append_line(bufnr, "(def {new_unique_99} 2)")
    vim.wait(200)

    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 15000)
    local saw = false
    for _, s in ipairs(res or {}) do
      if s.name == "new_unique_99" then saw = true; break end
    end
    lib.assert_truthy(saw,
      "documentSymbol after didChange missing newly-added symbol")
  end,
}
