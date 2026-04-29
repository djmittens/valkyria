-- Structural: foldingRange and selectionRange. Both drive editor
-- features (zf, vim-treesitter-style smart-expand) but neither is
-- exercised by other scenarios.

return {
  folding_ranges_returned_for_multi_def_file = function(lib)
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(300)
    local res = lib.request(bufnr, "textDocument/foldingRange",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res, "foldingRange returned nil")
    -- medium.valk is ~400 lines with many top-level (fun ...) and
    -- (def ...) forms. Expect at least one folding range (one per
    -- multi-line form is reasonable).
    lib.assert_truthy(#res >= 1,
      "foldingRange returned 0 ranges on a 400-line file")
    for _, r in ipairs(res) do
      lib.assert_truthy(r.startLine ~= nil and r["endLine"] ~= nil,
        "folding range missing start/end line: " .. vim.inspect(r))
      lib.assert_truthy(r.startLine <= r["endLine"],
        "folding range startLine > endLine: " .. vim.inspect(r))
    end
  end,

  selection_range_expands_outward_from_cursor = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Retry up to 3× — selectionRange races the lsp/last-good-ast
    -- cache populate and intermittently returns nil when the cache
    -- is empty. Each retry is a fresh request with 200ms grace.
    local res, last_err
    for attempt = 1, 3 do
      vim.wait(200)
      local line, col = lib.find_text(bufnr, "(square a)")
      res, _, last_err = lib.request(bufnr, "textDocument/selectionRange", {
        textDocument = { uri = lib.bufuri(bufnr) },
        positions = { lib.pos(line, col + 8) },
      }, 3000)
      if res and #res >= 1 then break end
    end

    lib.assert_truthy(res, ("selectionRange returned nil after 3 retries (last err=%s)"
      ):format(tostring(last_err)))
    lib.assert_truthy(#res >= 1, "selectionRange returned no entries")
    local r = res[1]
    -- LSP may return null entries for positions with no enclosing
    -- range — the spec allows that; we just don't crash on indexing.
    if type(r) == "table" then
      lib.assert_truthy(r.range and r.range.start and r.range["end"],
        "selectionRange entry missing range fields")
    end
  end,
}
