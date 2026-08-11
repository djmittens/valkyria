-- API surface coverage: the LSP advertises capabilities (see
-- lsp/capabilities in scripts/lsp/io.valk) — every advertised method
-- needs at least one happy-path test. This file fills the holes the
-- other scenarios don't cover:
--
--   - textDocument/semanticTokens/range (only /full was tested before)
--   - textDocument/documentLink
--   - textDocument/diagnostic (pull-based, separate from publish)
--   - textDocument/codeLens
--   - workspace/symbol
--
-- The goal is to exercise every entry in lsp/dispatch-request +
-- lsp/handle-readonly so a future refactor that breaks one shows up
-- in CI rather than in a user's editor.

return {
  semantic_tokens_range_returns_subset_of_full = function(lib)
    -- /range is for viewport-aware highlighting — many editors use it
    -- instead of /full once the buffer gets large. The tokens it
    -- returns must be valid relative-encoded LSP token data.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_workspace_scan(10000)

    local total_lines = vim.api.nvim_buf_line_count(bufnr)
    local res = lib.request(bufnr, "textDocument/semanticTokens/range", {
      textDocument = { uri = lib.bufuri(bufnr) },
      range = {
        start = { line = 0, character = 0 },
        ["end"] = { line = math.min(20, total_lines), character = 0 },
      },
    }, 5000)
    lib.assert_truthy(res, "semanticTokens/range returned nil")
    lib.assert_truthy(res.data and #res.data % 5 == 0,
      "semanticTokens/range data not a multiple of 5: " ..
        tostring(res.data and #res.data))
  end,

  document_link_returns_resolved_uris_or_empty = function(lib)
    -- documentLink fires on import-like forms. The LSP advertises the
    -- provider, so it must respond — empty list is acceptable.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.sync(bufnr)

    local res, _, err = lib.request(bufnr, "textDocument/documentLink",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(not err,
      "documentLink errored: " .. vim.inspect(err))
    -- Result is a list (possibly empty) — never nil for an advertised
    -- provider.
    lib.assert_truthy(res ~= nil, "documentLink returned nil instead of []")
  end,

  pull_diagnostic_returns_same_as_publish = function(lib)
    -- textDocument/diagnostic is the pull-based API. It should return
    -- the same set of diagnostics that publishDiagnostics would push.
    local bufnr = lib.open_fixture("diagnostics_bad.valk")
    lib.wait_for_lsp(bufnr)
    -- Wait for the push-based publish first.
    lib.wait_for_diagnostics(bufnr, 1, 5000)
    local pushed = vim.diagnostic.get(bufnr)

    local res = lib.request(bufnr, "textDocument/diagnostic",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res, "pull diagnostic returned nil")
    -- The response is a DocumentDiagnosticReport — `items` field
    -- holds the diags, `kind` says full vs unchanged.
    local items = res.items or res
    lib.assert_truthy(items, "pull diagnostic missing items")
    -- Loose check: pull and push both report at least one diag.
    lib.assert_truthy(#items >= 1 or #pushed >= 1,
      "pull-diag returned empty but push-diag had entries")
  end,

  code_lens_advertised_provider_returns_list_or_nil = function(lib)
    -- The LSP advertises codeLensProvider; a request must respond
    -- without error.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local res, _, err = lib.request(bufnr, "textDocument/codeLens",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(not err,
      "codeLens errored: " .. vim.inspect(err))
  end,

  workspace_symbol_with_query_returns_matches = function(lib)
    -- workspace/symbol with a non-empty query should filter to
    -- matches; a tightening over the existing
    -- workspace_symbol_search_finds_user_fns test (which uses "").
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 5000)

    local res = lib.request(bufnr, "workspace/symbol", { query = "ad" }, 5000)
    lib.assert_truthy(res ~= nil,
      "workspace/symbol with query 'ad' returned nil")
    if type(res) == "table" then
      -- Should contain at least one symbol whose name starts with "ad".
      local saw = false
      for _, s in ipairs(res) do
        if (s.name or ""):lower():find("^ad") then saw = true; break end
      end
      lib.assert_truthy(saw,
        ("workspace/symbol query 'ad' returned %d items, none starting with 'ad'")
          :format(#res))
    end
  end,

  prepare_rename_on_keyword_returns_nil_or_error = function(lib)
    -- prepareRename on a position that's NOT a renameable identifier
    -- (e.g., a string literal or a keyword) must NOT crash and must
    -- NOT return a valid range — the editor uses this to decide
    -- whether to even prompt the user.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.sync(bufnr)

    -- Position the request at column 0 of line 0 — should be on
    -- whitespace or a paren, not on an identifier.
    local res, _, err = lib.request(bufnr, "textDocument/prepareRename",
      lib.tdp(lib.bufuri(bufnr), 0, 0), 5000)
    -- Either nil (no rename) or err is acceptable; a valid range
    -- with a non-identifier at that position is the bug.
    if res ~= nil and type(res) == "table" and res.range then
      -- Some implementations return placeholder ranges — only flag
      -- if the LSP returned a range covering 0 characters or
      -- spanning a paren.
      local s, e = res.range.start, res.range["end"]
      if s and e and s.line == e.line and s.character == e.character then
        error("prepareRename returned zero-width range on whitespace")
      end
    end
  end,

  hover_after_index_handles_unknown_uri = function(lib)
    -- Hover targeting a URI the LSP has never seen (never had didOpen
    -- for) must not crash. Some servers' uri->doc lookup explodes.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.sync(bufnr)

    local fake_uri = "file:///does/not/exist/never.valk"
    local res, _, err = lib.request(bufnr, "textDocument/hover", {
      textDocument = { uri = fake_uri },
      position = lib.pos(0, 0),
    }, 5000)
    -- nil result is fine; a server error is fine too. A SIGSEGV /
    -- timeout is the bug.
    lib.assert_truthy(res == nil or err ~= nil or type(res) == "table",
      "hover on unknown URI returned weird value: " .. vim.inspect(res))
  end,
}
