-- Code actions: quick-fixes / refactors offered by the LSP for the
-- code at a given range. The LSP advertises `codeActionProvider`
-- with `codeActionKinds: ["quickfix"]`. nvim's <Leader>ca calls
-- textDocument/codeAction.
--
-- Hard to assert on action *content* without LSP-specific knowledge,
-- so the test verifies (1) the request returns a well-formed response
-- and (2) response shape is a list (possibly empty). A regression
-- that crashed the handler would surface here.

return {
  code_action_request_succeeds_on_diagnostic = function(lib)
    local bufnr = lib.open_fixture("diagnostics_bad.valk")
    lib.wait_for_lsp(bufnr)
    -- Wait for the diagnostic to publish so the codeAction context
    -- has a real diagnostic to react to.
    local diags = lib.wait_for_diagnostics(bufnr, 1, 5000)
    lib.assert_truthy(#diags > 0, "no diagnostics on bad fixture")

    -- Pick the first diagnostic and ask for code actions over its range.
    local d = diags[1]
    local lsp_diag = {
      range = {
        start = { line = d.lnum or 0, character = d.col or 0 },
        ["end"] = { line = d.end_lnum or d.lnum or 0,
                    character = d.end_col or (d.col or 0) + 1 },
      },
      severity = d.severity,
      message = d.message,
      source = d.source,
    }
    local res = lib.request(bufnr, "textDocument/codeAction", {
      textDocument = { uri = lib.bufuri(bufnr) },
      range = lsp_diag.range,
      context = { diagnostics = { lsp_diag } },
    }, 5000)
    -- Result is a list (possibly empty) of CodeAction or Command
    -- entries. nil is allowed (= "no actions"); errors aren't.
    lib.assert_truthy(res == nil or type(res) == "table",
      "codeAction returned non-list: " .. vim.inspect(res))
    if type(res) == "table" then
      for _, a in ipairs(res) do
        lib.assert_truthy(a.title, "code action missing title")
      end
    end
  end,

  code_action_request_succeeds_on_clean_code = function(lib)
    -- Code-action on a non-diagnostic location should also work
    -- (it'd return an empty list or a refactor). The handler must
    -- not crash on no-diagnostic context.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)
    local res = lib.request(bufnr, "textDocument/codeAction", {
      textDocument = { uri = lib.bufuri(bufnr) },
      range = {
        start = { line = 3, character = 0 },
        ["end"] = { line = 3, character = 0 },
      },
      context = { diagnostics = {} },
    }, 5000)
    lib.assert_truthy(res == nil or type(res) == "table",
      "codeAction crashed on no-diagnostic context: " .. vim.inspect(res))
  end,
}
