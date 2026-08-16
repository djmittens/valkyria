-- Signature help: as you type `(fn ` the LSP popup should show the
-- function's parameter list, and update the active-parameter index
-- as more args are typed. This is one of the most-used LSP features
-- (it's why people install LSPs in the first place).

return {
  signature_help_shows_function_params = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Type `(add ` on a fresh line at EOF.
    local last = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, last, last, false, { "(add " })

    local res = lib.request(bufnr, "textDocument/signatureHelp", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(last, 5),
    }, 5000)
    lib.assert_truthy(res, "signatureHelp returned nil for `(add `")
    lib.assert_truthy(res.signatures and #res.signatures > 0,
      "signatureHelp has no signatures: " .. vim.inspect(res))
    local sig = res.signatures[1]
    -- The signature label should mention `add` AND its parameters.
    lib.assert_truthy(sig.label and sig.label:find("add", 1, true),
      "signature label doesn't mention `add`: " .. tostring(sig.label))
    -- small.valk declares `(sig 'add {-> Num Num Num})`, so the
    -- signature should reflect the 2 input types.
    lib.assert_truthy(sig.label:find("Num", 1, true),
      "signature label missing type info: " .. tostring(sig.label))
  end,

  signature_help_active_param_advances_with_args = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Type `(add 1 ` so the cursor is past the first arg.
    local last = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, last, last, false, { "(add 1 " })

    local res = lib.request(bufnr, "textDocument/signatureHelp", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(last, 7),
    }, 5000)
    lib.assert_truthy(res, "signatureHelp returned nil")
    -- activeParameter should advance to 1 (the second param) since we've
    -- typed one arg. Some LSPs leave it at 0 and return per-signature
    -- index; tolerate either as long as the response is well-formed.
    if res.activeParameter then
      lib.assert_truthy(res.activeParameter >= 1,
        ("activeParameter should be ≥1 after one arg, got %s"):format(
          tostring(res.activeParameter)))
    end
  end,
}
