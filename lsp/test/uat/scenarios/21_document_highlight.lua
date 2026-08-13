-- Document highlight: when the cursor sits on a symbol, the LSP
-- returns ranges for OTHER occurrences of that symbol in the same
-- buffer so the editor can highlight them. Different from references
-- (which is workspace-wide); this is buffer-local.

return {
  document_highlight_finds_all_uses_in_file = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^square$", 3000)

    -- Cursor on the call site `(square a)` in pythag's body.
    local line, col = lib.find_text(bufnr, "(square a)")
    local res = lib.request(bufnr, "textDocument/documentHighlight",
      lib.tdp(lib.bufuri(bufnr), line, col + 2), 5000)
    lib.assert_truthy(res, "documentHighlight returned nil")
    -- small.valk references `square` at: sig line, fun line, two
    -- call sites in `(pythag a b)`. Expect at least 2 highlights
    -- (some LSPs may exclude the cursor's own location).
    lib.assert_truthy(#res >= 2,
      ("documentHighlight returned only %d ranges; expected ≥2"):format(#res))
    for _, h in ipairs(res) do
      lib.assert_truthy(h.range and h.range.start and h.range["end"],
        "documentHighlight entry missing range: " .. vim.inspect(h))
    end
  end,
}
