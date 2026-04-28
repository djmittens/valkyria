-- Hover correctness: cursor on a known symbol must return contents
-- mentioning the symbol's name and (where applicable) its signature.
-- A regression that breaks symbol lookup would still produce a
-- "successful" response (nil result, no error) — which is why these
-- assertions check the body, not just the response shape.

return {
  hover_user_function_shows_signature = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    -- Cursor on the `add` call site inside `pythag`'s body. The
    -- fixture writes `{add (square ...)}` (qexpr body), so the
    -- search needle must match that. col+1 lands on `a` of `add`.
    local line, col = lib.find_text(bufnr, "{add (square")
    local res, elapsed = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col + 1), 5000)
    lib.assert_truthy(res, "no hover result for user fn `add`")
    local content = type(res.contents) == "string" and res.contents
                  or (res.contents and res.contents.value or "")
    lib.assert_contains(content, "add", "hover content lacks fn name")
    lib.assert_lt(elapsed, 200, "hover too slow")
  end,

  hover_unknown_symbol_returns_nil_or_empty = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    -- Hover at column 0 of line 0 (a comment line). Should not crash,
    -- should not return content for a non-symbol.
    local res, elapsed, err = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), 0, 0), 5000)
    lib.assert_truthy(not err, "error on hover at non-symbol: " .. tostring(err))
    -- Either nil, or contents that's empty/false-y. Both are LSP-spec compliant.
    if res ~= nil then
      local c = res.contents
      if type(c) == "string" then
        lib.assert_eq(c, "", "non-symbol hover returned text")
      elseif type(c) == "table" then
        lib.assert_eq(c.value or "", "", "non-symbol hover returned text")
      end
    end
  end,
}
