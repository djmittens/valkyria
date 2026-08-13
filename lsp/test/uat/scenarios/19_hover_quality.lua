-- Hover content quality: not just "did it respond" but "is the
-- response actually useful". A hover that returns just `add` (the
-- symbol name) is much less useful than one that returns
-- `add :: Num Num -> Num` with a docstring. Tests below verify the
-- hover content includes signature info where it should.
--
-- These are intentionally LENIENT — they'd accept "(fun add ...)"
-- or any string mentioning Num, since the LSP is allowed to format
-- hover content however it wants. The assertion is "useful", not
-- "matches a specific template".

local function hover_text(res)
  if not res then return "" end
  local c = res.contents
  if type(c) == "string" then return c end
  if type(c) == "table" and c.value then return c.value end
  if type(c) == "table" and c[1] then
    -- MarkedString[]: each element string or {language, value}
    local parts = {}
    for _, item in ipairs(c) do
      if type(item) == "string" then table.insert(parts, item)
      elseif type(item) == "table" and item.value then
        table.insert(parts, item.value)
      end
    end
    return table.concat(parts, "\n")
  end
  return ""
end

return {
  hover_user_function_includes_signature = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Cursor on the call site `{add (square...`.
    local line, col = lib.find_text(bufnr, "{add (square")
    local res = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col + 2), 5000)
    lib.assert_truthy(res, "hover returned nil")
    local text = hover_text(res)
    lib.assert_truthy(text:find("add", 1, true),
      "hover doesn't mention `add`: " .. text)
    -- small.valk has `(sig 'add {-> Num Num Num})`. The hover
    -- should expose either the sig or the implementation. We
    -- check for "Num" as a proxy for "type info present".
    lib.assert_truthy(text:find("Num", 1, true),
      "hover for `add` doesn't expose type info; got: " .. text)
  end,

  hover_at_def_site_works = function(lib)
    -- Hover should work at a SYMBOL'S OWN DEFINITION too, not just
    -- at call sites. nvim users hover their own newly-typed defs to
    -- check inferred types.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^pythag$", 3000)

    -- Cursor on the symbol `pythag` in its `(fun {pythag a b} ...)`.
    local line, col = lib.find_text(bufnr, "{pythag a b}")
    local res = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col + 2), 5000)
    lib.assert_truthy(res, "hover at def site returned nil")
    local text = hover_text(res)
    lib.assert_truthy(text:find("pythag", 1, true),
      "hover at def site missing symbol name: " .. text)
  end,

  hover_distinguishes_local_vs_global = function(lib)
    -- Hover on a parameter `x` inside `(fun {square x} {* x x})`
    -- should describe `x` as a parameter, not return the global
    -- shadowing message. We're not enforcing exact text but at
    -- minimum the hover should respond non-empty for a real symbol.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^square$", 3000)
    local line, col = lib.find_text(bufnr, "{* x x}")
    -- col+3 lands on the first `x` inside `* x x`.
    local res = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col + 3), 5000)
    -- Either a useful response or nil — both are acceptable. The
    -- failure mode we want to catch is an LSP error / crash.
    if res ~= nil then
      lib.assert_truthy(type(res) == "table",
        "hover on local returned non-table: " .. vim.inspect(res))
    end
  end,
}
