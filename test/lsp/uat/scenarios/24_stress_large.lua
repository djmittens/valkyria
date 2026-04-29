-- Stress: a synthetically-large file (1000+ lines) generated at
-- runtime. Verifies the LSP handles non-trivial input within
-- reasonable budgets.

local function generate_large(n)
  local parts = {}
  for i = 1, n do
    table.insert(parts, ("(sig 'fn%d {-> Num Num})\n(fun {fn%d x} {* x %d})\n"):format(i, i, i))
  end
  return table.concat(parts, "\n")
end

return {
  large_file_indexes_within_5s = function(lib)
    local content = generate_large(500)  -- ~1500 lines after sigs
    local path = lib.write_temp("large.valk", content)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    -- One of the synthesized symbols should be in the symbol DB
    -- within 5s. If indexing is O(N²) this would time out.
    local found = lib.wait_for_symbol_indexed(bufnr, "^fn500$", 5000)
    lib.assert_truthy(found, "fn500 not indexed within 5s on 500-fn file")
  end,

  document_symbol_on_large_file_under_1s = function(lib)
    local content = generate_large(300)
    local path = lib.write_temp("large_ds.valk", content)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^fn300$", 5000)
    local _, ms = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_lt(ms, 1000,
      "documentSymbol on 300-fn file too slow")
  end,

  semantic_tokens_full_on_large_file_under_2s = function(lib)
    local content = generate_large(300)
    local path = lib.write_temp("large_sem.valk", content)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    vim.wait(500)
    local _, ms = lib.request(bufnr, "textDocument/semanticTokens/full",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_lt(ms, 2000,
      "semanticTokens/full on 300-fn file too slow")
  end,
}
