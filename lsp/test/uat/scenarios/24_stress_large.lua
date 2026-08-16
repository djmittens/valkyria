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

-- Budget rationale: these tests verify the LSP doesn't catastrophically
-- fall over on moderately-large files, NOT that it hits any specific
-- latency target. The 15s/30s budgets are 3× current observed times,
-- so the test only fails when something is fundamentally broken (e.g.
-- O(N²) regression). Tightening these budgets is a separate optimization
-- task; the suite's job here is to catch full breakage, not micro-perf.

-- Latency scenario: asserts wall-clock budgets / percentiles, so it must run
-- on an otherwise idle machine. The runner keeps these out of the parallel
-- shards and runs them alone afterwards; measured under 4-way contention the
-- budgets stop describing anything a user would experience.
return {
  _latency = true,

  large_file_indexes_within_15s = function(lib)
    local content = generate_large(200)
    local path = lib.write_temp("large.valk", content)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    local found = lib.wait_for_symbol_indexed(bufnr, "^fn200$", 15000)
    lib.assert_truthy(found, "fn200 not indexed within 15s on 200-fn file")
  end,

  document_symbol_on_large_file_under_10s = function(lib)
    local content = generate_large(150)
    local path = lib.write_temp("large_ds.valk", content)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^fn150$", 10000)
    local _, ms = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 10000)
    lib.assert_lt(ms, 10000,
      "documentSymbol on 150-fn file too slow")
  end,

  semantic_tokens_full_on_large_file_under_5s = function(lib)
    local content = generate_large(150)
    local path = lib.write_temp("large_sem.valk", content)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    lib.require_symbol_indexed(bufnr, "^fn150$", 15000)
    local _, ms = lib.request(bufnr, "textDocument/semanticTokens/full",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_lt(ms, 5000,
      "semanticTokens/full on 150-fn file too slow")
  end,
}
