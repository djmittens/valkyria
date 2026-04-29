-- Concurrent buffers: opening + editing several files in parallel
-- exercises the LSP's per-document state isolation. A regression
-- where state leaks across docs (e.g., in-string flag, AST cache
-- keyed by wrong URI) shows up here.

return {
  three_buffers_each_get_their_own_diagnostics = function(lib)
    -- Open three different fixtures, each with distinct content +
    -- distinct expected diagnostic state. Verify the LSP's
    -- per-buffer diagnostics don't mix up.
    local clean_buf = lib.open_fixture("diagnostics_clean.valk")
    lib.wait_for_lsp(clean_buf)
    -- Pace each open through the LSP. Opening 3 files in tight
    -- succession used to trigger a SIGSEGV in the GC's TLAB-refill
    -- path under suite load (publishDiagnostics evacuates onto the
    -- heap and races concurrent indexing). 100ms between opens
    -- gives the LSP time to settle each didOpen's dispatch chain.
    vim.wait(100)

    local bad_buf = lib.open_fixture("diagnostics_bad.valk")
    lib.wait_for_lsp(bad_buf)
    vim.wait(100)

    local small_buf = lib.open_fixture("small.valk")
    lib.wait_for_lsp(small_buf)

    -- Diagnostics for the bad buffer publish through lsp/edit-sys,
    -- which serializes behind any prior indexing work from earlier
    -- scenarios in the suite. 10s budget covers worst case.
    lib.wait_for_diagnostics(bad_buf, 1, 10000)

    -- Bad fixture should have ≥1 diag; clean should have 0; small
    -- should have 0.
    local bad_diags = vim.diagnostic.get(bad_buf)
    local clean_diags = vim.diagnostic.get(clean_buf)
    local small_diags = vim.diagnostic.get(small_buf)

    local bad_errors = 0
    for _, d in ipairs(bad_diags) do
      if d.severity == vim.diagnostic.severity.ERROR
         or d.severity == vim.diagnostic.severity.WARN then
        bad_errors = bad_errors + 1
      end
    end

    local clean_errors = 0
    for _, d in ipairs(clean_diags) do
      if d.severity == vim.diagnostic.severity.ERROR then
        clean_errors = clean_errors + 1
      end
    end

    lib.assert_truthy(bad_errors >= 1,
      ("bad fixture should have ≥1 error/warn, got %d"):format(bad_errors))
    lib.assert_eq(clean_errors, 0,
      ("clean fixture flagged %d errors: %s"):format(clean_errors,
        vim.inspect(vim.tbl_map(function(d) return d.message end, clean_diags))))
    -- small.valk shouldn't have errors but may have warns (unused etc.)
    local small_errors = 0
    for _, d in ipairs(small_diags) do
      if d.severity == vim.diagnostic.severity.ERROR then
        small_errors = small_errors + 1
      end
    end
    lib.assert_eq(small_errors, 0,
      ("small.valk flagged %d errors"):format(small_errors))
  end,

  hover_in_one_buffer_doesnt_use_other_buffers_text = function(lib)
    -- Open small.valk and diagnostics_clean.valk. Hover on `add`
    -- (only in small.valk) — the LSP must not return a result
    -- pointing at the OTHER buffer or use OTHER buffer's text for
    -- its lookup.
    local clean_buf = lib.open_fixture("diagnostics_clean.valk")
    lib.wait_for_lsp(clean_buf)
    local small_buf = lib.open_fixture("small.valk")
    lib.wait_for_lsp(small_buf)
    lib.wait_for_symbol_indexed(small_buf, "^add$", 3000)

    -- Hover at line+col of `add` in small.valk — this position in
    -- diagnostics_clean.valk is NOT on the symbol `double`. If the
    -- LSP looked up text from the wrong buffer it'd return wrong
    -- content (or nil).
    local line, col = lib.find_text(small_buf, "{add (square")
    local res = lib.request(small_buf, "textDocument/hover",
      lib.tdp(lib.bufuri(small_buf), line, col + 2), 5000)
    lib.assert_truthy(res, "hover in small.valk returned nil")
    local text = type(res.contents) == "string" and res.contents
                 or (res.contents and res.contents.value or "")
    lib.assert_truthy(text:find("add", 1, true),
      "hover content from wrong buffer: " .. text)
  end,
}
