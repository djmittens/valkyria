-- Latency-budget scenario: pound a real file with N hovers at varied
-- positions and report median / p95. Catches the "feels slow" pain
-- point that smoke tests miss.
--
-- Budgets here are DELIBERATELY generous; they're meant to catch a
-- 10× slowdown, not micro-optimize. Tighten as the LSP improves.

return {
  hover_p95_under_load = function(lib)
    local bufnr = lib.open_repo_file("scripts/lsp/io.valk")
    lib.wait_for_lsp(bufnr)
    -- Wait a beat for the workspace scan to advance; otherwise the
    -- first few hovers race the scan and skew the distribution.
    vim.wait(1500)

    -- Grab a sample of column positions from the buffer.
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local probes = {}
    local rng = math.random
    math.randomseed(42)  -- deterministic
    for _ = 1, 50 do
      local l = rng(1, #lines)
      local line = lines[l]
      if #line > 0 then
        table.insert(probes, { l - 1, rng(0, #line - 1) })
      end
    end

    local latencies = {}
    for _, p in ipairs(probes) do
      local _, ms = lib.request(bufnr, "textDocument/hover",
        lib.tdp(lib.bufuri(bufnr), p[1], p[2]), 5000)
      table.insert(latencies, ms)
    end

    local p50 = lib.percentile(latencies, 50)
    local p95 = lib.percentile(latencies, 95)
    local p99 = lib.percentile(latencies, 99)
    io.stderr:write(("[uat] hover under load: p50=%d p95=%d p99=%d ms (%d samples)\n")
      :format(p50, p95, p99, #latencies))
    lib.assert_lt(p95, 200, "hover p95 too slow")
    lib.assert_lt(p99, 500, "hover p99 too slow")
  end,

  semantic_tokens_full_under_500ms = function(lib)
    local bufnr = lib.open_repo_file("scripts/lsp/io.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(500)
    local _, ms = lib.request(bufnr, "textDocument/semanticTokens/full",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_lt(ms, 500,
      "semanticTokens/full on ~400-line real file too slow")
  end,
}
