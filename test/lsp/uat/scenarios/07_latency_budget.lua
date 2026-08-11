-- Latency-budget scenario: pound a real file with N hovers at varied
-- positions and report median / p95. Catches the "feels slow" pain
-- point that smoke tests miss.
--
-- Budgets here are DELIBERATELY generous; they're meant to catch a
-- 10× slowdown, not micro-optimize. Tighten as the LSP improves.

-- Latency scenario: asserts wall-clock budgets / percentiles, so it must run
-- on an otherwise idle machine. The runner keeps these out of the parallel
-- shards and runs them alone afterwards; measured under 4-way contention the
-- budgets stop describing anything a user would experience.
return {
  _latency = true,

  hover_p95_under_load = function(lib)
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    -- The first hovers must not race the workspace scan or they skew the
    -- distribution. Wait for the scan to actually report completion.
    lib.wait_for_workspace_scan(10000)

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
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_workspace_scan(10000)
    local _, ms = lib.request(bufnr, "textDocument/semanticTokens/full",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_lt(ms, 500,
      "semanticTokens/full on ~400-line real file too slow")
  end,
}
