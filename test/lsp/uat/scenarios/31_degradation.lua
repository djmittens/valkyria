-- Degradation tests: pin down whether the LSP gets slower as a session
-- progresses. A fresh LSP responds in <100ms; the user's complaint
-- "editing experience is bad" points at something that builds up over
-- minutes of work — async-handle leaks, dict bloat, GC pressure,
-- worker-queue depth, or symdb-query-time growth on accumulated rows.
--
-- These tests run a workload at two points and assert the second
-- isn't dramatically slower than the first. Catches regressions that
-- look fine in 1-shot benchmarks but bite real users.

local function mean(t)
  if #t == 0 then return 0 end
  local s = 0; for _, v in ipairs(t) do s = s + v end
  return s / #t
end

local function measure_hover_burst(lib, bufnr, line, col, n)
  local lat = {}
  for _ = 1, n do
    local _, elapsed = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col), 5000)
    table.insert(lat, elapsed)
  end
  return lat
end

return {
  hover_latency_does_not_degrade_after_open_close_churn = function(lib)
    -- Open and close 30 distinct buffers, then measure hover
    -- latency on a fresh-opened buffer. If close-time cleanup is
    -- incomplete, dict entries / async handles accumulate and
    -- subsequent hovers slow down.
    local baseline = lib.open_fixture("small.valk")
    lib.wait_for_lsp(baseline)
    lib.wait_for_symbol_indexed(baseline, "^add$", 3000)
    local line, col = lib.find_text(baseline, "(square a)")

    -- Baseline measurement.
    local lat_before = measure_hover_burst(lib, baseline, line, col + 1, 10)

    -- Churn: write/open/close 30 unique temp files.
    for i = 1, 30 do
      local p = lib.write_temp(("churn_%d.valk"):format(i),
        ("(def {item_%d} %d)\n"):format(i, i))
      local b = lib.open_path(p)
      lib.wait_for_lsp(b)
      vim.wait(20)
      lib.close_buffer(b)
      vim.wait(10)
    end

    -- Re-open baseline and let the async pipeline QUIESCE before measuring:
    -- the churn's 30 publishDiagnostics arrive asynchronously and are
    -- processed on nvim's main loop; measuring while they drain times
    -- nvim's redraw queue, not the server (server threads are idle in
    -- epoll throughout — verified by stack sampling). A true server leak
    -- degrades permanently and is still caught after the drain.
    local baseline2 = lib.open_fixture("small.valk")
    lib.wait_for_lsp(baseline2)
    vim.wait(1500)
    local lat_after = measure_hover_burst(lib, baseline2, line, col + 1, 10)

    local before_p99 = lib.percentile(lat_before, 99)
    local after_p99 = lib.percentile(lat_after, 99)
    io.stderr:write(("[uat] hover-degradation: before-p99=%.0fms after-p99=%.0fms (%.1fx)\n")
      :format(before_p99, after_p99, after_p99 / math.max(before_p99, 1)))
    -- Generous bound: degrade by at most 5x. If the LSP had a true
    -- leak, you'd see 100x quickly.
    lib.assert_truthy(after_p99 < before_p99 * 5 + 200,
      ("hover degraded %.1fx (%.0fms -> %.0fms) after 30-buffer churn")
        :format(after_p99 / math.max(before_p99, 1), before_p99, after_p99))
  end,

  semantic_tokens_does_not_degrade_after_edit_burst = function(lib)
    -- Same idea but for semantic tokens after an edit storm.
    -- Token recomputation depends on the AST cache + last-good
    -- cache; if those grow, latency creeps up.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(500)

    local function measure(n)
      local lat = {}
      for _ = 1, n do
        local _, elapsed = lib.request(bufnr, "textDocument/semanticTokens/full",
          { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
        table.insert(lat, elapsed)
      end
      return lat
    end

    local before = measure(5)

    -- 100 single-char edits at a benign location.
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, n, n, false, { "" })
    for i = 1, 100 do
      local ch = ((i % 26) + 96)  -- a-z cycling
      vim.api.nvim_buf_set_text(bufnr, n, 0, n, 0, { string.char(ch) })
      vim.wait(5)
    end
    vim.wait(300)  -- let cache catch up

    local after = measure(5)
    local before_p50 = lib.percentile(before, 50)
    local after_p50 = lib.percentile(after, 50)
    io.stderr:write(("[uat] semtok-degradation: before-p50=%.0fms after-p50=%.0fms\n")
      :format(before_p50, after_p50))
    lib.assert_truthy(after_p50 < before_p50 * 4 + 200,
      ("semanticTokens degraded after 100 edits: %.0fms -> %.0fms")
        :format(before_p50, after_p50))
  end,

  sustained_hover_burst_completes_within_budget = function(lib)
    -- 200 hovers in tight succession on a single buffer. p99 must
    -- stay reasonable; total wall time bounds throughput.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)
    local line, col = lib.find_text(bufnr, "(square a)")
    local tdp = lib.tdp(lib.bufuri(bufnr), line, col + 1)

    local t0 = vim.uv.hrtime()
    local lat = {}
    for _ = 1, 200 do
      local _, elapsed = lib.request(bufnr, "textDocument/hover", tdp, 3000)
      table.insert(lat, elapsed)
    end
    local total = (vim.uv.hrtime() - t0) / 1e6
    local p99 = lib.percentile(lat, 99)
    io.stderr:write(("[uat] sustained-hover: 200 reqs total=%.0fms p99=%.0fms throughput=%.0freq/s\n")
      :format(total, p99, 200 / total * 1000))
    lib.assert_lt(p99, 500,
      ("sustained hover p99 %.0fms exceeds 500ms"):format(p99))
  end,
}
