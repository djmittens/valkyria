-- Realistic user-input scenarios. Unlike the rest of the suite, these
-- use `nvim_input` / `nvim_feedkeys` instead of `nvim_buf_set_text` so
-- nvim's full input pipeline fires (TextChangedI, InsertCharPre,
-- InsertEnter, the LSP client's deferred-on-lines, completion-popup
-- triggers, etc.). They also measure WALL TIME from input to a visible
-- effect rather than LSP request RTT.
--
-- A user feels lag when their keystroke takes >50ms to render or when
-- a follow-up cue (completion popup, diagnostic clear, hover update)
-- arrives too late to be useful. Sync request RTT, which the rest of
-- the suite measures, doesn't catch either of those — it measures
-- only the LSP's own response time, not the editor pipeline including
-- autocmd cascades, on_lines debouncing, and worker-pool serialization.

local function now_ms()
  return vim.uv.hrtime() / 1e6
end

local function mean(t)
  if #t == 0 then return 0 end
  local s = 0; for _, v in ipairs(t) do s = s + v end
  return s / #t
end

-- Type a string by feeding individual characters through nvim_input,
-- letting the event loop process between each. Returns the per-key
-- elapsed times so the caller can compute distribution.
local function type_chars(s)
  local lat = {}
  for i = 1, #s do
    local t0 = now_ms()
    vim.api.nvim_input(s:sub(i, i))
    -- Yield to the event loop briefly so on_lines, autocmds, and any
    -- LSP didChange notifications get a chance to flush. 2ms matches
    -- the practical resolution of vim.wait — anything smaller still
    -- waits at least one tick.
    vim.wait(2)
    table.insert(lat, now_ms() - t0)
  end
  return lat
end

-- Feed termcode-aware input (handles <CR>, <Esc>, etc.) and run it
-- synchronously. Mode "nx" = no-remap + execute-now, which is the
-- closest equivalent to a real keystroke being processed inline. In
-- `nvim --headless -l` mode the input loop only runs when we yield,
-- so without "x" the keys sit in the typeahead and never fire.
local function feed(keys)
  local termcodes = vim.api.nvim_replace_termcodes(keys, true, false, true)
  vim.api.nvim_feedkeys(termcodes, "nx", false)
end

return {
  insert_mode_typing_does_not_block_main_thread = function(lib)
    -- The "typing lag" complaint. User opens a file, enters insert
    -- mode, types fluently. Measure the latency of each keystroke
    -- through nvim_input → on_lines callbacks → LSP didChange
    -- notification → return.
    --
    -- The LSP's didChange handler runs ON nvim's main thread (it's
    -- registered as an on_lines callback). If it does heavy work
    -- inline, every keystroke pays that cost. The fix is to keep
    -- handle-did-change as light as possible — just doc-store +
    -- dispatch, no parse / index inline.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(500)

    -- Position cursor at end of buffer and enter insert mode. Append
    -- a fresh line so we're not editing existing content.
    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })
    feed("Go")  -- open new line below in insert mode

    -- Type a non-trivial expression character-by-character.
    local sample = "(def {scratch} (+ 1 2 3 4 5 6 7 8 9 10))"
    local latencies = type_chars(sample)

    -- Exit insert mode so subsequent tests start in a known state.
    feed("<Esc>")
    vim.wait(20)

    local p50 = lib.percentile(latencies, 50)
    local p95 = lib.percentile(latencies, 95)
    local p99 = lib.percentile(latencies, 99)
    local m = mean(latencies)
    io.stderr:write(("[uat] insert-mode-typing: mean=%.1fms p50=%.1fms p95=%.1fms p99=%.1fms n=%d\n")
      :format(m, p50, p95, p99, #latencies))

    -- A keystroke that takes >50ms is visible lag. p95 > 50ms means
    -- 1 in 20 keys feels sticky. Real users notice this.
    lib.assert_lt(p95, 50,
      ("typing p95 %.1fms exceeds 50ms perceived-lag threshold"):format(p95))
  end,

  diagnostic_clears_within_user_attention_span = function(lib)
    -- The "diagnostic doesn't clear" complaint. User has bad code,
    -- LSP reports it. User fixes it. The red squiggle MUST disappear
    -- within ~500ms or the user thinks "it's still broken" and
    -- re-checks the code.
    local bufnr = lib.open_fixture("diagnostics_clean.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(300)

    -- Introduce an error by typing in insert mode at EOF.
    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })
    feed("Go(undefined-fn 1 2)<Esc>")
    vim.wait(150)  -- let didChange + dispatch fire

    -- Wait for the diagnostic to appear.
    local appeared = lib.wait_for_diagnostics(bufnr, 1, 3000)
    lib.assert_truthy(#appeared >= 1,
      "no diagnostic appeared after introducing undefined symbol")

    -- Now fix the error: delete the bad line entirely. Time how long
    -- it takes for the diagnostic to clear.
    local t0 = now_ms()
    vim.api.nvim_buf_set_lines(bufnr, n, n + 1, false, {})
    vim.wait(20)

    local cleared = lib.wait_for_diagnostics(bufnr, 0, 3000)
    local elapsed = now_ms() - t0
    io.stderr:write(("[uat] diag-clear-after-fix: %.0fms\n"):format(elapsed))

    local errors = 0
    for _, d in ipairs(cleared) do
      if d.severity == vim.diagnostic.severity.ERROR then errors = errors + 1 end
    end
    lib.assert_eq(errors, 0,
      "diagnostic still showing 3s after fix: " ..
        vim.inspect(vim.tbl_map(function(d) return d.message end, cleared)))
    lib.assert_lt(elapsed, 1000,
      ("diagnostic took %.0fms to clear (>1s feels broken)"):format(elapsed))
  end,

  completion_appears_within_typing_rhythm = function(lib)
    -- The "completion stale/slow" complaint. User starts typing a
    -- known symbol; completion menu MUST be ready before they finish
    -- typing the next char (~150ms typing rhythm). Otherwise the menu
    -- pops up showing pre-keystroke results, and the user's already
    -- typing past it.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Type `(ad` and immediately request completion. Repeat 10x to
    -- get a latency distribution — first run is cold-cache, later
    -- runs hit any caching paths.
    local latencies = {}
    local found_add = 0
    for run = 1, 10 do
      vim.api.nvim_set_current_buf(bufnr)
      local n = vim.api.nvim_buf_line_count(bufnr)
      vim.api.nvim_buf_set_lines(bufnr, n, n, false, { "" })
      vim.api.nvim_win_set_cursor(0, { n + 1, 0 })

      -- Type prefix in insert mode.
      feed("i(ad")
      vim.wait(20)

      -- Fire completion immediately, measure RTT.
      local t0 = now_ms()
      local res = lib.request(bufnr, "textDocument/completion", {
        textDocument = { uri = lib.bufuri(bufnr) },
        position = lib.pos(n, 3),
        context = { triggerKind = 2, triggerCharacter = "d" },
      }, 1500)
      table.insert(latencies, now_ms() - t0)

      feed("<Esc>")
      vim.wait(20)

      local items = res
      if type(res) == "table" and res.items then items = res.items end
      if type(items) == "table" then
        for _, it in ipairs(items) do
          if (it.label or it) == "add" then found_add = found_add + 1; break end
        end
      end
    end

    local p50 = lib.percentile(latencies, 50)
    local p95 = lib.percentile(latencies, 95)
    io.stderr:write(("[uat] completion-after-typing: p50=%.0fms p95=%.0fms add-found=%d/10\n")
      :format(p50, p95, found_add))

    -- p95 < 200ms keeps completion within typing rhythm. Most editors
    -- pop the menu after ~200ms so this is the user-perceptible bound.
    lib.assert_lt(p95, 200,
      ("completion p95 %.0fms exceeds typing-rhythm budget"):format(p95))
    -- Stale completion (missing `add` because the index lagged) is
    -- the worst UX bug — user types `add` thinking it'll autocomplete
    -- and gets nothing.
    lib.assert_truthy(found_add >= 8,
      ("completion stale: only %d/10 included `add`"):format(found_add))
  end,

  hover_reflects_just_edited_text = function(lib)
    -- The "hover wrong" complaint. After editing, hover MUST reflect
    -- the new state — a stale hover that shows pre-edit signature is
    -- worse than no hover at all because the user trusts it.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Append a uniquely-named function via real input.
    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })
    feed("Go(sig 'frobnicate {-> Num Num})<CR>(fun {frobnicate x} {* x x})<Esc>")
    vim.wait(300)  -- let the LSP catch up

    -- Hover on the `frobnicate` we just typed. Find its position.
    local line, col
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    for i, l in ipairs(lines) do
      local s = l:find("frobnicate", 1, true)
      if s then line, col = i - 1, s - 1; break end
    end
    lib.assert_truthy(line ~= nil, "couldn't locate `frobnicate` in buffer")

    -- Retry hover up to 3x with a 200ms gap because the LSP may
    -- still be indexing. The point is: it should resolve QUICKLY.
    local hover_text = nil
    for _ = 1, 3 do
      local res = lib.request(bufnr, "textDocument/hover",
        lib.tdp(lib.bufuri(bufnr), line, col + 2), 2000)
      if res and res.contents then
        local content = type(res.contents) == "string"
                          and res.contents
                          or (res.contents.value or "")
        if content:find("frobnicate", 1, true) then
          hover_text = content
          break
        end
      end
      vim.wait(200)
    end

    lib.assert_truthy(hover_text,
      "hover on just-typed `frobnicate` returned wrong content or nil; " ..
      "the LSP didn't index the new function fast enough for hover to be useful")
  end,

  typing_during_pending_heavy_request_stays_responsive = function(lib)
    -- The "editor freezes during typing" complaint. Fire a heavy LSP
    -- request (semanticTokens/full on a big file), then type chars.
    -- The typing itself should NOT slow down — nvim's main thread
    -- shouldn't be waiting for the LSP response.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(500)

    -- Fire a heavy request async; don't drain it.
    local doc = { textDocument = { uri = lib.bufuri(bufnr) } }
    local t = lib.request_async(bufnr, "textDocument/semanticTokens/full", doc)

    -- Type 30 chars in insert mode, measure per-key latency.
    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })
    feed("Go")
    local sample = "(def {while_busy} (+ 1 2 3 4 5 6))"
    local latencies = type_chars(sample)
    feed("<Esc>")
    vim.wait(20)

    -- Drain the heavy request so we don't leak a pending ticket.
    lib.drain_responses({ t }, 10000)

    local p95 = lib.percentile(latencies, 95)
    local p99 = lib.percentile(latencies, 99)
    io.stderr:write(("[uat] typing-during-heavy-req: p95=%.1fms p99=%.1fms\n")
      :format(p95, p99))

    -- A heavy LSP request must NOT block typing. p95 > 50ms means
    -- the user's typing pipeline is sharing a thread with the LSP.
    lib.assert_lt(p95, 75,
      ("typing p95 %.1fms while heavy LSP request pending — main thread is blocked")
        :format(p95))
  end,
}
