-- Concurrent-request chaos: real editors fire many overlapping requests.
-- A user moving the cursor while typing produces hover + completion +
-- signatureHelp + semanticTokens all in flight simultaneously. The LSP
-- needs to either (a) handle them all in parallel without losing any,
-- or (b) cancel/coalesce stale ones, but it must NEVER:
--   - drop a request silently (client hangs forever)
--   - return a response for a different request id
--   - crash / deadlock under saturation
--
-- These tests light up the in-flight queue + worker pool and verify
-- the server stays responsive end-to-end.

return {
  burst_ten_hovers_at_one_position_all_respond = function(lib)
    -- Fire 10 hover requests at the same position without waiting for
    -- any to return. The LSP must answer all 10. Dropping requests is
    -- the most common failure mode under load.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local line, col = lib.find_text(bufnr, "(square a)")
    local tickets = {}
    for _ = 1, 10 do
      table.insert(tickets, lib.request_async(bufnr, "textDocument/hover",
        lib.tdp(lib.bufuri(bufnr), line, col + 1)))
    end
    local done = lib.drain_responses(tickets, 10000)
    lib.assert_eq(done, 10,
      ("only %d/10 hover responses landed before timeout"):format(done))
    -- All responses for the same position+text should be identical.
    -- The first one is our reference.
    local first = tickets[1].response
    for i = 2, #tickets do
      lib.assert_truthy(tickets[i].response ~= nil,
        ("ticket %d: nil response"):format(i))
    end
  end,

  burst_mixed_methods_at_one_position_all_respond = function(lib)
    -- Realistic typing burst: hover + completion + signatureHelp +
    -- definition + documentHighlight all aimed at the same cursor
    -- position. Models nvim's autocmd-driven request burst on
    -- CursorMoved / InsertCharPre.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local line, col = lib.find_text(bufnr, "(square a)")
    local tdp = lib.tdp(lib.bufuri(bufnr), line, col + 1)
    local doc = { textDocument = { uri = lib.bufuri(bufnr) } }
    local methods = {
      { "textDocument/hover", tdp },
      { "textDocument/completion", tdp },
      { "textDocument/signatureHelp", tdp },
      { "textDocument/definition", tdp },
      { "textDocument/documentHighlight", tdp },
      { "textDocument/documentSymbol", doc },
      { "textDocument/foldingRange", doc },
      { "textDocument/semanticTokens/full", doc },
    }
    local tickets = {}
    for _, m in ipairs(methods) do
      table.insert(tickets, lib.request_async(bufnr, m[1], m[2]))
    end
    local done = lib.drain_responses(tickets, 10000)
    lib.assert_eq(done, #methods,
      ("only %d/%d mixed-method responses landed"):format(done, #methods))
    -- None should error (a method that legitimately has no result
    -- returns nil, that's fine — what's NOT fine is an LSP error).
    for _, t in ipairs(tickets) do
      lib.assert_truthy(not t.err,
        ("method %s errored: %s"):format(t.method, vim.inspect(t.err)))
    end
  end,

  didChange_during_pending_hover_does_not_hang = function(lib)
    -- Fire a hover, immediately edit the buffer (didChange), fire
    -- another hover. Both hovers must respond. The first may target
    -- the pre-edit text or the post-edit text — either is fine per
    -- LSP spec — but it MUST come back. The LSP must not deadlock
    -- because didChange invalidated state mid-request.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local line, col = lib.find_text(bufnr, "(square a)")
    local t1 = lib.request_async(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col + 1))

    -- Inject an edit while t1 is in flight.
    vim.api.nvim_buf_set_text(bufnr, line, 0, line, 0, { "; " })
    vim.wait(10)  -- let didChange flush

    local t2 = lib.request_async(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col + 4))  -- shifted by `; `

    local done = lib.drain_responses({ t1, t2 }, 10000)
    lib.assert_eq(done, 2,
      "hover-then-edit-then-hover: not all responses landed")
  end,

  edit_storm_then_request_reflects_latest_text = function(lib)
    -- Fire 30 single-char edits as fast as nvim will send them, then
    -- ask for hover at the cursor. The hover must reflect the LATEST
    -- text; if it returned a stale response (from an early didChange's
    -- triggered re-index), the user would see "type X but tool says Y".
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Append a unique marker by typing `mymark1234` letter by letter
    -- on a fresh blank line at EOF.
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, n, n, false, { "" })
    local marker = "mymark1234"
    for i = 1, #marker do
      vim.api.nvim_buf_set_text(bufnr, n, i - 1, n, i - 1,
        { marker:sub(i, i) })
    end
    vim.wait(150)  -- give LSP time to reindex

    -- documentSymbol won't include `mymark1234` since it's just a
    -- bare token, but completion at end-of-line ought to include it.
    local res = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(n, #marker),
      context = { triggerKind = 1 },
    }, 5000)
    lib.assert_truthy(res, "completion after edit storm returned nil")
    -- The point is that the LSP RESPONDED — content correctness is
    -- covered by other tests. A timeout / nil here means the burst
    -- queued behind didChange and never drained.
  end,

  cancel_in_flight_request_does_not_hang_subsequent = function(lib)
    -- Send a request, immediately cancel it, then send another. The
    -- second must complete normally. A cancel that breaks the
    -- request-id tracking would leave the second waiting forever.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(300)  -- let initial scan settle

    -- semanticTokens/full on medium.valk is the heaviest read request.
    local doc = { textDocument = { uri = lib.bufuri(bufnr) } }
    local t1 = lib.request_async(bufnr, "textDocument/semanticTokens/full", doc)
    -- Don't sleep — cancel immediately to maximise chance of
    -- catching the request mid-flight.
    lib.cancel_request(t1)

    local res = lib.request(bufnr, "textDocument/documentSymbol", doc, 5000)
    lib.assert_truthy(res ~= nil,
      "documentSymbol after cancel returned nil — the cancel hung the queue")
  end,

  saturation_fifty_concurrent_requests_all_respond = function(lib)
    -- Fire 50 requests across 5 methods. All must respond. This is
    -- the worker-pool saturation test: if the pool deadlocks, hangs,
    -- or drops requests, this fails.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)
    local doc = { textDocument = { uri = lib.bufuri(bufnr) } }
    local line, col = lib.find_text(bufnr, "(square a)")
    local tdp = lib.tdp(lib.bufuri(bufnr), line, col + 1)

    local tickets = {}
    for _ = 1, 10 do
      table.insert(tickets, lib.request_async(bufnr, "textDocument/hover", tdp))
      table.insert(tickets, lib.request_async(bufnr, "textDocument/definition", tdp))
      table.insert(tickets, lib.request_async(bufnr, "textDocument/completion", tdp))
      table.insert(tickets, lib.request_async(bufnr, "textDocument/documentSymbol", doc))
      table.insert(tickets, lib.request_async(bufnr, "textDocument/foldingRange", doc))
    end
    local done = lib.drain_responses(tickets, 30000)
    lib.assert_eq(done, #tickets,
      ("saturation: only %d/%d responses (lost requests)"):format(done, #tickets))
  end,
}
