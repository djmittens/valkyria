-- Cold-start latency: time from "open file" to "LSP returns first
-- meaningful response". This is what a user feels when they open a
-- new project. Industry rule of thumb is < 2s.
--
-- Important: this is the FIRST scenario file loaded by the runner, so
-- "first response" actually measures cold-start. Subsequent scenarios
-- benefit from a warm process + cached AST.

return {
  cold_start_to_first_hover_under_2s = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    local t0 = vim.uv.hrtime()
    lib.wait_for_lsp(bufnr, 10000)
    local _, name_col = lib.find_text(bufnr, "add")
    local res, _, err = lib.request(bufnr, "textDocument/hover", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(3, name_col),  -- 0-indexed: line 3 has `(fun {add ...})`
    }, 8000)
    local total_ms = (vim.uv.hrtime() - t0) / 1e6
    lib.assert_truthy(not err, "hover error: " .. tostring(err))
    lib.assert_lt(total_ms, 2000,
      "cold-start to first hover too slow")
    -- Don't assert on the hover *content* here — that's a separate
    -- correctness scenario. Cold-start is purely a latency check.
  end,

  -- Workspace scan should not block initial responses. Open a file in
  -- a real-sized workspace (the repo itself) and verify hover works
  -- before any background scan completes. The LSP currently kicks off
  -- workspace indexing in `lsp/idx-sys`; if the user-facing path
  -- waited for that, hover would feel sluggish on every cold open.
  cold_start_workspace_scan_does_not_block = function(lib)
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr, 10000)
    local res, elapsed_ms = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), 0, 0), 5000)
    -- Hover at start-of-file may legitimately return nil (a comment),
    -- but the *response* must arrive promptly even though the workspace
    -- scan is still in progress.
    lib.assert_lt(elapsed_ms, 1500,
      "hover blocked by workspace scan")
  end,
}
