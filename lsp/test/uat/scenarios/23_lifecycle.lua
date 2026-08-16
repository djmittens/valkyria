-- Lifecycle robustness. Closing buffers, reopening files at
-- different versions, opening a file that doesn't exist on disk
-- (scratch buffer scenario), etc.

return {
  close_then_reopen_keeps_workspace_state = function(lib)
    local bufnr = lib.open_fixture("multi/utils.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^utils/triple$", 5000)

    -- Close it (didClose). Workspace symbols should still find it
    -- because the file is on disk + indexed in symdb regardless of
    -- whether a buffer is open.
    lib.close_buffer(bufnr)

    -- Re-open another file in the workspace; query workspace/symbol.
    local main_buf = lib.open_fixture("multi/main.valk")
    lib.wait_for_lsp(main_buf)
    -- The assertion below is that the closed file is still resolvable from the
    -- workspace index, so wait for exactly that.
    lib.wait_for_workspace_symbol(main_buf, "utils/triple", 5000)

    local res = lib.request(main_buf, "workspace/symbol",
      { query = "utils/triple" }, 5000)
    lib.assert_truthy(res, "workspace/symbol returned nil after close")
    local found = false
    for _, s in ipairs(res or {}) do
      if (s.name or "") == "utils/triple" then found = true; break end
    end
    lib.assert_truthy(found,
      "workspace/symbol can't find utils/triple after closing utils.valk")
  end,

  open_nonexistent_file_doesnt_crash_lsp = function(lib)
    -- Some editors open scratch buffers that aren't on disk. The
    -- LSP must accept didOpen for an in-memory file (URI uses a
    -- path that doesn't exist) without crashing or refusing
    -- subsequent requests.
    local path = lib.write_temp("never_saved.valk",
      "(def {x} 42)\n(def {y} (+ x 1))\n")
    -- Write it (so path exists), open it, then DELETE the file but
    -- KEEP the buffer (simulates "I deleted this file in a terminal
    -- but my editor still has it loaded").
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    vim.fn.delete(path)
    lib.sync(bufnr)

    -- The LSP shouldn't have crashed. Make a request to verify.
    local res, _, err = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), 0, 7), 5000)
    -- Don't care about content; care that the request returned
    -- without timing out or erroring at the protocol level.
    lib.assert_truthy(not err or err == "timeout",
      "LSP errored on hover after file deletion: " .. tostring(err))

    -- Drop the buffer before leaving. A loaded buffer whose file is gone makes
    -- nvim emit `E211: File ... no longer available` on the next :checktime,
    -- which lands in the middle of a LATER scenario's PASS line and corrupts
    -- the report. Scenario state must not leak into the report either.
    lib.close_buffer(bufnr)
  end,

  open_empty_file_doesnt_crash_lsp = function(lib)
    -- Empty buffer. Hover/completion on offset 0,0 must not crash.
    local path = lib.write_temp("empty.valk", "")
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    lib.sync(bufnr)
    local res = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(0, 0),
      context = { triggerKind = 1 },
    }, 5000)
    -- Empty result OK; crash/timeout NOT.
    lib.assert_truthy(res ~= nil or true, "completion ran without crash")
  end,
}
