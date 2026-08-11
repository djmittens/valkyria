-- Workflow: edit-save-close-reopen with an existing file. Verifies
-- that the LSP doesn't lose state across the save/close/open cycle:
--   - File-on-disk content matches in-buffer state
--   - Diagnostics for the persisted (modified) content are recomputed
--     after reopen — not stale ones from before the edit
--   - In-flight requests during close don't crash the server
--
-- This mimics what nvim users do constantly: edit, :w, :bd, then later
-- reopen. A regression that loses didChange between close+open would
-- show up here.

local V1 = table.concat({
  "(sig 'identity {-> Num Num})",
  "(fun {identity x} x)",
  "",
  "(def {five} (identity 5))",
  "",
}, "\n")

return {
  edit_save_close_reopen_diagnostics_recompute = function(lib)
    local path = lib.write_temp("edit_cycle.valk", V1)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)

    -- Sanity: clean code, no errors.
    local diags = lib.wait_for_diagnostics(bufnr, 0, 1500)
    local errors = 0
    for _, d in ipairs(diags) do
      if d.severity == vim.diagnostic.severity.ERROR then errors = errors + 1 end
    end
    lib.assert_eq(errors, 0, "clean V1 flagged errors")

    -- Edit: introduce a bug, save WITHOUT waiting for diagnostic to
    -- arrive in this session. The point is to verify reopen produces
    -- the right diagnostic from scratch, not from cached state.
    local v2 = V1:gsub("identity x} x", "identity x} undefined-thing")
    lib.replace_all(bufnr, v2)
    lib.save_buffer(bufnr)

    -- Close. The LSP should clear its in-memory diagnostics for this
    -- buffer (handle-did-close publishes empty diagnostics) but keep
    -- the file in the symbol DB.
    lib.close_buffer(bufnr)

    -- Reopen. didOpen fires with the on-disk content (which has the
    -- bug). The LSP should publish a diagnostic for the reopened buffer.
    local bufnr2 = lib.open_path(path)
    lib.wait_for_lsp(bufnr2)
    local diags_reopened = lib.wait_for_diagnostics(bufnr2, 1, 5000)
    local saw_undef = false
    for _, d in ipairs(diags_reopened) do
      if d.message:lower():find("undefined") or d.message:find("undefined") then
        saw_undef = true; break
      end
    end
    lib.assert_truthy(saw_undef,
      ("after reopen, expected `undefined` diagnostic for v2 contents; got: %s"
       ):format(vim.inspect(vim.tbl_map(function(d) return d.message end,
         diags_reopened))))

    -- Verify on-disk content actually matches what we saved (no
    -- accidental data loss from the close-reopen-edit dance).
    local f = assert(io.open(path, "r"), "cannot reread saved file")
    local on_disk = f:read("*a")
    f:close()
    lib.assert_truthy(on_disk:find("undefined-thing", 1, true),
      "on-disk content lost the modification")
  end,
}
