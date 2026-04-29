-- Editing one file must propagate to other files' diagnostics and
-- completion. Specifically: deleting a symbol from utils.valk should
-- make main.valk's call site fail to resolve. Adding a new symbol
-- in utils.valk should make it visible to main.valk completion.
--
-- This is the hardest LSP correctness case because it requires:
--   1. didSave on utils.valk → re-index utils.valk in symdb
--   2. Cross-file diagnostics on main.valk to recompute (either via
--      file-watcher, didChangeWatchedFiles, or LSP server-internal
--      invalidation)

return {
  remove_symbol_from_one_file_breaks_caller = function(lib)
    local main_buf = lib.open_fixture("multi/main.valk")
    lib.wait_for_lsp(main_buf)
    lib.wait_for_symbol_indexed(main_buf, "^utils/double$", 5000)

    -- Open utils.valk in another buffer and delete utils/clamp.
    local utils_buf = lib.open_fixture("multi/utils.valk")
    lib.wait_for_lsp(utils_buf)
    -- Replace its content with a version missing utils/clamp.
    lib.replace_all(utils_buf, table.concat({
      "(sig 'utils/double {-> Num Num})",
      "(fun {utils/double x} {* x 2})",
      "",
      "(sig 'utils/triple {-> Num Num})",
      "(fun {utils/triple x} {* x 3})",
      "",
    }, "\n"))
    lib.save_buffer(utils_buf)
    vim.wait(800)  -- let cross-file index update

    -- main.valk still references utils/clamp. Reopening it should
    -- now produce a diagnostic for the missing symbol. We poll
    -- vim.diagnostic up to 5s; if no error appears we record it
    -- as a known limitation rather than a hard failure (the LSP
    -- may not actively repush diagnostics on workspace events
    -- without an explicit didChange on main.valk).
    local main_buf2 = lib.open_fixture("multi/main.valk")
    lib.wait_for_lsp(main_buf2)
    local diags = lib.wait_for_diagnostics(main_buf2, 1, 5000)
    -- Soft assertion: at least the call to `utils/clamp` should be
    -- flagged as undefined. If diagnostics are empty, that's a real
    -- LSP gap we want exposed.
    local saw_clamp_err = false
    for _, d in ipairs(diags) do
      if (d.message or ""):find("utils/clamp", 1, true) then
        saw_clamp_err = true; break
      end
    end
    lib.assert_truthy(saw_clamp_err,
      ("expected diagnostic for now-undefined utils/clamp in main.valk; got: %s"
       ):format(vim.inspect(vim.tbl_map(function(d) return d.message end, diags))))
  end,

  add_symbol_in_one_file_visible_in_caller_completion = function(lib)
    local utils_buf = lib.open_fixture("multi/utils.valk")
    lib.wait_for_lsp(utils_buf)
    -- Add a new function `utils/quadruple` and save.
    lib.append_line(utils_buf, "")
    lib.append_line(utils_buf, "(sig 'utils/quadruple {-> Num Num})")
    lib.append_line(utils_buf, "(fun {utils/quadruple x} {* x 4})")
    lib.save_buffer(utils_buf)
    vim.wait(800)

    -- Now open main.valk and ask for completion at a fresh `(utils/qu`.
    local main_buf = lib.open_fixture("multi/main.valk")
    lib.wait_for_lsp(main_buf)
    lib.wait_for_symbol_indexed(main_buf, "^utils/quadruple$", 5000)

    local last = vim.api.nvim_buf_line_count(main_buf)
    vim.api.nvim_buf_set_lines(main_buf, last, last, false, { "(utils/qu" })
    vim.wait(80)

    local res = lib.request(main_buf, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(main_buf) },
      position = lib.pos(last, 9),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    local found = false
    for _, it in ipairs(items or {}) do
      if (it.label or it) == "utils/quadruple" then found = true; break end
    end
    lib.assert_truthy(found,
      ("completion at (utils/qu doesn't include utils/quadruple; got %d items"
       ):format(items and #items or 0))
  end,
}
