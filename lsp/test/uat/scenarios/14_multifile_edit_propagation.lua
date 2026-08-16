-- Editing one file must propagate to other files' diagnostics and
-- completion. Specifically: deleting a symbol from the dependency should
-- make the caller's call site fail to resolve. Adding a new symbol in
-- the dependency should make it visible to the caller's completion.
--
-- This is the hardest LSP correctness case because it requires:
--   1. didSave on the dependency → re-index it in symdb
--   2. Cross-file diagnostics on the caller to recompute (either via
--      file-watcher, didChangeWatchedFiles, or LSP server-internal
--      invalidation)
--
-- **Isolation:** these tests mutate their dependency file, so they own a
-- private pair (fixtures/prop_dep.valk + fixtures/prop_caller.valk)
-- rather than sharing multi/. Mutating multi/utils.valk here leaked into
-- 13_multifile_navigation / 15_rename / 23_lifecycle, making those pass
-- or fail depending on execution order.
--
-- The pair lives in fixtures/ (not written at runtime) on purpose: it has
-- to be present before nvim starts so the server's startup workspace scan
-- indexes it from disk. That scan is what exposed the duplicate-file-row
-- bug where a symlinked workspace root produced two `files` rows per file
-- and deleted symbols stayed resolvable forever.

-- NOTE: the deleted symbol's basename must be unique across the whole
-- fixture workspace. The validator's vd/is-known-by-basename resolves
-- `a/foo` if ANY indexed symbol ends in `/foo`, so naming this
-- `prop/clamp` would silently resolve against multi/utils.valk's
-- `utils/clamp` and the "now undefined" assertion could never fire.
local DEP = "prop_dep.valk"
local CALLER = "prop_caller.valk"

-- Restored before each test so neither inherits the other's mutations.
-- Must stay byte-identical to fixtures/prop_dep.valk.
local DEP_FULL = table.concat({
  "(sig 'prop/double {-> Num Num})",
  "(fun {prop/double x} {* x 2})",
  "",
  "(sig 'prop/triple {-> Num Num})",
  "(fun {prop/triple x} {* x 3})",
  "",
  "(sig 'prop/zorble {-> Num Num Num Num})",
  "(fun {prop/zorble x lo hi}",
  "  {if (< x lo) lo",
  "    {if (> x hi) hi {x}}})",
  "",
}, "\n")

local CALLER_SRC = table.concat({
  '(load "' .. DEP .. '")',
  "",
  "(def {a} (prop/double 21))",
  "(def {b} (prop/triple 14))",
  "(def {c} (prop/zorble 50 0 100))",
  "",
  "(def {sum} (+ a (+ b c)))",
  "",
}, "\n")

local function reset_dep(lib)
  lib.write_temp(DEP, DEP_FULL)
  lib.write_temp(CALLER, CALLER_SRC)
  -- Open + save the dependency so the server indexes the restored
  -- content before the test starts mutating it.
  local buf = lib.open_fixture(DEP)
  lib.wait_for_lsp(buf)
  lib.save_buffer(buf)
  lib.require_symbol_indexed(buf, "^prop/zorble$", 5000)
  return buf
end

return {
  remove_symbol_from_one_file_breaks_caller = function(lib)
    local dep_buf = reset_dep(lib)

    local caller_buf = lib.open_fixture(CALLER)
    lib.wait_for_lsp(caller_buf)
    -- prop/double lives in the dependency, so this is a workspace-index wait.
    lib.require_workspace_symbol(caller_buf, "prop/double", 5000)

    -- Delete prop/zorble from the dependency and save.
    lib.replace_all(dep_buf, table.concat({
      "(sig 'prop/double {-> Num Num})",
      "(fun {prop/double x} {* x 2})",
      "",
      "(sig 'prop/triple {-> Num Num})",
      "(fun {prop/triple x} {* x 3})",
      "",
    }, "\n"))
    lib.save_buffer(dep_buf)
    -- Wait for the deletion to actually land in the index instead of guessing
    -- at 800ms: the definition disappearing is the precondition for the
    -- diagnostic we are about to assert.
    lib.wait_for_symbol_gone(dep_buf, "^prop/zorble$", 5000)

    -- The caller still references prop/zorble. Reopening it should now
    -- produce a diagnostic for the missing symbol.
    local caller_buf2 = lib.open_fixture(CALLER)
    lib.wait_for_lsp(caller_buf2)
    local diags = lib.wait_for_diagnostic_containing(caller_buf2, "prop/zorble", 5000)
    local saw_clamp_err = false
    for _, d in ipairs(diags) do
      if (d.message or ""):find("prop/zorble", 1, true) then
        saw_clamp_err = true; break
      end
    end
    lib.assert_truthy(saw_clamp_err,
      ("expected diagnostic for now-undefined prop/zorble in the caller; got: %s"
       ):format(vim.inspect(vim.tbl_map(function(d) return d.message end, diags))))
  end,

  add_symbol_in_one_file_visible_in_caller_completion = function(lib)
    local dep_buf = reset_dep(lib)

    -- Add a new function `prop/quadruple` and save.
    lib.append_line(dep_buf, "")
    lib.append_line(dep_buf, "(sig 'prop/quadruple {-> Num Num})")
    lib.append_line(dep_buf, "(fun {prop/quadruple x} {* x 4})")
    lib.save_buffer(dep_buf)
    lib.require_symbol_indexed(dep_buf, "^prop/quadruple$", 5000)

    -- Now open the caller and ask for completion at a fresh `(prop/qu`.
    local caller_buf = lib.open_fixture(CALLER)
    lib.wait_for_lsp(caller_buf)
    -- Cross-file: defined in the dependency, so poll the workspace index.
    lib.require_workspace_symbol(caller_buf, "prop/quadruple", 5000)

    local last = vim.api.nvim_buf_line_count(caller_buf)
    vim.api.nvim_buf_set_lines(caller_buf, last, last, false, { "(prop/qu" })
    lib.sync(caller_buf)

    local res = lib.request(caller_buf, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(caller_buf) },
      position = lib.pos(last, 8),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    local found = false
    for _, it in ipairs(items or {}) do
      if (it.label or it) == "prop/quadruple" then found = true; break end
    end
    lib.assert_truthy(found,
      ("completion at (prop/qu doesn't include prop/quadruple; got %d items"
       ):format(items and #items or 0))
  end,
}
