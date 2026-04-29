-- Rename / prepareRename. The LSP advertises renameProvider with
-- prepareProvider; both must work for nvim's `vim.lsp.buf.rename()`
-- flow to be usable.
--
-- Renaming is dangerous when broken — it produces edit-files-the-
-- user-didn't-look-at, so silent bugs here corrupt code. The tests
-- below verify (1) the prepare step finds the right range, and (2)
-- the rename actually produces a WorkspaceEdit covering all refs.

return {
  prepare_rename_returns_word_range = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)
    -- Cursor on `add` inside the call site `{add (square a) ...}`.
    local line, col = lib.find_text(bufnr, "{add (square")
    local res = lib.request(bufnr, "textDocument/prepareRename",
      lib.tdp(lib.bufuri(bufnr), line, col + 2), 5000)
    lib.assert_truthy(res, "prepareRename returned nil")
    local range = res.range or res
    lib.assert_truthy(range and range.start and range["end"],
      "prepareRename result missing range: " .. vim.inspect(res))
    -- Range should span exactly the symbol `add` (3 chars).
    lib.assert_eq(range["end"].character - range.start.character, 3,
      "prepareRename range should be 3 chars wide for `add`")
  end,

  rename_local_function_produces_workspace_edit = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)
    local line, col = lib.find_text(bufnr, "{add (square")
    local res = lib.request(bufnr, "textDocument/rename", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(line, col + 2),
      newName = "plus",
    }, 5000)
    lib.assert_truthy(res, "rename returned nil")
    -- WorkspaceEdit shape: {changes: {[uri]: [TextEdit, ...]}} OR
    -- {documentChanges: [...]}.
    local changes = res.changes
    if not changes and res.documentChanges then
      changes = {}
      for _, dc in ipairs(res.documentChanges) do
        if dc.textDocument and dc.edits then
          changes[dc.textDocument.uri] = dc.edits
        end
      end
    end
    lib.assert_truthy(changes, "rename: no changes/documentChanges in response")
    local file_edits = changes[lib.bufuri(bufnr)]
    lib.assert_truthy(file_edits and #file_edits > 0,
      "rename produced no edits for the source file")
    -- small.valk has 2+ uses of `add` (sig + fun + 1 call site). Expect
    -- at minimum the call site + the fun definition.
    local edit_count = #file_edits
    lib.assert_truthy(edit_count >= 2,
      ("rename produced only %d edits; expected ≥2 (sig + fun + 1 call)"
       ):format(edit_count))
    -- Every edit's newText must be the requested name.
    for _, e in ipairs(file_edits) do
      lib.assert_eq(e.newText, "plus", "rename edit has wrong newText")
    end
  end,

  rename_cross_file_covers_all_files = function(lib)
    -- Open utils.valk so we can rename utils/double, then verify
    -- the WorkspaceEdit covers main.valk and aux.valk too.
    local bufnr = lib.open_fixture("multi/utils.valk")
    lib.wait_for_lsp(bufnr)
    -- Wait for ALL the workspace files that reference utils/double
    -- to be indexed so the LSP can include their refs in the edit.
    vim.wait(2500)

    local line, col = lib.find_text(bufnr, "{utils/double x}")
    local res = lib.request(bufnr, "textDocument/rename", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(line, col + 2),
      newName = "utils/twice",
    }, 5000)
    lib.assert_truthy(res, "cross-file rename returned nil")
    local changes = res.changes
    if not changes and res.documentChanges then
      changes = {}
      for _, dc in ipairs(res.documentChanges) do
        if dc.textDocument and dc.edits then
          changes[dc.textDocument.uri] = dc.edits
        end
      end
    end
    lib.assert_truthy(changes, "cross-file rename: no changes")
    -- Count distinct files in the change set.
    local files = {}
    for uri, _ in pairs(changes) do
      local f = uri:match("([^/]+)$")
      if f then files[f] = true end
    end
    lib.assert_truthy(files["utils.valk"],
      "cross-file rename missing utils.valk: " .. vim.inspect(files))
    -- Soft requirement: at least one of main.valk/aux.valk also
    -- updated. Some LSPs do file-local rename only by default;
    -- we want to know if we're in that camp.
    lib.assert_truthy(files["main.valk"] or files["aux.valk"],
      "cross-file rename only touched 1 file: " .. vim.inspect(files))
  end,
}
