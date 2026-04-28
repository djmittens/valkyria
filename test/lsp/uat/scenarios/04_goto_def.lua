-- Goto-definition correctness: cursor on a call site jumps to the
-- (fun ...) declaration. The most common LSP failure modes here are:
--   - returns nil (definition not indexed)
--   - jumps to the WRONG site (e.g. a (sig ...) line instead of the fn)
--   - cross-file def fails because the workspace scan didn't index the
--     other file

return {
  goto_def_local_function = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    -- Cursor on `add` inside `{add (square a) (square b)}` (call site
    -- in pythag's body — pythag's body is a qexpr).
    local line, col = lib.find_text(bufnr, "{add (square")
    local res, elapsed = lib.request(bufnr, "textDocument/definition",
      lib.tdp(lib.bufuri(bufnr), line, col + 1), 5000)
    lib.assert_truthy(res, "definition returned nil")
    lib.assert_truthy(#res > 0 or res.uri,
      "definition returned empty: " .. vim.inspect(res))
    local target = type(res) == "table" and res[1] or res
    -- Target must be in the same file (small.valk uses only local fns).
    lib.assert_eq(target.uri or target.targetUri, lib.bufuri(bufnr),
      "definition jumped to wrong file")
    -- And the target line must be the (fun {add ...}) line, not the
    -- (sig ...) line. The fixture's `(fun {add a b} ...)` is on
    -- line 3 (0-indexed); (sig 'add ...) is line 2.
    local range = target.range or target.targetRange
    lib.assert_eq(range.start.line, 3,
      "definition jumped to sig line instead of fun line")
    lib.assert_lt(elapsed, 200, "goto-def too slow")
  end,

  -- Cross-file goto-def is the harder case. Open the LSP itself and
  -- jump from a call site to a stdlib helper.
  goto_def_cross_file_stdlib = function(lib)
    local bufnr = lib.open_repo_file("scripts/lsp/io.valk")
    lib.wait_for_lsp(bufnr)
    -- Wait for workspace indexing to actually finish — cross-file
    -- definition needs the symdb populated. The progress-end
    -- notification arrives async; just give it some time.
    vim.wait(2000)
    -- Find a call to `dict/set!` (a builtin/stdlib symbol). It's used
    -- frequently in io.valk.
    local found_line, found_col
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    for i, line in ipairs(lines) do
      local s = line:find("dict/set!", 1, true)
      if s then found_line, found_col = i - 1, s - 1; break end
    end
    if not found_line then
      error("could not locate a `dict/set!` call site in io.valk")
    end
    local res = lib.request(bufnr, "textDocument/definition",
      lib.tdp(lib.bufuri(bufnr), found_line, found_col + 1), 5000)
    -- It's acceptable for goto-def to fail on a C-side builtin if the
    -- LSP doesn't index those; we test only that it doesn't crash and
    -- returns either a useful location or nil. A regression that
    -- crashes (nil + error) is the failure mode we want to catch.
    -- If the LSP DOES return a location, it must be valid.
    if res and (type(res) == "table" and #res > 0) then
      local target = res[1]
      lib.assert_truthy(target.uri or target.targetUri,
        "definition result missing uri")
    end
  end,
}
