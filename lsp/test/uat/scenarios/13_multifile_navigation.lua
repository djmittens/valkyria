-- Multi-file navigation: goto-def, find-references, document symbols
-- across the multi/ fixture set. The LSP must index all .valk files
-- in the workspace and serve cross-file queries correctly.
--
-- These scenarios are where LSPs most commonly produce "wrong
-- answers" — single-file behavior is easier to get right than
-- cross-file because indexing depends on the workspace scan having
-- run AND on URI/path normalization being consistent.

return {
  goto_def_jumps_across_files = function(lib)
    local bufnr = lib.open_fixture("multi/main.valk")
    lib.wait_for_lsp(bufnr)
    -- utils/double is defined in utils.valk, not in this buffer, so this is a
    -- workspace-index wait — documentSymbol would never report it.
    lib.require_workspace_symbol(bufnr, "utils/double", 5000)

    local line, col = lib.find_text(bufnr, "(utils/double 21)")
    local res = lib.request(bufnr, "textDocument/definition",
      lib.tdp(lib.bufuri(bufnr), line, col + 2), 5000)
    lib.assert_truthy(res, "goto-def returned nil for cross-file ref")

    local locs = type(res) == "table" and res[1] and res or { res }
    if type(res) == "table" and res.uri then locs = { res } end
    local target = locs[1]
    lib.assert_truthy(target, "definition list empty")
    local target_uri = target.uri or target.targetUri
    lib.assert_truthy(target_uri:match("utils%.valk$"),
      ("goto-def landed in wrong file: %s"):format(target_uri))
  end,

  find_references_finds_uses_in_multiple_files = function(lib)
    -- Open utils.valk; find-refs on the `utils/double` definition
    -- should return uses in main.valk AND aux.valk.
    local bufnr = lib.open_fixture("multi/utils.valk")
    lib.wait_for_lsp(bufnr)

    local line, col = lib.find_text(bufnr, "{utils/double x}")
    local function refs_by_file()
      local res = lib.request(bufnr, "textDocument/references", {
        textDocument = { uri = lib.bufuri(bufnr) },
        position = lib.pos(line, col + 2),
        context = { includeDeclaration = true },
      }, 5000)
      local seen = {}
      for _, loc in ipairs(res or {}) do
        local uri = loc.uri or loc.targetUri or ""
        local file = uri:match("([^/]+)$")
        if file then seen[file] = true end
      end
      return seen
    end

    -- The call sites land in the index as the startup workspace scan
    -- progresses, so poll for the cross-file result rather than sleeping a
    -- fixed 2.5s. Retries the request itself because "references is complete"
    -- has no separate observable to wait on.
    local seen_files = select(2, lib.wait_until(function()
      local seen = refs_by_file()
      if seen["utils.valk"] and (seen["main.valk"] or seen["aux.valk"]) then
        return seen
      end
      return nil
    end, 5000, 25)) or refs_by_file()

    lib.assert_truthy(seen_files["utils.valk"], "missing ref in utils.valk")
    lib.assert_truthy(seen_files["main.valk"]
                  or seen_files["aux.valk"],
      "no cross-file references found: " .. vim.inspect(seen_files))
  end,

  document_symbols_lists_top_level_defs = function(lib)
    local bufnr = lib.open_fixture("multi/utils.valk")
    lib.wait_for_lsp(bufnr)
    -- Defined in THIS buffer, so documentSymbol is the right probe.
    lib.require_symbol_indexed(bufnr, "^utils/double$", 5000)

    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res, "documentSymbol returned nil")
    local names = {}
    for _, s in ipairs(res) do names[s.name] = true end
    -- Verify the three top-level functions appear by name.
    for _, expected in ipairs({ "utils/double", "utils/triple", "utils/clamp" }) do
      lib.assert_truthy(names[expected],
        ("documentSymbol missing %s; got %s"):format(expected, vim.inspect(names)))
    end
  end,

  workspace_symbol_search_finds_user_fns = function(lib)
    local bufnr = lib.open_fixture("multi/main.valk")
    lib.wait_for_lsp(bufnr)
    lib.require_workspace_symbol(bufnr, "utils/clamp", 5000)

    -- Cmd-T flow: query for "clamp" via workspace/symbol; expect
    -- a hit pointing at utils.valk.
    -- utils.valk is indexed asynchronously by the workspace scan, so a
    -- one-shot query can legitimately return before it lands (observed on
    -- loaded CI runners, where the sibling document_symbols assertion in
    -- this same scenario took 420ms). Poll until the cross-file hit shows
    -- up rather than asking exactly once.
    lib.require_until(function()
      local res = lib.request(bufnr, "workspace/symbol",
        { query = "clamp" }, 1000)
      if type(res) ~= "table" then return nil end
      for _, s in ipairs(res) do
        if (s.name or ""):match("clamp")
           and (s.location and s.location.uri or ""):match("utils%.valk$") then
          return true
        end
      end
      return nil
    end, "workspace/symbol clamp didn't return utils/clamp from utils.valk", 5000)
  end,
}
