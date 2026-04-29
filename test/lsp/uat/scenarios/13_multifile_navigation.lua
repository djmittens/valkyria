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
    -- Wait for utils.valk to be indexed in the workspace.
    lib.wait_for_symbol_indexed(bufnr, "^utils/double$", 5000)

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
    -- Wait for both call sites to be indexed via workspace scan.
    -- (Each .valk file in the workspace should be scanned.)
    vim.wait(2500)

    local line, col = lib.find_text(bufnr, "{utils/double x}")
    local res = lib.request(bufnr, "textDocument/references", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(line, col + 2),
      context = { includeDeclaration = true },
    }, 5000)
    lib.assert_truthy(res, "references returned nil")
    -- Collect URIs of returned ref locations.
    local seen_files = {}
    for _, loc in ipairs(res) do
      local uri = loc.uri or loc.targetUri or ""
      local file = uri:match("([^/]+)$")
      if file then seen_files[file] = true end
    end
    lib.assert_truthy(seen_files["utils.valk"], "missing ref in utils.valk")
    lib.assert_truthy(seen_files["main.valk"]
                  or seen_files["aux.valk"],
      "no cross-file references found: " .. vim.inspect(seen_files))
  end,

  document_symbols_lists_top_level_defs = function(lib)
    local bufnr = lib.open_fixture("multi/utils.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^utils/double$", 5000)

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
    lib.wait_for_symbol_indexed(bufnr, "^utils/clamp$", 5000)

    -- Cmd-T flow: query for "clamp" via workspace/symbol; expect
    -- a hit pointing at utils.valk.
    local res = lib.request(bufnr, "workspace/symbol",
      { query = "clamp" }, 5000)
    lib.assert_truthy(res, "workspace/symbol returned nil")
    local found = false
    for _, s in ipairs(res) do
      if (s.name or ""):match("clamp")
         and (s.location and s.location.uri or ""):match("utils%.valk$") then
        found = true; break
      end
    end
    lib.assert_truthy(found,
      "workspace/symbol clamp didn't return utils/clamp from utils.valk")
  end,
}
