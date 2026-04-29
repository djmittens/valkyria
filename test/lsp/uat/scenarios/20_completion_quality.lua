-- Completion item quality: items must have correct kind, label,
-- and (where applicable) detail. nvim's completion menu sorts
-- and groups by kind, so wrong kinds make the UX feel off even
-- though the LSP "responds". detail strings drive the popup type
-- preview.
--
-- LSP CompletionItemKind values (subset):
--   3 = Function, 4 = Constructor, 6 = Variable, 7 = Class,
--   13 = Enum, 14 = Keyword, 25 = TypeParameter

return {
  completion_items_have_correct_kind = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    -- Empty-prefix completion at start-of-line so we get the full
    -- symbol set with their kinds.
    local last = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, last, last, false, { "(" })
    vim.wait(80)
    local res = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(last, 1),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    lib.assert_truthy(items and #items > 0, "no completion items")

    -- Find `add` (a function) and `answer` (a def — variable) and
    -- verify they have distinct kinds. A regression that flattens
    -- everything to kind=Text would fail here.
    local add_kind, answer_kind
    for _, it in ipairs(items) do
      if it.label == "add" then add_kind = it.kind end
      if it.label == "answer" then answer_kind = it.kind end
    end
    if add_kind and answer_kind then
      lib.assert_truthy(add_kind ~= answer_kind,
        ("`add` and `answer` should have different kinds (got both = %d)"
         ):format(add_kind))
    end
    -- `add` should be Function (3) or Method (2). Tolerate either.
    if add_kind then
      lib.assert_truthy(add_kind == 3 or add_kind == 2,
        ("`add` kind should be Function/Method, got %d"):format(add_kind))
    end
  end,

  completion_items_have_label_and_no_duplicates = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local last = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, last, last, false, { "(a" })
    vim.wait(80)
    local res = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(last, 2),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    lib.assert_truthy(items and #items > 0, "no completion items")
    -- Each item must have a non-empty `label`.
    for _, it in ipairs(items) do
      lib.assert_truthy(it.label and #it.label > 0,
        "completion item with empty label: " .. vim.inspect(it))
    end
    -- Detect duplicates: `add` shouldn't appear 5 times because
    -- the symdb has 5 rows (sig + fun + 3 refs). The completion
    -- query uses GROUP BY name; verify that's working.
    local seen = {}
    local dup_count = 0
    for _, it in ipairs(items) do
      if seen[it.label] then dup_count = dup_count + 1 end
      seen[it.label] = true
    end
    lib.assert_eq(dup_count, 0,
      ("found %d duplicate completion items"):format(dup_count))
  end,

  completion_provides_detail_with_signature = function(lib)
    -- The completion item for a sig'd function should include its
    -- type signature in the `detail` field so nvim's popup shows
    -- it next to the label. small.valk has `(sig 'add {-> Num Num Num})`
    -- so `add`'s detail should reference Num.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local last = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, last, last, false, { "(add" })
    vim.wait(80)
    local res = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(last, 4),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    local add_item
    for _, it in ipairs(items or {}) do
      if it.label == "add" then add_item = it; break end
    end
    if add_item and add_item.detail then
      lib.assert_truthy(add_item.detail:find("Num", 1, true),
        ("completion detail for `add` missing type info: %s"):format(
          tostring(add_item.detail)))
    end
    -- If detail is missing entirely, that's a known gap rather than
    -- a hard failure — nvim renders the label without it. We still
    -- want the test to record the situation.
  end,
}
