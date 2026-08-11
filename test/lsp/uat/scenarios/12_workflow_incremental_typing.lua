-- Workflow: simulate a user typing a function character-by-character,
-- requesting hover/completion at intermediate positions. Catches bugs
-- where the LSP's symdb only refreshes on save, OR where mid-typing
-- requests return stale answers, OR where completion forgets the
-- partial expression the user is currently typing.
--
-- More aggressive than 06_rapid_typing — that test inserts characters
-- and only asks for semantic tokens. This one mixes edits with the
-- queries a user actually makes WHILE typing.

local SEED = table.concat({
  "(sig 'add {-> Num Num Num})",
  "(fun {add a b} {+ a b})",
  "",
  "",  -- this blank line is where we type
  "",
}, "\n")

-- Latency scenario: asserts wall-clock budgets / percentiles, so it must run
-- on an otherwise idle machine. The runner keeps these out of the parallel
-- shards and runs them alone afterwards; measured under 4-way contention the
-- budgets stop describing anything a user would experience.
return {
  _latency = true,

  hover_during_typing_returns_for_just_typed_symbol = function(lib)
    local path = lib.write_temp("incremental.valk", SEED)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    lib.require_symbol_indexed(bufnr, "^add$", 5000)

    -- Find the blank line we'll type into.
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local target_line = nil
    for i, l in ipairs(lines) do
      if l == "" and i > 2 then target_line = i - 1; break end
    end
    lib.assert_truthy(target_line, "no blank line in seed")

    -- Type `(def {result} (add 10 20))` one char at a time.
    local text = "(def {result} (add 10 20))"
    for i = 1, #text do
      local ch = text:sub(i, i)
      vim.api.nvim_buf_set_text(bufnr, target_line, i - 1,
                                 target_line, i - 1, { ch })
      lib.keystroke_gap()
    end

    -- After typing, hover on `add` (which we just typed) should still
    -- resolve to the existing top-level `add` function. The LSP must
    -- have processed didChange and re-parsed.
    local add_line, add_col = lib.find_text(bufnr, "(add 10 20)")
    local res, elapsed, err = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), add_line, add_col + 1), 5000)
    lib.assert_truthy(not err, "hover errored: " .. tostring(err))
    lib.assert_truthy(res, "hover after typing returned nil")
    lib.assert_lt(elapsed, 1000, "hover after typing too slow")
  end,

  completion_during_typing_includes_in_progress_symbol = function(lib)
    local path = lib.write_temp("incremental_completion.valk", SEED)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    lib.require_symbol_indexed(bufnr, "^add$", 5000)

    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local target_line = nil
    for i, l in ipairs(lines) do
      if l == "" and i > 2 then target_line = i - 1; break end
    end

    -- Type `(ad` and ask for completion. `add` from the existing fn
    -- must appear; the LSP must not have invalidated its index just
    -- because the user is typing.
    local prefix = "(ad"
    for i = 1, #prefix do
      vim.api.nvim_buf_set_text(bufnr, target_line, i - 1,
                                 target_line, i - 1, { prefix:sub(i, i) })
      lib.keystroke_gap()
    end

    local res = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(target_line, #prefix),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    lib.assert_truthy(items and #items > 0,
      "completion mid-typing returned no items")
    local saw_add = false
    for _, it in ipairs(items) do
      local label = it.label or it
      if label == "add" then saw_add = true; break end
    end
    lib.assert_truthy(saw_add,
      ("completion at `(ad` doesn't include `add` (got %d items)"):format(#items))
  end,
}
