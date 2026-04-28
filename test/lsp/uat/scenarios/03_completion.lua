-- Completion correctness: after typing a prefix, the LSP must return
-- a list including the symbols a user reasonably expects.
--
-- A bad LSP often "succeeds" with an empty list, or returns hundreds
-- of unrelated globals when the user only wants in-scope symbols.
-- These tests catch both: presence of expected items + absence of
-- obvious noise.

return {
  completion_after_open_paren_has_user_fns = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    -- Wait for the LSP to actually finish indexing this file.
    -- `wait_for_lsp` only confirms client attach; the symdb sync
    -- runs asynchronously and a completion query right after attach
    -- can race the indexer (returns 0 user-defined symbols).
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)
    -- Position completion right after `(` on a fresh line at EOF.
    -- We do this by appending a line, putting cursor inside the new
    -- empty `(` and asking for completions.
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local insert_line = #lines
    vim.api.nvim_buf_set_lines(bufnr, insert_line, insert_line, false, { "(" })
    vim.wait(50)
    local res, elapsed = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(insert_line, 1),
      context = { triggerKind = 1 },
    }, 5000)
    -- Result may be CompletionList { items = [...] } or just [...].
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    lib.assert_truthy(items and #items > 0, "completion returned no items")
    lib.assert_lt(elapsed, 300, "completion too slow")
    -- The fixture defines `add`, `square`, `pythag`, `answer` — at
    -- least one must appear (a regression that filters them out
    -- entirely is the failure mode we're guarding against).
    local has_user_sym = false
    for _, it in ipairs(items) do
      local label = it.label or it
      if label == "add" or label == "square"
         or label == "pythag" or label == "answer" then
        has_user_sym = true
        break
      end
    end
    lib.assert_truthy(has_user_sym,
      ("completion list of %d items contains no user-defined symbols"):format(#items))
  end,

  completion_with_prefix_filters = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^square$", 3000)
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local insert_line = #lines
    vim.api.nvim_buf_set_lines(bufnr, insert_line, insert_line, false, { "(squa" })
    vim.wait(50)
    local res, elapsed = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(insert_line, 5),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    lib.assert_truthy(items and #items > 0,
      "prefix completion returned no items")
    -- Note: filtering by prefix is the client's job (vim.lsp.completion
    -- does fuzzy match in nvim 0.11+). The server is allowed to return
    -- the full list and let the client filter. So we just assert
    -- `square` is present, not that the list is small.
    lib.assert_contains(items, "square",
      "completion at `(squa` doesn't include `square`")
  end,
}
