-- Reproduce the "orange text on edit" complaint by checking what nvim
-- actually renders, not just what the LSP sends. Uses
-- vim.lsp.semantic_tokens.get_at_pos to query the highlight tokens
-- nvim has applied to specific buffer positions.
--
-- The user's report is that newly-typed content on a fresh line
-- shows as default/uncolored ("orange") even after parse settles.
-- This UAT writes such content via real input and asserts that
-- nvim has registered semantic-token highlights for it.

local function now_ms()
  return vim.uv.hrtime() / 1e6
end

local function feed(keys)
  local termcodes = vim.api.nvim_replace_termcodes(keys, true, false, true)
  vim.api.nvim_feedkeys(termcodes, "nx", false)
end

-- Wait for nvim to have at least one semantic-token applied to the
-- given buffer line. Returns the count seen, or 0 on timeout.
local function wait_for_tokens_on_line(bufnr, line, timeout_ms)
  local deadline = now_ms() + timeout_ms
  while now_ms() < deadline do
    local toks = vim.lsp.semantic_tokens.get_at_pos(bufnr, line, 0)
    if toks and #toks > 0 then return #toks end
    -- Try a few columns in case col 0 is whitespace.
    for col = 1, 20 do
      toks = vim.lsp.semantic_tokens.get_at_pos(bufnr, line, col)
      if toks and #toks > 0 then return #toks end
    end
    vim.wait(100)
  end
  return 0
end

return {
  newly_typed_line_gets_semantic_tokens = function(lib)
    -- Open a fixture, append two new lines with code via real input,
    -- wait for parse to settle, then assert nvim has semantic-token
    -- highlights for the newly-typed code.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(800)  -- let initial /sem/full land + render

    -- Cursor at end of buffer in insert mode.
    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })

    -- Type a complete s-expression on a new line (parse should succeed).
    feed("Go(def {orange-test-sym} 42)<Esc>")
    vim.wait(500)  -- let didChange + cache-ast + /sem fire

    -- The new line is at index n (0-indexed: n was 1-indexed line count;
    -- after Go we appended a line so the new line is at line n in 0-indexed).
    local new_line_idx = vim.api.nvim_buf_line_count(bufnr) - 1
    local new_line_text = vim.api.nvim_buf_get_lines(bufnr, new_line_idx, new_line_idx + 1, false)[1]
    io.stderr:write(("[uat] new line %d: %q\n"):format(new_line_idx, new_line_text))

    -- Query nvim for tokens on that line.
    local count = wait_for_tokens_on_line(bufnr, new_line_idx, 3000)
    io.stderr:write(("[uat] tokens on new line %d: %d\n"):format(new_line_idx, count))

    -- A complete `(def {orange-test-sym} 42)` should produce at least 3
    -- tokens (def, orange-test-sym, 42). If 0, nvim has no highlights
    -- for that line — that's the orange bug.
    lib.assert_truthy(count >= 1,
      ("nvim has %d tokens on newly-typed line — orange repro confirmed"):format(count))
  end,

  second_consecutive_new_line_also_gets_tokens = function(lib)
    -- The user's specific repro: two consecutive new lines, second
    -- one stays orange. Type two complete expressions on two new lines.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(800)

    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })

    -- Two new lines, each with a complete expression.
    feed("Go(def {first-new-sym} 1)<CR>(def {second-new-sym} 2)<Esc>")
    vim.wait(800)

    local total = vim.api.nvim_buf_line_count(bufnr)
    local first_new = total - 2
    local second_new = total - 1

    local first_count = wait_for_tokens_on_line(bufnr, first_new, 3000)
    local second_count = wait_for_tokens_on_line(bufnr, second_new, 3000)
    io.stderr:write(("[uat] first new line %d: %d tokens, second new line %d: %d tokens\n")
      :format(first_new, first_count, second_new, second_count))

    lib.assert_truthy(first_count >= 1, "first new line has 0 tokens (orange)")
    lib.assert_truthy(second_count >= 1, "second new line has 0 tokens (orange)")
  end,

  mid_typing_broken_parse_keeps_some_tokens = function(lib)
    -- During typing of an INCOMPLETE s-expression, the line should
    -- still get SOME highlights via the lex fallback. This is the
    -- key case my last fix targeted.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(800)

    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })

    -- Open a new line and type an INCOMPLETE expression: open paren + symbol.
    feed("Go(broken-sym")
    vim.wait(500)  -- let didChange + /sem fire

    local new_line_idx = vim.api.nvim_buf_line_count(bufnr) - 1
    local count = wait_for_tokens_on_line(bufnr, new_line_idx, 2000)
    io.stderr:write(("[uat] mid-typing line %d: %d tokens (lex fallback expected)\n")
      :format(new_line_idx, count))

    feed("<Esc>")  -- exit insert mode for clean test state
    vim.wait(50)

    -- Lex fallback should produce ≥1 token for the symbol "broken-sym".
    -- 0 tokens means we're stuck on stale cache or skipping the response.
    lib.assert_truthy(count >= 1,
      ("mid-typing broken parse: %d tokens on new line (lex fallback not firing)"):format(count))
  end,
}
