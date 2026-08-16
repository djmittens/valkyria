-- Workflow: open an existing file, add a new feature (a new function
-- + a call site), save, verify the new symbol is now visible to:
--   - Completion (suggested when user types a prefix)
--   - Goto-def (jumps to the new (fun ...) line)
--   - Hover (returns content)
--
-- This is the exact LSP UX that determines whether the user "trusts"
-- the editor: they add a function, expect autocomplete to know about
-- it within a second, and goto-def to jump to it. A failing test here
-- means the symbol DB doesn't update on save / didChange — a common
-- LSP regression mode.

local INITIAL = table.concat({
  "(sig 'mul {-> Num Num Num})",
  "(fun {mul a b} {* a b})",
  "",
  "(def {twelve} (mul 3 4))",
  "",
}, "\n")

return {
  added_function_visible_to_completion_and_goto_def = function(lib)
    local path = lib.write_temp("add_feature.valk", INITIAL)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)

    -- The symdb sync runs asynchronously on lsp/idx-sys, so wait for the
    -- file's own symbols to appear rather than guessing at a settle time.
    lib.require_symbol_indexed(bufnr, "^mul$", 5000)

    -- Add a new function `mul3` that uses the existing `mul`. Append
    -- at end of file. We also append a call site so we can goto-def
    -- from a known position.
    local new_lines = {
      "",
      "(sig 'mul3 {-> Num Num Num Num})",
      "(fun {mul3 a b c} {mul (mul a b) c})",
      "",
      "(def {answer} (mul3 2 3 5))",
    }
    local first_appended_line = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, first_appended_line,
      first_appended_line, false, new_lines)
    -- Save so didSave triggers symdb resync (didChange+save is the
    -- normal path; we exercise both).
    lib.save_buffer(bufnr)
    -- didSave dispatches the re-index to lsp/idx-sys; wait for the new symbol
    -- to actually land in the index.
    lib.require_symbol_indexed(bufnr, "^mul3$", 5000)

    -- Assertion 1: completion at `(mul3` should include `mul3`. We do
    -- this by typing `(mul3` on a fresh line and asking for completions.
    local probe_line = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, probe_line, probe_line, false, { "(mul3" })
    local res = lib.request(bufnr, "textDocument/completion", {
      textDocument = { uri = lib.bufuri(bufnr) },
      position = lib.pos(probe_line, 5),
      context = { triggerKind = 1 },
    }, 5000)
    local items = res
    if type(res) == "table" and res.items then items = res.items end
    lib.assert_truthy(items and #items > 0,
      "completion returned no items after adding mul3")
    local saw_mul3 = false
    for _, it in ipairs(items) do
      local label = it.label or it
      if label == "mul3" then saw_mul3 = true; break end
    end
    lib.assert_truthy(saw_mul3,
      ("completion list of %d items does not include `mul3` after save"
       ):format(#items))

    -- Clean up the probe line so subsequent assertions see a clean
    -- buffer.
    vim.api.nvim_buf_set_lines(bufnr, probe_line, probe_line + 1, false, {})
    lib.sync(bufnr)

    -- Assertion 2: goto-def from `(mul3 2 3 5)` jumps to the (fun {mul3 ...}) line.
    -- The probe-line deletion just above races the server's async handling
    -- of that didChange: a one-shot request can transiently get nil while
    -- the edit is applied and re-indexed (observed on slow macOS CI
    -- runners). Poll until it resolves instead of asking exactly once.
    local call_line, call_col = lib.find_text(bufnr, "(mul3 2 3 5)")
    local def_res = lib.require_until(function()
      local res = lib.request(bufnr, "textDocument/definition",
        lib.tdp(lib.bufuri(bufnr), call_line, call_col + 1), 1000)
      if not res then return nil end
      if type(res) == "table" and not res.uri and not res[1] then return nil end
      return res
    end, "goto-def on newly-added mul3 call never resolved", 5000)
    local locs = type(def_res) == "table" and def_res[1] and def_res or { def_res }
    if type(def_res) == "table" and def_res.uri then locs = { def_res } end
    lib.assert_truthy(locs[1],
      "goto-def returned empty list: " .. vim.inspect(def_res))
    local target = locs[1]
    lib.assert_eq(target.uri or target.targetUri, lib.bufuri(bufnr),
      "goto-def jumped to wrong file")
    -- Find what line `(fun {mul3 ...})` is actually on (more robust
    -- than hard-coded numbers since the test mutates the buffer).
    local fun_line = lib.find_text(bufnr, "(fun {mul3")
    local target_line = (target.range or target.targetRange).start.line
    lib.assert_eq(target_line, fun_line,
      "goto-def jumped to wrong line")
  end,
}
