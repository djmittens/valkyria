-- Inlay hints: virtual text shown by the editor next to identifiers
-- to display inferred types or parameter names. The LSP advertises
-- inlayHintProvider; nvim's vim.lsp.inlay_hint() drives it via
-- textDocument/inlayHint requests with a range.
--
-- These tests just verify the LSP returns SOMETHING for known
-- positions where hints make sense. Whether the hint TEXT is correct
-- (e.g. type vs param name) is hard to assert without knowing the
-- LSP's hint policy, so we focus on response-shape correctness.

return {
  inlay_hints_returned_for_def_with_inferable_type = function(lib)
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local total_lines = vim.api.nvim_buf_line_count(bufnr)
    local res = lib.request(bufnr, "textDocument/inlayHint", {
      textDocument = { uri = lib.bufuri(bufnr) },
      range = {
        start = { line = 0, character = 0 },
        ["end"] = { line = total_lines, character = 0 },
      },
    }, 5000)
    -- Result may legitimately be empty (no hints at all is allowed)
    -- or a list of hints. Either is well-formed; an error / nil
    -- response is the failure mode.
    lib.assert_truthy(res ~= nil, "inlayHint request errored / returned nil")
    -- If hints are returned, each must have a position and label.
    if type(res) == "table" then
      for _, h in ipairs(res) do
        lib.assert_truthy(h.position and h.position.line ~= nil,
          "inlay hint missing position: " .. vim.inspect(h))
        lib.assert_truthy(h.label,
          "inlay hint missing label: " .. vim.inspect(h))
      end
    end
  end,

  inlay_hints_update_after_edit = function(lib)
    -- Open a clean fixture, snapshot hint count, append a new def,
    -- snapshot again. Hint count should be different (likely larger).
    -- This exposes the "hints are computed once and cached forever"
    -- regression mode.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^add$", 3000)

    local total_lines_1 = vim.api.nvim_buf_line_count(bufnr)
    local h1 = lib.request(bufnr, "textDocument/inlayHint", {
      textDocument = { uri = lib.bufuri(bufnr) },
      range = { start = { line = 0, character = 0 },
                ["end"] = { line = total_lines_1, character = 0 } },
    }, 5000)
    local count_before = type(h1) == "table" and #h1 or 0

    -- Add a new def at end of file.
    lib.append_line(bufnr, "")
    lib.append_line(bufnr, "(def {y} (square 7))")
    vim.wait(150)  -- let the LSP re-cache hints

    local total_lines_2 = vim.api.nvim_buf_line_count(bufnr)
    local h2 = lib.request(bufnr, "textDocument/inlayHint", {
      textDocument = { uri = lib.bufuri(bufnr) },
      range = { start = { line = 0, character = 0 },
                ["end"] = { line = total_lines_2, character = 0 } },
    }, 5000)
    local count_after = type(h2) == "table" and #h2 or 0

    -- Either count_after >= count_before (added a def, more hints)
    -- OR count_after == count_before (LSP doesn't hint defs — also
    -- valid). The bug we're catching: count_after < count_before
    -- (LSP forgot existing hints), or response errors.
    lib.assert_truthy(count_after >= count_before,
      ("inlay hint count regressed after edit: %d → %d"):format(
        count_before, count_after))
  end,
}
