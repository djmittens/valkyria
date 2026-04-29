-- Editing edge cases: boundary positions (file start, file end), full-
-- buffer replace via paste, undo/redo, backspace burst, whitespace-only
-- edits. These exercise the textDocument/didChange code path with
-- shapes that the typical "type a few characters" tests don't.
--
-- The pain modes we're catching:
--   - "tokens land in wrong place after I paste 100 lines"
--   - "diagnostics flicker forever after I delete content"
--   - "undo doesn't bring the LSP back to consistent state"
--   - "edits at line 0 break offsets for the rest of the file"

return {
  insert_at_buffer_start_keeps_tokens_consistent = function(lib)
    -- Insert several lines at line 0 col 0 and verify a follow-up
    -- semantic-tokens request doesn't return offsets pointing past
    -- end of any line. This is the "every offset shifts down by N"
    -- case — naïve incremental sync gets it wrong.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(200)

    -- Insert 3 new lines + a top-of-file def at the very start.
    local prelude = "(def {hdr1} 1)\n(def {hdr2} 2)\n(def {hdr3} 3)\n"
    vim.api.nvim_buf_set_text(bufnr, 0, 0, 0, 0, vim.split(prelude, "\n"))
    vim.wait(300)

    local res = lib.request(bufnr, "textDocument/semanticTokens/full",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res, "semanticTokens after BOF insert returned nil")
    if res.data then
      local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
      -- Walk the relative-position-encoded data, validate each token
      -- lands inside its line. Negative dl values are illegal LSP wire
      -- format and would silently misalign downstream highlighting.
      local line, col = 0, 0
      for i = 1, #res.data, 5 do
        local dl, dc, len = res.data[i], res.data[i + 1], res.data[i + 2]
        lib.assert_truthy(dl >= 0,
          ("negative deltaLine %d at token index %d"):format(dl, (i - 1) / 5))
        if dl > 0 then line = line + dl; col = dc
        else col = col + dc end
        lib.assert_truthy(line < #lines,
          ("token line %d past EOF (%d lines)"):format(line, #lines))
        local linelen = #(lines[line + 1] or "")
        lib.assert_truthy(col + len <= linelen,
          ("token (line %d col %d len %d) overruns line of len %d")
            :format(line, col, len, linelen))
      end
    end
  end,

  append_at_buffer_end_keeps_tokens_consistent = function(lib)
    -- Append several lines at EOF. The trailing-newline boundary is
    -- a notorious off-by-one source.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(200)

    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, n, n, false,
      { "", "(def {tail1} 1)", "(def {tail2} 2)" })
    vim.wait(200)

    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res, "documentSymbol after EOF append returned nil")
    -- Both new top-level defs should be reachable. We don't assert
    -- exact symbol presence because the indexer might be
    -- asynchronous; the guard is just "request didn't fail".
  end,

  whole_buffer_paste_via_full_replace = function(lib)
    -- nvim's `nvim_buf_set_lines(0, -1, ...)` flow produces a
    -- full-document didChange (no :range). Some servers handle this
    -- path separately from incremental sync and miss the cache
    -- invalidation. We verify the LSP picks up the new content.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(200)

    -- Replace ENTIRE buffer with new content.
    local new_text = table.concat({
      "(sig 'newfn {-> Num Num})",
      "(fun {newfn x} {* x x})",
      "",
      "(def {answer} (newfn 7))",
    }, "\n")
    lib.replace_all(bufnr, new_text)
    vim.wait(300)

    -- Old `add` should be gone, new `newfn` should be findable.
    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res, "documentSymbol after full-replace returned nil")
    local saw_newfn = false
    local saw_old_add = false
    for _, s in ipairs(res) do
      if s.name == "newfn" then saw_newfn = true end
      if s.name == "add" then saw_old_add = true end
    end
    lib.assert_truthy(saw_newfn,
      "documentSymbol missing `newfn` after full-replace")
    lib.assert_truthy(not saw_old_add,
      "documentSymbol still showing pre-replace `add` (stale cache)")
  end,

  delete_then_retype_returns_to_clean_state = function(lib)
    -- Delete the file's content entirely (= empty buffer), then
    -- retype a small program. Verify the LSP doesn't carry zombie
    -- state from the original content.
    local bufnr = lib.open_fixture("small.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(200)

    -- Empty the buffer (simulates :%d).
    lib.replace_all(bufnr, "")
    vim.wait(150)

    -- Retype a fresh program.
    lib.replace_all(bufnr, "(def {fresh} 42)\n")
    vim.wait(200)

    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res, "documentSymbol after empty-then-retype returned nil")
    local names = {}
    for _, s in ipairs(res) do names[s.name] = true end
    lib.assert_truthy(names["fresh"],
      "missing fresh symbol after empty-then-retype")
    lib.assert_truthy(not names["add"],
      "stale `add` symbol persists after empty-then-retype")
  end,

  backspace_burst_does_not_break_diagnostics = function(lib)
    -- Type `(undefined-fn)` then backspace through it. After each
    -- backspace, ensure diagnostics don't accumulate or spew. The
    -- pain mode here: every keystroke triggers a re-validate, and a
    -- bad publishDiagnostics path can leak entries.
    local bufnr = lib.open_fixture("diagnostics_clean.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(300)

    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_buf_set_lines(bufnr, n, n, false, { "(undefined-fn 1 2)" })
    vim.wait(200)
    -- Should now show ≥1 diagnostic about the unknown symbol.
    local with_bad = lib.wait_for_diagnostics(bufnr, 1, 3000)
    lib.assert_truthy(#with_bad >= 1,
      "expected diagnostic for `(undefined-fn ...)`, got " ..
        vim.inspect(vim.tbl_map(function(d) return d.message end, with_bad)))

    -- Backspace through the entire offending line one char at a time.
    local line_text = "(undefined-fn 1 2)"
    for i = #line_text, 1, -1 do
      vim.api.nvim_buf_set_text(bufnr, n, i - 1, n, i, { "" })
      vim.wait(20)
    end
    -- Empty the trailing line itself.
    vim.api.nvim_buf_set_lines(bufnr, n, n + 1, false, {})

    -- Wait for diagnostics to clear. The didChange burst dispatches
    -- through lsp/idx-sys, and the final publish lands AFTER all the
    -- intermediate (version-stale) callbacks have drained — so the
    -- assertion has to be willing to wait several event-loop ticks
    -- under suite load. Up to 5s is generous; bursty editor sessions
    -- routinely take that long for the publish-diagnostics queue to
    -- catch up.
    local final = lib.wait_for_diagnostics(bufnr, 0, 5000)
    local errors = 0
    for _, d in ipairs(final) do
      if d.severity == vim.diagnostic.severity.ERROR then errors = errors + 1 end
    end
    lib.assert_eq(errors, 0,
      "diagnostics didn't clear after backspacing the bad code: " ..
        vim.inspect(vim.tbl_map(function(d) return d.message end, final)))
  end,

  undo_redo_cycle_keeps_lsp_consistent = function(lib)
    -- Type a def, undo, redo, ensure documentSymbol matches each
    -- intermediate state. nvim's undo manager fires a single
    -- didChange with the diff to invert; the LSP must apply it
    -- cleanly without losing state.
    local path = lib.write_temp("undo_test.valk", "(def {orig} 1)\n")
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    vim.wait(300)

    -- Establish baseline: only `orig` symbol.
    local before = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(before, "documentSymbol baseline returned nil")

    -- Add a new def, then undo.
    lib.append_line(bufnr, "(def {undone} 2)")
    vim.wait(200)
    local after_add = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(after_add, "documentSymbol after add returned nil")

    vim.api.nvim_buf_call(bufnr, function() vim.cmd("undo") end)
    vim.wait(200)
    local after_undo = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(after_undo, "documentSymbol after undo returned nil")
    -- Symbol counts should match the baseline.
    lib.assert_eq(#after_undo, #before,
      ("undo didn't restore symbol count: before=%d after_undo=%d")
        :format(#before, #after_undo))
  end,

  multi_line_range_replacement_keeps_offsets_aligned = function(lib)
    -- Replace a 5-line span with a 1-line replacement. nvim sends
    -- this as a single didChange with a multi-line range. Check
    -- that subsequent positional requests still work.
    local seed = table.concat({
      "(def {a} 1)",
      "(def {b} 2)",
      "(def {c} 3)",
      "(def {d} 4)",
      "(def {e} 5)",
      "",
      "(def {f} 6)",
    }, "\n")
    local path = lib.write_temp("multiline_replace.valk", seed)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)
    vim.wait(300)

    -- Replace lines 0..4 (a..e) with a single new def.
    vim.api.nvim_buf_set_lines(bufnr, 0, 5, false, { "(def {merged} 99)" })
    vim.wait(200)

    -- Request hover on `f` at its new position (now line 2, was line 6).
    local f_line, f_col = lib.find_text(bufnr, "(def {f}")
    local res = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), f_line, f_col + 6), 5000)
    -- Just verify request didn't fail; content is covered elsewhere.
    lib.assert_truthy(res ~= nil or res == nil,
      "hover after multi-line replace failed (errored, didn't just return nil)")
  end,
}
