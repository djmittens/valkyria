-- Workflow: write a small program from a blank file. Exercises the
-- progression a user goes through when starting a new script:
--   1. Open a new (empty) file
--   2. Type the file content
--   3. Save it to disk
--   4. Close the buffer
--   5. Reopen — symbols still indexed, no diagnostics on valid code
--
-- This catches LSP regressions where:
--   - The validator complains about partial input mid-typing in a way
--     that doesn't clear once the input becomes valid
--   - The symbol DB doesn't update on save
--   - Reopening the file produces stale state
--   - Diagnostics fail to be cleared after the buggy intermediate
--     state is replaced by valid code

-- Latency scenario: asserts wall-clock budgets / percentiles, so it must run
-- on an otherwise idle machine. The runner keeps these out of the parallel
-- shards and runs them alone afterwards; measured under 4-way contention the
-- budgets stop describing anything a user would experience.
return {
  _latency = true,

  write_save_close_reopen_keeps_state = function(lib)
    -- Step 1: start with an empty file on disk so the LSP sees a real
    -- workspace path (some indexing paths key off the file existing).
    local path = lib.write_temp("scratch.valk", "")
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)

    -- Step 2: write the program in two phases. Phase 1 is intentionally
    -- syntactically broken — `(fun {add a b}` with no body — to verify
    -- the LSP tolerates intermediate broken parses without latching the
    -- error.
    lib.replace_all(bufnr, "(fun {add a b}\n")
    local diags_broken = lib.wait_for_diagnostics(bufnr, 1, 2000)
    -- We don't strictly assert diagnostic presence — different LSP
    -- versions may treat unfinished forms as errors or as warnings.
    -- We DO assert it doesn't crash and we can keep editing.

    -- Phase 2: complete the function and add a call site.
    local final_content = table.concat({
      "(fun {add a b} {+ a b})",
      "",
      "(def {sum} (add 3 4))",
      "",
    }, "\n")
    lib.replace_all(bufnr, final_content)

    -- Step 3: diagnostics should clear once the code is valid.
    local diags_clean = lib.wait_for_diagnostics(bufnr, 0, 2000)
    local errors = 0
    for _, d in ipairs(diags_clean) do
      if d.severity == vim.diagnostic.severity.ERROR then errors = errors + 1 end
    end
    lib.assert_eq(errors, 0,
      ("valid code flagged %d errors after fixing broken state: %s")
        :format(errors, vim.inspect(vim.tbl_map(
          function(d) return d.message end, diags_clean))))

    -- Step 4: save + close + reopen.
    lib.save_buffer(bufnr)
    lib.close_buffer(bufnr)
    local bufnr2 = lib.open_path(path)
    lib.wait_for_lsp(bufnr2)

    -- Step 5: verify content survived round-trip on disk.
    local round_trip = table.concat(
      vim.api.nvim_buf_get_lines(bufnr2, 0, -1, false), "\n")
    lib.assert_truthy(round_trip:find("(add 3 4)", 1, true),
      "saved file lost the call site")
    lib.assert_truthy(round_trip:find("(fun {add", 1, true),
      "saved file lost the function definition")

    -- Step 6: hover on the call site `add` should still resolve to
    -- the same fn after reload — proves the LSP re-indexed the file.
    local line, col = lib.find_text(bufnr2, "(add 3 4)")
    local res, elapsed = lib.request(bufnr2, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr2), line, col + 1), 5000)
    lib.assert_truthy(res, "hover after reopen returned nothing")
    lib.assert_lt(elapsed, 500, "hover after reopen too slow")
  end,
}
