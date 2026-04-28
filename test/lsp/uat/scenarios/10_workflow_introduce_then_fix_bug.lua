-- Workflow: open clean code, introduce a bug, watch the diagnostic
-- appear, fix the bug, watch the diagnostic clear. This is the most
-- common debugging cycle a user goes through, and the LSP must keep
-- the diagnostic state in sync with the buffer.
--
-- Three failure modes guarded against:
--   1. Bug introduced but no diagnostic — user thinks code is fine
--   2. Bug fixed but diagnostic lingers — user ignores the error,
--      eventually misses real ones
--   3. Save vs change diagnostic state divergence — diagnostic
--      depends on whether didSave fired, which it shouldn't

local CLEAN = table.concat({
  "(sig 'half {-> Num Num})",
  "(fun {half x} {/ x 2})",
  "",
  "(def {answer} (half 10))",
  "",
}, "\n")

return {
  diagnostic_appears_on_bug_clears_on_fix = function(lib)
    local path = lib.write_temp("debug_cycle.valk", CLEAN)
    local bufnr = lib.open_path(path)
    lib.wait_for_lsp(bufnr)

    -- Step 1: clean code, no diagnostic errors.
    local diags0 = lib.wait_for_diagnostics(bufnr, 0, 2000)
    local errors0 = 0
    for _, d in ipairs(diags0) do
      if d.severity == vim.diagnostic.severity.ERROR then errors0 = errors0 + 1 end
    end
    lib.assert_eq(errors0, 0,
      ("clean fixture flagged %d errors at start: %s"):format(errors0,
        vim.inspect(vim.tbl_map(function(d) return d.message end, diags0))))

    -- Step 2: introduce a bug — change the divisor to 0. Replace the
    -- whole buffer to keep the change atomic.
    local buggy = CLEAN:gsub("/ x 2", "/ x 0")
    lib.replace_all(bufnr, buggy)

    -- Wait for the diagnostic to arrive. We expect at least one
    -- error mentioning division-by-zero.
    local diags_buggy = lib.wait_for_diagnostics(bufnr, 1, 5000)
    local saw_div_err = false
    for _, d in ipairs(diags_buggy) do
      if d.severity == vim.diagnostic.severity.ERROR
         or d.severity == vim.diagnostic.severity.WARN then
        if d.message:lower():find("divis") or d.message:find("/ ") then
          saw_div_err = true; break
        end
      end
    end
    lib.assert_truthy(saw_div_err,
      ("introduced (/ x 0) but no division diagnostic; got: %s"):format(
        vim.inspect(vim.tbl_map(function(d) return d.message end, diags_buggy))))

    -- Step 3: save the buggy version to disk, verify diagnostic survives
    -- the save (didSave shouldn't clear errors that are still valid).
    lib.save_buffer(bufnr)
    vim.wait(400)
    local diags_after_save = vim.diagnostic.get(bufnr)
    local errors_after_save = 0
    for _, d in ipairs(diags_after_save) do
      if d.severity == vim.diagnostic.severity.ERROR
         or d.severity == vim.diagnostic.severity.WARN then
        errors_after_save = errors_after_save + 1
      end
    end
    lib.assert_truthy(errors_after_save >= 1,
      "diagnostic disappeared after save while bug still present")

    -- Step 4: fix the bug.
    lib.replace_all(bufnr, CLEAN)

    -- Wait for the diagnostic to clear. The validator runs async via
    -- idx-sys; we give it up to 3s before declaring the diagnostic
    -- stuck.
    local cleared = false
    local deadline = vim.uv.hrtime() + 3e9
    while vim.uv.hrtime() < deadline do
      local d = vim.diagnostic.get(bufnr)
      local errors = 0
      for _, di in ipairs(d) do
        if di.severity == vim.diagnostic.severity.ERROR then errors = errors + 1 end
      end
      if errors == 0 then cleared = true; break end
      vim.wait(100)
    end
    lib.assert_truthy(cleared,
      ("diagnostic stuck after fix; current diagnostics: %s"):format(
        vim.inspect(vim.tbl_map(function(d) return d.message end,
          vim.diagnostic.get(bufnr)))))
  end,
}
