-- Diagnostics correctness: known-bad code is flagged, known-good code
-- is not. Diagnostics arrive asynchronously via publishDiagnostics
-- notifications; we poll vim.diagnostic for the buffer rather than
-- making a request.
--
-- Two failure modes guarded against:
--   1. Bad code produces no diagnostics → user sees no red squigglies
--      on broken code, ships it, gets confused at runtime.
--   2. Good code produces diagnostics → user sees red squigglies on
--      working code, has to ignore them, eventually misses real ones.

local function wait_for_diagnostics(bufnr, timeout_ms, want_count_min)
  local deadline = vim.uv.hrtime() + timeout_ms * 1e6
  local last_diags = {}
  while vim.uv.hrtime() < deadline do
    last_diags = vim.diagnostic.get(bufnr)
    if want_count_min == 0 then
      -- "no diagnostics" — wait the full timeout to be sure none arrive
      vim.wait(100)
      last_diags = vim.diagnostic.get(bufnr)
    elseif #last_diags >= want_count_min then
      return last_diags
    end
    vim.wait(50)
  end
  return last_diags
end

return {
  diagnostics_flag_known_bad_code = function(lib)
    local bufnr = lib.open_fixture("diagnostics_bad.valk")
    lib.wait_for_lsp(bufnr)
    local diags = wait_for_diagnostics(bufnr, 5000, 1)
    lib.assert_truthy(#diags >= 1,
      ("expected >=1 diagnostic on bad fixture, got %d"):format(#diags))
    -- Check at least one diagnostic mentions division. The exact
    -- wording is the validator's choice.
    local saw_div = false
    for _, d in ipairs(diags) do
      if d.message:lower():find("division") or d.message:find("/") then
        saw_div = true; break
      end
    end
    if not saw_div then
      io.stderr:write("[uat] note: no `division` diagnostic; got: "
        .. vim.inspect(vim.tbl_map(function(d) return d.message end, diags))
        .. "\n")
    end
  end,

  diagnostics_silent_on_clean_code = function(lib)
    local bufnr = lib.open_fixture("diagnostics_clean.valk")
    lib.wait_for_lsp(bufnr)
    -- Wait long enough that a slow validator would have spoken up.
    local diags = wait_for_diagnostics(bufnr, 3000, 0)
    -- Allow at most 0 errors. Warnings/hints are tolerated since the
    -- LSP may legitimately suggest e.g. unused-binding hints.
    local errors = 0
    for _, d in ipairs(diags) do
      if d.severity == vim.diagnostic.severity.ERROR then errors = errors + 1 end
    end
    lib.assert_eq(errors, 0,
      ("clean fixture flagged %d errors: %s"):format(errors,
       vim.inspect(vim.tbl_map(function(d) return d.message end, diags))))
  end,
}
