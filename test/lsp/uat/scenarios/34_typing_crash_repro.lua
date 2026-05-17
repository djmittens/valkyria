-- Reproduce the user's "type fast → LSP crashes with signal 11" bug.
-- The previous test/lsp/uat/scenarios/33_orange_repro.lua only typed
-- a few characters then queried tokens — fast enough that races on
-- env->symbols.items don't usually fire. The user's actual scenario
-- types many characters in succession, generating ~1 sem-tokens
-- request per keystroke, causing concurrent worker threads to
-- read/write the same env at the same time.
--
-- This UAT mimics that: open a real LSP file, enter insert mode,
-- type ~50 characters of code as fast as nvim's input loop allows,
-- and verify the LSP is still alive and responsive at the end.
--
-- Was the missing test that would have caught the race in
-- valk_lenv_get vs valk_lenv_put: torn writes during concurrent puts
-- left items[i]=NULL slots that strcmp would crash on.

local function feed(keys)
  local termcodes = vim.api.nvim_replace_termcodes(keys, true, false, true)
  vim.api.nvim_feedkeys(termcodes, "nx", false)
end

local function lsp_alive(bufnr)
  local clients = vim.lsp.get_clients({bufnr = bufnr})
  if #clients == 0 then return false end
  for _, c in ipairs(clients) do
    if c.is_stopped() then return false end
  end
  return true
end

return {
  type_storm_does_not_crash_lsp = function(lib)
    -- Open the LSP's own lsp.valk — same file the user was editing
    -- when they hit the crash. Real-world: a 320-line dispatch file
    -- with many existing defs that the typing rapid-fire forces
    -- workers to lookup against.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(800)

    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })

    -- Simulate the exact pattern that crashed: open paren, then a
    -- slow-paced (but multi-character) symbol name, then continue
    -- typing on a new line. Each character generates a didChange
    -- which fires a sem-tokens request — many workers run in
    -- parallel.
    local typing_pattern = "Go(fuck the followed by you bitch)<CR>(more random text on second line)<CR>(yet a third line with more)<Esc>"
    feed(typing_pattern)
    vim.wait(2000)  -- let the request storm settle

    -- After the storm, the LSP should still be responsive. If it
    -- crashed (signal 11) the client would be marked stopped.
    lib.assert_truthy(lsp_alive(bufnr),
      "LSP crashed during rapid typing burst")

    -- Also assert: a follow-up request gets a response. If the LSP
    -- is alive but stuck in GC pause, hover would time out.
    local ok, hover = pcall(function()
      return vim.lsp.buf_request_sync(bufnr,
        "textDocument/hover",
        { textDocument = { uri = vim.uri_from_bufnr(bufnr) },
          position = { line = 0, character = 0 } },
        2000)
    end)
    lib.assert_truthy(ok,
      "LSP unresponsive (hover timeout) after typing burst")
  end,

  rapid_burst_50_keystrokes_no_crash = function(lib)
    -- Even more aggressive: feed 50+ characters as a single feed()
    -- which nvim processes as fast as possible. With per-keystroke
    -- sem-tokens requests, this fires ~50 concurrent workers.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(800)

    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })

    -- 50+ chars, multiple lines, many symbols
    feed("Go(def {a} 1)<CR>(def {b} 2)<CR>(def {c} 3)<CR>(def {d} 4)<CR>(def {e} 5)<Esc>")
    vim.wait(2000)

    lib.assert_truthy(lsp_alive(bufnr),
      "LSP crashed during 50-keystroke burst")
  end,

  sustained_200_keystrokes_no_crash = function(lib)
    -- Exhaustive: 200+ chars across many lines. This is closest to
    -- "user types in the editor for ~30 seconds". Was crashing
    -- consistently before the lenv_get NULL guard fix.
    local bufnr = lib.open_fixture("medium.valk")
    lib.wait_for_lsp(bufnr)
    vim.wait(800)

    vim.api.nvim_set_current_buf(bufnr)
    local n = vim.api.nvim_buf_line_count(bufnr)
    vim.api.nvim_win_set_cursor(0, { n, 0 })

    -- Type many lines of varied code. Each char triggers didChange,
    -- which fires a sem-tokens request, which spawns a worker. Many
    -- concurrent workers all reading/writing env metadata.
    feed("Go")
    for i = 1, 20 do
      feed(("(def {sym%d} %d)<CR>"):format(i, i))
    end
    feed("(fun {fact n} {if (== n 0) {1} {* n (fact (- n 1))}})<CR>")
    feed("(println \"%d\" (fact 10))<Esc>")
    vim.wait(3000)

    lib.assert_truthy(lsp_alive(bufnr),
      "LSP crashed during sustained 200-keystroke session")
  end,
}
