-- Position encoding. The server reports every column as a byte offset and
-- advertises positionEncoding "utf-8"; it refuses to initialize against a
-- client that doesn't offer utf-8, because there is no utf-16 code path.
--
-- Nothing else in the suite puts a cursor on a line containing multi-byte
-- text, so without this file the entire byte-column assumption — hover,
-- definition, documentSymbol, and the incremental didChange splice — is
-- unverified against a real client.

return {
  server_negotiated_utf8 = function(lib)
    local bufnr = lib.open_fixture("unicode.valk")
    lib.wait_for_lsp(bufnr)

    local clients = vim.lsp.get_clients({ bufnr = bufnr })
    lib.assert_truthy(#clients >= 1, "no client attached")
    lib.assert_eq(clients[1].server_capabilities.positionEncoding, "utf-8",
      "server must advertise the encoding it actually speaks")
    lib.assert_eq(clients[1].offset_encoding, "utf-8",
      "client must have adopted utf-8 for all position math")
  end,

  hover_on_symbol_after_multibyte_text = function(lib)
    local bufnr = lib.open_fixture("unicode.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^uni/greet$", 5000)

    -- (uni/greet name) sits after "日本語 😀 " on the uni/shout line. The same
    -- cursor is byte 45, utf-16 unit 37, codepoint 36. A utf-16 reading of
    -- our byte column lands 8 columns early, inside the string literal.
    local line, col = lib.find_text(bufnr, "(uni/greet name)")
    local res = lib.request(bufnr, "textDocument/hover",
      lib.tdp(lib.bufuri(bufnr), line, col + 1), 5000)

    lib.assert_truthy(res and res.contents, "no hover after multi-byte text")
    local value = type(res.contents) == "table"
      and (res.contents.value or "") or tostring(res.contents)
    lib.assert_contains(value, "uni/greet",
      "hover resolved the wrong symbol - column was read as utf-16")
  end,

  definition_from_call_after_multibyte_text = function(lib)
    local bufnr = lib.open_fixture("unicode.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^uni/shout$", 5000)

    -- (uni/shout "wörld") follows "ünïcødé — ø" on the uni/tail line.
    local line, col = lib.find_text(bufnr, "(uni/shout \"wörld\")")
    local res = lib.request(bufnr, "textDocument/definition",
      lib.tdp(lib.bufuri(bufnr), line, col + 1), 5000)

    lib.assert_truthy(res, "no definition after multi-byte text")
    local loc = res[1] or res
    lib.assert_truthy(loc and (loc.range or loc.targetRange),
      "definition result has no range")
    local def_line = (loc.range or loc.targetRange).start.line
    local want = select(1, lib.find_text(bufnr, "(fun {uni/shout name}"))
    lib.assert_eq(def_line, want, "jumped to the wrong line")
  end,

  document_symbol_columns_are_bytes = function(lib)
    local bufnr = lib.open_fixture("unicode.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_workspace_scan(10000)
    lib.require_symbol_indexed(bufnr, "^uni/tail$", 10000)

    -- lib.document_symbols returns names only; the ranges are the point
    -- here, so request them directly.
    local res = lib.request(bufnr, "textDocument/documentSymbol",
      { textDocument = { uri = lib.bufuri(bufnr) } }, 5000)
    lib.assert_truthy(res and #res > 0, "no document symbols")

    -- Every reported range must be a byte range this buffer can actually
    -- slice: a utf-16 column would be short and land mid-codepoint.
    local lines = vim.api.nvim_buf_get_lines(bufnr, 0, -1, false)
    local checked = 0
    for _, s in ipairs(res) do
      local r = s.range or (s.location and s.location.range)
      lib.assert_truthy(r, ("symbol %s has no range"):format(s.name or "?"))
      local text = lines[r.start.line + 1] or ""
      lib.assert_truthy(r.start.character <= #text,
        ("symbol %s starts past end of line (%d > %d bytes)")
          :format(s.name or "?", r.start.character, #text))
      checked = checked + 1
    end
    lib.assert_truthy(checked >= 3, "expected at least 3 symbols, got " .. checked)
  end,

  incremental_edit_after_multibyte_text = function(lib)
    -- The didChange splice converts the client's character index straight
    -- into a byte offset. An edit placed after multi-byte text is the case
    -- that corrupts the server's copy if the encodings disagree.
    local bufnr = lib.open_fixture("unicode.valk")
    lib.wait_for_lsp(bufnr)
    lib.wait_for_symbol_indexed(bufnr, "^uni/tail$", 5000)

    local line, col = lib.find_text(bufnr, "(uni/shout \"wörld\")")
    lib.insert_at(bufnr, line, col, "(uni/greet \"x\") ")
    lib.sync(bufnr)

    local edited = vim.api.nvim_buf_get_lines(bufnr, line, line + 1, false)[1]
    lib.assert_contains(edited, "(uni/greet \"x\") (uni/shout",
      "buffer edit did not land where expected")

    -- Hover reads the server's own copy of the document. If the splice used
    -- the wrong byte offset, the server's text stays shifted relative to the
    -- buffer and this position resolves to the wrong symbol forever.
    --
    -- Polled, not one-shot: hover answers from the cached AST, which a
    -- background job refreshes after didChange. lib.sync only proves the
    -- notification was dequeued, not that the re-parse landed.
    local hline, hcol = lib.find_text(bufnr, "(uni/greet \"x\")")
    lib.require_until(function()
      local res = lib.request(bufnr, "textDocument/hover",
        lib.tdp(lib.bufuri(bufnr), hline, hcol + 1), 5000)
      if not (res and res.contents) then return false end
      local value = type(res.contents) == "table"
        and (res.contents.value or "") or tostring(res.contents)
      return value:find("uni/greet", 1, true) ~= nil
    end, "server never resolved uni/greet at the inserted byte column - its " ..
         "document copy diverged from the buffer after an edit past " ..
         "multi-byte text", 5000, 50)
  end,
}
