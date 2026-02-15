-- Neovim configuration for Valkyria project
-- This file sets up a keybinding to run .valk files with build/valk

-- Function to run the current .valk file
local function run_valk_file()
  -- Get the current buffer's file path
  local filepath = vim.fn.expand('%:p')

  -- Check if it's a .valk file
  if not filepath:match('%.valk$') then
    -- Not a .valk file, return false to indicate we didn't handle it
    -- This allows the keybinding to fall through to other handlers
    return false
  end

  -- Get the project root (where build/valk is located)
  -- Assuming we're in the valkyria project directory
  local project_root = vim.fn.getcwd()
  local valk_executable = project_root .. '/build/valk'

  -- Check if the executable exists
  if vim.fn.filereadable(valk_executable) == 0 then
    vim.notify('build/valk not found. Run "make build" first.', vim.log.levels.ERROR)
    return true -- We handled it (with an error)
  end

  -- Construct the command
  local cmd = 'make build && ' .. valk_executable .. ' ' .. vim.fn.shellescape(filepath)

  -- Run the command in a terminal split
  vim.cmd('split | terminal ' .. cmd)

  -- Enter insert mode to see the output immediately
  vim.cmd('startinsert')

  return true -- We handled it successfully
end

-- Only set up the global keybinding for .valk files if we're in a .valk file
-- This way it doesn't interfere with other <leader>r mappings
vim.api.nvim_create_autocmd({'BufEnter', 'BufRead', 'BufNewFile'}, {
  pattern = '*.valk',
  callback = function()
    -- Buffer-local mapping that overrides global <leader>r only for .valk files
    vim.keymap.set('n', '<leader>r', run_valk_file, {
      buffer = true,
      desc = 'Run current .valk file',
      silent = true
    })
  end
})

-- Optional: Set up a command as well
vim.api.nvim_create_user_command('RunValk', run_valk_file, {
  desc = 'Run current .valk file with build/valk'
})

-- Set commentstring for .valk files (Lisp-style comments)
vim.api.nvim_create_autocmd({'BufRead', 'BufNewFile'}, {
  pattern = '*.valk',
  callback = function()
    vim.bo.commentstring = ';; %s'
  end
})

-- Register .valk filetype and tree-sitter parser
vim.filetype.add({
  extension = {
    valk = 'valk',
  },
})
vim.treesitter.language.register('valk', 'valk')

-- LSP client for valk-lsp (via build/valk --lsp)
vim.api.nvim_create_autocmd('FileType', {
  pattern = 'valk',
  callback = function()
    local root = vim.fs.root(0, { '.git', 'CMakeLists.txt' })
    local valk_exe = (root or vim.fn.getcwd()) .. '/build/valk'
    if vim.fn.executable(valk_exe) == 0 then return end

    vim.lsp.start({
      name = 'valk-lsp',
      cmd = { valk_exe, '--lsp' },
      root_dir = root,
      capabilities = vim.lsp.protocol.make_client_capabilities(),
    })
  end,
})

-- Setup the build command
vim.keymap.set('n', '<leader>b', ":mak build<CR>", {
  desc = 'Build project',
})

-- DAP debug configurations
local dap = require('dap')
local cwd = vim.fn.getcwd()

dap.configurations.c = {
  {
    name = 'test_prelude_valk',
    type = 'gdb',
    request = 'launch',
    program = cwd .. '/build/valk',
    args = { 'test/test_prelude.valk' },
    cwd = cwd,
    stopAtBeginningOfMainSubprogram = true,
    env = { ASAN_OPTIONS = 'detect_leaks=0' },
  },
  {
    name = 'valk',
    type = 'gdb',
    request = 'launch',
    program = cwd .. '/build/valk',
    args = function()
      return { vim.fn.expand('%:p') }
    end,
    cwd = cwd,
  },
  {
    name = 'test_std',
    type = 'gdb',
    request = 'launch',
    program = cwd .. '/build/test_std',
    cwd = cwd,
    env = { ASAN_OPTIONS = 'detect_leaks=0' },
  },
  {
    name = 'test_memory',
    type = 'gdb',
    request = 'launch',
    program = cwd .. '/build/test_memory',
    cwd = cwd,
    env = { ASAN_OPTIONS = 'detect_leaks=0' },
  },
  {
    name = 'test_concurrency',
    type = 'gdb',
    request = 'launch',
    program = cwd .. '/build/test_concurrency',
    cwd = cwd,
    env = { ASAN_OPTIONS = 'detect_leaks=0' },
  },
  {
    name = 'test_networking',
    type = 'gdb',
    request = 'launch',
    program = cwd .. '/build/test_networking',
    cwd = cwd,
    env = { ASAN_OPTIONS = 'detect_leaks=0' },
  },
  {
    name = 'test_networking_lisp',
    type = 'gdb',
    request = 'launch',
    program = cwd .. '/build/test_networking_lisp',
    cwd = cwd,
    env = { ASAN_OPTIONS = 'detect_leaks=0' },
  },
}
