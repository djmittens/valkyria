#!/bin/bash
# Profile the valk-lsp load path via real neovim.
#
# Drives nvim --headless: writes a minimal init.lua that starts valk-lsp
# through build/lsp_proxy, opens a fixture .valk file, waits long enough
# for initial LSP traffic to settle, exits. Then parses the proxy log and
# prints a per-phase breakdown.
#
# Env overrides:
#   VALK_LSP_FIXTURE   file to open in nvim (default lsp/workspace.valk)
#   VALK_LSP_WAIT_MS   how long to wait in nvim after open (default 4000)
#   VALK_LSP_PROXY_LOG proxy log path (default /tmp/valk-lsp-proxy.log)

set -eu

cd "$(dirname "$0")/.."
REPO="$PWD"

PROXY="$REPO/build/lsp_proxy"
SERVER="$REPO/build/valk-lsp"
FIXTURE="${VALK_LSP_FIXTURE:-lsp/workspace.valk}"
WAIT_MS="${VALK_LSP_WAIT_MS:-4000}"
LOG="${VALK_LSP_PROXY_LOG:-/tmp/valk-lsp-proxy.log}"

if [[ ! -x "$PROXY" ]]; then
  echo "missing $PROXY — run: cmake --build build --target lsp_proxy" >&2
  exit 1
fi
if [[ ! -x "$SERVER" ]]; then
  echo "missing $SERVER — run: ./build/valk --build lsp/build-main.valk -o $SERVER" >&2
  exit 1
fi
if [[ ! -f "$FIXTURE" ]]; then
  echo "fixture not found: $FIXTURE" >&2
  exit 1
fi

INIT="$(mktemp -t valk-lsp-init.XXXXXX.lua)"
trap 'rm -f "$INIT"' EXIT

cat > "$INIT" <<LUA
-- Minimal nvim config for LSP profiling. Registers .valk filetype and
-- attaches an LSP client that talks through the proxy to valk-lsp.

vim.filetype.add({ extension = { valk = "valk" } })

local proxy  = "$PROXY"
local server = "$SERVER"
local root   = "$REPO"

vim.api.nvim_create_autocmd("FileType", {
  pattern = "valk",
  callback = function(args)
    local ok, err = pcall(vim.lsp.start, {
      name = "valk-lsp",
      cmd = { proxy, server },
      root_dir = root,
    })
    if not ok then
      io.stderr:write("vim.lsp.start failed: " .. tostring(err) .. "\n")
    end
  end,
})

-- Print timing checkpoints to stderr so the outer script can correlate.
local t0 = vim.uv.hrtime()
local function mark(label)
  io.stderr:write(string.format("[nvim] +%.1f ms %s\n",
    (vim.uv.hrtime() - t0) / 1e6, label))
end

vim.api.nvim_create_autocmd("LspAttach", {
  callback = function(args)
    mark("LspAttach bufnr=" .. args.buf)
    -- Explicitly request semantic tokens — nvim's automatic semantic-token
    -- refresh only fires when a window is visible, which headless lacks.
    local client = vim.lsp.get_client_by_id(args.data.client_id)
    if client and client.server_capabilities
       and client.server_capabilities.semanticTokensProvider then
      mark("requesting semanticTokens/full")
      client:request("textDocument/semanticTokens/full", {
        textDocument = vim.lsp.util.make_text_document_params(args.buf),
      }, function(err, result, ctx)
        mark("semanticTokens/full reply (err=" .. tostring(err) ..
             ", tokens=" .. tostring(result and #(result.data or {}) or 0) .. ")")
      end, args.buf)
    end
  end,
})

mark("init.lua loaded")
LUA

echo "== profiling valk-lsp via nvim =="
echo "   fixture: $FIXTURE"
echo "   proxy log: $LOG"
echo

rm -f "$LOG"

# Use --cmd so -u still loads our init.lua; then sleep + quit.
nvim --headless -u "$INIT" \
  -c "edit $FIXTURE" \
  -c "lua vim.wait($WAIT_MS)" \
  -c "quitall!" 2>&1 | sed 's/^/    /' || true

echo
echo "== proxy log summary =="

python3 - "$LOG" <<'PY'
import sys, os

path = sys.argv[1]
if not os.path.exists(path):
    print(f"no log at {path}")
    sys.exit(0)

events = []
with open(path) as f:
    for line in f:
        if line.startswith("#"):
            continue
        parts = line.rstrip("\n").split("\t")
        if len(parts) < 4: continue
        try:
            us = int(parts[0])
        except ValueError:
            continue
        events.append((us, parts[1], parts[2], parts[3]))

if not events:
    print("(log empty)")
    sys.exit(0)

# Print all messages with timing
print(f"{'elapsed_ms':>10}  {'dir':<4}  {'bytes':>7}  method/id")
print("-" * 60)
for us, d, b, m in events:
    print(f"{us/1000:>10.1f}  {d:<4}  {b:>7}  {m}")

print()
print("-- key phase latencies --")

# Find key landmarks
def first(pred):
    for e in events:
        if pred(e): return e
    return None

def find_reply_for(req_method):
    # Find the request, then the next S2C message whose id matches
    req = None
    for e in events:
        us, d, b, m = e
        if d == "C2S" and m == req_method:
            req = e
            # Grab the id from the body (we only have method in summary,
            # but for requests with ids, method is still shown — we need
            # to re-open the log to look up id. Simpler: take the *next*
            # S2C message that isn't a notification.
            for e2 in events:
                if e2[0] <= us: continue
                if e2[1] == "S2C" and e2[3].startswith("id="):
                    return req, e2
            return req, None
    return None, None

init_req, init_resp = find_reply_for("initialize")
sem_req, sem_resp = find_reply_for("textDocument/semanticTokens/full")

def phase(label, a, b):
    if a and b:
        dt_ms = (b[0] - a[0]) / 1000
        print(f"  {label:<36}  {dt_ms:>8.1f} ms")
    else:
        print(f"  {label:<36}  (missing)")

start = events[0]
phase("proxy_start -> initialize_sent",  start, init_req)
phase("initialize request -> response",  init_req, init_resp)
phase("initialize_resp -> semTokens_req", init_resp, sem_req)
phase("semTokens_req -> response",       sem_req, sem_resp)
if start and sem_resp:
    phase("TOTAL proxy_start -> sem_resp", start, sem_resp)
PY
