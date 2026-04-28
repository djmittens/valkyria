#!/bin/bash
# UAT entry point: drive the valk-lsp through real neovim, run all
# scenarios under test/lsp/uat/scenarios/, report pass/fail.
#
# Exit codes:
#   0 — all scenarios passed (or skipped: nvim missing in non-strict mode)
#   1 — at least one scenario failed
#   2 — environment broken (no LSP binary, results missing, etc.)
#
# Env:
#   NVIM           override nvim binary path (default: nvim)
#   VALK_LSP_BIN   override LSP binary path  (default: build/valk-lsp)
#   VALK_UAT_FILTER  Lua pattern; only run scenarios matching ($1 also works)
#   VALK_UAT_STRICT  if set non-empty, missing nvim is fatal (default: skip)
#
# Output:
#   stderr: per-scenario PASS/FAIL line + summary
#   stdout: nothing (script is composable into other test runners)

set -eu

cd "$(dirname "$0")/../../.."
REPO="$PWD"

NVIM="${NVIM:-nvim}"
SERVER="${VALK_LSP_BIN:-$REPO/build/valk-lsp}"
FILTER="${1:-${VALK_UAT_FILTER:-}}"

if ! command -v "$NVIM" >/dev/null 2>&1; then
  if [ -n "${VALK_UAT_STRICT:-}" ]; then
    echo "UAT: nvim not found (VALK_UAT_STRICT set; treating as failure)" >&2
    exit 2
  fi
  echo "UAT: nvim not found, skipping" >&2
  exit 0
fi

if [ ! -x "$SERVER" ]; then
  echo "UAT: missing LSP binary at $SERVER" >&2
  echo "     build it: $REPO/build/valk --build $REPO/scripts/lsp/build-main.valk -o $SERVER" >&2
  exit 2
fi

RESULTS="$(mktemp -t valk-uat-XXXXXX.jsonl)"
trap "rm -f \"$RESULTS\"" EXIT

VALK_LSP_BIN="$SERVER" \
VALK_UAT_RESULTS="$RESULTS" \
  "$NVIM" --headless -l "$REPO/test/lsp/uat/runner.lua" "$FILTER" 2>&1 || true

if [ ! -s "$RESULTS" ]; then
  echo "UAT: runner produced no results — nvim crashed or scenarios all filtered out" >&2
  exit 2
fi

# Summarize. The runner's stderr already printed per-scenario lines;
# we just need to set the exit code.
fails=$(grep -c '"status":"fail"' "$RESULTS" || true)
passes=$(grep -c '"status":"pass"' "$RESULTS" || true)
echo "UAT: $passes passed, $fails failed" >&2

if [ "$fails" -gt 0 ]; then exit 1; fi
exit 0
