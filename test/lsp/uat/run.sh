#!/bin/bash
# UAT entry point: drive the valk-lsp through real neovim, run all
# scenarios under test/lsp/uat/scenarios/, report pass/fail.
#
# **Workspace isolation:** each run mkdirs a fresh temp dir, copies
# test/lsp/uat/fixtures/ into it, and points nvim's cwd + LSP root_dir
# at that dir. This keeps:
#   - The real .valk/symdb.sqlite untouched (no cross-run pollution)
#   - Workspace scan to a small fixed set of fixtures (not 180+ repo files)
#   - Each invocation reproducible regardless of repo state
#   - /tmp file scenarios indistinguishable from in-workspace ones
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
#   VALK_UAT_KEEP    if set non-empty, retain the temp workspace on exit
#                    (debugging — find it under $TMPDIR/valk-uat-*)

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

# Optional belt-and-suspenders: cap the UAT subtree's RSS via cgroup
# under systemd. Note we do NOT use `ulimit -v` (RLIMIT_AS) because
# valk's GC reserves ~36 GiB of virtual address space at startup
# (PROT_NONE, not committed) and would fail to start under any
# realistic AS cap.
#
# Set VALK_UAT_MEMMAX=2G (or similar systemd format) to opt in.
# Requires `systemd-run` and the user-scope to be available; falls
# through silently otherwise.
if [ -n "${VALK_UAT_MEMMAX:-}" ] && command -v systemd-run >/dev/null 2>&1; then
  exec systemd-run --user --scope --quiet \
    -p "MemoryMax=$VALK_UAT_MEMMAX" \
    -p "MemorySwapMax=0" \
    -- "$0" "$@"
fi

# Orphan check: if a previous interrupted run left a valk-lsp (ours)
# behind, warn loudly. The cleanup trap below tries hard to prevent
# this, but if the process tree was SIGKILL'd from outside no trap
# could have run.
existing_orphans=$(pgrep -f "^${SERVER}\$" 2>/dev/null | wc -l)
if [ "$existing_orphans" -gt 0 ]; then
  echo "UAT: WARNING — $existing_orphans pre-existing valk-lsp process(es) detected:" >&2
  pgrep -af "^${SERVER}\$" >&2 || true
  echo "     Kill them with: pkill -KILL -f '^${SERVER}\$'" >&2
  echo "     Continuing; new run will spawn its own LSP." >&2
fi

WORKSPACE="$(mktemp -d -t valk-uat-XXXXXX)"
RESULTS="$(mktemp -t valk-uat-results-XXXXXX.jsonl)"

# Track the nvim child so we can kill the whole subtree on any exit
# path. Without this, an external SIGTERM (e.g. from `timeout` or
# Ctrl-C) kills the bash wrapper but leaves nvim + valk-lsp running
# as orphans, each holding ~1GB of GC heap. Multiple interrupted runs
# pile up orphan LSPs and have OOM'd the host (lesson learned).
NVIM_PID=
LSP_PROC_GLOB="${VALK_LSP_BIN:-build/valk-lsp}"

cleanup() {
  # Block re-entry of this trap during our own kill burst.
  trap '' EXIT INT TERM HUP

  if [ -n "$NVIM_PID" ] && kill -0 "$NVIM_PID" 2>/dev/null; then
    kill -TERM "$NVIM_PID" 2>/dev/null || true
    # Hand-collect descendants in case nvim exited before forwarding
    # to its LSP child. pgrep -P walks the parent-pid tree.
    pgrep -P "$NVIM_PID" 2>/dev/null | xargs -r kill -TERM 2>/dev/null || true
    sleep 0.3
    kill -KILL "$NVIM_PID" 2>/dev/null || true
    pgrep -P "$NVIM_PID" 2>/dev/null | xargs -r kill -KILL 2>/dev/null || true
  fi
  # Fallback: if pids leaked beyond what we can track (e.g. nvim was
  # SIGKILL'd before its trap ran and the LSP child got reparented),
  # sweep by exact binary path. This is intentionally narrow — only
  # processes pointing at OUR build of valk-lsp.
  pkill -TERM -f "^${LSP_PROC_GLOB}\$" 2>/dev/null || true
  sleep 0.1
  pkill -KILL -f "^${LSP_PROC_GLOB}\$" 2>/dev/null || true

  rm -f "$RESULTS"
  if [ -z "${VALK_UAT_KEEP:-}" ]; then
    rm -rf "$WORKSPACE"
  else
    echo "UAT: kept workspace at $WORKSPACE" >&2
  fi
}
trap cleanup EXIT INT TERM HUP

# Seed the workspace with the fixtures the scenarios reference. Everything
# else (per-scenario temp files, mutated buffers, etc.) lives under
# this dir and disappears on exit.
cp -r "$REPO/test/lsp/uat/fixtures/." "$WORKSPACE/"

VALK_LSP_BIN="$SERVER" \
VALK_UAT_RESULTS="$RESULTS" \
VALK_UAT_WORKSPACE="$WORKSPACE" \
  "$NVIM" --headless -l "$REPO/test/lsp/uat/runner.lua" "$FILTER" 2>&1 &
NVIM_PID=$!

# Watchdog process. SIGKILL on the bash wrapper bypasses traps, so
# the cleanup() above doesn't run. The watchdog is a separate
# background process that polls our pid and, if we vanish, kills the
# specific nvim child we spawned and any valk-lsp descendants. Yes,
# the watchdog itself can be SIGKILL'd — but a typical "kill the
# test" only targets the foreground bash pid, not its background
# descendants (which is what bit us last time and OOM'd the host).
#
# It ignores terminal-driven SIGINT/SIGHUP so a Ctrl-C on a parent
# shell doesn't take it out before the cleanup completes.
WATCHDOG_PID=
PARENT_PID=$$
(
  trap '' INT HUP
  while kill -0 "$PARENT_PID" 2>/dev/null; do
    sleep 1
  done
  # Parent vanished without notifying us. Take the whole tree down.
  if kill -0 "$NVIM_PID" 2>/dev/null; then
    pgrep -P "$NVIM_PID" 2>/dev/null | xargs -r kill -KILL 2>/dev/null || true
    kill -KILL "$NVIM_PID" 2>/dev/null || true
  fi
  # Path-based sweep catches any LSP that escaped (e.g. nvim already
  # died but its child got reparented).
  pkill -KILL -f "^${SERVER}\$" 2>/dev/null || true
) &
WATCHDOG_PID=$!
disown 2>/dev/null || true
# `wait` is interruptible — if a SIGTERM arrives while waiting, the
# trap fires, kills the tree, and we resume here with wait returning
# the signal status. Either way, on return the cleanup trap will run.
wait "$NVIM_PID" 2>/dev/null || true

# Clean shutdown path: signal the watchdog to exit. (Unclean shutdowns
# leave the watchdog to do its job.)
if [ -n "$WATCHDOG_PID" ]; then
  kill "$WATCHDOG_PID" 2>/dev/null || true
fi

if [ ! -s "$RESULTS" ]; then
  echo "UAT: runner produced no results — nvim crashed or scenarios all filtered out" >&2
  exit 2
fi

fails=$(grep -c '"status":"fail"' "$RESULTS" || true)
passes=$(grep -c '"status":"pass"' "$RESULTS" || true)
echo "UAT: $passes passed, $fails failed" >&2

if [ "$fails" -gt 0 ]; then exit 1; fi
exit 0
