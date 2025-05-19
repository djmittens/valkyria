#!/usr/bin/env bash

set -uo pipefail  # remove `-e` so we don’t exit on test failure

WATCH_DIRS=("src" "test")

run_tests() {
  clear
  echo "Change detected at $(date). Running 'make test'..."
  echo "=============================================="
  if ! make test; then
    echo "⚠️  'make test' failed, but continuing to watch..."
  fi
  echo "=============================================="
  echo "Waiting for further changes..."
}

echo "Watching ${WATCH_DIRS[*]} for changes. Press Ctrl+C to stop."

case "$(uname)" in
  Darwin)
    if ! command -v fswatch >/dev/null; then
      echo "Error: fswatch not found. Install with 'brew install fswatch'"
      exit 1
    fi

    fswatch -o "${WATCH_DIRS[@]}" | while read -r _; do
      run_tests
    done
    ;;

  Linux)
    if ! command -v inotifywait >/dev/null; then
      echo "Error: inotifywait not found. Install with 'sudo pacman -S inotify-tools'"
      exit 1
    fi

    while true; do
      run_tests
      inotifywait -qq -r -e modify,create,delete,move "${WATCH_DIRS[@]}"
    done
    ;;

  *)
    echo "Unsupported OS: $(uname)"
    exit 1
    ;;
esac
