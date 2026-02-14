#!/bin/bash
# Generate CPU flame graph for Valkyria
# Usage: ./scripts/flamegraph.sh [output.svg] [executable] [args...]
#
# Examples:
#   ./scripts/flamegraph.sh                    # Default: profile valk with prelude
#   ./scripts/flamegraph.sh cpu.svg            # Custom output file
#   ./scripts/flamegraph.sh gc.svg build/valk src/prelude.valk test/test_gc.valk
#
# Requirements:
#   - Linux: perf, FlameGraph tools (or install via: git clone https://github.com/brendangregg/FlameGraph)
#   - macOS: dtrace (sudo required), FlameGraph tools

set -e

# Parse arguments
OUTPUT="${1:-cpu.svg}"
shift 2>/dev/null || true

if [ $# -eq 0 ]; then
    EXECUTABLE="build/valk"
    ARGS="src/prelude.valk test/test_prelude.valk"
else
    EXECUTABLE="$1"
    shift
    ARGS="$*"
fi

# Find FlameGraph tools
if command -v stackcollapse-perf.pl &>/dev/null; then
    FLAMEGRAPH_DIR=""
elif [ -d "$HOME/FlameGraph" ]; then
    FLAMEGRAPH_DIR="$HOME/FlameGraph/"
elif [ -d "/opt/FlameGraph" ]; then
    FLAMEGRAPH_DIR="/opt/FlameGraph/"
else
    echo "FlameGraph tools not found. Install with:"
    echo "  git clone https://github.com/brendangregg/FlameGraph ~/FlameGraph"
    exit 1
fi

STACKCOLLAPSE="${FLAMEGRAPH_DIR}stackcollapse-perf.pl"
FLAMEGRAPH="${FLAMEGRAPH_DIR}flamegraph.pl"

echo "=== Flame Graph Generation ==="
echo "Output: $OUTPUT"
echo "Command: $EXECUTABLE $ARGS"
echo

UNAME=$(uname -s)

if [ "$UNAME" = "Linux" ]; then
    echo "Recording with perf (99 Hz, 30 seconds max)..."
    
    # Record
    perf record -F 99 -g --call-graph dwarf -o perf.data -- $EXECUTABLE $ARGS
    
    # Generate folded stacks
    echo "Processing stacks..."
    perf script -i perf.data | $STACKCOLLAPSE > out.folded
    
    # Generate flame graph
    echo "Generating flame graph..."
    $FLAMEGRAPH \
        --title "Valkyria CPU Profile" \
        --subtitle "$EXECUTABLE $ARGS" \
        --hash \
        --width 1200 \
        out.folded > "$OUTPUT"
    
    # Cleanup
    rm -f perf.data out.folded
    
elif [ "$UNAME" = "Darwin" ]; then
    echo "Recording with dtrace (requires sudo)..."
    
    # Need to run dtrace separately
    STACKS_FILE=$(mktemp)
    
    # Start the program in background
    $EXECUTABLE $ARGS &
    PID=$!
    sleep 1
    
    if ! ps -p $PID > /dev/null 2>&1; then
        echo "Process exited too quickly for profiling"
        exit 1
    fi
    
    echo "Profiling PID $PID for 30 seconds..."
    sudo dtrace -x ustackframes=100 -n "
        profile-99 /pid == $PID/ {
            @[ustack()] = count();
        }
        tick-30s { exit(0); }
    " -o "$STACKS_FILE" 2>/dev/null || true
    
    # Kill if still running
    kill $PID 2>/dev/null || true
    
    # Generate flame graph
    echo "Generating flame graph..."
    ${FLAMEGRAPH_DIR}stackcollapse.pl "$STACKS_FILE" | $FLAMEGRAPH \
        --title "Valkyria CPU Profile" \
        --subtitle "$EXECUTABLE $ARGS" \
        --hash \
        --width 1200 \
        > "$OUTPUT"
    
    rm -f "$STACKS_FILE"
else
    echo "Unsupported platform: $UNAME"
    exit 1
fi

echo
echo "Generated: $OUTPUT"

# Try to open
if [ "$UNAME" = "Linux" ] && command -v xdg-open &>/dev/null; then
    xdg-open "$OUTPUT" 2>/dev/null &
elif [ "$UNAME" = "Darwin" ]; then
    open "$OUTPUT" 2>/dev/null &
fi
