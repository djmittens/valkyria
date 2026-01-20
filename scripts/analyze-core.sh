#!/bin/bash
# Analyze a core dump with GDB/LLDB
# Usage: ./scripts/analyze-core.sh [executable] [core-file]
#
# Examples:
#   ./scripts/analyze-core.sh                    # Auto-detect latest core
#   ./scripts/analyze-core.sh build/valk core    # Specific core file
#   ./scripts/analyze-core.sh build/valk         # Use coredumpctl on Linux

set -e

EXECUTABLE="${1:-build/valk}"
COREFILE="$2"

UNAME=$(uname -s)

echo "=== Core Dump Analysis ==="
echo "Platform: $UNAME"
echo "Executable: $EXECUTABLE"

# Find core file if not specified
if [ -z "$COREFILE" ]; then
    if [ "$UNAME" = "Linux" ]; then
        # Try coredumpctl first
        if command -v coredumpctl &>/dev/null; then
            echo "Using systemd coredumpctl..."
            echo
            coredumpctl info 2>/dev/null || echo "No recent core dumps found"
            echo
            echo "=== Backtrace from latest dump ==="
            coredumpctl gdb -q --batch \
                -ex "bt full" \
                -ex "info threads" \
                -ex "thread apply all bt" \
                2>/dev/null || echo "Could not analyze with coredumpctl"
            exit 0
        fi
        
        # Look for core files
        for pattern in "core" "core.*" "/tmp/core.*" "/var/crash/core.*"; do
            FOUND=$(ls -t $pattern 2>/dev/null | head -1)
            if [ -n "$FOUND" ]; then
                COREFILE="$FOUND"
                break
            fi
        done
    elif [ "$UNAME" = "Darwin" ]; then
        # macOS cores
        COREFILE=$(ls -t /cores/core.* 2>/dev/null | head -1)
    fi
fi

if [ -z "$COREFILE" ] || [ ! -f "$COREFILE" ]; then
    echo "No core file found."
    echo
    echo "To enable core dumps:"
    echo "  ulimit -c unlimited"
    echo
    if [ "$UNAME" = "Linux" ]; then
        echo "Check /proc/sys/kernel/core_pattern for dump location"
        echo "Or use: coredumpctl list"
    elif [ "$UNAME" = "Darwin" ]; then
        echo "Core dumps go to /cores/"
    fi
    exit 1
fi

echo "Core file: $COREFILE"
echo

if [ "$UNAME" = "Linux" ]; then
    # Use GDB
    if ! command -v gdb &>/dev/null; then
        echo "GDB not found. Install with: apt install gdb"
        exit 1
    fi
    
    gdb -batch \
        -ex "file $EXECUTABLE" \
        -ex "core-file $COREFILE" \
        -ex "echo === Signal Information ===\n" \
        -ex "info signal" \
        -ex "echo \n=== Crash Location ===\n" \
        -ex "frame" \
        -ex "list" \
        -ex "echo \n=== Full Backtrace ===\n" \
        -ex "bt full" \
        -ex "echo \n=== Registers ===\n" \
        -ex "info registers" \
        -ex "echo \n=== All Threads ===\n" \
        -ex "info threads" \
        -ex "thread apply all bt" \
        -ex "quit"
        
elif [ "$UNAME" = "Darwin" ]; then
    # Use LLDB
    if ! command -v lldb &>/dev/null; then
        echo "LLDB not found (should be installed with Xcode)"
        exit 1
    fi
    
    lldb --batch \
        -o "target create \"$EXECUTABLE\" --core \"$COREFILE\"" \
        -o "bt" \
        -o "bt all" \
        -o "register read" \
        -o "quit"
fi

echo
echo "=== Analysis Complete ==="
echo
echo "For interactive debugging:"
if [ "$UNAME" = "Linux" ]; then
    echo "  gdb $EXECUTABLE $COREFILE"
else
    echo "  lldb --core $COREFILE $EXECUTABLE"
fi
