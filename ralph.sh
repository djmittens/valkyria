#!/bin/bash
# Ralph Wiggum Loop - Autonomous AI Development
# Usage: ./ralph.sh [plan] [max_iterations]
# Examples:
#   ./ralph.sh              # Build mode, unlimited iterations
#   ./ralph.sh 20           # Build mode, max 20 iterations
#   ./ralph.sh plan         # Plan mode, unlimited iterations
#   ./ralph.sh plan 5       # Plan mode, max 5 iterations

# Parse arguments
if [ "$1" = "plan" ]; then
    MODE="plan"
    PROMPT_FILE="PROMPT_plan.md"
    MAX_ITERATIONS=${2:-0}
elif [[ "$1" =~ ^[0-9]+$ ]]; then
    MODE="build"
    PROMPT_FILE="PROMPT_build.md"
    MAX_ITERATIONS=$1
else
    MODE="build"
    PROMPT_FILE="PROMPT_build.md"
    MAX_ITERATIONS=0
fi

ITERATION=0
CURRENT_BRANCH=$(git branch --show-current)
LOG_FILE="ralph-$(date +%Y%m%d-%H%M%S).log"

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Mode:   $MODE"
echo "Prompt: $PROMPT_FILE"
echo "Branch: $CURRENT_BRANCH"
echo "Log:    $LOG_FILE"
[ $MAX_ITERATIONS -gt 0 ] && echo "Max:    $MAX_ITERATIONS iterations"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Verify prompt file exists
if [ ! -f "$PROMPT_FILE" ]; then
    echo "Error: $PROMPT_FILE not found"
    exit 1
fi

while true; do
    if [ $MAX_ITERATIONS -gt 0 ] && [ $ITERATION -ge $MAX_ITERATIONS ]; then
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        echo "Reached max iterations: $MAX_ITERATIONS"
        echo "Log saved to: $LOG_FILE"
        echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
        break
    fi

    ITERATION=$((ITERATION + 1))
    START_TIME=$(date +%s)
    
    echo ""
    echo "╔═══════════════════════════════════════════════════════════════╗"
    echo "║  RALPH ITERATION $ITERATION - $(date '+%Y-%m-%d %H:%M:%S')                       ║"
    echo "╚═══════════════════════════════════════════════════════════════╝"
    echo ""

    # Run Ralph iteration with selected prompt
    # Show output in real-time AND log it
    cat "$PROMPT_FILE" | claude -p \
        --dangerously-skip-permissions \
        --verbose 2>&1 | tee -a "$LOG_FILE"

    END_TIME=$(date +%s)
    DURATION=$((END_TIME - START_TIME))
    
    echo ""
    echo "┌───────────────────────────────────────────────────────────────┐"
    echo "│  Iteration $ITERATION completed in ${DURATION}s                              │"
    echo "└───────────────────────────────────────────────────────────────┘"

    # Push changes after each iteration
    git push origin "$CURRENT_BRANCH" 2>/dev/null || {
        echo "[RALPH] Creating remote branch..."
        git push -u origin "$CURRENT_BRANCH"
    }

    # Show git log of what was committed this iteration
    echo ""
    echo "Recent commits:"
    git log --oneline -3
    echo ""
done
