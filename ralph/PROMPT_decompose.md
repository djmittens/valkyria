# DECOMPOSE Stage

A task was killed because it was too large (exceeded context or timeout limits).
You must break it down into smaller subtasks.

## Step 1: Get the Failed Task

Run `ralph query` to see the task that needs decomposition.
The `next.task` field shows:
- `name`: The task that failed
- `kill_reason`: Why it was killed ("timeout" or "context_limit")
- `kill_log`: Path to the log from the failed iteration

## Step 2: Review the Failed Iteration Log (if available)

If `kill_log` is provided in the task, review it to understand what went wrong.

**CRITICAL**: The log file may be HUGE (it killed the previous iteration's context!). 
NEVER read the entire file. Always use head/tail:

```bash
# First check the size
wc -l <kill_log_path>

# Read ONLY the header (first 50 lines) - shows what task started
head -50 <kill_log_path>

# Read ONLY the tail (last 100 lines) - shows where it stopped  
tail -100 <kill_log_path>

# If you need to search for specific content
grep -n -E "error|Error|ERROR|failed|FAILED" <kill_log_path> | head -20
```

From this limited sample, determine:
- What work was started but not completed
- Where the iteration got stuck or ran out of context
- Which files were being modified
- Any partial progress that was made
- **What output flooded the context** (e.g., sanitizer output, verbose test logs)
  - This is important! Subtasks may need to suppress or redirect verbose output

If no `kill_log` is provided, skip this step and proceed to analyze the task based on its description.

## Step 3: Analyze the Task

Use subagents to understand what the task requires:

```
Task: "Analyze what's needed to implement: [task name]

Research the codebase and report:
1. Which files need to be modified
2. What are the distinct pieces of work
3. What order should they be done in
4. Any dependencies between pieces"
```

## Step 4: Create Subtasks

Break the original task into 2-5 smaller tasks that:
- Can each be completed in ONE iteration
- Have clear, specific scope
- Together accomplish the original task
- Account for any partial progress from the failed iteration

For each subtask, **include `parent` to link back to the original task**:
```
ralph task add '{"name": "Specific subtask", "notes": "What to do", "accept": "How to verify", "parent": "<original-task-id>"}'
```

Use `deps` to specify order if needed.

## Step 5: Remove the Original Task

After adding all subtasks, delete the original oversized task:
```
ralph task delete <task-id>
```

## Step 6: Report

```
[RALPH] === DECOMPOSE COMPLETE ===
[RALPH] Original: <original task name>
[RALPH] Kill reason: <timeout|context_limit>
[RALPH] Split into: N subtasks
```

Then EXIT to let the build loop process the new subtasks.

## Rules

- ALWAYS read the log file first to understand what happened
- Each subtask should be completable in ONE iteration (< 100k tokens)
- Be specific: "Add X to file Y" not "Implement feature Z"
- If a subtask is still too big, it will be killed and decomposed again
- DO NOT try to implement anything - just create the task breakdown
