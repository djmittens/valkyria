# DECOMPOSE Stage

A task was killed because it was too large (exceeded context or timeout limits).
You must break it down into smaller subtasks.

## Step 1: Get the Failed Task

Run `ralph query` to see the task that needs decomposition.
The `next.task` field shows:
- `name`: The task that failed
- `notes`: Original implementation guidance
- `kill_reason`: Why it was killed ("timeout" or "context_limit")
- `kill_log`: Path to the log from the failed iteration

## Step 2: Review the Failed Iteration Log

**CRITICAL**: Log may be HUGE. NEVER read entire file:

```bash
wc -l <kill_log_path>
head -50 <kill_log_path>
tail -100 <kill_log_path>
```

Determine: what was completed, what caused context explosion, partial progress.

## Step 3: Research the Breakdown

Use subagent to analyze:

```
Task: "Analyze how to decompose: [task name]
Original notes: [task notes]

Return JSON:
{
  \"remaining_work\": [
    {\"subtask\": \"<specific piece>\", \"files\": [{\"path\": \"file.py\", \"lines\": \"100-150\"}], \"effort\": \"small|medium\"}
  ],
  \"context_risks\": \"<what caused explosion>\",
  \"mitigation\": \"<how subtasks avoid it>\"
}"
```

## Step 4: Create Subtasks with Full Context

Each subtask MUST include:

1. **Source locations**: Exact file paths with line numbers
2. **What to do**: Specific bounded action
3. **How to do it**: Implementation approach
4. **Context from parent**: What was learned
5. **Risk mitigation**: How to avoid re-kill

**Template:**
```
ralph task add '{"name": "Specific subtask", "notes": "Source: <file> lines <N-M>. <Action>. Imports: <list>. Context from parent: <findings>. Risk mitigation: <avoid context explosion by...>", "accept": "<measurable>", "parent": "<task-id>"}'
```

**Example:**
```json
{
  "name": "Create fallback.py with DashboardState dataclass",
  "notes": "Source: powerplant/ralph lines 4022-4045 (DashboardState only). Create ralph/tui/fallback.py with just dataclass. Imports: dataclass, field, Optional, deque. Risk mitigation: Don't extract full class yet - just dataclass.",
  "accept": "python3 -c 'from ralph.tui.fallback import DashboardState' exits 0",
  "parent": "t-original"
}
```

## Step 5: Delete Original Task

```
ralph task delete <original-task-id>
```

## Step 6: Report

```
[RALPH] === DECOMPOSE COMPLETE ===
[RALPH] Original: <task name>
[RALPH] Kill reason: <timeout|context_limit>
[RALPH] Context risk: <what caused explosion>
[RALPH] Mitigation: <how subtasks avoid it>
[RALPH] Split into: N subtasks
```

## Validation

Subtasks are validated. REJECTED if:
- Notes < 50 chars or missing source line numbers
- Modification tasks without specific locations
- Acceptance criteria is vague

## Rules

1. ALWAYS review kill log first (head/tail only!)
2. Each subtask < 100k tokens - completable in ONE iteration
3. Preserve context from parent task notes
4. Include line numbers for every subtask
5. Measurable acceptance criteria
6. Include risk mitigation for each subtask
7. Maximum decomposition depth: 3 levels
8. DO NOT implement - just create task breakdown
