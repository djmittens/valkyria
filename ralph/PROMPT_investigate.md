# INVESTIGATE Stage

Issues were discovered during build. Research and resolve ALL of them in parallel.

## Step 1: Get All Issues

Run `ralph query issues` to see all pending issues.

## Step 2: Parallel Investigation

Use the Task tool to investigate ALL issues in parallel. Launch one subagent per issue:

```
For each issue, launch a Task with prompt:
"Investigate this issue: <issue description>
Issue priority: <issue priority or 'medium' if not set>

1. Read relevant code to understand the problem
2. Determine root cause
3. Decide resolution:
   - If fix is non-trivial: describe the fix task needed
   - If fix is trivial: describe the simple fix
   - If out of scope: explain why

Return a JSON object:
{
  \"issue_id\": \"<id>\",
  \"root_cause\": \"<what you found>\",
  \"resolution\": \"task\" | \"trivial\" | \"out_of_scope\",
  \"task\": {  // only if resolution is \"task\"
    \"name\": \"<fix description>\",
    \"notes\": \"<root cause and approach>\",
    \"accept\": \"<how to verify>\",
    \"priority\": \"<inherit from issue priority above>\"
  },
  \"trivial_fix\": \"<description>\"  // only if resolution is \"trivial\"
}
"
```

## Step 3: Collect Results and Apply

After all subagents complete:

1. Add all tasks in batch (include `created_from` to link back to issue, and `priority` from originating issue):
```
ralph task add '{"name": "...", "notes": "...", "accept": "...", "created_from": "i-xxxx", "priority": "high|medium|low"}'
ralph task add '{"name": "...", "notes": "...", "accept": "...", "created_from": "i-yyyy", "priority": "high|medium|low"}'
...
```

2. Clear all issues in one command:
```
ralph issue done-all
```

Or if only clearing specific issues:
```
ralph issue done-ids i-abc1 i-def2 i-ghi3
```

## Step 4: Report Summary

```
[RALPH] === INVESTIGATE COMPLETE ===
[RALPH] Processed: N issues
[RALPH] Tasks created: X
[RALPH] Trivial fixes: Y
[RALPH] Out of scope: Z
```

## Handling Auto-Generated Pattern Issues

Issues starting with "REPEATED REJECTION" or "COMMON FAILURE PATTERN" are auto-generated from rejection analysis.
These require special handling:

**For REPEATED REJECTION issues:**
1. The same task has failed 3+ times with similar errors
2. Read the spec and task to understand what's expected
3. Compare with rejection reasons to find the gap
4. Usually indicates: missing prerequisite, wrong approach, or spec ambiguity
5. Create a HIGH PRIORITY blocking task that addresses the root cause
6. Consider if the failing task's `deps` should include the new task

**For COMMON FAILURE PATTERN issues:**
1. Multiple different tasks fail with the same error type
2. This strongly indicates a missing prerequisite that all tasks need
3. Read the spec section about the failing functionality
4. The error message tells you what's missing (e.g., "argument count mismatch" = API changed)
5. Create a single HIGH PRIORITY task to fix the root cause
6. Mark existing failing tasks as depending on this new task using `ralph task add '{"deps": [...]}'`

**Example:**
If multiple tasks fail with "grep returns 0, expected 1" and they all involve `aio/then`, likely:
- The API wasn't changed to return handles yet
- A prerequisite C implementation task is missing
- Create: `ralph task add '{"name": "Refactor X to return handle", "priority": "high", "notes": "..."}'`

## IMPORTANT

- Launch ALL investigations in parallel using multiple Task tool calls in a single message
- Wait for all results before applying any changes
- Do NOT make code changes during investigation - only create tasks
- Use `ralph issue done-all` to clear all issues at once
- EXIT after all issues are resolved
