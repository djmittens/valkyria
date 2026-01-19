# INVESTIGATE Stage

Issues were discovered during build. Research and resolve ALL of them in parallel.

## Step 1: Get All Issues

Run `ralph query issues` to see all pending issues.

## Step 2: Parallel Investigation

Use the Task tool to investigate ALL issues in parallel. Launch one subagent per issue:

```
For each issue, launch a Task with prompt:
"Investigate this issue: <issue description>

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
    \"accept\": \"<how to verify>\"
  },
  \"trivial_fix\": \"<description>\"  // only if resolution is \"trivial\"
}
"
```

## Step 3: Collect Results and Apply

After all subagents complete:

1. Add all tasks in batch:
```
ralph task add '{"name": "...", "notes": "...", "accept": "..."}'
ralph task add '{"name": "...", "notes": "...", "accept": "..."}'
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

## IMPORTANT

- Launch ALL investigations in parallel using multiple Task tool calls in a single message
- Wait for all results before applying any changes
- Do NOT make code changes during investigation - only create tasks
- Use `ralph issue done-all` to clear all issues at once
- EXIT after all issues are resolved
