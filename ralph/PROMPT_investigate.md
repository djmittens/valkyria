# INVESTIGATE Stage

Issues were discovered during build or verification. Research and resolve ALL of them in parallel.

## Step 1: Get All Issues

Run `ralph query issues` to see all pending issues.

## Step 2: Parallel Investigation with Structured Output

Use the Task tool to investigate ALL issues in parallel. Each subagent MUST return structured findings:

```
Task: "Investigate this issue: <issue description>
Issue ID: <id>
Issue priority: <priority or 'medium'>

Analyze the codebase and return a JSON object:
{
  \"issue_id\": \"<id>\",
  \"root_cause\": \"<specific file:line reference>\",
  \"resolution\": \"task\" | \"trivial\" | \"out_of_scope\",
  \"task\": {
    \"name\": \"<specific fix>\",
    \"notes\": \"Root cause: <file:line>. Fix: <approach>. Imports: <needed>. Risk: <side effects>.\",
    \"accept\": \"<measurable command + expected result>\",
    \"priority\": \"<from issue>\",
    \"research\": {\"files_analyzed\": [\"path:lines\"], \"root_cause_location\": \"file:line\"}
  }
}"
```

## Step 3: Create Tasks with Full Context

After subagents complete, create tasks preserving research:

```
ralph task add '{"name": "Fix: <desc>", "notes": "Root cause: <file:line>. Fix: <approach>. Pattern: <similar code>. Risk: <effects>.", "accept": "<measurable>", "created_from": "<issue-id>", "priority": "<from issue>", "research": {"files_analyzed": ["path:lines"], "root_cause_location": "file:line"}}'
```

### Task Notes Template for Issues

```
Root cause: <file:line - specific problem>. 
Current behavior: <what happens>. Expected: <what should happen>. 
Fix approach: <how to fix>. Similar pattern: <existing code ref>. 
Imports needed: <any>. Risk: <side effects>.
```

## Step 4: Clear Issues

```
ralph issue done-all
```

## Step 5: Report

```
[RALPH] === INVESTIGATE COMPLETE ===
[RALPH] Processed: N issues
[RALPH] Tasks created: X (with full context)
```

## Handling Auto-Generated Pattern Issues

**REPEATED REJECTION issues:** Same task failed 3+ times
- Create HIGH PRIORITY blocking task addressing root cause
- Notes MUST include: which task fails, rejection pattern, how new task unblocks it

**COMMON FAILURE PATTERN issues:** Multiple tasks fail same way
- Create single HIGH PRIORITY task fixing root cause
- Notes MUST include: error pattern, affected tasks, fix approach

## Validation

Tasks from issues are validated. REJECTED if:
- Notes < 50 chars or missing root cause location
- Acceptance criteria is vague
- Missing file:line references

## Rules

- Launch ALL investigations in parallel
- Preserve research in notes with file:line references
- Measurable acceptance for every task
- Use `created_from` to link to source issue
- EXIT after all issues resolved
