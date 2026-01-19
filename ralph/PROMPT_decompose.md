# DECOMPOSE Stage

A task was killed because it was too large (exceeded context or timeout limits).
You must break it down into smaller subtasks.

## Step 1: Get the Failed Task

Run `ralph query` to see the task that needs decomposition.
The `next.task` field shows the task with `needs_decompose: true`.

## Step 2: Analyze the Task

Use subagents to understand what the task requires:

```
Task: "Analyze what's needed to implement: [task name]

Research the codebase and report:
1. Which files need to be modified
2. What are the distinct pieces of work
3. What order should they be done in
4. Any dependencies between pieces"
```

## Step 3: Create Subtasks

Break the original task into 2-5 smaller tasks that:
- Can each be completed in ONE iteration
- Have clear, specific scope
- Together accomplish the original task

For each subtask:
```
ralph task add '{"name": "Specific subtask", "notes": "What to do", "accept": "How to verify"}'
```

Use `deps` to specify order if needed.

## Step 4: Remove the Original Task

After adding all subtasks, delete the original oversized task:
```
ralph task delete <task-id>
```

## Step 5: Report

```
[RALPH] === DECOMPOSE COMPLETE ===
[RALPH] Original: <original task name>
[RALPH] Split into: N subtasks
```

Then EXIT to let the build loop process the new subtasks.

## Rules

- Each subtask should be completable in ONE iteration (< 100k tokens)
- Be specific: "Add X to file Y" not "Implement feature Z"
- If a subtask is still too big, it will be killed and decomposed again
- DO NOT try to implement anything - just create the task breakdown
