# BUILD Stage

Implement the next pending task.

## Step 1: Get Task

Run `ralph query` to get current state. The `next.task` field shows:
- `name`: what to do
- `notes`: implementation hints (if provided)
- `accept`: how to verify it works (if provided)

## Step 2: Understand Context

1. Read the spec file: `ralph/specs/<spec>`
2. Search codebase first - don't assume something isn't implemented
3. Review `notes` for implementation hints

## Step 3: Implement

Build the feature/fix. Rules:
- Complete implementations only, no stubs
- No code comments unless explicitly requested

## Step 4: Validate

Before marking done, verify the implementation:
1. If `accept` criteria provided, verify those specifically
2. Run relevant tests
3. Ensure the implementation matches the spec

## Step 5: Complete

```
ralph task done
```

This marks the task done and auto-commits.

## Discovering Issues

If you find a problem unrelated to the current task:
```
ralph issue add "description of issue"
```

Issues are investigated later in the INVESTIGATE stage.

## Progress Reporting

```
[RALPH] === START: <task name> ===
```

```
[RALPH] === DONE: <task name> ===
[RALPH] RESULT: <summary>
```

## EXIT after marking task done
