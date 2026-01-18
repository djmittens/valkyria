0a. Run `git branch --show-current` to identify the current branch.
0b. Study `ralph/specs/*` to understand requirements.
0c. Study @ralph/IMPLEMENTATION_PLAN.md for current task list.

## Branch Awareness

IMPORTANT: Check the **Branch:** field in @ralph/IMPLEMENTATION_PLAN.md.
- If it matches current branch, continue with tasks.
- If it doesn't match, the plan is from different work - proceed carefully or run `ralph plan` first.
- Update **Last updated:** when you complete a task.

## CRITICAL: ONE TASK, THEN EXIT

1. Pick ONE incomplete item from @ralph/IMPLEMENTATION_PLAN.md
2. Implement it (search first - don't assume not implemented)
3. Run tests to validate
4. Update @ralph/IMPLEMENTATION_PLAN.md (mark complete, update timestamp)
5. `git add -A && git commit && git push`
6. **EXIT** - the loop restarts you fresh

## Progress Reporting

```
[RALPH] BRANCH: <current branch>
[RALPH] === START: <task> ===
[RALPH] FILE: <file>
```

```
[RALPH] === DONE: <task> ===
[RALPH] RESULT: <summary>
```

## Issue Handling

1. Document issues in @ralph/IMPLEMENTATION_PLAN.md under "## Discovered Issues"
2. DO NOT work around problems - fix them or document them
3. If stuck >5 min, document and EXIT

## Rules

- ONE task, then EXIT
- Complete implementations only, no stubs
- No comments in code unless asked
