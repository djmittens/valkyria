Follow all rules from AGENTS.md (prepended above). This prompt adds ralph-specific workflow.

## Setup

1. Run `git branch --show-current` to identify the current branch
2. Read `ralph/specs/*` for requirements
3. Read @ralph/IMPLEMENTATION_PLAN.md for current task list and issues

Check **Branch:** field matches current branch. If not, the plan is stale.

## Workflow: ONE TASK OR ISSUE, THEN EXIT

Pick ONE of the following (in priority order):

### A) Open Issue (status: OPEN or BLOCKED)
If there are issues without `**[NEEDS_DECISION]**` or `**[RESOLVED]**` status:
1. Investigate: reproduce, find root cause
2. If clear fix exists: implement it, run tests, mark `**[RESOLVED]**`
3. If multiple valid approaches: document options in the issue, mark `**[NEEDS_DECISION]**`
4. If creates new tasks: add them to plan, mark issue `**[RESOLVED]**`

### B) Incomplete Task
If no actionable issues, pick ONE incomplete `- [ ]` item:
1. Implement it fully (search first - don't assume not implemented)
2. Run `make build && make test` to validate
3. Mark `- [x]`, update timestamp

Then: `git add -A && git commit && git push` and **EXIT**

## Issue Statuses

- `**[OPEN]**` or no marker - Needs investigation (pick this up)
- `**[BLOCKED]**` - Known blocker, needs investigation (pick this up)
- `**[NEEDS_DECISION]**` - Options documented, waiting for user (SKIP)
- `**[RESOLVED]**` - Fixed (SKIP)
- `**[WONTFIX]**` - Intentionally not fixing (SKIP)

## Documenting Options (for NEEDS_DECISION)

When marking an issue as NEEDS_DECISION, format it like:

```
- **[NEEDS_DECISION]** Title: Root cause explanation.
  - **Option A**: [approach] - Pros: ... Cons: ...
  - **Option B**: [approach] - Pros: ... Cons: ...
  - **Recommendation**: [which option and why]
```

## Progress Signals

```
[RALPH] === START: <task or issue> ===
[RALPH] === DONE: <task or issue> ===
```

## Creating New Issues

When blocked by something new, add to "## Discovered Issues":

```
- **[OPEN]** Title: What's wrong. Reproduction: `command`. Tried: what failed.
```

Then EXIT - don't work around it.
