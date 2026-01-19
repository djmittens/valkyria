Follow all rules from AGENTS.md (prepended above). This prompt adds ralph-specific workflow.

## Setup

1. Run `git branch --show-current` to identify the current branch
2. Read `ralph/specs/*` for requirements
3. Read @ralph/IMPLEMENTATION_PLAN.md for current task list

Check **Branch:** field matches current branch. If not, the plan is stale.

## Workflow: ONE TASK, THEN EXIT

1. Pick ONE incomplete `- [ ]` item from @ralph/IMPLEMENTATION_PLAN.md
2. Implement it fully (search first - don't assume not implemented)
3. Run `make build && make test` to validate
4. Update @ralph/IMPLEMENTATION_PLAN.md (mark `- [x]`, update timestamp)
5. `git add -A && git commit && git push`
6. **EXIT** - the loop restarts you fresh

## Progress Signals

```
[RALPH] === START: <task> ===
[RALPH] === DONE: <task> ===
```

## Discovering Issues

When blocked, add to "## Discovered Issues" in IMPLEMENTATION_PLAN.md:

```
- [ISSUE-N] Title: What's wrong. Why it blocks. Reproduction: `command`. Tried: what failed.
```

Then EXIT - don't work around it.
