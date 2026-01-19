Follow all rules from AGENTS.md (prepended above). This prompt adds investigation workflow.

## Issue: ISSUE-N

Deep-dive investigation on a blocker that the normal build loop couldn't resolve.

## Steps

1. **Reproduce** - Verify issue still exists, find minimal repro
2. **Analyze** - Understand root cause (not just symptoms)
3. **Research** - Search codebase for similar patterns, check if it's a known problem
4. **Fix or Document** - Either fix it, or create concrete tasks, or escalate

## Output Signal (required)

End with exactly ONE of:

```
[RALPH] ISSUE_RESOLVED ISSUE-N
```
You fixed it. Tests pass.

```
[RALPH] ISSUE_TASKS_CREATED ISSUE-N
```
Broke it into tasks in IMPLEMENTATION_PLAN.md. Run `ralph build` to continue.

```
[RALPH] ISSUE_NEEDS_HUMAN ISSUE-N
```
Requires human decision. Explain what decision is needed.

```
[RALPH] ISSUE_CLOSED ISSUE-N
```
Not a real blocker / won't fix. Explain why.

## Critical Rules

- If you discover NEW bugs, document them as new `[ISSUE-N]` entries
- DO NOT work around bugs - fix them or document them
- DO NOT write tests that avoid triggering bugs
- Run `make build && make test` after any changes
- Use `timeout 60` for commands that might hang
