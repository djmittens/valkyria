Follow all rules from AGENTS.md (prepended above). This prompt adds investigation workflow.

## Issue: ISSUE-N

Deep-dive investigation on a blocker. This is a RESEARCH-ONLY task - do not implement fixes.

## Steps

1. **Reproduce** - Verify issue still exists, find minimal repro
2. **Analyze** - Understand root cause (not just symptoms)
3. **Research** - Search codebase AND web for similar patterns, known issues, solutions
4. **Document** - Update the issue in IMPLEMENTATION_PLAN.md with findings and options

## Web Search

Use web search to:
- Find known issues / bug reports for similar problems
- Check library documentation for correct usage
- Research error messages
- Find solutions others have used

Do NOT use web search for:
- Project-specific code (use codebase search)
- Things you already know confidently

## Output: Update the Issue

Update the issue in IMPLEMENTATION_PLAN.md with your findings:

```
- **[NEEDS_DECISION]** Title: Root cause explanation.
  - **Option A**: [approach] - Pros: ... Cons: ...
  - **Option B**: [approach] - Pros: ... Cons: ...
  - **Recommendation**: [which option and why]
```

If only one clear fix exists, you may mark it `**[RESOLVED]**` and implement it.

## Output Signal (required)

```
[RALPH] ISSUE_DOCUMENTED ISSUE-N
```
Options documented, waiting for user decision.

```
[RALPH] ISSUE_RESOLVED ISSUE-N
```
Clear fix existed, implemented and tested.

```
[RALPH] ISSUE_WONTFIX ISSUE-N
```
Not a real blocker / intentionally not fixing. Explain why.

## Critical Rules

- **Research first, document options** - Don't jump to implementation
- If multiple valid approaches exist, document them and let user decide
- If you discover NEW bugs, document them as new issues
- DO NOT work around bugs - fix them or document them
- Use `timeout 60` for commands that might hang
