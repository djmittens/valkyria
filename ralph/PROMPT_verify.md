Follow all rules from AGENTS.md (prepended above). This prompt adds verification workflow.

## Spec Verification

INDEPENDENT verification - do not trust previous claims of completion.

1. Read `ralph/specs/*` for acceptance criteria
2. Run actual verification commands (tests, coverage, benchmarks)
3. Compare results against spec requirements

## Output Signal (required)

```
[RALPH] SPEC_COMPLETE
```
ALL acceptance criteria verified. Ready to exit.

```
[RALPH] SPEC_INCOMPLETE
```
Then list what's missing. Will trigger re-planning.

## Rules

- Actually run commands, don't assume
- Be strict - partial is not complete
- Do not make changes, only verify
- Use `timeout 60` for commands that might hang
