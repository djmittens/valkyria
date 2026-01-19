0a. Run `git branch --show-current` to identify the current branch.
0b. List files in `ralph/specs/` to see active specifications.
0c. Study the source code to understand the current implementation.

## Task: Gap Analysis

Compare specs against the CURRENT codebase and generate a fresh task list:

1. Use subagents to study each spec file and relevant source code
2. For each spec requirement, check if it's already implemented
3. Create tasks ONLY for what's missing or broken
4. DO NOT implement anything - planning only

## Spec Lifecycle

Specs in `ralph/specs/` are ACTIVE work. When fully implemented, they get deleted (git preserves history).

If `ralph/specs/` is empty:
- Output: `[RALPH] ALL_SPECS_COMPLETE`
- EXIT immediately - nothing to plan

## Updating an Existing Plan

The plan is disposable - regenerate it based on current reality, not the old plan.

If @ralph/IMPLEMENTATION_PLAN.md exists:
- IGNORE the old pending tasks (they may be stale)
- KEEP the "## Completed" section as historical record  
- KEEP the "## Discovered Issues" section
- Generate NEW pending tasks from fresh gap analysis

## Output

Write @ralph/IMPLEMENTATION_PLAN.md with:

```markdown
# Implementation Plan

**Branch:** `<current branch>`
**Last updated:** <timestamp>

## Spec: <spec-filename.md>

- [ ] Task 1 for this spec
- [ ] Task 2 for this spec

## Spec: <another-spec.md>

- [ ] Task 1 for another spec

## Completed

- [x] Previous completed tasks (preserve from old plan)

## Discovered Issues

- Issues found during implementation (preserve from old plan)
```

Rules:
- Each task should be completable in ONE iteration
- Order by priority (most important first)
- Be specific - "Add X to Y" not "Improve Z"
- Group tasks under their source spec using `## Spec: <filename>`
- Only create sections for specs that exist in `ralph/specs/`
