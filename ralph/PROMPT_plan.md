Follow all rules from AGENTS.md (prepended above). This prompt adds planning workflow.

## Setup

1. Run `git branch --show-current`
2. Read `ralph/specs/*` for requirements
3. Read current codebase to understand what exists

## Task: Gap Analysis

Compare specs against CURRENT codebase. Create tasks ONLY for what's missing or broken.

DO NOT implement anything - planning only.

## Updating Existing Plan

If @ralph/IMPLEMENTATION_PLAN.md exists:
- IGNORE old pending tasks (may be stale)
- KEEP "## Completed" section
- KEEP "## Discovered Issues" section
- Generate NEW pending tasks from fresh analysis

## Output Format

Write @ralph/IMPLEMENTATION_PLAN.md:

```markdown
# Implementation Plan

**Branch:** `<branch>`
**Last updated:** <timestamp>

## Spec: <spec-file.md>

## Pending Tasks

- [ ] Task 1 (highest priority)
- [ ] Task 2

## Completed

- [x] Previous tasks (preserve)

## Discovered Issues

- [ISSUE-N] Title: description, reproduction steps, what was tried
```

## Rules

- Each task completable in ONE iteration
- Order by priority
- Be specific - "Add X to Y" not "Improve Z"
