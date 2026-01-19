Follow all rules from AGENTS.md (prepended above). This prompt adds planning workflow.

## Setup

1. Run `git branch --show-current`
2. Read `ralph/specs/*` for requirements
3. Read current codebase to understand what exists

## Research (when needed)

Use web search to:
- Find best practices for unfamiliar patterns
- Check library/API documentation
- Research architectural approaches
- Understand error messages or edge cases

Do NOT use web search for:
- Project-specific code questions (use codebase search instead)
- Things you already know confidently

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

(Issue IDs like ISSUE-1, ISSUE-2 are auto-assigned by ralph - don't add them manually)

- **[OPEN]** Title: description (or no status marker = OPEN)
- **[BLOCKED]** Title: known blocker, needs investigation
- **[NEEDS_DECISION]** Title: options documented, waiting for user
  - **Option A**: approach - Pros/Cons
  - **Option B**: approach - Pros/Cons
- **[RESOLVED]** Title: fixed
- **[WONTFIX]** Title: intentionally not fixing
```

## Issue Status Rules

- Preserve existing issues and their statuses
- OPEN/BLOCKED: Build loop will investigate and either fix or document options
- NEEDS_DECISION: Waiting for user to choose (build skips these)
- RESOLVED/WONTFIX: Done (build skips these)

## Rules

- Each task completable in ONE iteration
- Order by priority
- Be specific - "Add X to Y" not "Improve Z"
