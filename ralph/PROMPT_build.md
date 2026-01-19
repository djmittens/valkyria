0a. Run `git branch --show-current` to identify the current branch.
0b. Study @ralph/IMPLEMENTATION_PLAN.md for current task list.
0c. List files in `ralph/specs/` to see active specifications.

## Branch Awareness

IMPORTANT: Check the **Branch:** field in @ralph/IMPLEMENTATION_PLAN.md.
- If it matches current branch, continue with tasks.
- If it doesn't match, the plan is from different work - proceed carefully or run `ralph plan` first.

## Termination Check

If `ralph/specs/` is empty (no spec files):
- Output: `[RALPH] ALL_SPECS_COMPLETE`
- EXIT immediately - all work is done

If @ralph/IMPLEMENTATION_PLAN.md has no pending tasks (no `- [ ]` items):
- Output: `[RALPH] ALL_SPECS_COMPLETE`
- EXIT immediately

## CRITICAL: ONE TASK, THEN EXIT

1. Pick ONE incomplete `- [ ]` item from @ralph/IMPLEMENTATION_PLAN.md
2. Identify which `## Spec:` section the task belongs to
3. Read ONLY that specific spec file from `ralph/specs/`
4. Implement the task (search codebase first - don't assume not implemented)
5. Run tests to validate the functionality
6. Update @ralph/IMPLEMENTATION_PLAN.md:
   - Mark task complete: `- [x]`
   - Update **Last updated:** timestamp
7. `git add -A && git commit && git push`

## Spec Completion Check

After marking a task complete, check if ALL tasks under that spec's `## Spec:` section are now `[x]`.

If ALL tasks for a spec are complete:
1. **VALIDATE**: Re-read the spec file and verify ALL requirements/acceptance criteria are met
2. If validation PASSES:
   - Delete the spec file: `rm ralph/specs/<filename>.md`
   - Move completed tasks to "## Completed" section
   - Output: `[RALPH] SPEC_COMPLETE: <filename>.md`
   - `git add -A && git commit -m "spec complete: <filename>" && git push`
3. If validation FAILS:
   - Add new tasks to the spec's section for missing requirements
   - Document gaps in "## Discovered Issues"
   - Output: `[RALPH] SPEC_INCOMPLETE: <filename>.md - <reason>`

**EXIT** after completing ONE task (and any spec validation).

## Progress Reporting

```
[RALPH] BRANCH: <current branch>
[RALPH] SPEC: <spec-filename.md>
[RALPH] === START: <task> ===
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

- ONE task, then EXIT (the loop restarts you fresh)
- Complete implementations only, no stubs
- No comments in code unless explicitly requested
- Validate spec completion thoroughly before archiving
