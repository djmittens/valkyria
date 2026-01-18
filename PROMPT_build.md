0a. Study `specs/*` with parallel subagents to learn the project specifications.
0b. Study @IMPLEMENTATION_PLAN.md.
0c. For reference, the C runtime is in `src/*.c` and `src/*.h`, tests in `test/`.

1. Your task is to implement functionality per the specifications using parallel subagents. Follow @IMPLEMENTATION_PLAN.md and choose the most important item to address. Before making changes, search the codebase (don't assume not implemented) using subagents.
2. After implementing functionality or resolving problems, run `make build && make test` to validate. If functionality is missing then it's your job to add it as per the specifications. Ultrathink.
3. When you discover issues, immediately update @IMPLEMENTATION_PLAN.md with your findings. When resolved, update and remove the item.
4. When the tests pass, update @IMPLEMENTATION_PLAN.md, then `git add -A` then `git commit` with a message describing the changes. After the commit, `git push`.

## Progress Reporting

After EACH significant action, print a status line:
```
[RALPH] ACTION: <what you just did>
[RALPH] STATUS: <current state - building/testing/passing/failing>
[RALPH] NEXT: <what you will do next>
```

When starting a task:
```
[RALPH] === STARTING TASK: <task name from plan> ===
[RALPH] FILE: <primary file being worked on>
[RALPH] GOAL: <what success looks like>
```

When finishing a task:
```
[RALPH] === COMPLETED: <task name> ===
[RALPH] RESULT: <pass/fail and brief summary>
[RALPH] COVERAGE: <if relevant, coverage delta>
```

## Issue Handling - CRITICAL

When you encounter a problem (test failure, build error, unexpected behavior):

1. **STOP and DOCUMENT FIRST** - Add the issue to @IMPLEMENTATION_PLAN.md under a new section "## Discovered Issues" with:
   - File and line number
   - What you expected vs what happened
   - Root cause if known
   - Suggested fix

2. **DO NOT WORK AROUND** - Never:
   - Skip a failing test
   - Add LCOV exclusions to hide coverage gaps
   - Comment out problematic code
   - Add defensive checks that mask the real bug

3. **FIX SYSTEMATICALLY** - Either:
   - Fix the root cause properly, OR
   - Document it fully and move to next task if fix is too large

4. **If stuck for >5 minutes on same issue**: Document what you tried, mark as blocked, move on.

99999. Important: When authoring documentation, capture the why — tests and implementation importance.
999999. Important: Single sources of truth, no migrations/adapters. If tests unrelated to your work fail, resolve them as part of the increment.
9999999. Run `make lint` before committing. All lint errors must be fixed.
99999999. You may add extra logging if required to debug issues.
999999999. Keep @IMPLEMENTATION_PLAN.md current with learnings — future work depends on this to avoid duplicating efforts. Update especially after finishing your turn.
9999999999. When you learn something new about how to run the application, update @AGENTS.md but keep it brief.
99999999999. For any bugs you notice, resolve them or document them in @IMPLEMENTATION_PLAN.md even if unrelated to current work.
999999999999. Implement functionality completely. Placeholders and stubs waste efforts and time redoing the same work.
9999999999999. When @IMPLEMENTATION_PLAN.md becomes large, periodically clean out completed items.
99999999999999. DO NOT add comments to code unless explicitly asked.
999999999999999. IMPORTANT: Keep @AGENTS.md operational only — status updates belong in IMPLEMENTATION_PLAN.md.
