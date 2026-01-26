# VERIFY Stage

Verify that done tasks meet their acceptance criteria.

## Step 1: Get State

Run `ralph query` to get:
- `spec`: the current spec name
- `tasks.done`: list of done tasks with their acceptance criteria

## Step 2: Run Shared Tests ONCE (if needed)

If ANY task's acceptance criteria mentions `make test`, `make build`, or running the test suite:

```bash
mkdir -p build/logs
make build > build/logs/build.log 2>&1 && make test > build/logs/test.log 2>&1
echo "Exit code: $?"
```

**Run this ONCE.** Only check exit code - do NOT read the log files unless tests fail.

**If tests fail**: Read the LAST 50 lines of `build/logs/test.log` to diagnose. Do NOT read the entire log.

### Timeout/Hang Failures - ESCALATE, DON'T RETRY

If tests **timeout or hang** (no clear error, just stops):

1. **Do NOT guess at fixes** - async bugs require execution traces
2. **Capture with rr**:
   ```bash
   timeout 120 rr record --chaos build/test_<name> 2>&1 || true
   ```
3. **Create issue and skip**:
   ```
   ralph issue add "Test <name> hangs. rr recording at ~/.local/share/rr/. Needs human debugging."
   ```

Signs to escalate immediately: timeout with no error, intermittent failures, TSAN races.

## Step 3: Verify Each Done Task

For each done task, check its `accept` criteria:

**Simple criteria** (grep, file exists, specific command): Run directly, no subagent needed.

**Complex criteria** (requires code analysis): Spawn a subagent:
```
Task: "Verify task '{task.name}' meets: {task.accept}
1. Find the implementation
2. Check acceptance criteria
Return JSON: {\"task_id\": \"...\", \"passed\": true|false, \"evidence\": \"...\", \"reason\": \"...\"}"
```

**Test-dependent criteria**: Use the shared test result from Step 2. Do NOT re-run tests.

## Step 4: Apply Results

**Passed** -> `ralph task accept <task-id>`

**Failed** -> Choose one:
- Implementation bug: `ralph task reject <task-id> "<reason>"`
- Architectural blocker: `ralph issue add "..."` then `ralph task delete <task-id>`

Signs of architectural blocker:
- Same rejection reason recurring
- Requires changes outside this spec's scope

## Step 5: Check Spec Acceptance Criteria (Unchecked Only)

Read the spec's **Acceptance Criteria section only**: `ralph/specs/<spec-name>`

**SKIP checked criteria** (`- [x]`) - these were verified when checked. Do NOT re-verify them.

**For unchecked criteria** (`- [ ]`):
- If covered by a pending/done task: skip (will be verified when task completes)
- If NOT covered by any task: create a task for it:
  ```
  ralph task add '{"name": "...", "notes": "<file paths + approach>", "accept": "..."}'
  ```

## Step 6: Final Decision

All tasks accepted, no new tasks needed:
```
[RALPH] SPEC_COMPLETE
```

Otherwise:
```
[RALPH] SPEC_INCOMPLETE: <summary>
```
