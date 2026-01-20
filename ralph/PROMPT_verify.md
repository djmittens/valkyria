# VERIFY Stage

All tasks are done. Verify they meet their acceptance criteria.

## Step 1: Get State

Run `ralph query` to get:
- `spec`: the current spec name (e.g., "construct-mode.md")
- `tasks.done`: list of done tasks with their acceptance criteria

## Step 2: Verify Done Tasks (MAX 5 PER ITERATION)

**IMPORTANT:** 
- Do NOT spawn subagents
- Verify **at most 5 tasks** per iteration
- **Sort by complexity - simplest first:**
  1. File existence checks (`test -f`) - instant
  2. Grep/code inspection - fast  
  3. Single commands (`make build`) - seconds
  4. Test runs - slower

For each task, verify based on `accept` criteria:

- "file exists" → `test -f <path>`
- "make X" → run `make X`
- "test passes" → run the test
- code changes → grep/read to confirm

## Step 3: Apply Results

For each verified task:

**If passed** → `ralph task accept <task-id>`

**If failed** → Choose one:

1. **Implementation bug** (can be fixed):
   `ralph task reject <task-id> "<reason>"`

2. **Architectural blocker** (cannot be done):
   `ralph issue add "Task <task-id> blocked: <why>"`
   `ralph task delete <task-id>`

## Step 4: Check Completion

After verifying up to 5 tasks:

- If more done tasks remain unverified:
  ```
  [RALPH] SPEC_INCOMPLETE: N tasks still need verification
  ```

- If all tasks verified and accepted, check spec acceptance criteria:
  Read `ralph/specs/<spec-name>` → "## Acceptance Criteria" section
  
  For any unchecked criteria (`- [ ]`) not covered by tasks:
  ```
  ralph task add '{"name": "...", "accept": "..."}\'
  ```

- If all tasks accepted AND no gaps:
  ```
  [RALPH] SPEC_COMPLETE
  ```
