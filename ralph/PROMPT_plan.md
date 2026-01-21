## Target Spec: {{SPEC_FILE}}

1. Run `ralph query` to see current state
2. Read the spec file: `ralph/specs/{{SPEC_FILE}}`

## CRITICAL: Use Subagents for Research

Your context window is LIMITED. Do NOT read many files yourself.

**Launch subagents in parallel to research different aspects:**

```
Task: "Research how [aspect] is currently implemented. Find relevant files, understand the patterns used, and report back what exists and what's missing for [spec requirement]"
```

Launch multiple Task calls in a single message to parallelize research.

## Task: Gap Analysis for {{SPEC_FILE}}

Compare the spec against the CURRENT codebase and generate a task list:

1. Use subagents to study the spec and relevant source code thoroughly
2. For each requirement in the spec, check if it's already implemented
3. Create tasks ONLY for what's missing or broken
4. DO NOT implement anything - planning only

## Output

For each task identified, run:
```
ralph task add '{"name": "Short task name", "notes": "Implementation details", "accept": "How to verify", "deps": ["t-xxxx"]}'
```

Task fields:
- `name` (required): Short description of what to do (e.g., "Add unit tests for parser")
- `notes` (required): Implementation details - what files to modify, what approach to take, relevant context
- `accept` (required): **MEASURABLE** acceptance criteria - MUST specify concrete verification steps
- `deps` (optional): List of task IDs this task depends on

**CRITICAL: Acceptance criteria MUST be measurable and specific.**

Good `accept` examples:
- "pytest tests/test_parser.py passes"
- "`make build` exits with code 0"
- "file test/test_foo.valk exists and `make test` passes"
- "grep -c 'aio/within' src/builtins.c returns 1"
- "output contains 'Success' when running `./build/valk test.valk`"

Bad `accept` examples (WILL BE REJECTED):
- "works correctly" - too vague
- "tests pass" - which tests?
- "is implemented" - not measurable
- "feature works" - how do you verify?

**IMPORTANT**: Every task MUST have `notes` with implementation guidance. Tasks without `notes` will fail during BUILD.

The command returns the new task ID (e.g., "Task added: t-1a2b - ..."). Use this ID when other tasks depend on it.

Rules:
- Each task should be completable in ONE iteration
- Add tasks in dependency order - add prerequisite tasks first so you have their IDs
- Be specific - "Add X to Y" not "Improve Z"
- Tasks are for {{SPEC_FILE}} only
- `accept` MUST be measurable (command to run, expected output, exit code)
- Use `deps` when a task requires another task to be done first

When done adding tasks, output:
```
[RALPH] PLAN_COMPLETE: Added N tasks for {{SPEC_FILE}}
```
