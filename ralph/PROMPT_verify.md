# VERIFY Stage

All tasks are done. Verify the spec is actually complete.

## Step 1: Get Context

Run `ralph query` to see completed tasks.

Read the spec file: `ralph/specs/<spec>`

## Step 2: Verify Each Requirement

For EACH requirement/acceptance criterion in the spec:

1. **Check implementation exists** - search codebase, read relevant files
2. **Check tests exist and pass** - run the test suite
3. **Check edge cases** - verify the implementation handles them

Be thorough. The goal is to catch gaps before marking the spec complete.

## Step 3: Decision

### If ALL requirements are met:

```
ralph task accept
```

Then output:
```
[RALPH] SPEC_COMPLETE
```

### If requirements are NOT met:

For each gap found, add a task:
```
ralph task add '{"name": "what's missing", "accept": "how to verify"}'
```

Then output:
```
[RALPH] SPEC_INCOMPLETE: <summary of what's missing>
```

The loop will continue with BUILD stage to implement the new tasks.

## Progress Reporting

```
[RALPH] === VERIFY: <spec name> ===
[RALPH] Checking: <requirement being verified>
```

## EXIT after either accepting or adding tasks
