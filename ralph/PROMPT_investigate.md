# INVESTIGATE Stage

An issue was discovered during build. Research and resolve it.

## Step 1: Get Issue

Run `ralph query` to see current state. The `next.item` shows the issue description.

## Step 2: Research

Investigate thoroughly:
1. Read relevant code
2. Run tests to understand the failure
3. Check git history if relevant
4. Understand root cause before acting

## Step 3: Resolve

Choose ONE approach:

### Option A: Create a fix task

If the fix is non-trivial:
```
ralph task add '{"name": "fix for issue", "notes": "root cause analysis", "accept": "how to verify fix"}'
ralph issue done
```

### Option B: Fix directly

If the fix is trivial (typo, simple bug):
1. Make the fix
2. Run tests to verify
3. Mark resolved:
```
ralph issue done
```

### Option C: Out of scope

If the issue is outside the current spec's scope:
```
ralph issue done
```
Note in the commit message why it's being deferred.

## Progress Reporting

```
[RALPH] === INVESTIGATE: <issue description> ===
[RALPH] Root cause: <what you found>
[RALPH] Resolution: <what you're doing about it>
```

## EXIT after resolving the issue
