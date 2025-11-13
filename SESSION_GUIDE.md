# Session-to-Session Work Guide

## Starting a New Session

### Step 1: Check Status
```bash
# See what's implemented
grep -n "\[x\]" docs/IMPLEMENTATION_CHECKLIST.md | head -10

# See what's next
grep -n "\[ \]" docs/IMPLEMENTATION_CHECKLIST.md | head -5

# Check for blockers
grep -n "BLOCKED" docs/IMPLEMENTATION_CHECKLIST.md
```

### Step 2: Pick Up Work
1. Open `docs/IMPLEMENTATION_CHECKLIST.md`
2. Find the first unchecked item under current phase
3. That's your task

### Step 3: Tell the Agent/Assistant
```
"Continue Valkyria development from docs/IMPLEMENTATION_CHECKLIST.md
Current task: [section number and name]
Please implement the unchecked items in that section
Use the validation criteria to verify completion"
```

## For Specific Tasks

### Task 0.1: Tail Call Optimization (CURRENT BLOCKER)
```
"Implement Phase 0.1 Tail Call Optimization from IMPLEMENTATION_CHECKLIST.md
This involves modifying src/vm.c to detect and eliminate tail calls
The validation test should allow recursive functions with 100000+ calls without stack overflow"
```

### Task 0.2: Async/Await in Lisp
```
"Implement Phase 0.2 Async/Await from IMPLEMENTATION_CHECKLIST.md
Expose futures to Lisp with (await) and (async) support
The validation test should show non-blocking HTTP requests"
```

### Task 1.2: Test Framework
```
"Implement Phase 1.2 Lisp Test Framework from IMPLEMENTATION_CHECKLIST.md
Create src/prelude_test.valk with deftest, assert, and run-tests functions
Validate by writing and running a simple test"
```

### Task 1.3: REPL Safety
```
"Implement Phase 1.3 REPL Safety from IMPLEMENTATION_CHECKLIST.md
Add signal handlers and stack limits to prevent crashes
Validate that infinite recursion and division by zero don't crash REPL"
```

## Ending a Session

### Update the Checklist
```markdown
In docs/IMPLEMENTATION_CHECKLIST.md:
- [x] Mark completed items
- Add "BLOCKED: [reason]" if stuck
- Update "Owner" field to "Next session"
```

### Leave Notes
```markdown
At the bottom of IMPLEMENTATION_CHECKLIST.md:
**Last Session**: 2025-11-13
**Completed**: Items 1.1.1 through 1.1.3
**Blocked On**: Need to understand valk_lenv_put internals
**Next Step**: Continue with 1.1.4
```

## For Complex Multi-Session Tasks

### Using Agents for Research
```
"Explore the codebase to understand how HTTP/2 requests are handled
Focus on src/aio_uv.c function __http2_on_request_recv
Document the flow from request receipt to response send"
```

### Using Agents for Implementation
```
"Implement the validation test for Phase 1.1
The test should create an HTTP server in Lisp that responds with 'Hello'
Follow the pattern in test/test_networking_lisp.c"
```

## Quick Reference Card

| What You Need | Where It Is | Command |
|--------------|-------------|----------|
| Current task | IMPLEMENTATION_CHECKLIST.md | `grep -n "\[ \]" docs/IMPLEMENTATION_CHECKLIST.md \| head -1` |
| Test if working | Run validation code | `./build/valk test.valk` |
| Check compilation | Build project | `make build` |
| Run tests | Test suite | `make test` |
| Find TODOs | Code TODOs | `make todo` |
| Memory check | ASAN | `make asan` |

## Common Blockers & Solutions

| Blocker | Solution |
|---------|----------|
| "Don't understand X" | Use Task agent with Explore mode on that subsystem |
| "Tests failing" | Check test output, use debugger (`make debug`) |
| "Segfault" | Run with ASAN (`make asan`), check for NULL pointers |
| "Not sure if complete" | Run validation code from checklist |
| "Too complex for one session" | Break into subtasks, mark partially complete |

## Example Session Flow

```bash
# Start
$ grep -n "\[ \]" docs/IMPLEMENTATION_CHECKLIST.md | head -1
45:- [ ] Define request struct in Lisp

# Work
[Implement the feature]

# Test
$ make build
$ ./build/valk validation_test.valk

# Update
$ vi docs/IMPLEMENTATION_CHECKLIST.md
[Mark items complete]

# Commit
$ git add -A
$ git commit -m "Implement request struct for HTTP/2 handlers"
```

## Rules

1. **One phase at a time** - Don't jump ahead
2. **Validate everything** - Use the validation criteria
3. **Update checklist** - Mark items immediately when done
4. **Document blockers** - Help the next session
5. **Test before marking complete** - Must actually work

---

**Current Phase**: 0 (Critical Infrastructure)
**Next Task**: 0.1 Tail Call Optimization
**Files to Edit**: `src/vm.c`, `src/parser.c`
**Why Blocked**: Can't implement async HTTP handlers without TCO and async/await