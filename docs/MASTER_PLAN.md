# Valkyria Master Plan

## Quick Status
- **Current**: Phase 0 (Critical Infrastructure) - NEW BLOCKER
- **Next Task**: Tail Call Optimization (0.1)
- **Blocker**: Can't do async HTTP handlers without TCO & async/await
- **Target**: Phase 0 (3 weeks) → Phase 1 (2 weeks) → Validation (6 weeks)

## The Plan

### Now → 3 Weeks: Phase 0 - Critical Infrastructure
1. Tail call optimization (1 week) - BLOCKING
2. Async/await in Lisp (1 week) - BLOCKING
3. Promise composition (3 days)
4. Testing & validation (4 days)

### Weeks 4-5: Complete Phase 1 (With Async)
1. Async server handlers (3 days)
2. Test framework (2 days)
3. REPL safety (2 days)
4. HTTP helpers (1 day)
5. Documentation (1 day)

### Weeks 4-8: Validation Project (PICK ONE)
- **Game**: Pong/Tetris with hot reload
- **CI**: Build system for real projects
- **Web**: API server under load

### After Validation
- Phase 2: Type System (2 months)
- Phase 3: Protocols (1 month)
- Phase 5: Rich REPL (1 month)
- Phase 6: Embed everywhere (2 months)
- Phase 7: Self-host (6 months)

## Implementation Guide

**Primary Document**: [`IMPLEMENTATION_CHECKLIST.md`](IMPLEMENTATION_CHECKLIST.md)
- Detailed task lists with checkboxes
- Validation criteria for each task
- Session handoff instructions

**Architecture Docs** (reference only):
- [`TECHNICAL_ROADMAP_WIKI.md`](TECHNICAL_ROADMAP_WIKI.md) - Full vision
- [`ARCHITECTURE_OVERVIEW.md`](ARCHITECTURE_OVERVIEW.md) - System design

## Work Assignment

### For Next Session

Open IMPLEMENTATION_CHECKLIST.md and:
1. Start with section 1.1 (Server Request Handler API)
2. Check off completed items
3. Run validation tests
4. Move to next unchecked item

### For Agents

```
Task: Implement [section number] from IMPLEMENTATION_CHECKLIST.md
Context: [paste current section]
Validate: [paste validation section]
```

## Key Files to Edit

| Task | Files to Modify |
|------|----------------|
| 1.1 Server Handlers | `src/aio_uv.c`, `src/parser.c` |
| 1.2 Test Framework | `src/prelude_test.valk` (create) |
| 1.3 REPL Safety | `src/repl.c`, `src/vm.c` |
| 1.4 HTTP Helpers | `src/prelude.valk` |

## Validation Requirements

### Task Complete When
- Code compiles (`make build`)
- Tests pass (`make test`)
- Validation code works in REPL
- No memory leaks (ASAN clean)

### Phase Complete When
- All checkboxes marked
- Integration test passes
- Performance acceptable (<200μs for simple ops)
- Can build 1000+ line program

## Current TODOs in Code

Run `make todo` to see current TODOs.
High priority ones for Phase 1:
- `src/aio_ssl.c`: SSL error strings
- `src/aio_uv.c`: Buffer lifetime issues
- `test/test_networking.c`: Connection cleanup

---

**Remember**: Nothing is production-ready until validated by a real application!